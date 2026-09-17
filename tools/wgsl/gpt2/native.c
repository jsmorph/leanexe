/* Host bindings and schedule only. All numerical model operations, BPE, and
 * sampling execute in the Lean-generated Wasm and generated WGSL artifacts. */
#include <wasm.h>
#include <wasmtime.h>
#include "webgpu-headers/webgpu.h"
#include "wgpu.h"
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
#else
#include <openssl/sha.h>
#endif
#include "artifacts.h"

enum { F64=160000000, F32=161000000, WIDTH=768, CACHE_WORDS=196608 };
typedef struct { uint8_t *data; size_t size; } Bytes;
typedef struct { uint64_t *data; size_t size; } Words;
typedef struct { wasmtime_instance_t instance; wasmtime_memory_t memory; } Module;
typedef struct { wasm_engine_t *engine; wasmtime_store_t *store; wasmtime_context_t *ctx;
  Module model, tokenizer, transfer; Bytes table, params; } Runtime;
typedef struct { WGPUInstance instance; WGPUAdapter adapter; WGPUDevice device; WGPUQueue queue;
  WGPUComputePipeline pipelines[6]; WGPUBindGroup groups[50]; WGPUBuffer weights[50], a,c,read; } GPU;
static const size_t inner[6]={768,768,768,3072,768,768}, cols[6]={2304,768,3072,768,25129,25128};
static size_t shape(size_t matrix){return matrix<48?matrix%4:matrix-44;}
static void need(bool ok,const char *message){if(!ok){fprintf(stderr,"gpt2: %s\n",message);exit(1);}}
static void checked(wasmtime_error_t *error,wasm_trap_t *trap){
  if(error){wasm_name_t t;wasmtime_error_message(error,&t);fprintf(stderr,"%.*s\n",(int)t.size,t.data);wasm_name_delete(&t);wasmtime_error_delete(error);exit(1);}
  if(trap){wasm_message_t t;wasm_trap_message(trap,&t);fprintf(stderr,"%.*s\n",(int)t.size,t.data);wasm_name_delete(&t);wasm_trap_delete(trap);exit(1);}
}
static void *allocate(size_t n){void *p=calloc(n?n:1,1);need(p!=NULL,"allocation");return p;}
static Bytes artifact(const char *directory,const char *name){
  size_t index=0;for(;index<ARTIFACT_COUNT;index++)if(!strcmp(name,artifact_names[index]))break;
  need(index<ARTIFACT_COUNT,"artifact absent from build manifest");char path[4096];
  need(snprintf(path,sizeof path,"%s/%s",directory,name)<(int)sizeof path,"artifact path");
  FILE *f=fopen(path,"rb");need(f!=NULL,"cannot open artifact");need(!fseek(f,0,SEEK_END),"seek");long n=ftell(f);
  need(n>0&&(size_t)n==artifact_sizes[index],"artifact size differs from this build");rewind(f);
  Bytes b={allocate((size_t)n+1),(size_t)n};need(fread(b.data,1,b.size,f)==b.size,"read artifact");fclose(f);
  unsigned char hash[32];
#ifdef __APPLE__
  CC_SHA256(b.data,(CC_LONG)b.size,hash);
#else
  SHA256(b.data,b.size,hash);
#endif
  char text[65];for(size_t i=0;i<32;i++)snprintf(text+2*i,3,"%02x",hash[i]);
  need(!strcmp(text,artifact_hashes[index]),"artifact SHA-256 differs from this build");return b;
}
static wasmtime_extern_t get(Runtime *r,Module *m,const char *name,wasmtime_extern_kind_t kind){
  wasmtime_extern_t x;need(wasmtime_instance_export_get(r->ctx,&m->instance,name,strlen(name),&x),"missing Wasm export");need(x.kind==kind,"Wasm export type");return x;
}
static void instantiate(Runtime *r,Module *m,const char *dir,const char *name){
  Bytes b=artifact(dir,name);wasmtime_module_t *module=NULL;checked(wasmtime_module_new(r->engine,b.data,b.size,&module),NULL);free(b.data);
  wasm_trap_t *trap=NULL;wasmtime_error_t *e=wasmtime_instance_new(r->ctx,module,NULL,0,&m->instance,&trap);checked(e,trap);wasmtime_module_delete(module);
  m->memory=get(r,m,"memory",WASMTIME_EXTERN_MEMORY).of.memory;
}
static uint64_t invoke(Runtime *r,Module *m,const char *name,const uint64_t *arguments,size_t n,bool result){
  need(n<=5,"Wasm arity");wasmtime_func_t fn=get(r,m,name,WASMTIME_EXTERN_FUNC).of.func;wasmtime_val_t a[5]={0},b={0};
  for(size_t i=0;i<n;i++){a[i].kind=WASMTIME_I64;memcpy(&a[i].of.i64,arguments+i,8);}
  wasm_trap_t *trap=NULL;wasmtime_error_t *e=wasmtime_func_call(r->ctx,&fn,a,n,&b,result?1:0,&trap);checked(e,trap);
  if(!result)return 0;need(b.kind==WASMTIME_I64,"Wasm result type");uint64_t word;memcpy(&word,&b.of.i64,8);return word;
}
static uint8_t *region(Runtime *r,Module *m,uint64_t start,size_t n){
  size_t size=wasmtime_memory_data_size(r->ctx,&m->memory);need(start<=size&&n<=size-start,"Wasm memory bounds");return wasmtime_memory_data(r->ctx,&m->memory)+start;
}
static uint64_t array(Runtime *r,Module *m,Words words){
  uint64_t size=8+8*words.size,pointer=invoke(r,m,"alloc",&size,1,true),length=words.size;
  uint8_t *p=region(r,m,pointer,(size_t)size);memcpy(p,&length,8);if(words.size)memcpy(p+8,words.data,8*words.size);return pointer;
}
static Words result_array(Runtime *r,Module *m,uint64_t p,size_t maximum){
  uint64_t n;memcpy(&n,region(r,m,p,8),8);need(n<=maximum,"unexpected Wasm result length");
  Words result={allocate(n*8),(size_t)n};memcpy(result.data,region(r,m,p+8,n*8),n*8);return result;
}
static void reset(Runtime *r,Module *m){checked(wasmtime_context_set_fuel(r->ctx,2000000000),NULL);invoke(r,m,"reset",NULL,0,false);}
static Words compute(Runtime *r,uint64_t op,Words x,Words aux,Words params,size_t position,size_t expected){
  reset(r,&r->model);uint64_t a[5]={op,array(r,&r->model,x),array(r,&r->model,aux),array(r,&r->model,params),position};
  Words result=result_array(r,&r->model,invoke(r,&r->model,"compute",a,5,true),expected);
  need(result.size==expected,"model rejected stage inputs");return result;
}
static Words tokenize(Runtime *r,uint64_t op,Words input){
  reset(r,&r->tokenizer);uint64_t a[3]={op,array(r,&r->tokenizer,(Words){(uint64_t *)r->table.data,r->table.size/8}),array(r,&r->tokenizer,input)};
  return result_array(r,&r->tokenizer,invoke(r,&r->tokenizer,"tokens",a,3,true),65536);
}
static Words parameter(Runtime *r,size_t offset,size_t n){need((offset+n)*8<=r->params.size,"parameter bounds");return (Words){(uint64_t *)r->params.data+offset,n};}
static Words embedding(Runtime *r,size_t index,uint64_t kind){
  uint64_t a[2]={index,kind};invoke(r,&r->transfer,"embedding",a,2,false);Words w={allocate(768*8),768};memcpy(w.data,region(r,&r->transfer,F64,768*8),768*8);return w;
}
static void init_runtime(Runtime *r,const char *dir){
  memset(r,0,sizeof *r);uint16_t endian=1;need(*(uint8_t *)&endian==1,"this host needs little-endian storage");
  wasm_config_t *config=wasm_config_new();wasmtime_config_consume_fuel_set(config,true);r->engine=wasm_engine_new_with_config(config);need(r->engine!=NULL,"Wasm engine");
  r->store=wasmtime_store_new(r->engine,NULL,NULL);need(r->store!=NULL,"Wasm store");wasmtime_store_limiter(r->store,384*1024*1024,10000,10,10,10);r->ctx=wasmtime_store_context(r->store);
  checked(wasmtime_context_set_fuel(r->ctx,2000000000),NULL);instantiate(r,&r->model,dir,"model.wasm");instantiate(r,&r->tokenizer,dir,"tokenizer.wasm");instantiate(r,&r->transfer,dir,"transfer.wasm");
  r->table=artifact(dir,"tokenizer.bin");r->params=artifact(dir,"params.bin");Bytes embeddings=artifact(dir,"embedding.bin");
  need(embeddings.size==154782720,"embedding size");memcpy(region(r,&r->transfer,0,embeddings.size),embeddings.data,embeddings.size);free(embeddings.data);
}
static void adapter_callback(WGPURequestAdapterStatus status,WGPUAdapter a,WGPUStringView message,void *user,void *unused){
  (void)unused;if(status!=WGPURequestAdapterStatus_Success)fprintf(stderr,"adapter: %.*s\n",(int)message.length,message.data);*(WGPUAdapter *)user=a;
}
static void device_callback(WGPURequestDeviceStatus status,WGPUDevice d,WGPUStringView message,void *user,void *unused){
  (void)unused;if(status!=WGPURequestDeviceStatus_Success)fprintf(stderr,"device: %.*s\n",(int)message.length,message.data);*(WGPUDevice *)user=d;
}
static void gpu_error(WGPUDevice const *device,WGPUErrorType type,WGPUStringView message,void *user,void *unused){
  (void)device;(void)type;(void)user;(void)unused;fprintf(stderr,"WebGPU: %.*s\n",(int)message.length,message.data);exit(1);
}
static void map_callback(WGPUMapAsyncStatus status,WGPUStringView message,void *user,void *unused){
  (void)unused;if(status!=WGPUMapAsyncStatus_Success)fprintf(stderr,"map: %.*s\n",(int)message.length,message.data);*(int *)user=status==WGPUMapAsyncStatus_Success?1:-1;
}
static WGPUBuffer buffer(GPU *g,size_t size,WGPUBufferUsage usage){WGPUBuffer b=wgpuDeviceCreateBuffer(g->device,&(WGPUBufferDescriptor){.size=size,.usage=usage});need(b!=NULL,"GPU buffer");return b;}
static void init_gpu(GPU *g,const char *dir){
  memset(g,0,sizeof *g);g->instance=wgpuCreateInstance(NULL);need(g->instance!=NULL,"WebGPU instance");
  wgpuInstanceRequestAdapter(g->instance,&(WGPURequestAdapterOptions){.featureLevel=WGPUFeatureLevel_Core,.backendType=WGPUBackendType_Vulkan,.forceFallbackAdapter=true},
    (WGPURequestAdapterCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=adapter_callback,.userdata1=&g->adapter});need(g->adapter!=NULL,"Vulkan CPU adapter unavailable");
  WGPUAdapterInfo info={0};wgpuAdapterGetInfo(g->adapter,&info);fprintf(stderr,"WebGPU: %.*s (%.*s), Vulkan\n",(int)info.device.length,info.device.data,(int)info.description.length,info.description.data);wgpuAdapterInfoFreeMembers(info);
  wgpuAdapterRequestDevice(g->adapter,&(WGPUDeviceDescriptor){.uncapturedErrorCallbackInfo={.callback=gpu_error}},
    (WGPURequestDeviceCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=device_callback,.userdata1=&g->device});need(g->device!=NULL,"WebGPU device");g->queue=wgpuDeviceGetQueue(g->device);
  g->a=buffer(g,3072*4,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);g->c=buffer(g,25129*4,WGPUBufferUsage_Storage|WGPUBufferUsage_CopySrc);g->read=buffer(g,25129*4,WGPUBufferUsage_MapRead|WGPUBufferUsage_CopyDst);
  for(size_t s=0;s<6;s++){
    char name[40];snprintf(name,sizeof name,"kernel-%zu.wgsl",s);Bytes shader=artifact(dir,name);
    WGPUShaderSourceWGSL source={.chain={.sType=WGPUSType_ShaderSourceWGSL},.code={(char *)shader.data,shader.size}};
    WGPUShaderModule module=wgpuDeviceCreateShaderModule(g->device,&(WGPUShaderModuleDescriptor){.nextInChain=&source.chain});need(module!=NULL,"WGSL module");
    g->pipelines[s]=wgpuDeviceCreateComputePipeline(g->device,&(WGPUComputePipelineDescriptor){.compute={.module=module,.entryPoint={"gemm_f32",WGPU_STRLEN}}});need(g->pipelines[s]!=NULL,"WGSL pipeline");wgpuShaderModuleRelease(module);free(shader.data);
  }
  for(size_t m=0;m<50;m++){
    char name[40];snprintf(name,sizeof name,"matrix-%02zu.bin",m);Bytes weight=artifact(dir,name);size_t s=shape(m);need(weight.size==4*inner[s]*cols[s],"matrix dimensions");
    g->weights[m]=buffer(g,weight.size,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);wgpuQueueWriteBuffer(g->queue,g->weights[m],0,weight.data,weight.size);free(weight.data);
    WGPUBindGroupLayout layout=wgpuComputePipelineGetBindGroupLayout(g->pipelines[s],0);
    WGPUBindGroupEntry entries[]={{.binding=0,.buffer=g->a,.size=4*inner[s]},{.binding=1,.buffer=g->weights[m],.size=4*inner[s]*cols[s]},{.binding=2,.buffer=g->c,.size=4*cols[s]}};
    g->groups[m]=wgpuDeviceCreateBindGroup(g->device,&(WGPUBindGroupDescriptor){.layout=layout,.entryCount=3,.entries=entries});need(g->groups[m]!=NULL,"GPU bindings");wgpuBindGroupLayoutRelease(layout);
  }
  wgpuDevicePoll(g->device,true,NULL);fprintf(stderr,"Loaded pretrained GPT-2; demo artifact proofs are incomplete.\n");
}
static Words dispatch(GPU *g,Runtime *r,size_t matrix,Words x){
  size_t s=shape(matrix),bytes=4*cols[s];need(x.size==inner[s],"matrix input shape");
  memcpy(region(r,&r->transfer,F64,x.size*8),x.data,x.size*8);uint64_t args[2]={0,x.size};invoke(r,&r->transfer,"convert",args,2,false);
  wgpuQueueWriteBuffer(g->queue,g->a,0,region(r,&r->transfer,F32,x.size*4),x.size*4);
  WGPUCommandEncoder encoder=wgpuDeviceCreateCommandEncoder(g->device,NULL);WGPUComputePassEncoder pass=wgpuCommandEncoderBeginComputePass(encoder,NULL);
  wgpuComputePassEncoderSetPipeline(pass,g->pipelines[s]);wgpuComputePassEncoderSetBindGroup(pass,0,g->groups[matrix],0,NULL);wgpuComputePassEncoderDispatchWorkgroups(pass,(uint32_t)((cols[s]+7)/8),1,1);wgpuComputePassEncoderEnd(pass);wgpuComputePassEncoderRelease(pass);
  wgpuCommandEncoderCopyBufferToBuffer(encoder,g->c,0,g->read,0,bytes);WGPUCommandBuffer command=wgpuCommandEncoderFinish(encoder,NULL);wgpuQueueSubmit(g->queue,1,&command);wgpuCommandBufferRelease(command);wgpuCommandEncoderRelease(encoder);
  int mapped=0;wgpuBufferMapAsync(g->read,WGPUMapMode_Read,0,bytes,(WGPUBufferMapCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=map_callback,.userdata1=&mapped});wgpuDevicePoll(g->device,true,NULL);need(mapped==1,"GPU readback failed");
  const void *data=wgpuBufferGetConstMappedRange(g->read,0,bytes);need(data!=NULL,"GPU mapped output");memcpy(region(r,&r->transfer,F32,bytes),data,bytes);wgpuBufferUnmap(g->read);
  args[0]=1;args[1]=cols[s];invoke(r,&r->transfer,"convert",args,2,false);Words out={allocate(cols[s]*8),cols[s]};memcpy(out.data,region(r,&r->transfer,F64,cols[s]*8),cols[s]*8);return out;
}
static Words forward(Runtime *r,GPU *g,Words *cache,size_t token,size_t position,bool head){
  Words empty={0},e=embedding(r,token,0),p=embedding(r,position,1),x=compute(r,0,e,p,empty,0,768);free(e.data);free(p.data);
  for(size_t layer=0;layer<12;layer++){
    size_t o=layer*9984;Words n=compute(r,1,x,empty,parameter(r,o,1536),0,768);
    Words qkv=dispatch(g,r,layer*4,n);free(n.data);
    Words attended=compute(r,2,qkv,cache[layer],parameter(r,o+1536,2304),position,2304);free(qkv.data);
    memcpy(cache[layer].data+position*768,attended.data,768*8);memcpy(cache[layer].data+128*768+position*768,attended.data+768,768*8);
    Words projected=dispatch(g,r,layer*4+1,(Words){attended.data+1536,768});free(attended.data);
    Words residual=compute(r,3,x,projected,parameter(r,o+3840,768),0,768);free(x.data);free(projected.data);x=residual;
    n=compute(r,1,x,empty,parameter(r,o+4608,1536),0,768);Words expanded=dispatch(g,r,layer*4+2,n);free(n.data);
    Words activated=compute(r,4,expanded,empty,parameter(r,o+6144,3072),0,3072);free(expanded.data);
    projected=dispatch(g,r,layer*4+3,activated);free(activated.data);
    residual=compute(r,3,x,projected,parameter(r,o+9216,768),0,768);free(x.data);free(projected.data);x=residual;
  }
  if(!head){free(x.data);return empty;}
  Words n=compute(r,1,x,empty,parameter(r,12*9984,1536),0,768);free(x.data);
  Words left=dispatch(g,r,48,n),right=dispatch(g,r,49,n);free(n.data);
  Words logits={allocate(50257*8),50257};memcpy(logits.data,left.data,left.size*8);memcpy(logits.data+left.size,right.data,right.size*8);free(left.data);free(right.data);return logits;
}
static size_t number(const char *s,size_t maximum){char *end=NULL;need(*s>='0'&&*s<='9',"invalid integer");unsigned long long n=strtoull(s,&end,10);need(end&&*end==0&&n<=maximum,"integer out of range");return (size_t)n;}
int main(int argc,char **argv){
  need(argc>=4,"usage: gpt2 BUNDLE --prompt TEXT [--generate 64] [--temperature 0|0.7|0.8|1] [--seed 42] [--logits FILE] [--tokenize TEXT]");
  const char *prompt=NULL,*logits_path=NULL,*trace_path=NULL;size_t count=64;uint64_t sampling[3]={0x3FE999999999999A,40,42};bool only_tokens=false;
  for(int i=2;i<argc;i++){
    need(i+1<argc,"missing option value");const char *option=argv[i],*v=argv[++i];
    if(!strcmp(option,"--prompt")||!strcmp(option,"--tokenize")){need(!prompt,"duplicate prompt");prompt=v;only_tokens=!strcmp(option,"--tokenize");}
    else if(!strcmp(option,"--generate")){count=number(v,127);need(count>0,"generate must be positive");}
    else if(!strcmp(option,"--seed")){sampling[2]=number(v,UINT32_MAX);need(sampling[2]>0,"seed must be positive");}
    else if(!strcmp(option,"--temperature")){
      if(!strcmp(v,"0"))sampling[0]=0;else if(!strcmp(v,"0.7"))sampling[0]=0x3FE6666666666666;
      else if(!strcmp(v,"0.8"))sampling[0]=0x3FE999999999999A;else if(!strcmp(v,"1"))sampling[0]=0x3FF0000000000000;else need(false,"temperature must be 0, 0.7, 0.8 or 1");
    }else if(!strcmp(option,"--logits")){need(!logits_path,"duplicate logits path");logits_path=v;}
    else if(!strcmp(option,"--trace")){need(!trace_path,"duplicate trace path");trace_path=v;}else need(false,"unknown option");
  }
  need(prompt&&strlen(prompt)>0&&strlen(prompt)<=16384,"prompt must contain 1..16384 UTF-8 bytes");Runtime r;init_runtime(&r,argv[1]);
  Words bytes={allocate(strlen(prompt)*8),strlen(prompt)};for(size_t i=0;i<bytes.size;i++)bytes.data[i]=(unsigned char)prompt[i];
  Words tokens=tokenize(&r,0,bytes);free(bytes.data);need(tokens.size>0,"empty tokenization");for(size_t i=0;i<tokens.size;i++)need(tokens.data[i]<50257,"invalid UTF-8 prompt");
  if(only_tokens){for(size_t i=0;i<tokens.size;i++)printf("%s%" PRIu64,i?",":"",tokens.data[i]);putchar('\n');return 0;}
  need(tokens.size+count<=128,"prompt plus requested output exceeds the 128-token demo context");
  GPU g;init_gpu(&g,argv[1]);Words cache[12];for(size_t i=0;i<12;i++)cache[i]=(Words){allocate(CACHE_WORDS*8),CACHE_WORDS};
  Words logits={0};for(size_t i=0;i<tokens.size;i++){logits=forward(&r,&g,cache,tokens.data[i],i,i+1==tokens.size);fprintf(stderr,"\rPrompt %zu/%zu",i+1,tokens.size);}fputc('\n',stderr);
  if(logits_path){FILE *f=fopen(logits_path,"wb");need(f!=NULL,"cannot write logits");need(fwrite(logits.data,8,logits.size,f)==logits.size,"write logits");fclose(f);}
  fwrite(prompt,1,strlen(prompt),stdout);fflush(stdout);
  FILE *trace=NULL;if(trace_path){trace=fopen(trace_path,"wb");need(trace!=NULL,"cannot write trace");}
  for(size_t step=0;step<count;step++){
    Words picked=compute(&r,5,logits,(Words){0},(Words){sampling,3},0,2);uint64_t token=picked.data[0];sampling[2]=picked.data[1];free(picked.data);need(token<50257,"sampled token range");
    if(trace){need(fwrite(&token,8,1,trace)==1&&fwrite(logits.data,8,logits.size,trace)==logits.size,"write trace");}
    free(logits.data);logits=(Words){0};if(token==50256)break;
    Words text=tokenize(&r,1,(Words){&token,1});for(size_t i=0;i<text.size;i++){need(text.data[i]<256,"decoded byte range");fputc((int)text.data[i],stdout);}free(text.data);fflush(stdout);
    if(step+1<count)logits=forward(&r,&g,cache,token,tokens.size+step,true);
  }
  putchar('\n');if(trace)fclose(trace);free(logits.data);free(tokens.data);for(size_t i=0;i<12;i++)free(cache[i].data);
  for(size_t i=0;i<50;i++){wgpuBindGroupRelease(g.groups[i]);wgpuBufferRelease(g.weights[i]);}for(size_t i=0;i<6;i++)wgpuComputePipelineRelease(g.pipelines[i]);
  wgpuBufferRelease(g.a);wgpuBufferRelease(g.c);wgpuBufferRelease(g.read);wgpuQueueRelease(g.queue);wgpuDeviceRelease(g.device);wgpuAdapterRelease(g.adapter);wgpuInstanceRelease(g.instance);
  free(r.table.data);free(r.params.data);wasmtime_store_delete(r.store);wasm_engine_delete(r.engine);return 0;
}
