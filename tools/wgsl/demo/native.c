/* Native artifact host: no implementation of transformer arithmetic here. */
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

enum { WEIGHT_BYTES=23872, A=24576, B=24640, C=28736, LOGITS=29760 };
typedef struct { uint8_t *data; size_t size; } Bytes;
typedef struct { wasm_engine_t *engine; wasmtime_store_t *store; wasmtime_context_t *ctx;
  wasmtime_instance_t hidden, finish, transfer; wasmtime_memory_t hm, tm; } Runtime;
typedef struct { WGPUInstance instance; WGPUAdapter adapter; WGPUDevice device; WGPUQueue queue;
  WGPUComputePipeline pipeline; WGPUBindGroup group; WGPUBuffer a,b,c,read; } GPU;
static void need(bool ok,const char *message){ if(!ok){fprintf(stderr,"gpt128: %s\n",message);exit(1);} }
static void checked(wasmtime_error_t *error,wasm_trap_t *trap){
  if(error){wasm_name_t text;wasmtime_error_message(error,&text);fprintf(stderr,"%.*s\n",(int)text.size,text.data);wasm_name_delete(&text);wasmtime_error_delete(error);exit(1);}
  if(trap){wasm_message_t text;wasm_trap_message(trap,&text);fprintf(stderr,"%.*s\n",(int)text.size,text.data);wasm_name_delete(&text);wasm_trap_delete(trap);exit(1);}
}
static Bytes read_file(const char *path){
  FILE *f=fopen(path,"rb");need(f!=NULL,"cannot open artifact");need(!fseek(f,0,SEEK_END),"seek");long n=ftell(f);need(n>0&&n<16*1024*1024,"artifact size");rewind(f);
  Bytes b={malloc((size_t)n+1),(size_t)n};need(b.data!=NULL,"allocation");need(fread(b.data,1,b.size,f)==b.size,"read");fclose(f);b.data[b.size]=0;return b;
}
static Bytes artifact(const char *dir,size_t index){
  char path[4096];need(snprintf(path,sizeof path,"%s/%s",dir,artifact_names[index])<(int)sizeof path,"path too long");Bytes b=read_file(path);unsigned char hash[32];
#ifdef __APPLE__
  CC_SHA256(b.data,(CC_LONG)b.size,hash);
#else
  SHA256(b.data,b.size,hash);
#endif
  char text[65];for(size_t i=0;i<32;i++)snprintf(text+2*i,3,"%02x",hash[i]);
  need(strcmp(text,artifact_hashes[index])==0,"artifact SHA-256 differs from this build");return b;
}
static wasmtime_extern_t get(Runtime *r,wasmtime_instance_t *instance,const char *name,wasmtime_extern_kind_t kind){
  wasmtime_extern_t item;need(wasmtime_instance_export_get(r->ctx,instance,name,strlen(name),&item),"missing Wasm export");need(item.kind==kind,"Wasm export type");return item;
}
static void instantiate(Runtime *r,Bytes bytes,wasmtime_instance_t *instance,const wasmtime_extern_t *imports,size_t n){
  wasmtime_module_t *module=NULL;checked(wasmtime_module_new(r->engine,bytes.data,bytes.size,&module),NULL);wasm_trap_t *trap=NULL;
  wasmtime_error_t *e=wasmtime_instance_new(r->ctx,module,imports,n,instance,&trap);checked(e,trap);wasmtime_module_delete(module);
}
static void invoke(Runtime *r,wasmtime_instance_t *instance,const char *name,const uint64_t *args,size_t n,uint64_t *result,size_t count,bool i32result){
  need(n<=4&&count<=4,"Wasm arity");wasmtime_func_t fn=get(r,instance,name,WASMTIME_EXTERN_FUNC).of.func;wasmtime_val_t a[4]={0},b[4]={0};
  for(size_t i=0;i<n;i++){a[i].kind=WASMTIME_I64;memcpy(&a[i].of.i64,args+i,8);}wasm_trap_t *trap=NULL;
  wasmtime_error_t *e=wasmtime_func_call(r->ctx,&fn,a,n,b,count,&trap);checked(e,trap);
  for(size_t i=0;i<count;i++){need(b[i].kind==(i32result?WASMTIME_I32:WASMTIME_I64),"Wasm result type");if(i32result)result[i]=(uint32_t)b[i].of.i32;else memcpy(result+i,&b[i].of.i64,8);}
}
static uint8_t *region(Runtime *r,wasmtime_memory_t *memory,uint64_t start,size_t n){
  size_t size=wasmtime_memory_data_size(r->ctx,memory);need(start<=size&&n<=size-start,"Wasm memory bounds");return wasmtime_memory_data(r->ctx,memory)+start;
}
static void put64(uint8_t *p,uint64_t n){for(size_t i=0;i<8;i++)p[i]=(uint8_t)(n>>(i*8));}
static uint64_t get_word(const uint8_t *p,size_t n){uint64_t w=0;for(size_t i=0;i<n;i++)w|=(uint64_t)p[i]<<(8*i);return w;}
static uint64_t array(Runtime *r,const uint8_t *data,size_t count,bool byte_tokens){
  uint64_t size=8+8*count,pointer;invoke(r,&r->hidden,"alloc",&size,1,&pointer,1,false);
  uint8_t *p=region(r,&r->hm,pointer,(size_t)size);put64(p,count);
  if(byte_tokens){for(size_t i=0;i<count;i++)put64(p+8+8*i,data[i]);}else memcpy(p+8,data,8*count);
  return pointer;
}
static void init_runtime(Runtime *r,Bytes *files){
  memset(r,0,sizeof *r);wasm_config_t *config=wasm_config_new();wasmtime_config_consume_fuel_set(config,true);r->engine=wasm_engine_new_with_config(config);need(r->engine!=NULL,"Wasm engine");
  r->store=wasmtime_store_new(r->engine,NULL,NULL);need(r->store!=NULL,"Wasm store");wasmtime_store_limiter(r->store,256*1024*1024,10000,10,10,10);r->ctx=wasmtime_store_context(r->store);
  checked(wasmtime_context_set_fuel(r->ctx,1000000000),NULL);
  instantiate(r,files[0],&r->hidden,NULL,0);instantiate(r,files[2],&r->finish,NULL,0);
  wasmtime_extern_t bias=get(r,&r->finish,"finish",WASMTIME_EXTERN_FUNC);instantiate(r,files[1],&r->transfer,&bias,1);
  r->hm=get(r,&r->hidden,"memory",WASMTIME_EXTERN_MEMORY).of.memory;r->tm=get(r,&r->transfer,"memory",WASMTIME_EXTERN_MEMORY).of.memory;
  memcpy(region(r,&r->tm,0,WEIGHT_BYTES),files[4].data,WEIGHT_BYTES);invoke(r,&r->transfer,"weights",NULL,0,NULL,0,false);
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
static void init_gpu(GPU *g,Bytes shader,Runtime *r){
  memset(g,0,sizeof *g);g->instance=wgpuCreateInstance(NULL);need(g->instance!=NULL,"WebGPU instance");
  wgpuInstanceRequestAdapter(g->instance,&(WGPURequestAdapterOptions){.featureLevel=WGPUFeatureLevel_Core,.backendType=WGPUBackendType_Vulkan,.forceFallbackAdapter=true},
    (WGPURequestAdapterCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=adapter_callback,.userdata1=&g->adapter});
  need(g->adapter!=NULL,"Vulkan CPU adapter unavailable");
  WGPUAdapterInfo info={0};wgpuAdapterGetInfo(g->adapter,&info);fprintf(stderr,"WebGPU: %.*s (%.*s), Vulkan\n",(int)info.device.length,info.device.data,(int)info.description.length,info.description.data);wgpuAdapterInfoFreeMembers(info);
  wgpuAdapterRequestDevice(g->adapter,&(WGPUDeviceDescriptor){.uncapturedErrorCallbackInfo={.callback=gpu_error}},
    (WGPURequestDeviceCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=device_callback,.userdata1=&g->device});need(g->device!=NULL,"WebGPU device");g->queue=wgpuDeviceGetQueue(g->device);
  WGPUShaderSourceWGSL source={.chain={.sType=WGPUSType_ShaderSourceWGSL},.code={(char *)shader.data,shader.size}};
  WGPUShaderModule module=wgpuDeviceCreateShaderModule(g->device,&(WGPUShaderModuleDescriptor){.nextInChain=&source.chain});need(module!=NULL,"WGSL module");
  g->pipeline=wgpuDeviceCreateComputePipeline(g->device,&(WGPUComputePipelineDescriptor){.compute={.module=module,.entryPoint={"gemm_f32",WGPU_STRLEN}}});need(g->pipeline!=NULL,"WGSL compute pipeline");wgpuShaderModuleRelease(module);
  g->a=buffer(g,16,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);g->b=buffer(g,4096,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);
  g->c=buffer(g,1024,WGPUBufferUsage_Storage|WGPUBufferUsage_CopySrc);g->read=buffer(g,1024,WGPUBufferUsage_MapRead|WGPUBufferUsage_CopyDst);
  WGPUBindGroupLayout layout=wgpuComputePipelineGetBindGroupLayout(g->pipeline,0);
  WGPUBindGroupEntry entries[]={{.binding=0,.buffer=g->a,.size=16},{.binding=1,.buffer=g->b,.size=4096},{.binding=2,.buffer=g->c,.size=1024}};
  g->group=wgpuDeviceCreateBindGroup(g->device,&(WGPUBindGroupDescriptor){.layout=layout,.entryCount=3,.entries=entries});need(g->group!=NULL,"GPU bindings");wgpuBindGroupLayoutRelease(layout);
  wgpuQueueWriteBuffer(g->queue,g->b,0,region(r,&r->tm,B,4096),4096);
}
static void dispatch(GPU *g,Runtime *r){
  wgpuQueueWriteBuffer(g->queue,g->a,0,region(r,&r->tm,A,16),16);
  WGPUCommandEncoder encoder=wgpuDeviceCreateCommandEncoder(g->device,NULL);need(encoder!=NULL,"command encoder");
  WGPUComputePassEncoder pass=wgpuCommandEncoderBeginComputePass(encoder,NULL);wgpuComputePassEncoderSetPipeline(pass,g->pipeline);wgpuComputePassEncoderSetBindGroup(pass,0,g->group,0,NULL);wgpuComputePassEncoderDispatchWorkgroups(pass,32,1,1);wgpuComputePassEncoderEnd(pass);wgpuComputePassEncoderRelease(pass);
  wgpuCommandEncoderCopyBufferToBuffer(encoder,g->c,0,g->read,0,1024);WGPUCommandBuffer command=wgpuCommandEncoderFinish(encoder,NULL);wgpuQueueSubmit(g->queue,1,&command);wgpuCommandBufferRelease(command);wgpuCommandEncoderRelease(encoder);
  int mapped=0;wgpuBufferMapAsync(g->read,WGPUMapMode_Read,0,1024,(WGPUBufferMapCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=map_callback,.userdata1=&mapped});wgpuDevicePoll(g->device,true,NULL);need(mapped==1,"GPU readback failed");
  const void *data=wgpuBufferGetConstMappedRange(g->read,0,1024);need(data!=NULL,"mapped GPU output");memcpy(region(r,&r->tm,C,1024),data,1024);wgpuBufferUnmap(g->read);
}
static void trace_words(FILE *f,const char *name,const uint8_t *bytes,size_t count,size_t width){fprintf(f,"\"%s\":[",name);for(size_t i=0;i<count;i++)fprintf(f,"%s\"%" PRIu64 "\"",i?",":"",get_word(bytes+i*width,width));fputc(']',f);}
static size_t number(const char *s,size_t maximum){char *end=NULL;need(*s>='0'&&*s<='9',"invalid number");unsigned long n=strtoul(s,&end,10);need(end&&*end==0&&n<=maximum,"number out of range");return n;}
static size_t parse_tokens(const char *s,uint8_t *tokens){size_t n=0;while(*s){need(n<128&&*s>='0'&&*s<='9',"invalid byte token list");char *end;unsigned long v=strtoul(s,&end,10);need(v<=255&&(*end==0||*end==','),"invalid byte token");tokens[n++]=(uint8_t)v;if(!*end)break;s=end+1;need(*s!=0,"trailing token comma");}return n;}
int main(int argc,char **argv){
  need(argc>=4,"usage: gpt128 BUNDLE --prompt TEXT [--generate N] [--trace FILE] (or --tokens 0,1,...)");
  uint8_t tokens[128]={0};size_t length=0,steps=32;const char *prompt=NULL,*trace_path=NULL,*weights_path=NULL;bool supplied=false;
  for(int i=2;i<argc;i++){need(i+1<argc,"missing option value");const char *option=argv[i],*v=argv[++i];
    if(strcmp(option,"--prompt")==0){need(!supplied,"duplicate prompt");supplied=true;prompt=v;length=strlen(v);need(length<=128,"prompt exceeds 128 UTF-8 bytes");memcpy(tokens,v,length);}
    else if(strcmp(option,"--tokens")==0){need(!supplied,"duplicate tokens");supplied=true;length=parse_tokens(v,tokens);}
    else if(strcmp(option,"--generate")==0){steps=number(v,1024);need(steps>0,"generate must be 1..1024");}
    else if(strcmp(option,"--trace")==0){need(!trace_path,"duplicate trace");trace_path=v;}
    else if(strcmp(option,"--test-weights")==0){weights_path=v;}
    else need(false,"unknown option");
  }
  need(supplied&&length>=1&&length<=128,"expected 1..128 input bytes");
  Bytes files[5];for(size_t i=0;i<5;i++)files[i]=artifact(argv[1],i);need(files[4].size==WEIGHT_BYTES,"wrong checkpoint size");
  if(weights_path){free(files[4].data);files[4]=read_file(weights_path);need(files[4].size==WEIGHT_BYTES,"test weight size");fprintf(stderr,"Using explicit test weight override\n");}
  Runtime r;init_runtime(&r,files);GPU g;init_gpu(&g,files[3],&r);FILE *trace=NULL;
  if(trace_path){trace=fopen(trace_path,"wx");need(trace!=NULL,"trace exists or cannot be created");}
  fprintf(stderr,"Demo: generated hidden Wasm and transfer adapter have incomplete artifact proofs.\n");
  if(prompt)fwrite(prompt,1,strlen(prompt),stdout);
  for(size_t step=0;step<steps;step++){
    checked(wasmtime_context_set_fuel(r.ctx,1000000000),NULL);invoke(&r,&r.hidden,"reset",NULL,0,NULL,0,false);
    uint64_t inputs[2]={array(&r,files[4].data,2984,false),array(&r,tokens,length,true)},hidden[4],next;
    invoke(&r,&r.hidden,"hidden",inputs,2,hidden,4,false);invoke(&r,&r.transfer,"prepare",hidden,4,NULL,0,false);dispatch(&g,&r);invoke(&r,&r.transfer,"finish",NULL,0,&next,1,true);need(next<256,"next byte out of range");
    if(trace){uint8_t hw[32];for(size_t i=0;i<4;i++)put64(hw+8*i,hidden[i]);fprintf(trace,"{\"step\":%zu,\"token\":%" PRIu64 ",",step,next);trace_words(trace,"hidden",hw,4,8);fputc(',',trace);trace_words(trace,"headWords",region(&r,&r.tm,C,1024),256,4);fputc(',',trace);trace_words(trace,"logits",region(&r,&r.tm,LOGITS,2048),256,8);fprintf(trace,"}\n");}
    fputc((int)next,stdout);fflush(stdout);if(length==128){memmove(tokens,tokens+1,127);length=127;}tokens[length++]=(uint8_t)next;
  }
  fputc('\n',stdout);if(trace)fclose(trace);
  wgpuBindGroupRelease(g.group);wgpuComputePipelineRelease(g.pipeline);wgpuBufferRelease(g.a);wgpuBufferRelease(g.b);wgpuBufferRelease(g.c);wgpuBufferRelease(g.read);wgpuQueueRelease(g.queue);wgpuDeviceRelease(g.device);wgpuAdapterRelease(g.adapter);wgpuInstanceRelease(g.instance);
  wasmtime_store_delete(r.store);wasm_engine_delete(r.engine);for(size_t i=0;i<5;i++)free(files[i].data);return 0;
}
