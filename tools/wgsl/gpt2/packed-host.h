/* Native WebGPU bindings for the experimental packed parent module.
 * No floating-point arithmetic: input/output words are copied unchanged.
 * Wasm allocates the output before invoking either synchronous import. */
#include "webgpu-headers/webgpu.h"
#include "wgpu.h"

typedef struct {
  WGPUInstance instance;
  WGPUAdapter adapter;
  WGPUDevice device;
  WGPUQueue queue;
  WGPUComputePipeline pipelines[6];
  WGPUBindGroup groups[50];
  WGPUBuffer weights[50], input, output, readback;
  uint64_t weight_pointer;
  bool loaded;
  size_t dispatches;
} PackedGPU;
static PackedGPU packed_gpu;
static const size_t packed_inner[6]={768,768,768,3072,768,768};
static const size_t packed_cols[6]={2304,768,3072,768,25129,25128};
static const size_t packed_offsets[4]={1536,1773312,2365440,4727808};
static const size_t packed_block_words=7087872, packed_blocks_offset=39383808;
static const char *packed_roles[6]={"qkv","attention","expansion","projection","vocabularyLeft","vocabularyRight"};

static void packed_need(bool ok,const char *message) { if(!ok) die(message); }
static size_t packed_shape(size_t matrix) { return matrix<48?matrix%4:matrix-44; }
static uint8_t *packed_region(Runtime *runtime,uint64_t start,size_t length) {
  size_t size=wasmtime_memory_data_size(runtime->context,&runtime->memory);
  packed_need(runtime->has_memory&&start<=size&&length<=size-start,"packed Wasm memory range");
  return wasmtime_memory_data(runtime->context,&runtime->memory)+start;
}
static void packed_adapter(WGPURequestAdapterStatus status,WGPUAdapter adapter,WGPUStringView message,void *user,void *unused) {
  (void)unused;(void)message;packed_need(status==WGPURequestAdapterStatus_Success,"CPU WebGPU adapter");
  *(WGPUAdapter *)user=adapter;
}
static void packed_device(WGPURequestDeviceStatus status,WGPUDevice device,WGPUStringView message,void *user,void *unused) {
  (void)unused;(void)message;packed_need(status==WGPURequestDeviceStatus_Success,"CPU WebGPU device");
  *(WGPUDevice *)user=device;
}
static void packed_error(WGPUDevice const *device,WGPUErrorType type,WGPUStringView message,void *user,void *unused) {
  (void)device;(void)type;(void)user;(void)unused;
  fprintf(stderr,"WebGPU: %.*s\n",(int)message.length,message.data);exit(1);
}
static void packed_mapped(WGPUMapAsyncStatus status,WGPUStringView message,void *user,void *unused) {
  (void)message;(void)unused;*(int *)user=status==WGPUMapAsyncStatus_Success?1:-1;
}
static WGPUBuffer packed_buffer(size_t bytes,WGPUBufferUsage usage) {
  WGPUBuffer buffer=wgpuDeviceCreateBuffer(packed_gpu.device,&(WGPUBufferDescriptor){.size=bytes,.usage=usage});
  packed_need(buffer!=NULL,"packed WebGPU buffer");return buffer;
}
static void packed_initialize(void) {
  PackedGPU *g=&packed_gpu;
  if(g->device)return;
  const char *directory=getenv("LEANEXE_PACKED_SHADERS");
  packed_need(directory!=NULL,"set LEANEXE_PACKED_SHADERS to the checked shader directory");
  g->instance=wgpuCreateInstance(NULL);packed_need(g->instance!=NULL,"WebGPU instance");
  wgpuInstanceRequestAdapter(g->instance,&(WGPURequestAdapterOptions){.featureLevel=WGPUFeatureLevel_Core,
    .backendType=WGPUBackendType_Vulkan,.forceFallbackAdapter=true},
    (WGPURequestAdapterCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=packed_adapter,.userdata1=&g->adapter});
  packed_need(g->adapter!=NULL,"Vulkan CPU adapter unavailable");
  WGPUAdapterInfo info={0};wgpuAdapterGetInfo(g->adapter,&info);
  fprintf(stderr,"Packed WebGPU: %.*s (%.*s)\n",(int)info.device.length,info.device.data,(int)info.description.length,info.description.data);
  packed_need(info.adapterType==WGPUAdapterType_CPU,"packed test requires a CPU adapter");wgpuAdapterInfoFreeMembers(info);
  wgpuAdapterRequestDevice(g->adapter,&(WGPUDeviceDescriptor){.uncapturedErrorCallbackInfo={.callback=packed_error}},
    (WGPURequestDeviceCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=packed_device,.userdata1=&g->device});
  packed_need(g->device!=NULL,"WebGPU device");g->queue=wgpuDeviceGetQueue(g->device);
  g->input=packed_buffer(3072*4,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);
  g->output=packed_buffer(25129*4,WGPUBufferUsage_Storage|WGPUBufferUsage_CopySrc);
  g->readback=packed_buffer(25129*4,WGPUBufferUsage_MapRead|WGPUBufferUsage_CopyDst);
  for(size_t shape=0;shape<6;shape++) {
    char file[4096];packed_need(snprintf(file,sizeof file,"%s/%s/kernel.wgsl",directory,packed_roles[shape])<(int)sizeof file,"shader path");
    size_t size;uint8_t *bytes=read_file(file,&size);
    WGPUShaderSourceWGSL source={.chain={.sType=WGPUSType_ShaderSourceWGSL},.code={(char *)bytes,size}};
    WGPUShaderModule module=wgpuDeviceCreateShaderModule(g->device,&(WGPUShaderModuleDescriptor){.nextInChain=&source.chain});
    packed_need(module!=NULL,"packed shader module");
    g->pipelines[shape]=wgpuDeviceCreateComputePipeline(g->device,&(WGPUComputePipelineDescriptor){
      .compute={.module=module,.entryPoint={"lean_kernel",WGPU_STRLEN}}});
    packed_need(g->pipelines[shape]!=NULL,"packed pipeline");wgpuShaderModuleRelease(module);free(bytes);
  }
}
static void packed_load_weights(Runtime *runtime,uint64_t pointer,uint64_t size) {
  PackedGPU *g=&packed_gpu;
  packed_need(size==497759232,"parent weight byte count");
  if(g->loaded){packed_need(g->weight_pointer==pointer,"weight pointer changed; start a new session");return;}
  packed_initialize();const uint8_t *weights=packed_region(runtime,pointer,(size_t)size);
  for(size_t matrix=0;matrix<50;matrix++) {
    size_t shape=packed_shape(matrix),cols=packed_cols[shape],inner=packed_inner[shape];
    size_t bytes=4*(inner*cols+(matrix<48?cols:0));uint8_t *transposed=NULL;
    const uint8_t *source;
    if(matrix<48) source=weights+4*(packed_blocks_offset+(matrix/4)*packed_block_words+packed_offsets[shape]);
    else {
      transposed=malloc(bytes);packed_need(transposed!=NULL,"vocabulary staging allocation");
      size_t start=matrix==48?0:25129;
      for(size_t k=0;k<inner;k++)for(size_t col=0;col<cols;col++)
        memcpy(transposed+4*(k*cols+col),weights+4*((start+col)*768+k),4);
      source=transposed;
    }
    g->weights[matrix]=packed_buffer(bytes,WGPUBufferUsage_Storage|WGPUBufferUsage_CopyDst);
    wgpuQueueWriteBuffer(g->queue,g->weights[matrix],0,source,bytes);free(transposed);
    WGPUBindGroupLayout layout=wgpuComputePipelineGetBindGroupLayout(g->pipelines[shape],0);
    WGPUBindGroupEntry entries[]={{.binding=0,.buffer=g->input,.size=inner*4},
      {.binding=1,.buffer=g->weights[matrix],.size=bytes},{.binding=2,.buffer=g->output,.size=cols*4}};
    g->groups[matrix]=wgpuDeviceCreateBindGroup(g->device,&(WGPUBindGroupDescriptor){.layout=layout,.entryCount=3,.entries=entries});
    packed_need(g->groups[matrix]!=NULL,"packed bind group");wgpuBindGroupLayoutRelease(layout);
  }
  wgpuDevicePoll(g->device,true,NULL);g->weight_pointer=pointer;g->loaded=true;
}
static void packed_dispatch(Runtime *runtime,size_t matrix,uint64_t input,uint64_t output) {
  PackedGPU *g=&packed_gpu;size_t shape=packed_shape(matrix),bytes=4*packed_cols[shape];
  wgpuQueueWriteBuffer(g->queue,g->input,0,packed_region(runtime,input,4*packed_inner[shape]),4*packed_inner[shape]);
  WGPUCommandEncoder encoder=wgpuDeviceCreateCommandEncoder(g->device,NULL);
  WGPUComputePassEncoder pass=wgpuCommandEncoderBeginComputePass(encoder,NULL);
  wgpuComputePassEncoderSetPipeline(pass,g->pipelines[shape]);wgpuComputePassEncoderSetBindGroup(pass,0,g->groups[matrix],0,NULL);
  wgpuComputePassEncoderDispatchWorkgroups(pass,(uint32_t)((packed_cols[shape]+7)/8),1,1);
  wgpuComputePassEncoderEnd(pass);wgpuComputePassEncoderRelease(pass);
  wgpuCommandEncoderCopyBufferToBuffer(encoder,g->output,0,g->readback,0,bytes);
  WGPUCommandBuffer command=wgpuCommandEncoderFinish(encoder,NULL);wgpuQueueSubmit(g->queue,1,&command);
  wgpuCommandBufferRelease(command);wgpuCommandEncoderRelease(encoder);
  int mapped=0;wgpuBufferMapAsync(g->readback,WGPUMapMode_Read,0,bytes,
    (WGPUBufferMapCallbackInfo){.mode=WGPUCallbackMode_AllowSpontaneous,.callback=packed_mapped,.userdata1=&mapped});
  wgpuDevicePoll(g->device,true,NULL);packed_need(mapped==1,"packed readback completion");
  const void *data=wgpuBufferGetConstMappedRange(g->readback,0,bytes);packed_need(data!=NULL,"packed mapped output");
  memcpy(packed_region(runtime,output,bytes),data,bytes);wgpuBufferUnmap(g->readback);g->dispatches++;
}
static wasm_trap_t *packed_callback(void *data,wasmtime_caller_t *caller,const wasmtime_val_t *args,size_t argc,
                                    wasmtime_val_t *results,size_t resultc) {
  (void)caller;(void)results;Runtime *runtime=data;uint64_t a[12];
  packed_need((argc==12||argc==7)&&resultc==0,"packed import signature");
  for(size_t i=0;i<argc;i++){packed_need(args[i].kind==WASMTIME_I64,"packed import parameter");a[i]=(uint64_t)args[i].of.i64;}
  packed_load_weights(runtime,a[1],a[2]);
  if(argc==12) {
    size_t matrix=50;
    for(size_t i=0;i<48;i++) {
      size_t shape=i%4,offset=packed_blocks_offset+(i/4)*packed_block_words+packed_offsets[shape];
      if(a[6]==offset && a[7]==offset+packed_inner[shape]*packed_cols[shape] &&
         a[8]==packed_inner[shape] && a[9]==packed_cols[shape]) {matrix=i;break;}
    }
    packed_need(matrix<48&&a[10]==1&&a[5]==4*a[8],"unsupported packed linear request");
    packed_dispatch(runtime,matrix,a[4],a[11]);
  } else {
    packed_need(a[5]==3072,"packed vocabulary input length");
    packed_dispatch(runtime,48,a[4],a[6]);packed_dispatch(runtime,49,a[4],a[6]+25129*4);
  }
  return NULL;
}
static void packed_imports(Runtime *runtime,wasmtime_extern_t imports[2]) {
  for(size_t i=0;i<2;i++) {
    size_t count=i==0?12:7;wasm_valtype_t *types[12];
    for(size_t j=0;j<count;j++)types[j]=wasm_valtype_new_i64();
    wasm_valtype_vec_t params,results;wasm_valtype_vec_new(&params,count,types);wasm_valtype_vec_new_empty(&results);
    wasm_functype_t *type=wasm_functype_new(&params,&results);imports[i].kind=WASMTIME_EXTERN_FUNC;
    wasmtime_func_new(runtime->context,type,packed_callback,runtime,NULL,&imports[i].of.func);wasm_functype_delete(type);
  }
}

static void packed_cleanup(void) {
  PackedGPU *g=&packed_gpu;
  if(!g->device)return;
  fprintf(stderr,"Packed WebGPU dispatches: %zu\n",g->dispatches);
  for(size_t i=0;i<50;i++) {
    if(g->groups[i])wgpuBindGroupRelease(g->groups[i]);
    if(g->weights[i])wgpuBufferRelease(g->weights[i]);
  }
  for(size_t i=0;i<6;i++)wgpuComputePipelineRelease(g->pipelines[i]);
  wgpuBufferRelease(g->input);wgpuBufferRelease(g->output);wgpuBufferRelease(g->readback);
  wgpuQueueRelease(g->queue);wgpuDeviceRelease(g->device);wgpuAdapterRelease(g->adapter);wgpuInstanceRelease(g->instance);
  memset(g,0,sizeof *g);
}
