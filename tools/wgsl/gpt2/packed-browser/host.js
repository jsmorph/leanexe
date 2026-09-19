// WebGPU API calls and raw word movement only; numerical work is Wasm/WGSL.
const need=(ok,message)=>{if(!ok)throw Error(message);};
const shapes={qkv:[768,2304],attention:[768,768],expansion:[768,3072],projection:[3072,768],
  vocabularyLeft:[768,25129],vocabularyRight:[768,25128]};
class GPUHost {
  static async create(cpu,shared,notify){
    need(navigator.gpu&&crossOriginIsolated,"WebGPU and an isolated localhost/HTTPS page are required");
    const adapter=await navigator.gpu.requestAdapter({forceFallbackAdapter:cpu});need(adapter,"Requested WebGPU adapter is unavailable");
    const info=adapter.info;need(!cpu||info.isFallbackAdapter,"A CPU fallback adapter was requested");
    const device=await adapter.requestDevice();
    const host=new GPUHost();Object.assign(host,{device,shared,views:new Map(),dispatches:0,weights:null,closed:false});
    host.info={vendor:info.vendor,architecture:info.architecture,device:info.device,description:info.description,isFallbackAdapter:info.isFallbackAdapter};
    notify({type:"adapter",info:host.info});
    const buffer=(size,usage)=>device.createBuffer({size,usage});
    host.a=buffer(12288,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST);
    host.c=buffer(201028,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_SRC);
    host.read=buffer(201028,GPUBufferUsage.COPY_DST|GPUBufferUsage.MAP_READ);
    host.pipelines={};device.addEventListener("uncapturederror",event=>{host.failure=event.error;});
    device.lost.then(info=>{if(!host.closed)host.failure=Error(`WebGPU device lost: ${info.message}`);});
    for(const role of Object.keys(shapes)){
      const response=await fetch(`/bundle/shaders/${role}/kernel.wgsl`);need(response.ok,`Cannot load ${role} shader`);
      const module=device.createShaderModule({code:await response.text()});
      host.pipelines[role]=await device.createComputePipelineAsync({layout:"auto",compute:{module,entryPoint:"lean_kernel"}});
    }
    return host;
  }
  view(role,weightOffset=0,biasOffset=0){
    const key=`${role}:${weightOffset}:${biasOffset}`;if(this.views.has(key))return this.views.get(key);
    need(this.weights&&this.views.size<64,"GPU weight view capacity");
    const [inner,cols]=shapes[role],vocabulary=role.startsWith("vocabulary"),count=inner*cols;
    let data;
    if(vocabulary){
      const start=role==="vocabularyLeft"?0:25129;
      data=new Uint32Array(count);
      for(let k=0;k<inner;k++)for(let c=0;c<cols;c++)data[k*cols+c]=this.weights[(start+c)*inner+k];
    }else{
      need(Number.isSafeInteger(weightOffset)&&weightOffset>=0&&weightOffset+count<=this.weights.length,"Matrix weight extent");
      need(Number.isSafeInteger(biasOffset)&&biasOffset>=0&&biasOffset+cols<=this.weights.length,"Matrix bias extent");
      data=new Uint32Array(count+cols);data.set(this.weights.subarray(weightOffset,weightOffset+count));
      data.set(this.weights.subarray(biasOffset,biasOffset+cols),count);
    }
    const b=this.device.createBuffer({size:data.byteLength,usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST});
    this.device.queue.writeBuffer(b,0,data);
    const group=this.device.createBindGroup({layout:this.pipelines[role].getBindGroupLayout(0),entries:[
      {binding:0,resource:{buffer:this.a,size:inner*4}},{binding:1,resource:{buffer:b}},
      {binding:2,resource:{buffer:this.c,size:cols*4}}]});
    const view={b,group};this.views.set(key,view);return view;
  }
  async product(role,weightOffset,biasOffset,outputOffset){
    if(this.failure)throw this.failure;need(!this.closed,"GPU host was closed");
    const {device}=this,[inner,cols]=shapes[role],view=this.view(role,weightOffset,biasOffset);
    // writeBuffer takes an ordinary snapshot; SharedArrayBuffer is not accepted
    // by all implementations of WebGPU's BufferSource arguments.
    device.queue.writeBuffer(this.a,0,new Uint8Array(this.shared,64,inner*4).slice());
    const encoder=device.createCommandEncoder(),pass=encoder.beginComputePass();
    pass.setPipeline(this.pipelines[role]);pass.setBindGroup(0,view.group);pass.dispatchWorkgroups(Math.ceil(cols/8));pass.end();
    encoder.copyBufferToBuffer(this.c,0,this.read,0,cols*4);device.queue.submit([encoder.finish()]);
    await this.read.mapAsync(GPUMapMode.READ,0,cols*4);
    try{new Uint8Array(this.shared,16384+outputOffset,cols*4).set(new Uint8Array(this.read.getMappedRange(0,cols*4)));}
    finally{this.read.unmap();}this.dispatches++;
  }
  async dispatch(request){
    if(request.kind==="vocabulary"){
      await this.product("vocabularyLeft",0,0,0);await this.product("vocabularyRight",0,0,25129*4);
    }else{
      const role=Object.keys(shapes).find(r=>!r.startsWith("vocabulary")&&shapes[r][0]===request.inner&&shapes[r][1]===request.cols);
      need(role,"Unsupported matrix shape");await this.product(role,request.weightOffset,request.biasOffset,0);
    }
  }
  close(){if(this.closed)return;this.closed=true;this.device.destroy();this.weights=null;this.views.clear();}
}
export async function runPacked(options,onEvent=()=>{}){
  const shared=new SharedArrayBuffer(16384+201028),control=new Int32Array(shared,0,1);
  const host=await GPUHost.create(options.cpu!==false,shared,onEvent);
  const worker=new Worker(new URL("worker.js",import.meta.url),{type:"module"});
  let settled=false;
  return new Promise((resolve,reject)=>{
    const cleanup=()=>{settled=true;worker.terminate();host.close();options.signal?.removeEventListener("abort",abort);};
    const fail=error=>{if(settled)return;Atomics.store(control,0,-1);Atomics.notify(control,0);cleanup();reject(error);};
    const abort=()=>fail(new DOMException("Generation stopped","AbortError"));
    options.signal?.addEventListener("abort",abort,{once:true});
    if(options.signal?.aborted){abort();return;}
    worker.onerror=event=>fail(Error(event.message));
    worker.onmessage=async({data})=>{
      if(settled)return;
      try{
        if(data.type==="weights"){
          need(data.bytes.byteLength===497759232,"Checkpoint byte length");
          need(new Uint8Array(new Uint32Array([1]).buffer)[0]===1,"Little-endian host required");
          host.weights=new Uint32Array(data.bytes);
        }else if(data.type==="dispatch"){
          await host.dispatch(data.request);Atomics.store(control,0,1);Atomics.notify(control,0);
        }else if(data.type==="error")fail(Error(data.message));
        else if(data.type==="done"){
          const result={...data,dispatches:host.dispatches,views:host.views.size,adapter:host.info};
          onEvent(result);cleanup();resolve(result);
        }else onEvent(data);
      }catch(error){fail(error);}
    };
    const {signal,...serializable}=options;worker.postMessage({...serializable,shared});
  });
}
