// Exact u32 column and Gram reductions. Source comes directly from the
// Lean program whose parser identity and reduction semantics are proved.
export async function createWordGpu(source,{allowSoftware=false}={}) {
  const {create,globals}=await import('../../build/spectral-kl-gpu/node_modules/webgpu/index.js');
  Object.assign(globalThis,globals);
  const provider=create(process.env.WEBGPU_BACKEND ? [`backend=${process.env.WEBGPU_BACKEND}`] : []);
  const adapter=await provider.requestAdapter({powerPreference:'high-performance'});
  if(!adapter) throw new Error('No WebGPU adapter is available');
  const info=adapter.info;
  const software=Boolean(info?.isFallbackAdapter||/lavapipe|llvmpipe|swiftshader|software/i.test(
    `${info?.vendor} ${info?.architecture} ${info?.device} ${info?.description}`));
  if(software&&!allowSoftware) throw new Error('Software adapter requires --allow-software');
  const device=await adapter.requestDevice();
  try {
    const module=device.createShaderModule({code:source});
    const diagnostics=await module.getCompilationInfo();
    const errors=diagnostics.messages.filter(m=>m.type==='error');
    if(errors.length) throw new Error(errors.map(m=>`${m.lineNum}:${m.linePos}: ${m.message}`).join('\n'));
    const layout=device.createBindGroupLayout({entries:[
      {binding:0,visibility:GPUShaderStage.COMPUTE,buffer:{type:'uniform'}},
      {binding:1,visibility:GPUShaderStage.COMPUTE,buffer:{type:'read-only-storage'}},
      {binding:2,visibility:GPUShaderStage.COMPUTE,buffer:{type:'storage'}},
    ]});
    const pipeline=await device.createComputePipelineAsync({
      layout:device.createPipelineLayout({bindGroupLayouts:[layout]}),compute:{module,entryPoint:'main'},
    });
    return {
      provider,info:{description:info?.description ?? '',device:info?.device ?? '',software},
      async moments(rows,width) {
        const n=rows.length,entries=width+width*width;
        if(!Number.isInteger(width)||width<1||width>32||n<1||n*width>524288||
          rows.some(row=>row.length!==width||row.some(x=>!Number.isInteger(x)||x<0||x>=65536)))
          throw new Error('Invalid encoded observation matrix');
        const data=Uint32Array.from(rows.flat()),buffers=[];
        const buffer=(size,usage)=>{const b=device.createBuffer({size,usage});buffers.push(b);return b;};
        device.pushErrorScope('validation');
        let scoped=true;
        try {
          const params=buffer(16,GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST);
          const samples=buffer(data.byteLength,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST);
          const output=buffer(8*entries,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_SRC);
          const readback=buffer(8*entries,GPUBufferUsage.MAP_READ|GPUBufferUsage.COPY_DST);
          device.queue.writeBuffer(params,0,new Uint32Array([n,width,entries,0]));
          device.queue.writeBuffer(samples,0,data);
          const bind=device.createBindGroup({layout,entries:[params,samples,output]
            .map((b,binding)=>({binding,resource:{buffer:b}}))});
          const encoder=device.createCommandEncoder(),pass=encoder.beginComputePass();
          pass.setPipeline(pipeline);pass.setBindGroup(0,bind);
          pass.dispatchWorkgroups(Math.ceil(entries/64));pass.end();
          encoder.copyBufferToBuffer(output,0,readback,0,8*entries);
          device.queue.submit([encoder.finish()]);
          const error=await device.popErrorScope();scoped=false;
          if(error) throw new Error(error.message);
          await readback.mapAsync(GPUMapMode.READ);
          const result=Array.from(new Uint32Array(readback.getMappedRange()));
          readback.unmap();
          return result;
        } finally {
          if(scoped) await device.popErrorScope();
          for(const b of buffers) b.destroy();
        }
      },
      destroy() {device.destroy();this.provider=null;},
    };
  } catch(error) {device.destroy();throw error;}
}
