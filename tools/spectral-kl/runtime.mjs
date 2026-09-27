// Host adapter shared by the CPU and WebGPU pipelines. The matrix solve and
// stable kernel always execute the Lean-compiled WASM implementation.
export function validateFeatures(features, width) {
  if (!Number.isInteger(width) || width < 1 || width > 32 ||
      features.length === 0 || features.length > 524288 || features.length % width) {
    throw new Error('Expected 1–32 features and a nonempty rectangular array of at most 524288 values');
  }
  if (!(features instanceof Float32Array)) {
    throw new Error('Features must be Float32Array so both backends receive identical inputs');
  }
  for (const x of features) {
    if (!Number.isFinite(x) || Math.abs(x) > 16) throw new Error('Features must be finite and in [-16,16]');
  }
}

const scratch = new DataView(new ArrayBuffer(8));
function bits(x) { scratch.setFloat64(0,x,true); return scratch.getBigUint64(0,true); }
function value(x) { scratch.setBigUint64(0,BigInt.asUintN(64,x),true); return scratch.getFloat64(0,true); }

export class CpuEstimator {
  constructor(instance) { this.exports = instance.exports; }
  static async create(bytes) {
    const { instance } = await WebAssembly.instantiate(bytes, {});
    return new CpuEstimator(instance);
  }
  put(values) {
    const p = this.exports.alloc(BigInt(8+8*values.length));
    const view = new DataView(this.exports.memory.buffer);
    view.setBigUint64(Number(p),BigInt(values.length),true);
    for (let i=0;i<values.length;i++) view.setFloat64(Number(p)+8+8*i,values[i],true);
    return p;
  }
  moments(features,width) {
    validateFeatures(features,width);
    try {
      const out = Number(this.exports.moments(this.put(features),BigInt(width)));
      const view = new DataView(this.exports.memory.buffer);
      const size = Number(view.getBigUint64(out,true));
      if (size !== width+width*width) throw new Error('WASM moment computation rejected the input');
      return Float64Array.from({length:size},(_,i)=>view.getFloat64(out+8+8*i,true));
    } finally { this.exports.reset(); }
  }
  score(p,q,width,eta) {
    try {
      const [status,result] = this.exports.score(this.put(p),this.put(q),BigInt(width),bits(eta));
      const messages = ['success','invalid moments or regularization','spectrum outside [1/2,3/2]',
        'Cholesky or finite-result check failed','Jacobi did not converge'];
      if (status !== 0n) throw new Error(`Spectral KL: ${messages[Number(status)] ?? status}`);
      return value(result);
    } finally { this.exports.reset(); }
  }
  estimate(p,q,width,eta) {
    return this.score(this.moments(p,width),this.moments(q,width),width,eta);
  }
}

export class GpuMoments {
  constructor(device,first,second,layout,info) {
    Object.assign(this,{device,first,second,layout,info});
  }
  static async create(gpu,source,{allowSoftware=false}={}) {
    if (!gpu) throw new Error('WebGPU is unavailable');
    const adapter = await gpu.requestAdapter({powerPreference:'high-performance'});
    if (!adapter) throw new Error('No WebGPU adapter is available');
    const info = adapter.info;
    const software = info?.isFallbackAdapter || /lavapipe|llvmpipe|swiftshader|software/i.test(
      `${info?.vendor} ${info?.architecture} ${info?.device} ${info?.description}`);
    if (software && !allowSoftware) throw new Error('Software adapter requires explicit allowSoftware for validation');
    const device = await adapter.requestDevice();
    try {
      const module = device.createShaderModule({code:source});
      const diagnostics = await module.getCompilationInfo();
      const errors = diagnostics.messages.filter(m=>m.type==='error');
      if (errors.length) throw new Error(errors.map(m=>`${m.lineNum}:${m.linePos}: ${m.message}`).join('\n'));
      const layout = device.createBindGroupLayout({entries:[
        {binding:0,visibility:GPUShaderStage.COMPUTE,buffer:{type:'uniform'}},
        {binding:1,visibility:GPUShaderStage.COMPUTE,buffer:{type:'read-only-storage'}},
        {binding:2,visibility:GPUShaderStage.COMPUTE,buffer:{type:'storage'}},
        {binding:3,visibility:GPUShaderStage.COMPUTE,buffer:{type:'storage'}},
      ]});
      const pipelineLayout = device.createPipelineLayout({bindGroupLayouts:[layout]});
      const first = await device.createComputePipelineAsync({layout:pipelineLayout,compute:{module,entryPoint:'partial'}});
      const second = await device.createComputePipelineAsync({layout:pipelineLayout,compute:{module,entryPoint:'finish'}});
      return new GpuMoments(device,first,second,layout,{
        description:info?.description ?? '',device:info?.device ?? '',software:Boolean(software),
      });
    } catch (error) { device.destroy(); throw error; }
  }
  async moments(features,width) {
    validateFeatures(features,width);
    const n = features.length/width, blocks = Math.ceil(n/256), entries = width+width*width;
    const d = this.device, buffers=[];
    const buffer = (size,usage) => {
      const b=d.createBuffer({size,usage}); buffers.push(b); return b;
    };
    d.pushErrorScope('validation');
    let scoped = true;
    try {
      const params=buffer(16,GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST);
      const samples=buffer(features.byteLength,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST);
      const partials=buffer(4*blocks*entries,GPUBufferUsage.STORAGE);
      const output=buffer(4*entries,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_SRC);
      const readback=buffer(4*entries,GPUBufferUsage.MAP_READ|GPUBufferUsage.COPY_DST);
      d.queue.writeBuffer(params,0,new Uint32Array([n,width,blocks,entries]));
      d.queue.writeBuffer(samples,0,features);
      const bind=d.createBindGroup({layout:this.layout,entries:[params,samples,partials,output]
        .map((b,binding)=>({binding,resource:{buffer:b}}))});
      const encoder=d.createCommandEncoder();
      const p=encoder.beginComputePass();
      p.setBindGroup(0,bind); p.setPipeline(this.first); p.dispatchWorkgroups(entries,blocks); p.end();
      const q=encoder.beginComputePass();
      q.setBindGroup(0,bind); q.setPipeline(this.second); q.dispatchWorkgroups(entries); q.end();
      encoder.copyBufferToBuffer(output,0,readback,0,4*entries);
      d.queue.submit([encoder.finish()]);
      const error=await d.popErrorScope(); scoped=false;
      if (error) throw new Error(error.message);
      await readback.mapAsync(GPUMapMode.READ);
      const result=Float64Array.from(new Float32Array(readback.getMappedRange()));
      readback.unmap();
      if (!result.every(Number.isFinite)) throw new Error('WebGPU returned a nonfinite moment');
      return result;
    } finally {
      if (scoped) await d.popErrorScope();
      for (const b of buffers) b.destroy();
    }
  }
  destroy() { this.device.destroy(); }
}
