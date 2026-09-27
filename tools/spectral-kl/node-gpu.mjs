import fs from 'node:fs/promises';
import {GpuMoments} from './runtime.mjs';

// The optional Dawn dependency is local to this example, outside the compiler.
export async function createNodeGpu({allowSoftware=false}={}) {
  const {create,globals}=await import('../../build/spectral-kl-gpu/node_modules/webgpu/index.js');
  Object.assign(globalThis,globals);
  const options=process.env.WEBGPU_BACKEND ? [`backend=${process.env.WEBGPU_BACKEND}`] : [];
  const provider=create(options);
  const source=await fs.readFile(new URL('./moments.wgsl',import.meta.url),'utf8');
  const moments=await GpuMoments.create(provider,source,{allowSoftware});
  // Keep Dawn alive until the device and all pending work have been released.
  moments.provider=provider;
  const destroy=moments.destroy.bind(moments);
  moments.destroy=()=>{destroy();moments.provider=null;};
  return moments;
}
