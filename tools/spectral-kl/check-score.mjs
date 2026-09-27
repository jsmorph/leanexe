import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import processes from '../run-process.js';
import {solve} from './reference.mjs';

const root=fileURLToPath(new URL('../../',import.meta.url));
const wordView=new DataView(new ArrayBuffer(8));
function word(x) {
  if (!Number.isFinite(x)) throw new Error('Nonfinite checker input');
  wordView.setFloat64(0,x,true);
  return wordView.getBigUint64(0,true).toString();
}
function rows(input,width) {
  return Array.from({length:input.length/width},(_,r)=>
    Array.from({length:width},(_,j)=>word(input[r*width+j])));
}

// This proposes witnesses only. Correctness does not depend on this solver:
// the Lean checker validates their residuals directly against the observations.
export function witnesses(pm,qm,width,eta,count) {
  const d=Array.from({length:width},(_,i)=>pm[i]-qm[i]);
  return Array.from({length:count},(_,i)=>{
    const r=(i+0.5)/count;
    const matrix=Array.from({length:width*width},(_,j)=>
      r*pm[width+j]+(1-r)*qm[width+j]+(j%(width+1)===0?eta:0));
    return {end:word((i+1)/count),x:Array.from(solve(matrix,d,width),word)};
  });
}

export async function checkScore({p,q,width,eta,score,pm,qm,tolerance=1e-6,cells=8}) {
  if (!Number.isFinite(tolerance) || tolerance<=0) throw new Error('Tolerance must be positive and finite');
  if (!Number.isInteger(cells) || cells<1 || cells>4096) throw new Error('Interval count must be an integer in [1,4096]');
  const directory=path.join(root,'build/spectral-kl-checks');
  await fs.mkdir(directory,{recursive:true});
  const run=await fs.mkdtemp(path.join(directory,'run-'));
  const request=path.join(run,'request.json');
  await fs.writeFile(request,JSON.stringify({features:width,p:rows(p,width),q:rows(q,width),
    eta:word(eta),score:word(score),tolerance:word(tolerance),
    cells:witnesses(pm,qm,width,eta,cells)}));
  const checked=processes.runChecked(['lake','--dir',path.join(root,'proofs/talos/lean'),
    'env','lean','--run',path.join(root,'tools/spectral-kl/check.lean'),request],
    {encoding:'utf8',timeout:300000,maxBuffer:16*1024*1024});
  const result=JSON.parse(checked.stdout);
  if (result.accepted!==true || result.theorem!=='Project.SpectralKL.Certificate.accepts_sound') {
    throw new Error('Lean did not establish the requested error bound');
  }
  await fs.writeFile(path.join(run,'result.json'),JSON.stringify(result,null,2));
  return {absoluteErrorBound:tolerance,inputPath:request,result};
}
