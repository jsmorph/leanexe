const fs=require('node:fs');
const {runChecked}=require('../run-process');
const out='.lake/build/spectral-kl/matrix.wasm';
function build() {
  fs.mkdirSync('.lake/build/spectral-kl',{recursive:true});
  runChecked(['lake','build','LeanExe.Examples.SpectralMatrix'],{encoding:'utf8',timeout:120000});
  runChecked(['lake','--dir','proofs/talos/lean','build','Project.SpectralKL.Executable',
    'Project.SpectralKL.CertificateRun'],{encoding:'utf8',timeout:300000});
  runChecked([process.env.LEAN_WASM_EXE||'.lake/build/bin/lean-wasm','compile',
    '--module','LeanExe.Examples.SpectralMatrix',
    '--entries','LeanExe.Examples.SpectralMatrix.moments,LeanExe.Examples.SpectralMatrix.score',
    '--out',out],{encoding:'utf8',timeout:120000});
  return out;
}
if(require.main===module) { build(); console.log(out); }
module.exports={build,out};
