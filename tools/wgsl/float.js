"use strict";
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto');
const {lean,audit}=require('./package'),{checkBundle}=require('./bundle'),{execute}=require('./gpt-runtime');
const root=path.resolve(__dirname,'../..'),proofRoot=path.join(root,'proofs/talos/lean');
const write=(p,x)=>fs.writeFileSync(p,x,{flag:'wx'}),json=(p,x)=>write(p,JSON.stringify(x,null,2)+'\n');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const requireThat=(ok,message)=>{if(!ok)throw Error(message);};
const names=['Project.TinyGpt2.FloatSpec.Correspondence.hidden_eq','Project.TinyGpt2.FloatSpec.Correspondence.logits_eq',
  'Project.TinyGpt2.FloatSpec.Evaluation.hidden_eq',
  ...['hidden_interface','finish_interface','hidden_artifact','artifact'].map(x=>`Project.WGSL.GptFloatArtifact.${x}`),
  ...['negative_zero','head_zero_sign','head_subnormals','balanced_order','sequential_differs','exponential_cutoff','canonical_nan']
    .map(x=>`Project.TinyGpt2.FloatSpec.ContractTests.${x}`)];
const specFiles=['proofs/talos/lean/Project/TinyGpt2/FloatSpec/Algorithm.lean','proofs/talos/lean/Project/WGSL/PrecisionModel.lean'];

async function checkFiles(directory,log){
  const output=await lean('exact float artifact bytes and word-domain checks',['lake','-d',proofRoot,'env','lean','--run',
    path.join(__dirname,'FloatCheck.lean'),'--check',...['hidden.wasm','finish.wasm','weights.bin'].map(n=>path.join(directory,n))],log);
  const axioms=audit(output,names);
  requireThat(output.split('\n').filter(x=>x==='WGSL_FLOAT_ARTIFACTS_VERIFIED').length===1,'missing float artifact marker');
  return axioms;
}
async function check(directory){
  const checked=await checkBundle(directory);
  try {
    requireThat(checked.metadata.profile.id==='leanexe-f32-rne-separate-v1','float equality requires the separate profile');
    const snapshots={};
    for(const [name,max] of [['hidden.wasm',32768],['finish.wasm',1024],['weights.bin',2488*8]]){
      const bytes=fs.readFileSync(path.join(checked.directory,name));requireThat(bytes.length<=max,`${name} exceeds size limit`);
      write(path.join(checked.attempt,name),bytes);snapshots[name]=bytes;
    }
    const specSources=Object.fromEntries(specFiles.map(p=>[p,fs.readFileSync(path.join(root,p))]));
    await lean('float specification proof dependencies',['lake','-d',proofRoot,'build',
      'Project.WGSL.GptFloatArtifact','Project.TinyGpt2.FloatSpec.ContractTests','Project.TinyGpt2.FloatSpec.Evaluation'],path.join(checked.attempt,'float-dependencies.log'));
    const axioms=await checkFiles(checked.attempt,path.join(checked.attempt,'float-verify.log'));
    const proof=path.join(checked.attempt,'FloatPackageProof.lean');
    write(proof,'import Project.WGSL.GptFloatArtifact\n'+fs.readFileSync(path.join(checked.attempt,'Proof.lean'),'utf8')+
      '\ntheorem checkedFloatShape : CheckedWGSLPackage.package.kernel.ast.config = Project.WGSL.GptHead.config := by rfl\n'+
      'theorem checkedFloatProfile : CheckedWGSLPackage.package.tag.profile = LeanExe.WGSL.restricted := by rfl\n'+
      'def checkedFloatExecution := @Project.WGSL.GptFloatArtifact.artifact _ _ CheckedWGSLPackage.package checkedFloatShape checkedFloatProfile\n'+
      '#print axioms checkedFloatShape\n#print axioms checkedFloatProfile\n#print axioms checkedFloatExecution\n');
    const output=await lean('bind this exact shader to float algorithm correctness',['lake','-d',proofRoot,'env','lean','--run',proof,
      checked.shaderPath,checked.manifestPath],path.join(checked.attempt,'float-package-verify.log'));
    const compositionAxioms=audit(output,['package','artifact','numerical','numericalWide','exact'].map(x=>`CheckedWGSLPackage.${x}`)
      .concat(['checkedFloatShape','checkedFloatProfile','checkedFloatExecution']));
    for(const [name,bytes] of Object.entries(snapshots))requireThat(bytes.equals(fs.readFileSync(path.join(checked.attempt,name))),`${name} snapshot changed`);
    for(const [name,bytes] of Object.entries(specSources))requireThat(bytes.equals(fs.readFileSync(path.join(root,name))),`${name} changed during checking`);
    const receipt={schemaVersion:1,status:'pass',subject:'Artifact implements the independent floating-point word algorithm',
      specification:'Project.TinyGpt2.FloatSpec.logits:v1',theorem:'Project.WGSL.GptFloatArtifact.artifact',
      specificationSources:Object.fromEntries(Object.entries(specSources).map(([p,bytes])=>[p,sha(bytes)])),
      shaderSha256:sha(checked.shader),manifestSha256:sha(checked.manifest),bridgeSha256:sha(checked.hostBytes),
      artifacts:Object.fromEntries(Object.entries(snapshots).map(([name,bytes])=>[name,{sha256:sha(bytes),bytes:bytes.length}])),
      proofSha256:sha(fs.readFileSync(proof)),axioms,compositionAxioms,
      claims:['hidden Wasm decode, validation and exact words','hidden memory preservation','bridge termination',
        'raw binary32 output words equal the specification','finish Wasm decode, validation and exact binary64 words'],
      theoremDomain:'Runtime parameter arrays of at least 2488 words; every four-byte context and every position 0–3; explicit memory/transfer and runtime premises',
      harnessDomain:'Exactly 2488 finite binary64 parameter words with sign-cleared encoding <= 0x4010000000000000',
      profile:checked.metadata.profile,realReferenceRequired:false,numericalErrorTolerance:null,runtimeConformanceEstablished:false,
      boundary:'Formal Wasm uses the pinned IEEE word model, including its canonical NaNs. Finite conversion and separate-profile native execution/transfer must match the stated word semantics. JavaScript/native engines are not verified here.',
      baseBundleReceipt:'bundle-verification.json'};
    json(path.join(checked.attempt,'float-verification.json'),receipt);
    console.log(`Float algorithm artifact verified: ${checked.attempt}`);
    return {...checked,hiddenBytes:snapshots['hidden.wasm'],finishBytes:snapshots['finish.wasm'],weightsBytes:snapshots['weights.bin'],receipt};
  }catch(error){json(path.join(checked.attempt,'float-failure.json'),{status:'error',error:error.message});throw error;}
}
async function run(checked,tokens,position,label){
  requireThat(tokens.length===4&&tokens.every(x=>Number.isInteger(x)&&x>=0&&x<256),'expected four byte tokens');
  requireThat(Number.isInteger(position)&&position>=0&&position<4,'expected position 0–3');
  const file=path.join(checked.attempt,'weights.bin');
  requireThat(fs.readFileSync(file).equals(checked.weightsBytes),'parameter snapshot changed before reference evaluation');
  const output=await lean('independent float specification evaluation',['lake','-d',proofRoot,'env','lean','--run',
    path.join(__dirname,'FloatCheck.lean'),'--reference',file,String(position),...tokens.map(String)],path.join(checked.attempt,`float-${label}-reference.log`));
  audit(output,names);
  requireThat(fs.readFileSync(file).equals(checked.weightsBytes),'parameter snapshot changed during reference evaluation');
  const lines=output.split('\n').filter(x=>x.startsWith('{'));requireThat(lines.length===1,'missing float reference output');
  const reference=JSON.parse(lines[0]);requireThat(reference.position===position,'reference position mismatch');
  json(path.join(checked.attempt,`float-${label}-reference.json`),reference);
  const result=execute(checked,tokens,reference,label,undefined,position);
  console.log(`Float specification execution passed: ${result.checkedElements} logits and raw head words; position ${position}`);
  return result;
}
async function corpus(directory){
  directory=path.resolve(directory);fs.mkdirSync(path.dirname(directory),{recursive:true});fs.mkdirSync(directory);
  const config=JSON.parse(fs.readFileSync(path.join(__dirname,'float-corpus.json'),'utf8'));
  const checked=await check(path.join(root,'test/wgsl/gpt')),results=[];
  const variants=new Map([['checkpoint',checked]]);
  const {adversarial}=require('./audit/cases');
  for(const [name,sign] of [['adversarial-plus',1],['adversarial-minus',-1]]){
    const attempt=path.join(directory,name);fs.mkdirSync(attempt);
    const weightsBytes=adversarial(sign);write(path.join(attempt,'weights.bin'),weightsBytes);
    for(const [file,bytes] of [['hidden.wasm',checked.hiddenBytes],['finish.wasm',checked.finishBytes]])write(path.join(attempt,file),bytes);
    await checkFiles(attempt,path.join(attempt,'verify.log'));
    variants.set(name,{...checked,attempt,weightsBytes});
  }
  for(const item of config.positive){
    const variant=variants.get(item.weights);requireThat(variant,'unknown parameter fixture');
    const result=await run(variant,item.tokens,item.position,item.name);
    results.push({name:item.name,status:result.status,position:item.position,weightsSha256:sha(variant.weightsBytes),
      evidence:path.relative(directory,path.join(variant.attempt,`gpt-${item.name}.json`))});
  }
  for(const item of config.negative){
    const attempt=path.join(directory,item.name);fs.mkdirSync(attempt);
    for(const [name,source] of [['hidden.wasm',checked.hiddenBytes],['finish.wasm',checked.finishBytes],['weights.bin',checked.weightsBytes]]){
      const bytes=Buffer.from(source);if(name===item.file){if(item.word)bytes.writeBigUInt64LE(BigInt(item.word));else bytes[item.offset]^=item.xor;}
      write(path.join(attempt,name),bytes);
    }
    const log=path.join(attempt,'verify.log');let failed=false;
    try{await checkFiles(attempt,log);}catch{failed=true;}
    requireThat(failed&&fs.readFileSync(log,'utf8').includes(item.failure),`${item.name} did not fail for the expected reason`);
    results.push({name:item.name,status:'rejected',diagnostics:path.relative(directory,log)});
  }
  const report={schemaVersion:1,status:'pass',verification:path.relative(directory,path.join(checked.attempt,'float-verification.json')),
    checkedLogits:256*config.positive.length,checkedRawHeadWords:256*config.positive.length,results};
  json(path.join(directory,'corpus.json'),report);console.log(`Float specification corpus passed: ${results.length} cases; ${directory}`);
}
async function main([command,directory,...rest]){
  if(command==='wgsl-float-check'){requireThat(rest.length===0,'unexpected arguments');await check(directory);}
  else if(command==='wgsl-float-run'){
    requireThat(rest.length===5&&rest.every(x=>/^(0|[1-9][0-9]*)$/.test(x)),'expected POSITION T0 T1 T2 T3');
    const [position,...tokens]=rest.map(Number);await run(await check(directory),tokens,position,'input');
  }else if(command==='wgsl-float-corpus'){requireThat(rest.length===0,'unexpected arguments');await corpus(directory);}
  else throw Error(`unknown float command: ${command}`);
}
module.exports={main,check,run,corpus};
