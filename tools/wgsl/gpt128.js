"use strict";

const fs = require("node:fs"), path = require("node:path"), crypto = require("node:crypto");
const { isDeepStrictEqual } = require("node:util");
const { performance } = require("node:perf_hooks");
const { lean, audit } = require("./package"), { checkBundle } = require("./bundle");
const { instantiate, nativeDispatch } = require("./wasm-host");
const root = path.resolve(__dirname, "../.."), proofRoot = path.join(root, "proofs/talos/lean");
const requireThat = (ok, message) => { if (!ok) throw Error(message); };
const write = (p, value) => fs.writeFileSync(p, value, { flag: "wx" });
const json = (p, value) => write(p, JSON.stringify(value, null, 2) + "\n");
const sha = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const names = ["GptSequence.finish_interface", "GptSequence.headWord_eq", "GptSequence.dispatch_word",
  "GptSequence.completes", "FinishBinary.artifact_exact"].map(n => "Project.WGSL." + n)
  .concat(["infer_word", "checked_word"].map(n => "Project.TinyGpt2Seq.Mixed." + n));
const specification = "Project.TinyGpt2Seq.Mixed.inferChecked:v1";
const layout = [
  ["token", [256,4]], ["position", [128,4]], ["query", [4,4]], ["key", [4,4]], ["value", [4,4]],
  ["attention", [4,4]], ["attention_bias", [4]], ["expand", [4,8]], ["expand_bias", [8]],
  ["contract", [8,4]], ["contract_bias", [4]], ["head", [4,256]], ["head_bias", [256]],
  ["norm1_scale", [4]], ["norm1_bias", [4]], ["norm2_scale", [4]], ["norm2_bias", [4]],
  ["norm_final_scale", [4]], ["norm_final_bias", [4]],
];
const modelFiles = ["Project/TinyGpt2Seq/Model.lean", "Project/TinyGpt2Seq/Layout.lean",
  "Project/TinyGpt2Seq/Inference.lean", "Project/TinyGpt2Seq/Mixed.lean", "Project/SequenceSoftmax/Model.lean",
  "Project/TinyGpt2/Model.lean", "Project/TinyGpt2/FloatSpec/Algorithm.lean", "Project/WGSL/PrecisionModel.lean",
  "Project/F64Clip/Model.lean"];

function checkpoint(file) {
  const bytes = fs.readFileSync(file);
  requireThat(bytes.length <= 2*1024*1024, "checkpoint exceeds 2 MiB");
  const data = JSON.parse(bytes);
  requireThat(data.format === "leanexe-tiny-gpt2-checkpoint-v1", "unsupported checkpoint format");
  const architecture = { context:128, vocabulary:256, width:4, heads:2, head_width:2, feedforward_width:8,
    blocks:1, activation:"tanh-gelu", epsilon:"1/100000", pre_normalized:true, qkv_bias:false,
    attention_output_bias:true, head_tied:false, matrix_layout:"input-by-output, row-major" };
  requireThat(isDeepStrictEqual(data.architecture, architecture), "expected the GPT2/128 architecture");
  requireThat(isDeepStrictEqual(Object.keys(data.weights).sort(), layout.map(([n]) => n).sort()), "unexpected parameter tensors");
  const words = layout.flatMap(([name, shape]) => {
    const item = data.weights[name], count = shape.reduce((a,b) => a*b, 1);
    requireThat(isDeepStrictEqual(item.shape, shape) && Array.isArray(item.bits) && item.bits.length === count,
      `invalid ${name} tensor shape`);
    return item.bits.map(word => {
      requireThat(typeof word === "string" && /^[0-9a-fA-F]{16}$/.test(word), `invalid ${name} parameter word`);
      return BigInt("0x" + word);
    });
  });
  requireThat(words.length === 2984, "expected 2984 parameter words");
  const weights = Buffer.alloc(words.length*8); words.forEach((w,i) => weights.writeBigUInt64LE(w, i*8));
  return { bytes, weights };
}
function tokensValid(tokens) {
  return Array.isArray(tokens) && tokens.length >= 1 && tokens.length <= 128 &&
    tokens.every(t => Number.isInteger(t) && t >= 0 && t < 256);
}
function boundWord(bound) {
  requireThat(Number.isFinite(bound) && bound >= 0 && bound <= 10, "bound must be finite and between zero and ten");
  const bytes = Buffer.alloc(8); bytes.writeDoubleLE(bound); return bytes.readBigUInt64LE().toString();
}
function words64(strings) {
  const bytes = Buffer.alloc(strings.length*8);
  strings.forEach((word,i) => bytes.writeBigUInt64LE(BigInt(word), i*8));
  return bytes;
}
function decimal(word) {
  const bytes = Buffer.alloc(8); bytes.writeBigUInt64LE(BigInt(word)); return bytes.readDoubleLE();
}
function checkWords(value, length, bits, field) {
  requireThat(Array.isArray(value) && value.length === length && value.every(w =>
    typeof w === "string" && /^(0|[1-9][0-9]*)$/.test(w) && BigInt(w) < 2n**BigInt(bits)), `invalid reference ${field}`);
}

async function check(checkpointPath) {
  const input = checkpoint(checkpointPath);
  const checked = await checkBundle(path.join(root, "test/wgsl/gpt"));
  try {
    requireThat(checked.metadata.profile.id === "leanexe-f32-rne-separate-v1", "separate profile required");
    const finishBytes = fs.readFileSync(path.join(checked.directory, "finish.wasm"));
    write(path.join(checked.attempt, "finish.wasm"), finishBytes);
    write(path.join(checked.attempt, "checkpoint.json"), input.bytes);
    write(path.join(checked.attempt, "weights.bin"), input.weights);
    const sources = Object.fromEntries(modelFiles.map(p => [p,fs.readFileSync(path.join(proofRoot,p))]));
    await lean("GPT2/128 mixed function and head proof", ["lake", "-d", proofRoot, "build", "Project.WGSL.GptSequence"],
      path.join(checked.attempt, "gpt128-dependencies.log"));
    const output = await lean("GPT2/128 finish artifact identity", ["lake", "-d", proofRoot, "env", "lean", "--run",
      path.join(__dirname, "Gpt128Check.lean"), "--check", path.join(checked.attempt, "finish.wasm")],
    path.join(checked.attempt, "gpt128-check.log"));
    const axioms = audit(output, names);
    requireThat(output.split("\n").filter(x => x === "WGSL_GPT128_FINISH_VERIFIED").length === 1, "missing finish verification marker");
    const proof = path.join(checked.attempt, "Gpt128PackageProof.lean");
    write(proof, "import Project.WGSL.GptSequence\n" + fs.readFileSync(path.join(checked.attempt, "Proof.lean"), "utf8") +
      "\ntheorem checkedSequenceShape : CheckedWGSLPackage.package.kernel.ast.config = Project.WGSL.GptHead.config := by rfl\n" +
      "theorem checkedSequenceProfile : CheckedWGSLPackage.package.tag.profile = LeanExe.WGSL.restricted := by rfl\n" +
      "def checkedSequenceExecution := @Project.WGSL.GptSequence.completes _ _ CheckedWGSLPackage.package checkedSequenceShape checkedSequenceProfile\n" +
      "#print axioms checkedSequenceShape\n#print axioms checkedSequenceProfile\n#print axioms checkedSequenceExecution\n");
    const composed = await lean("bind GPT2/128 head theorem to exact shader", ["lake", "-d", proofRoot, "env", "lean", "--run",
      proof, checked.shaderPath, checked.manifestPath], path.join(checked.attempt, "gpt128-package-check.log"));
    const compositionAxioms = audit(composed, ["package", "artifact", "numerical", "numericalWide", "exact"]
      .map(n => "CheckedWGSLPackage."+n).concat(["checkedSequenceShape", "checkedSequenceProfile", "checkedSequenceExecution"]));
    requireThat(finishBytes.equals(fs.readFileSync(path.join(checked.attempt, "finish.wasm"))), "finish snapshot changed");
    for (const [p,bytes] of Object.entries(sources)) requireThat(bytes.equals(fs.readFileSync(path.join(proofRoot,p))), `model source changed: ${p}`);
    const receipt = { schemaVersion:1, status:"pass", specification, theorem:"Project.WGSL.GptSequence.completes",
      formalScope:"Exact Wasm bridge, parsed WGSL projection, and finish Wasm; given the Lean sequence hidden row and stated transfer/runtime premises",
      hiddenBackend:"Lean evaluation of Project.TinyGpt2Seq.hidden", hiddenWasmExecuted:false,
      completePipelineArtifactProof:false, runtimeConformanceEstablished:false,
      contextDomain:"1–128 byte tokens", parameterPolicy:"Parent F64Clip.prepare: 2984 finite words, clipped to caller bound in [0,10]",
      checkpointSha256:sha(input.bytes), weightsSha256:sha(input.weights),
      shaderSha256:sha(checked.shader), bridgeSha256:sha(checked.hostBytes), finishSha256:sha(finishBytes),
      manifestSha256:sha(checked.manifest), proofSha256:sha(fs.readFileSync(proof)),
      modelSources:Object.fromEntries(Object.entries(sources).map(([p,bytes]) => [p,sha(bytes)])),
      axioms, compositionAxioms, profile:checked.metadata.profile, realReferenceRequired:false,
      baseBundleReceipt:"bundle-verification.json" };
    json(path.join(checked.attempt, "gpt128-verification.json"), receipt);
    return { ...checked, finishBytes, weightsBytes:input.weights, checkpointBytes:input.bytes, sources, receipt };
  } catch (error) {
    json(path.join(checked.attempt,"gpt128-failure.json"),{status:"error",error:error.message}); throw error;
  }
}

async function run(checked, tokens, bound, label) {
  requireThat(tokensValid(tokens), "expected 1 to 128 byte tokens");
  requireThat(/^[a-z0-9-]+$/.test(label), "invalid evidence label");
  const boundBits = boundWord(bound), base = path.join(checked.attempt, "gpt128-"+label);
  json(base+"-tokens.json", tokens);
  const weightsPath = path.join(checked.attempt,"weights.bin");
  requireThat(checked.weightsBytes.equals(fs.readFileSync(weightsPath)), "parameter snapshot changed");
  for (const [p,bytes] of Object.entries(checked.sources)) requireThat(bytes.equals(fs.readFileSync(path.join(proofRoot,p))), `model source changed: ${p}`);
  const output = await lean("GPT2/128 Lean hidden computation and exact reference", ["lake", "-d", proofRoot, "env", "lean", "--run",
    path.join(__dirname,"Gpt128Check.lean"), "--reference", weightsPath, base+"-tokens.json", boundBits], base+"-reference.log");
  audit(output,names);
  requireThat(checked.weightsBytes.equals(fs.readFileSync(weightsPath)), "parameter snapshot changed during evaluation");
  for (const [p,bytes] of Object.entries(checked.sources)) requireThat(bytes.equals(fs.readFileSync(path.join(proofRoot,p))), `model source changed during evaluation: ${p}`);
  const lines=output.split("\n").filter(x => x.startsWith("{"));requireThat(lines.length===1,"missing Lean reference");
  const reference=JSON.parse(lines[0]);
  requireThat(reference.specification===specification && reference.boundWord===boundBits &&
    isDeepStrictEqual(reference.tokens,tokens), "reference context or specification mismatch");
  for(const [field,length,bits] of [["preparedWeights",2984,64],["hidden",4,64],["a",4,32],["b",1024,32],
    ["bias",256,64],["headWords",256,32],["promotedWords",256,64],["logits",256,64],["binary64Logits",256,64]])
    checkWords(reference[field],length,bits,field);
  json(base+"-reference.json",reference);
  const report={schemaVersion:1,status:"error",specification,tokens,bound,boundWord:boundBits,
    hiddenBackend:checked.receipt.hiddenBackend,hiddenWasmExecuted:false,completePipelineArtifactProof:false,
    checkpointSha256:checked.receipt.checkpointSha256,weightsSha256:sha(checked.weightsBytes),
    preparedWeightsSha256:sha(words64(reference.preparedWeights)),shaderSha256:sha(checked.shader),
    bridgeSha256:sha(checked.hostBytes),finishSha256:sha(checked.finishBytes),
    profile:checked.metadata.profile,runtimeConformanceEstablished:false,wasmRuntime:{node:process.version,v8:process.versions.v8}};
  try {
    const started=performance.now();
    const bridge=instantiate(checked.hostBytes,checked.metadata,inputs => nativeDispatch(checked,inputs,base+"-native.log"));
    const memory=bridge.instance.exports.memory,view=new DataView(memory.buffer),a=64,b=128,c=4288;
    reference.a.forEach((w,i)=>view.setUint32(a+4*i,Number(w),true));
    reference.b.forEach((w,i)=>view.setUint32(b+4*i,Number(w),true));
    const before=Buffer.from(new Uint8Array(memory.buffer));
    requireThat(bridge.instance.exports.run(a,b,c)===0&&bridge.calls===1,"head dispatch failed");
    const after=Buffer.from(memory.buffer);
    requireThat(after.subarray(0,c).equals(before.subarray(0,c))&&after.subarray(c+1024).equals(before.subarray(c+1024)),
      "bridge changed memory outside output");
    const head=Array.from({length:256},(_,j)=>view.getUint32(c+4*j,true).toString());
    requireThat(isDeepStrictEqual(head,reference.headWords),"raw head words differ from Lean");
    const finish=new WebAssembly.Instance(new WebAssembly.Module(checked.finishBytes),{});
    const scratch=Buffer.alloc(8),logits=head.map((_,j)=>{
      scratch.writeDoubleLE(view.getFloat32(c+4*j,true));
      const promoted=scratch.readBigUInt64LE();
      requireThat(promoted.toString()===reference.promotedWords[j],"promotion differs from Lean");
      return BigInt.asUintN(64,finish.exports.finish(promoted,BigInt(reference.bias[j]))).toString();
    });
    requireThat(isDeepStrictEqual(logits,reference.logits),"final logits differ from Lean mixed function");
    const values=logits.map(decimal);requireThat(values.every(Number.isFinite),"nonfinite logit");
    const ranked=values.map((logit,token)=>({token,byte:JSON.stringify(String.fromCharCode(token)),logit})).sort((x,y)=>y.logit-x.logit||x.token-y.token);
    Object.assign(report,{status:"pass",hidden:reference.hidden,headWords:head,logits,checkedRawHeadWords:256,checkedLogits:256,
      bridgeMemoryOutsideOutputPreserved:true,runtime:bridge.last.runtime,headAndFinishMs:performance.now()-started,
      topBytes:ranked.slice(0,8),maximumObservedDifferenceFromBinary64:Math.max(...values.map((x,j)=>Math.abs(x-decimal(reference.binary64Logits[j]))))});
    console.log(`GPT2/128 passed: ${tokens.length} input bytes; 256 raw head words and 256 logits match Lean; top byte ${ranked[0].token}`);
    return report;
  } catch(error) {report.error=error.message;throw error;}
  finally {json(base+".json",report);}
}

function parseRun(args) {
  let bound=10,tokens;
  if(args[0]==="--bound") {requireThat(args.length>=2,"missing bound");bound=Number(args[1]);args=args.slice(2);}
  if(args[0]==="--text"&&args.length===2) tokens=[...Buffer.from(args[1],"utf8")];
  else if(args[0]==="--tokens"&&args.length>1&&args.slice(1).every(x=>/^(0|[1-9][0-9]*)$/.test(x))) tokens=args.slice(1).map(Number);
  else throw Error("expected [--bound B] --text TEXT or --tokens T0 ...");
  requireThat(tokensValid(tokens),"expected 1 to 128 byte tokens");boundWord(bound);return {tokens,bound};
}
async function corpus(directory) {
  fs.mkdirSync(path.dirname(path.resolve(directory)),{recursive:true});fs.mkdirSync(directory);
  const config=JSON.parse(fs.readFileSync(path.join(__dirname,"gpt128-corpus.json"),"utf8"));
  const checked=await check(path.join(root,config.checkpoint)),results=[];
  for(const item of config.positive){
    const tokens=item.tokens || (item.range ? Array.from({length:item.range},(_,i)=>i) : Array(item.length).fill(item.repeat));
    const result=await run(checked,tokens,item.bound??10,item.name);
    results.push({name:item.name,status:result.status,length:tokens.length,
      evidence:path.relative(directory,path.join(checked.attempt,`gpt128-${item.name}.json`))});
  }
  for(const item of config.invalidTokens){
    const tokens=item.tokens || Array(item.length).fill(item.repeat);
    requireThat(!tokensValid(tokens),`invalid context accepted: ${item.name}`);
    results.push({name:item.name,status:"rejected"});
  }
  json(path.join(directory,"corpus.json"),{schemaVersion:1,status:"pass",verification:path.relative(directory,path.join(checked.attempt,"gpt128-verification.json")),
    checkedRawHeadWords:256*config.positive.length,checkedLogits:256*config.positive.length,results});
  console.log(`GPT2/128 corpus passed: ${directory}; evidence ${checked.attempt}`);
}
async function main([command,directory,...args]) {
  if(command==="wgsl-gpt128-run") {const input=parseRun(args);const checked=await check(directory);await run(checked,input.tokens,input.bound,"input");console.log(`Evidence: ${checked.attempt}`);}
  else if(command==="wgsl-gpt128-corpus") {requireThat(args.length===0,"unexpected arguments");await corpus(directory);}
  else throw Error(`unknown GPT2/128 command: ${command}`);
}
module.exports={main,check,run,checkpoint,tokensValid,parseRun};
