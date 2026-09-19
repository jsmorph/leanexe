#!/usr/bin/env node
"use strict";
// Replay the parent's controller proofs against the independently parsed hybrid
// module. Every generated declaration is checked by Lean; text substitution is
// proof preparation, never a certificate of equivalence.
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
const {spawnResultAsync}=require("../../run-process");
const {proofSource}=require("./packed-regions");
const {lean,audit}=require("../package");
const root=path.resolve(__dirname,"../../.."),proofRoot=path.join(root,"proofs/talos/lean");
const parent="Project.Gpt2CachedStep",hybrid="Project.Gpt2Hybrid";
const sourceRoot=path.join(proofRoot,"Project/Gpt2CachedStep");
const hash=s=>crypto.createHash("sha256").update(s).digest("hex");
const replaceNamespace=s=>s.replaceAll(parent,hybrid);
const read=rel=>fs.readFileSync(path.join(sourceRoot,rel+".lean"),"utf8");

function shiftCalls(s) {
  return s.replace(/\.call (\d+)/g,(_,n)=>`.call ${Number(n)+2}`)
    .replace(/(TerminatesWith env «module» )(\d+)/g,(_,p,n)=>p+(Number(n)+2))
    .replace(/(PackedWordRead\.exact «module» )17/g,"$119")
    .replace(/(PackedAllocExport\.exact «module» env )39/g,"$141")
    .replace(/(PackedReleaseMany\.program_spec env «module» )42/g,"$144")
    .replace(/(PackedReleaseMany\.program [^\n]*? )42(?=\s*(?:\+\+|:=|=))/g,"$144")
    .replace(/(PackedReleaseGuard\.programTwo owner 164 161 )42/g,"$144")
    .replace(/(«module»\.findExport "[^"]+" = some )(\d+)/g,(_,p,n)=>p+(Number(n)+2));
}

// The selected parent theorem headers use named, typed binders. Preserve the
// entire header; collect only top-level binder names to apply the old theorem.
function theoremHeader(text,name) {
  const start=text.indexOf(`theorem ${name} `);
  if(start<0)throw Error(`missing parent theorem ${name}`);
  const assignment=/ :=(?: by|\n  (?=\S))/.exec(text.slice(start));
  if(!assignment)throw Error(`missing theorem assignment ${name}`);
  const end=start+assignment.index;
  const header=text.slice(start,end),names=[];
  let pos=`theorem ${name} `.length;
  for(;pos<header.length;) {
    if(/\s/.test(header[pos])){pos++;continue;}
    if(header[pos]===":")break;
    if(!"({".includes(header[pos]))throw Error(`unsupported binder in ${name}: ${header.slice(pos,pos+30)}`);
    const from=++pos;let depth=1;
    for(;pos<header.length&&depth;pos++) {
      if("({[".includes(header[pos]))depth++;
      if(")}]".includes(header[pos]))depth--;
    }
    const binder=header.slice(from,pos-1),colon=binder.indexOf(":");
    if(colon<0)throw Error(`untyped binder in ${name}`);
    names.push(...binder.slice(0,colon).trim().split(/\s+/));
  }
  return {header,names};
}

function transported(rel,name,index) {
  const original=read(rel),ns=original.match(/^namespace (.+)$/m)[1];
  const {header,names}=theoremHeader(original,name);
  const opens=[...original.matchAll(/^open (.+)$/gm)].map(m=>m[0]).join("\n");
  return `import ${parent}.${rel.replaceAll("/",".")}
import ${hybrid}.Program
namespace ${replaceNamespace(ns)}
open ${parent} ${ns.split(".").slice(0,-1).join(".")} ${ns}
${opens}
${shiftCalls(header)} := by
  exact helper_correct env ${index} (by decide) _ _ _
    (${ns}.${name} ${names.join(" ")})
#print axioms ${name}
end ${replaceNamespace(ns)}
`;
}

async function compose(emitted,shaders,attempt,{resume=false,through=null}={}) {
  emitted=path.resolve(emitted);shaders=path.resolve(shaders);attempt=path.resolve(attempt);
  if(fs.existsSync(attempt)&&!resume)throw Error("attempt exists; use a fresh directory or --resume");
  const src=path.join(attempt,"src"),lib=path.join(attempt,"lib"),logs=path.join(attempt,"logs");
  fs.mkdirSync(logs,{recursive:true});fs.mkdirSync(lib,{recursive:true});
  const units=new Map();
  units.set("Program",proofSource(emitted).code.replaceAll("Project.Gpt2PackedRuntime",hybrid));
  const roles=["qkv","attention","expansion","projection","vocabularyLeft","vocabularyRight"];
  const shader=role=>JSON.stringify(fs.readFileSync(path.join(shaders,role,"kernel.wgsl"),"utf8"));
  for(const role of roles)units.set(`Certificate/${role}`,`import Project.Gpt2.PackedBackend\n`+
    fs.readFileSync(path.join(shaders,role,"source-equality.lean.txt"),"utf8"));
  units.set("Backend",roles.map(r=>`import ${hybrid}.Certificate.${r}`).join("\n")+`
import ${hybrid}.Program
namespace ${hybrid}
open Project.Gpt2.PackedBackend
def kernels : Kernels where
  text role := match role with
    | .qkv => ${shader("qkv")}
    | .attention => ${shader("attention")}
    | .expansion => ${shader("expansion")}
    | .projection => ${shader("projection")}
  checked role := by
    cases role
    · exact LeanExe.WGSL.Gpt2Packed.qkv.wgslExecutionCorrect
    · exact LeanExe.WGSL.Gpt2Packed.attention.wgslExecutionCorrect
    · exact LeanExe.WGSL.Gpt2Packed.expansion.wgslExecutionCorrect
    · exact LeanExe.WGSL.Gpt2Packed.projection.wgslExecutionCorrect
  leftText := ${shader("vocabularyLeft")}
  rightText := ${shader("vocabularyRight")}
  leftChecked := LeanExe.WGSL.Gpt2.vocabularyLeft.wgslExecutionCorrect
  rightChecked := LeanExe.WGSL.Gpt2.vocabularyRight.wgslExecutionCorrect
instance : Code «module» := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end ${hybrid}
`);
  // Transfer proved helper contracts via the closed call-region theorem.
  const layouts=[...read("Layout").matchAll(/theorem (\w+_exact)[\s\S]*?TerminatesWith env «module» (\d+)/g)];
  units.set("Layout",layouts.map(([,n,i])=>transported("Layout",n,Number(i))).join("\n")
    .replace(/\nimport [^\n]+/g,"") // put imports once, before all declarations
    .replace(/^import [^\n]+/,`import ${parent}.Layout\nimport ${hybrid}.Program`));
  const helperSpecs=[["LayerNorm/Spec","layerNorm_exact",20],["CachedAttention/Spec","cachedAttention_exact",29],
    ["AddRows/Spec","addRows_exact",30],["Activate/Spec","activate_exact",32],["Release","release_owned",42]];
  for(const [rel,n,i] of helperSpecs)units.set(rel,transported(rel,n,i));
  units.set("WordRead",`import Project.ProofKit.PackedWordRead
import ${hybrid}.Program
namespace ${hybrid}.PackedWordReadBridge
open Wasm Project.ProofKit PackedMemory
theorem exact (env : HostEnv Unit) (initial : Store Unit) (owner ptr : UInt64)
    (bytes : ByteArray) (index : Nat) (hBytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hValid : index * 4 + 4 ≤ bytes.size) :
    TerminatesWith env «module» 19 initial
      [.i64 (UInt64.ofNat index), .i64 (UInt64.ofNat bytes.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Packed.getUInt32LE! bytes (index * 4)).toUInt64]) :=
  helper_correct env 17 (by decide) _ _ _
    (PackedWordRead.exact ${parent}.«module» 17 (some 17) rfl rfl env initial owner ptr bytes index hBytes hValid)
#print axioms exact
end ${hybrid}.PackedWordReadBridge
`);
  units.set("Vocabulary/Spec",`import ${parent}.Vocabulary.Spec
import ${hybrid}.Backend
namespace ${hybrid}.Vocabulary.Spec
open Wasm
def vocabularyHead_exact (env : HostEnv Unit) [Project.Gpt2.PackedBackend.Host «module» env kernels] :=
  Project.Gpt2.PackedBackend.vocabulary_exact «module» env kernels
end ${hybrid}.Vocabulary.Spec
`);
  // Controller proof text is reused, with only function-index renaming,
  // explicit external-host assumptions, and the four replacement leaf calls.
  const copies=["Initialize","Spec"];
  for(const dir of ["CachedBlock","CachedHidden","Entry","Session"])
    for(const file of fs.readdirSync(path.join(sourceRoot,dir)).filter(x=>x.endsWith(".lean")))
      copies.push(`${dir}/${file.slice(0,-5)}`);
  const redirect=new Set([...units.keys(),...copies]);
  const matrixRoles={Qkv:["qkv",768,2304],Projection:["attention",768,768],Expanded:["expansion",768,3072],Projected2:["projection",3072,768]};
  for(const rel of copies) {
    let text=read(rel);
    text=text.replace(/^import Project\.Gpt2CachedStep\.([\w.]+)$/gm,(all,suffix)=>
      redirect.has(suffix.replaceAll(".","/"))?`import ${hybrid}.${suffix}`:all);
    text=text.replace(/^(namespace|end) Project\.Gpt2CachedStep(.*)$/gm,`$1 ${hybrid}$2`);
    text=shiftCalls(text);
    if(text.includes("PackedWordRead.exact «module» 19")) {
      text=text.replaceAll("PackedWordRead.exact «module» 19 (some 17) rfl rfl env","PackedWordReadBridge.exact env");
      text=`import ${hybrid}.WordRead\n`+text;
    }
    text=text.replace(/theorem ([\s\S]*?)(?= :=)/g,(all)=>all.replace(/\(env : HostEnv Unit\)/g,
      "(env : HostEnv Unit) [Project.Gpt2.PackedBackend.Host «module» env kernels]"));
    text=text.replace(/^namespace (.+)$/gm,(all,ns)=>all+`\nopen ${parent}\nopen ${ns.replace(hybrid,parent)}`);
    text=`import ${hybrid}.Backend\nimport ${hybrid}.Layout\nimport ${hybrid}.Release\nimport ${parent}.${rel.replaceAll("/",".")}\n`+text;
    const leaf=rel.split("/").at(-1),role=matrixRoles[leaf];
    if(role&&rel.startsWith("CachedBlock/")) {
      const [name,inner,cols]=role;
      text=text.replace("LinearRows.Spec.linearRows_owned env initial heap",
        `Project.Gpt2.PackedBackend.linear_owned «module» env kernels .${name} initial heap`);
      text=text.replace(`${inner} ${cols} 1\n    hHeap`,"\n    hHeap");
      text=text.replace("(by decide) (by decide) (by decide) hResources","hResources");
      text=text.replace(/\(by rw \[(h\w+Size)\]\)/g,"(by rw [$1]; decide)");
      text=text.replace(/(  simp only \[h\w+Size\] at hCall)/,
        "  dsimp only [Project.Gpt2.PackedBackend.Role.inner, Project.Gpt2.PackedBackend.Role.cols, Project.Gpt2.PackedLinear.need, Project.Gpt2.PackedLinear.bytes] at hCall\n$1");
    }
    units.set(rel,text);
  }
  // All imports must name an available unit; Lean also checks each literal
  // controller body against the actual parsed function declarations.
  for(const [rel,original] of units) {
    const text=original.replace(/^import Project\.Gpt2Hybrid\./gm,"import Gpt2Hybrid.");
    units.set(rel,text);
    const file=path.join(src,"Gpt2Hybrid",rel+".lean");fs.mkdirSync(path.dirname(file),{recursive:true});
    if(!fs.existsSync(file)||fs.readFileSync(file,"utf8")!==text)fs.writeFileSync(file,text);
  }
  let run=1;while(fs.existsSync(path.join(logs,`run-${run}.json`)))run++;
  const record={status:"running",units:[],fullHybridSessionProved:false};
  const recordPath=path.join(logs,`run-${run}.json`);
  const save=()=>fs.writeFileSync(recordPath,JSON.stringify(record,null,2)+"\n");save();
  try {
    await lean("hybrid composition dependencies",["lake","-d",proofRoot,"build","Project.Gpt2.PackedBackend",
      "Project.FunctionRegion.Imports","Project.Gpt2CachedStep.Session.Spec"],path.join(logs,`dependencies-${run}.log`));
    const paths=await spawnResultAsync([path.join(root,"tools/leanrun"),"--timeout","30s","lake","-d",proofRoot,
      "env","node","-e","console.log('LEAN_PATH_JSON '+JSON.stringify(process.env.LEAN_PATH))"],{cwd:root,env:process.env,stdio:["ignore","pipe","pipe"]});
    if(paths.status!==0)throw Error("cannot resolve checked dependency paths");
    process.env.LEAN_PATH=lib+path.delimiter+JSON.parse(paths.stdout.toString().split("\n").find(l=>l.startsWith("LEAN_PATH_JSON ")).slice(15));
    const externalStamps=new Map();
    const externalStamp=name=>{
      if(externalStamps.has(name))return externalStamps.get(name);
      const file=process.env.LEAN_PATH.split(path.delimiter).map(p=>path.join(p,name.replaceAll(".","/")+".olean")).find(fs.existsSync);
      if(!file)throw Error(`missing checked external dependency ${name}`);
      const stamp=hash(fs.readFileSync(file));externalStamps.set(name,stamp);return stamp;
    };
    const done=new Map(),visiting=new Set();
    async function build(rel) {
      if(done.has(rel))return done.get(rel);
      if(visiting.has(rel))throw Error(`cyclic proof dependency ${rel}`);
      visiting.add(rel);const code=units.get(rel);if(code===undefined)throw Error(`missing generated proof ${rel}`);
      const imports=[...code.matchAll(/^import Gpt2Hybrid\.([\w.]+)$/gm)].map(m=>m[1].replaceAll(".","/"));
      const stamps=[];for(const dep of imports)stamps.push(await build(dep));
      for(const [,name] of code.matchAll(/^import ([\w.]+)$/gm))
        if(!name.startsWith("Gpt2Hybrid."))stamps.push(externalStamp(name));
      const stamp=hash(code+stamps.join("")),out=path.join(lib,"Gpt2Hybrid",rel+".olean");
      const receipt=out+".json",old=fs.existsSync(receipt)?JSON.parse(fs.readFileSync(receipt)):null;
      if(!old||old.stamp!==stamp||!fs.existsSync(out)) {
        fs.mkdirSync(path.dirname(out),{recursive:true});
        const output=await lean(`hybrid ${rel}`,["lean","--root",src,"-o",out,path.join(src,"Gpt2Hybrid",rel+".lean")],
          path.join(logs,`${rel.replaceAll("/","-")}-${run}.log`));
        const names=[...output.matchAll(/'([^']+)' (?:depends on axioms:|does not depend on any axioms)/g)].map(m=>m[1]);
        fs.writeFileSync(receipt,JSON.stringify({stamp,axioms:audit(output,names)},null,2)+"\n");
      }
      visiting.delete(rel);done.set(rel,stamp);record.units.push(rel);save();return stamp;
    }
    await build(through||"Session/Spec");
    if(!through)await build("Spec");
    record.status="pass";record.fullHybridSessionProved=!through;save();
    console.log(`Hybrid composition ${through||"step and session"} checked: ${recordPath}`);
  } catch(error) {record.status="failed";record.error=error.message;save();throw error;}
}
if(require.main===module) {
  const args=process.argv.slice(2),resume=args.includes("--resume"),at=args.indexOf("--through");
  const through=at<0?null:args[at+1];if(at>=0)args.splice(at,2);if(resume)args.splice(args.indexOf("--resume"),1);
  if(args.length!==3)throw Error("usage: packed-compose.js EMITTED_PROGRAM CHECKED_SHADERS ATTEMPT [--resume] [--through MODULE]");
  compose(...args,{resume,through}).catch(e=>{console.error(e.message);process.exitCode=1;});
}
module.exports={compose};
