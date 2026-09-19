// Test bindings only. Tokenization, decoding and token selection execute in Wasm.
import fs from "node:fs";
import path from "node:path";
const [bundle,inputFile,outputFile]=process.argv.slice(2);
const input=JSON.parse(fs.readFileSync(inputFile,"utf8"));
const load=async name=>(await WebAssembly.instantiate(fs.readFileSync(path.join(bundle,name)))).instance.exports;
const tokenizer=await load("tokenizer.wasm"),sampler=await load("sampler.wasm");
const table=fs.readFileSync(path.join(bundle,"tokenizer.bin"));
function array(w,data){
  const p=w.alloc(BigInt(8+data.byteLength));
  new DataView(w.memory.buffer).setBigUint64(Number(p),BigInt(data.byteLength/8),true);
  new Uint8Array(w.memory.buffer,Number(p)+8,data.byteLength).set(data);return p;
}
function encodeWords(values){
  const data=new Uint8Array(values.length*8),view=new DataView(data.buffer);
  values.forEach((v,i)=>view.setBigUint64(i*8,BigInt(v),true));return data;
}
function result(w,p){
  const view=new DataView(w.memory.buffer),n=Number(view.getBigUint64(Number(p),true));
  if(n>65536||Number(p)+8+n*8>view.byteLength)throw Error("Wasm result bounds");
  return Array.from({length:n},(_,i)=>view.getBigUint64(Number(p)+8+i*8,true));
}
function tokens(op,values){
  tokenizer.reset();return result(tokenizer,tokenizer.tokens(BigInt(op),array(tokenizer,table),array(tokenizer,encodeWords(values))));
}
const cases=input.texts.map(text=>{
  const encoded=tokens(0,Array.from(new TextEncoder().encode(text)));
  return {text,tokens:encoded.map(Number),decoded:tokens(1,encoded).map(Number)};
});
// Known bit patterns: zero logits except EOS = binary64 1. Greedy must select EOS.
sampler.reset();const logits=new Uint8Array(50257*8);
new DataView(logits.buffer).setBigUint64(50256*8,0x3ff0000000000000n,true);
const eos=result(sampler,sampler.compute(5n,array(sampler,logits),array(sampler,new Uint8Array()),
  array(sampler,encodeWords([0n,40n,42n])),0n));
fs.writeFileSync(outputFile,JSON.stringify({cases,eos:eos.map(String)})+"\n",{flag:"wx"});
