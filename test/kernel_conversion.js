#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const { S,V,P,L,A,arrow,encode } = require("./kernel_terms");
const prop=S(0), type=S(1), redex=A(L("A",type,V("A")),prop);
const redexFn=A(L("A",type,V("A")),arrow(prop,prop));
const withFunctions=(binder,body)=>binder("F",arrow(arrow(prop,prop),type),binder("f",arrow(prop,prop),body));
const etaIndex=A(V("F"),L("p",prop,A(V("f"),V("p"))));
const cases = [
  ["beta in domain",encode(L("x",redex,V("x")),arrow(prop,prop)),500,0],
  ["beta exposes function type",encode(L("f",redexFn,L("p",prop,A(V("f"),V("p")))),arrow(arrow(prop,prop),arrow(prop,prop))),1000,0],
  ["clear nonconvertible sorts",encode(L("x",redex,V("x")),arrow(type,type)),500,1],
  ["exhaustion distinct",encode(L("x",redex,V("x")),arrow(prop,prop)),1,5],
  // Eta for function-valued indices is deliberately unsupported.
  ["eta remains inconclusive",encode(
    withFunctions(L,L("x",A(V("F"),V("f")),V("x"))),
    withFunctions(P,arrow(A(V("F"),V("f")),etaIndex))),2000,3],
];
let artifact=compile("Conversion","checkConversion","m0-9");
let native=reference("Conversion",cases.map(([,c,f])=>`(checkConversion ${leanArray(c.graph)} ${c.roots.join(" ")} ${f}).toNat`));
for(const [i,[name,c,f,expected]] of cases.entries()) {
  assert.equal(BigInt(native[i]),BigInt(expected),`Lean: ${name}`);
  assert.equal(host.callI64(artifact,"checkConversion",[host.arrayU64(c.graph),...c.roots.map(host.i64),host.i64(f)]),BigInt(expected),`WASM: ${name}`);
}
const reductions = [
  ["beta",[0,0,0,1,0,0,3,0,1,4,2,0],3,100,[0,0]],
  ["capture avoidance",[0,0,0,1,1,0,3,0,1,3,0,2,1,0,0,4,3,4],5,100,[3,[0,0],[1,1]]],
  ["neutral",[1,0,0,0,0,0,4,0,1],2,100,[4,[1,0],[0,0]]],
  ["nontermination exhausts",[0,0,0,1,0,0,4,1,1,3,0,2,4,3,3],4,50,5],
];
artifact=compile("Reduce","reduceHead","m0-9-reduce");
native=reference("Reduce",reductions.map(([,g,r,f])=>`reduceHead ${leanArray(g)} ${r} ${f}`));
const words=text=>[...text.matchAll(/\d+/g)].map(m=>BigInt(m[0]));
function term(g,r){const i=Number(r)*3,t=Number(g[i]);return t<2?[t,Number(g[i+1])]:[t,term(g,g[i+1]),term(g,g[i+2])];}
for(const [i,[name,g,r,f,expected]] of reductions.entries()){
  const actual=words(host.call(artifact,"reduceHead","array-u64",[host.arrayU64(g),host.i64(r),host.i64(f)]));
  assert.deepEqual(actual,words(native[i]),name);
  if(typeof expected==="number")assert.deepEqual(actual,[BigInt(expected)],name);
  else {assert.equal(actual[0],0n,name);assert.deepEqual(term(actual.slice(2),actual[1]),expected,name);}
}
console.log(`checked ${cases.length} conversion and ${reductions.length} reduction cases in WASM/standard Lean; artifacts: m0-9, m0-9-reduce`);
