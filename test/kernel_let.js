#!/usr/bin/env node
const { assert,host,compile,leanArray,reference }=require("./kernel_helpers");
const { S,V,P,L,A,E,arrow,encode }=require("./kernel_terms");
const prop=S(0), type=S(1);
const context=(binder,body)=>binder("p",prop,binder("hp",V("p"),body));
const identityType=P("p",prop,arrow(V("p"),V("p")));
const cases=[
  ["proof let",encode(context(L,E("h",V("p"),V("hp"),V("h"))),identityType),0],
  ["dependent local definition",encode(E("A",type,prop,L("x",V("A"),V("x"))),arrow(prop,prop)),0],
  ["unused valid value",encode(context(L,E("h",V("p"),V("hp"),V("hp"))),identityType),0],
  ["unused invalid value",encode(context(L,E("bad",prop,V("hp"),V("hp"))),identityType),1],
  ["invalid annotation",encode(context(L,E("bad",V("hp"),V("hp"),V("hp"))),identityType),1],
  ["let in function position",encode(A(E("f",arrow(prop,prop),L("p",prop,V("p")),V("f")),identityType),prop),0],
  ["zeta in claimed type",encode(L("p",prop,V("p")),E("A",type,prop,arrow(V("A"),V("A")))),0],
  ["bad binder container",{graph:[0,0,0,5,0,0],roots:[1,0]},4],
];
const artifact=compile("Let","checkLet","m0-10");
const native=reference("Let",cases.map(([,c])=>`(checkLet ${leanArray(c.graph)} ${c.roots.join(" ")} 3000).toNat`));
for(const [i,[name,c,expected]] of cases.entries()){
  assert.equal(BigInt(native[i]),BigInt(expected),`Lean: ${name}`);
  assert.equal(host.callI64(artifact,"checkLet",[host.arrayU64(c.graph),...c.roots.map(host.i64),host.i64(3000)]),BigInt(expected),`WASM: ${name}`);
}
console.log(`checked ${cases.length} M0.10 WASM/standard-Lean let judgments; artifact: ${artifact}`);
