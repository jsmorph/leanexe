#!/usr/bin/env node
const { assert, host, compile, leanArray, reference } = require("./kernel_helpers");
const { S,V,P,L,A,arrow,encode } = require("./kernel_terms");
const prop = S(0), type = S(1);
function compose(binder, body) {
  return binder("p",prop,binder("q",prop,binder("r",prop,
    binder("f",arrow(V("p"),V("q")),binder("g",arrow(V("q"),V("r")),binder("hp",V("p"),body))))));
}
function dependent(binder, body) {
  return binder("A",type,binder("P",arrow(V("A"),type),
    binder("f",P("x",V("A"),A(V("P"),V("x"))),binder("x",V("A"),body))));
}
const redex = A(L("A",type,V("A")),prop);
const cases = [
  ["implication composition",encode(compose(L,A(V("g"),A(V("f"),V("hp")))),compose(P,V("r"))),0],
  ["dependent application",encode(dependent(L,A(V("f"),V("x"))),dependent(P,A(V("P"),V("x")))),0],
  ["applied identity",encode(A(L("p",prop,V("p")),P("q",prop,arrow(V("q"),V("q")))),prop),0],
  ["wrong argument universe",encode(A(L("p",prop,V("p")),prop),prop),1],
  ["non-function",encode(A(prop,prop),prop),1],
  ["beta conversion now supported",encode(L("x",redex,V("x")),arrow(prop,prop)),0],
  ["sort beta now supported",encode(L("h",redex,L("p",V("h"),V("p"))),P("h",prop,arrow(V("h"),V("h")))),0],
];
const artifact = compile("Application","checkApplication","m0-8");
const native = reference("Application",cases.map(([,c]) => `(checkApplication ${leanArray(c.graph)} ${c.roots.join(" ")} 10000).toNat`));
for (const [i,[name,c,expected]] of cases.entries()) {
  assert.equal(BigInt(native[i]),BigInt(expected),`Lean: ${name}`);
  assert.equal(host.callI64(artifact,"checkApplication",[host.arrayU64(c.graph),...c.roots.map(host.i64),host.i64(10000)]),BigInt(expected),`WASM: ${name}`);
}
console.log(`checked ${cases.length} M0.8 WASM/standard-Lean application judgments; artifact: ${artifact}`);
