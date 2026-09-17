"use strict";
const fs = require("node:fs");
const path = require("node:path");
const root = path.resolve(__dirname, "../../..");
function adversarial(direction) {
  const w = new Float64Array(2488), s = [1, 1, -1, -1];
  for (let i = 0; i < 4; i++) {
    w[i] = s[i]; w[4+i] = -s[i]; w[12+i] = 1;
    w[1036+i] = direction * 2 ** -55 * s[i];
    for (const offset of [2464, 2472, 2480]) w[offset+i] = 4;
    for (let j = 0; j < 4; j++) {
      w[1040+4*i+j] = w[1056+4*i+j] = 4*s[i];
      w[1072+4*i+j] = w[1088+4*i+j] = 4*s[i]*s[j];
    }
    for (let j = 0; j < 8; j++) w[1108+8*i+j] = 4*s[i];
    for (let j = 0; j < 256; j++) w[1184+256*i+j] = 4*s[i]*(j%2 ? -1 : 1);
  }
  for (let i = 0; i < 8; i++) for (let j = 0; j < 4; j++) w[1148+4*i+j] = 4*s[j];
  const bytes = Buffer.alloc(2488*8);
  w.forEach((x, i) => bytes.writeDoubleLE(x, i*8));
  return bytes;
}
function cases() {
  const weights = fs.readFileSync(path.join(root, "test/wgsl/gpt/weights.bin"));
  return [
    { name: "checkpoint-lean", tokens: [76,101,97,110], weights },
    { name: "checkpoint-zeros", tokens: [0,0,0,0], weights },
    { name: "checkpoint-byte-edges", tokens: [255,128,1,0], weights },
    ...[1,-1,0].map(direction => ({ name: `adversarial-${direction===1 ? "plus" : direction===-1 ? "minus" : "zero"}`,
      tokens: [0,1,2,3], weights: adversarial(direction) })),
  ];
}
module.exports = { root, cases, adversarial };
