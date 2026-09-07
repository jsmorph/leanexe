#!/usr/bin/env node
"use strict";
const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");
const { loadArtifactRegistry, validateArtifactManifest, sha256 } = require("./artifact-manifest");
const { callI64Slots } = require("./wasmtime-host");

const repoRoot = path.resolve(__dirname, "..");
const dataset = "euler-rusanov-step-v1";
const artifactCase = "euler_rusanov_step";
const artifactSha256 = "0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511";
const exportedFunction = "sodQuarterStepCheckedBits";
const expectedWords = Object.freeze([
  0n, 0x3fe9e00000000000n, 0x3fbcccccccccccccn, 0x4000100000000000n,
  0x3fd4400000000000n, 0x3fbccccccccccccen, 0x3fe7c00000000000n,
]);

function gcd(a, b) {
  a = a < 0n ? -a : a; b = b < 0n ? -b : b;
  while (b) [a, b] = [b, a % b];
  return a;
}
// Independent exact rational reference; no native floating arithmetic here.
function rational(n, d = 1n) {
  n = BigInt(n); d = BigInt(d);
  if (!d) throw new Error("zero rational denominator");
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d);
  return [n / g, d / g];
}
const add = (a, b) => rational(a[0]*b[1] + b[0]*a[1], a[1]*b[1]);
const sub = (a, b) => rational(a[0]*b[1] - b[0]*a[1], a[1]*b[1]);
const mul = (a, b) => rational(a[0]*b[0], a[1]*b[1]);
const div = (a, b) => rational(a[0]*b[1], a[1]*b[0]);
const text = a => a[1] === 1n ? `${a[0]}` : `${a[0]}/${a[1]}`;
function decode(word) {
  if (word < 0n || word >= (1n << 64n)) throw new Error("not a UInt64 word");
  const exponent = Number((word >> 52n) & 2047n);
  if (exponent === 2047) throw new Error("nonfinite payload");
  let magnitude = word & ((1n << 52n) - 1n);
  if (exponent) magnitude += 1n << 52n;
  if (word >> 63n) magnitude = -magnitude;
  const power = exponent ? exponent - 1075 : -1074;
  return power >= 0 ? rational(magnitude << BigInt(power)) : rational(magnitude, 1n << BigInt(-power));
}
const zero = rational(0), half = rational(1, 2), quarter = rational(1, 4);
const gammaMinusOne = rational(2, 5), alpha = rational(7, 4);
function conservative([rho, u, p]) {
  return [rho, mul(rho, u), add(div(p, gammaMinusOne), mul(half, mul(rho, mul(u, u))))];
}
function physicalFlux(state) {
  const [rho, u, p] = state, U = conservative(state);
  return [U[1], add(mul(U[1], u), p), mul(add(U[2], p), u)];
}
function flux(left, right) {
  const a = conservative(left), b = conservative(right);
  const fa = physicalFlux(left), fb = physicalFlux(right);
  return fa.map((v, i) => sub(mul(half, add(v, fb[i])), mul(mul(half, alpha), sub(b[i], a[i]))));
}
function exactReference() {
  const left = [rational(1), zero, rational(1)];
  const right = [rational(1, 8), zero, decode(0x3fb999999999999an)];
  const ul = conservative(left), ur = conservative(right);
  const ll = flux(left, left), lr = flux(left, right), rr = flux(right, right);
  return [ul.map((v, i) => sub(v, mul(quarter, sub(lr[i], ll[i])))),
    ur.map((v, i) => sub(v, mul(quarter, sub(rr[i], lr[i]))))];
}
function compareNumerics(words) {
  assert.deepEqual(words, expectedWords, "runtime words differ from the proved fixed dataset");
  const cells = [words.slice(1, 4).map(decode), words.slice(4, 7).map(decode)];
  const reference = exactReference();
  const errors = cells.map((cell, j) => cell.map((v, i) => sub(v, reference[j][i])));
  const epsilon = rational(1, 1n << 52n);
  const expectedErrors = [[zero, mul(epsilon, rational(-3, 64)), mul(epsilon, rational(-7, 512))],
    [zero, mul(epsilon, rational(5, 64)), mul(epsilon, rational(-25, 512))]];
  assert.deepEqual(errors, expectedErrors, "independent exact-rational cell error mismatch");
  const residual = errors[0].map((e, i) => add(e, errors[1][i]));
  assert.deepEqual(residual, [zero, mul(epsilon, rational(1, 32)), mul(epsilon, rational(-1, 16))]);
  const pressures = cells.map(([rho, momentum, energy]) => {
    assert.ok(rho[0] > 0n, "nonpositive decoded density");
    const pressure = mul(gammaMinusOne, sub(energy, div(mul(momentum, momentum), mul(rational(2), rho))));
    assert.ok(pressure[0] > 0n, "nonpositive exact decoded pressure");
    return pressure;
  });
  return { cells, reference, errors, residual, pressures };
}
const decimal = r => Number(r[0]) / Number(r[1]);
function plotCells(cells) {
  const initial = [[1,0,2.5],[0.125,0,0.25]];
  const updated = cells.map(cell => cell.map(decimal));
  const labels = ["Density", "Momentum", "Energy"];
  const parts = [
    '<svg xmlns="http://www.w3.org/2000/svg" width="1080" height="410" viewBox="0 0 1080 410" role="img" aria-labelledby="title desc">',
    '<title id="title">Verified two-cell Sod update</title>',
    '<desc id="desc">Initial and updated conservative cell averages for the fixed Rusanov step. This plot is host presentation outside the formal proof.</desc>',
    '<rect width="1080" height="410" fill="#f7f9fb"/>',
    '<g font-family="Arial, sans-serif" fill="#183047">',
    '<text x="42" y="40" font-size="24" font-weight="700">Verified two-cell Sod update</text>',
    '<text x="42" y="67" font-size="14">t = 1/8 · gamma = 7/5 · alpha = 7/4 · dt/dx = 1/4</text>',
    '<path d="M745 40h28" stroke="#83929f" stroke-width="2" stroke-dasharray="6 4"/><text x="782" y="45" font-size="13">Initial</text>',
    '<path d="M895 40h28" stroke="#187aa0" stroke-width="3"/><text x="932" y="45" font-size="13">Updated</text>',
  ];
  for (let i=0;i<3;++i) {
    const left=68+i*350, top=126, width=268, height=204;
    const max=Math.max(initial[0][i],initial[1][i],updated[0][i],updated[1][i])*1.15;
    const y=v=>(top+height-height*v/max).toFixed(3);
    parts.push(`<text x="${left}" y="106" font-size="16" font-weight="700">${labels[i]}</text>`);
    for(const fraction of [0,0.5,1]) {
      const value=max*fraction, py=y(value);
      parts.push(`<path d="M${left} ${py}h${width}" stroke="#dbe3e9"/><text x="${left-9}" y="${Number(py)+4}" text-anchor="end" font-size="11">${value.toPrecision(3)}</text>`);
    }
    for(const [data,color,dash] of [[initial,"#83929f",' stroke-dasharray="6 4"'],[updated,"#187aa0",""]]) {
      parts.push(`<path d="M${left} ${y(data[0][i])}H${left+width/2}V${y(data[1][i])}H${left+width}" fill="none" stroke="${color}" stroke-width="3"${dash}/>`);
    }
    for(const [fraction,label] of [[0,"0"],[0.5,"0.5"],[1,"1"]])
      parts.push(`<text x="${left+width*fraction}" y="350" text-anchor="middle" font-size="12">${label}</text>`);
    parts.push(`<text x="${left+width/2}" y="370" text-anchor="middle" font-size="12">Position x</text>`);
  }
  parts.push('<text x="42" y="398" font-size="12" fill="#52687a">Lines show cell averages. Presentation only; exact words and theorem references accompany the dataset.</text></g></svg>');
  return `${parts.join("\n")}\n`;
}
function buildDataset() {
  const { registry } = loadArtifactRegistry(repoRoot);
  const entry = registry.artifacts.find(x => x.case === artifactCase);
  assert.ok(entry, "fixed-step exact artifact is not registered");
  assert.equal(entry.sha256, artifactSha256);
  const artifact = validateArtifactManifest(repoRoot, entry);
  assert.equal(artifact.manifest.byteLength, 2551);
  assert.deepEqual(artifact.manifest.hostAssumptions, []);
  const words = callI64Slots(artifact.binaryPath, exportedFunction, 7, []);
  const checked = compareNumerics(words);
  const hex = w => w.toString(16).padStart(16, "0");
  const rawCsv = "cell,center_x,status_u64,density_bits,momentum_bits,energy_bits\n" +
    [0, 1].map(j => [j === 0 ? "left" : "right", j === 0 ? "0.25" : "0.75", "0",
      ...words.slice(1 + 3*j, 4 + 3*j).map(hex)].join(",")).join("\n") + "\n";
  const comparisonCsv = "cell,component,decoded_exact,reference_exact,signed_error\n" +
    checked.cells.flatMap((cell,j) => cell.map((v,i) => [j ? "right" : "left",
      ["density","momentum","energy"][i],text(v),text(checked.reference[j][i]),text(checked.errors[j][i])].join(","))).join("\n") + "\n";
  const presentationCsv = "cell,center_x,density,momentum,energy,velocity,pressure\n" +
    checked.cells.map((cell,j) => [j?"right":"left",j?"0.75":"0.25",
      ...[...cell,div(cell[1],cell[0]),checked.pressures[j]].map(r=>decimal(r).toPrecision(17))].join(",")).join("\n")+"\n";
  const svg=plotCells(checked.cells);
  const source = fs.readFileSync(__filename);
  const manifest = {
    schemaVersion: 1, dataset, registryEntry: artifactCase, wasmSha256: artifactSha256,
    wasmByteLength: 2551, exportedFunction, rowOrder: ["left", "right"],
    wordEncoding: "lowercase fixed-width 16-digit hexadecimal; raw IEEE 754 binary64",
    parameters: {gamma:"7/5",alpha:"7/4",dtOverDx:"1/4",dx:"1/2",dt:"1/8",rightPressureBits:"3fb999999999999a"},
    formalProofModule: "Project.EulerRusanovStep.StepData",
    formalProofTheorem: "Project.EulerRusanovStep.StepData.artifact_stepV1",
    generatorSourceSha256: sha256(source),
    rawCsv: {file:`${dataset}.csv`,sha256:sha256(Buffer.from(rawCsv)),byteLength:Buffer.byteLength(rawCsv)},
    comparison: {file:"exact-comparison.csv",sha256:sha256(Buffer.from(comparisonCsv)),
      description:"Independent host rational regression against the dyadic-input Euler stencil; not formal proof evidence"},
    presentation: [{file:"presentation.csv",sha256:sha256(Buffer.from(presentationCsv))},
      {file:"cell-averages.svg",sha256:sha256(Buffer.from(svg))}],
    exactDecodedBalanceResidual: checked.residual.map(text),
    exactDecodedPressures: checked.pressures.map(text),
    claim: "One fixed two-cell Sod step, finite and admissible, with exact signed rounding errors; no full-solver or convergence claim",
  };
  return {words,checked,files:new Map([[`${dataset}.csv`,rawCsv],["exact-comparison.csv",comparisonCsv],
    ["presentation.csv",presentationCsv],["cell-averages.svg",svg],
    ["manifest.json",`${JSON.stringify(manifest,null,2)}\n`]])};
}
function publish(built, write) {
  const dir = path.join(repoRoot,"data",dataset);
  if(write)fs.mkdirSync(dir,{recursive:true});
  for(const [name,contents] of built.files) {
    const file=path.join(dir,name);
    if(fs.existsSync(file))assert.equal(fs.readFileSync(file,"utf8"),contents,`refusing to replace differing ${file}`);
    else if(write)fs.writeFileSync(file,contents,{flag:"wx"});
    else throw new Error(`missing published dataset file: ${file}`);
  }
}
if(require.main===module) {
  try {
    const cmd=process.argv[2]||"check";
    assert.ok(process.argv.length<=3&&["write","check"].includes(cmd),"usage: node tools/euler-rusanov-step-data.js [write|check]");
    const built=buildDataset();publish(built,cmd==="write");
    console.log(`checked ${dataset}: exact seven WASM words, six rational cell errors, admissibility, and nonzero balance residual`);
  }catch(error){console.error(error.message);process.exitCode=1;}
}
module.exports={dataset,expectedWords,decode,compareNumerics,buildDataset,publish};
