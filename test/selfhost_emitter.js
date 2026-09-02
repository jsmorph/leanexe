#!/usr/bin/env node

const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const { runChecked } = require("../tools/run-process");
const host = require("./wasmtime_host");

const leanExe = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const outDir = path.join(".lake", "build", "selfhost");
const wasm = path.join(outDir, "emitter-stage1.wasm");
const image = path.join(outDir, "emitter-stage1.image");
const reproduced = path.join(outDir, "emitter-stage2.wasm");
const moduleName = "LeanExe.Wasm.Image.Emit";
const sourceEntry = "LeanExe.Wasm.Image.emitImage";
const exportEntry = "emitImage";
const corpusDir = path.join(outDir, "corpus");
const corpusCases = JSON.parse(fs.readFileSync(path.join("proofs", "talos", "cases.json"))).cases;
const artifactRegistry = JSON.parse(
  fs.readFileSync(path.join("proofs", "artifacts", "registry.json")),
).artifacts;
const registeredArtifacts = new Map(artifactRegistry.map((item) => [item.case, item]));

function compileInputs() {
  fs.mkdirSync(outDir, { recursive: true });
  runChecked([
    leanExe,
    "compile",
    "--module",
    moduleName,
    "--entry",
    sourceEntry,
    "--out",
    wasm,
  ], { encoding: "utf8", stdio: "inherit" });
  runChecked([
    leanExe,
    "compile-image",
    "--module",
    moduleName,
    "--entry",
    sourceEntry,
    "--out",
    image,
  ], { encoding: "utf8", stdio: "inherit" });

  fs.mkdirSync(corpusDir, { recursive: true });
  for (const testCase of corpusCases) {
    const wasmOut = path.join(corpusDir, `${testCase.name}.wasm`);
    const imageOut = path.join(corpusDir, `${testCase.name}.image`);
    runChecked([
      leanExe,
      "compile",
      "--module",
      testCase.module,
      "--entry",
      testCase.entry,
      "--out",
      wasmOut,
    ], { encoding: "utf8", stdio: "inherit" });
    runChecked([
      leanExe,
      "compile-image",
      "--module",
      testCase.module,
      "--entry",
      testCase.entry,
      "--out",
      imageOut,
    ], { encoding: "utf8", stdio: "inherit" });
  }
}

function callExceptBytes(input, modulePath = wasm) {
  const commands = [`alloc 1 ${input.length}`];
  const chunkSize = 4096;
  for (let offset = 0; offset < input.length; offset += chunkSize) {
    const chunk = input.subarray(offset, Math.min(offset + chunkSize, input.length));
    commands.push(`write-bytes 1 ${offset} ${chunk.toString("hex")}`);
  }
  commands.push("arg-ptr 1", `arg-u64 ${input.length}`);
  const result = host.script(modulePath, commands, exportEntry, 5, [
    "read-memory result:1 result:2",
    "read-memory result:3 result:4",
  ]);
  const tag = Number(result.slots[0]);
  if (tag !== 0 && tag !== 1) {
    throw new Error(`emitImage returned invalid Except tag ${tag}`);
  }
  const ptrIndex = tag === 0 ? 1 : 3;
  const lenIndex = ptrIndex + 1;
  const ptr = result.slots[ptrIndex];
  const length = Number(result.slots[lenIndex]);
  const chunk = result.memoryChunks.find(
    (item) => item.start === ptr && item.bytes.length === length,
  );
  if (!chunk) {
    throw new Error(`emitImage result memory ${ptr}+${length} was not returned by the host`);
  }
  return { tag, bytes: Buffer.from(chunk.bytes) };
}

function digest(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function firstDifference(left, right) {
  const limit = Math.min(left.length, right.length);
  for (let index = 0; index < limit; index += 1) {
    if (left[index] !== right[index]) return index;
  }
  return left.length === right.length ? -1 : limit;
}

function expectBytes(label, actual, expected) {
  const difference = firstDifference(actual, expected);
  if (difference !== -1) {
    throw new Error(
      `${label}: mismatch at byte ${difference}; got ${actual.length} bytes, ` +
        `expected ${expected.length} bytes`,
    );
  }
}

function registeredArtifactBytes(testCase) {
  const registered = registeredArtifacts.get(testCase.name);
  if (!registered) throw new Error(`unregistered self-host corpus case ${testCase.name}`);
  return fs.readFileSync(path.join("proofs", "artifacts", path.dirname(registered.manifest), "program.wasm"));
}

function checkRegisteredCorpus() {
  for (const testCase of corpusCases) {
    const expected = registeredArtifactBytes(testCase);
    const native = fs.readFileSync(path.join(corpusDir, `${testCase.name}.wasm`));
    const caseImage = fs.readFileSync(path.join(corpusDir, `${testCase.name}.image`));
    expectBytes(`${testCase.name} native image route`, native, expected);

    const stage1 = callExceptBytes(caseImage);
    if (stage1.tag === 0) {
      throw new Error(`${testCase.name} Stage 1 error: ${stage1.bytes.toString("utf8")}`);
    }
    expectBytes(`${testCase.name} Wasmtime Stage 1`, stage1.bytes, expected);

    const stage2 = callExceptBytes(caseImage, reproduced);
    if (stage2.tag === 0) {
      throw new Error(`${testCase.name} Stage 2 error: ${stage2.bytes.toString("utf8")}`);
    }
    expectBytes(`${testCase.name} JavaScript Stage 2`, stage2.bytes, expected);
  }
}

function checkMalformedImages() {
  const magic = Buffer.from("LXEIMG", "ascii");
  const cases = [
    ["invalid magic", Buffer.from("bad image", "utf8"), "leanexe-image: invalid magic"],
    ["truncated profile", Buffer.concat([magic, Buffer.from([2])]), "leanexe-image: truncated field"],
    ["unsupported version", Buffer.concat([magic, Buffer.from([99])]), "leanexe-image: unsupported version"],
    ["unsupported profile", Buffer.concat([magic, Buffer.from([2, 99])]), "leanexe-image: unsupported profile"],
    ["noncanonical version", Buffer.concat([magic, Buffer.from([0x82, 0])]), "leanexe-image: noncanonical integer"],
  ];
  for (const [name, input, expected] of cases) {
    for (const [hostName, result] of [
      ["Wasmtime Stage 1", callExceptBytes(input)],
      ["Wasmtime Stage 2", callExceptBytes(input, reproduced)],
    ]) {
      if (result.tag !== 0 || result.bytes.toString("utf8") !== expected) {
        throw new Error(`${name} ${hostName}: tag ${result.tag}, bytes ${result.bytes}`);
      }
    }
  }
  return cases.length;
}

function main() {
  if (!process.argv.includes("--use-existing")) {
    compileInputs();
  }
  if (!fs.existsSync(wasm) || !fs.existsSync(image)) {
    throw new Error("self-host inputs are missing; run without --use-existing first");
  }

  const expected = fs.readFileSync(wasm);
  const result = callExceptBytes(fs.readFileSync(image));
  if (result.tag === 0) {
    throw new Error(`emitImage rejected its self image: ${result.bytes.toString("utf8")}`);
  }
  fs.writeFileSync(reproduced, result.bytes);
  expectBytes("self-host Stage 1", result.bytes, expected);

  const repeated = callExceptBytes(fs.readFileSync(image), reproduced);
  if (repeated.tag === 0) {
    throw new Error(`Stage 2 rejected its self image: ${repeated.bytes.toString("utf8")}`);
  }
  expectBytes("Stage 2 fixed point", repeated.bytes, result.bytes);

  checkRegisteredCorpus();
  const malformedCount = checkMalformedImages();

  process.stdout.write(
    `Wasmtime Stage 1 and Stage 2 reproduced ${expected.length} bytes; ` +
      `SHA-256 ${digest(expected)}\n`,
  );
  process.stdout.write(`self image is ${fs.statSync(image).size} bytes; SHA-256 ${digest(fs.readFileSync(image))}\n`);
  process.stdout.write(
    `matched ${corpusCases.length} registered artifacts and ${malformedCount} malformed-image cases\n`,
  );
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
