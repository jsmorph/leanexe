"use strict";

const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { checkPackage, generate, lean, audit } = require("./package");
const { instantiate, nativeDispatch } = require("./wasm-host");
const root = path.resolve(__dirname, "../..");
const proofRoot = path.join(root, "proofs/talos/lean");
const write = (file, value) => fs.writeFileSync(file, value, { flag: "wx" });
const writeJson = (file, value) => write(file, JSON.stringify(value, null, 2) + "\n");
const digest = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const requireThat = (condition, message) => { if (!condition) throw new Error(message); };
const hostNames = ["HostBinary.encoded", "HostBinary.interface", "HostMemory.upload_word",
  "HostExecution.completes", "HostExecution.exact", "HostExecution.numerical", "HostExecution.numerical_wide"].map(name => `Project.WGSL.${name}`);

async function checkBundle(directory) {
  const checked = await checkPackage(directory);
  try {
    const hostBytes = fs.readFileSync(path.join(checked.directory, "host.wasm"));
    requireThat(hostBytes.length <= 1024, "host artifact exceeds 1 KiB");
    const hostPath = path.join(checked.attempt, "host.wasm");
    write(hostPath, hostBytes);
    await lean("Wasm host proof dependencies", ["lake", "-d", proofRoot, "build", "Project.WGSL.HostExecution"],
      path.join(checked.attempt, "host-dependencies.log"));
    const output = await lean("Wasm exact bytes and host composition", ["lake", "-d", proofRoot, "env", "lean", "--run",
      path.join(__dirname, "HostCheck.lean"), "--check", hostPath], path.join(checked.attempt, "host-verify.log"));
    const hostAxioms = audit(output, hostNames);
    requireThat(output.split("\n").filter(line => line === "WGSL_WASM_HOST_VERIFIED").length === 1,
      "missing host verification marker");
    const proof = path.join(checked.attempt, "BundleProof.lean");
    write(proof, "import Project.WGSL.HostExecution\n" + fs.readFileSync(path.join(checked.attempt, "Proof.lean"), "utf8") +
      "\ndef checkedHostExact := @Project.WGSL.HostExecution.exact _ _ CheckedWGSLPackage.package\n" +
      "def checkedHostNumerical := @Project.WGSL.HostExecution.numerical _ _ CheckedWGSLPackage.package\n" +
      "def checkedHostNumericalWide := @Project.WGSL.HostExecution.numerical_wide _ _ CheckedWGSLPackage.package\n" +
      "#print axioms checkedHostExact\n#print axioms checkedHostNumerical\n#print axioms checkedHostNumericalWide\n");
    const composed = await lean("compose this shader package with the Wasm host", ["lake", "-d", proofRoot, "env",
      "lean", "--run", proof, checked.shaderPath, checked.manifestPath], path.join(checked.attempt, "bundle-verify.log"));
    const bundleAxioms = audit(composed, ["package", "artifact", "numerical", "numericalWide", "exact"].map(n => `CheckedWGSLPackage.${n}`)
      .concat(["checkedHostExact", "checkedHostNumerical", "checkedHostNumericalWide"]));
    requireThat(fs.readFileSync(hostPath).equals(hostBytes) && fs.readFileSync(checked.shaderPath).equals(checked.shader) &&
      fs.readFileSync(checked.manifestPath).equals(checked.manifest), "bundle snapshot changed during checking");
    const receipt = { ...checked.receipt, hostSha256: digest(hostBytes), hostAxioms, bundleAxioms,
      bundleProofSha256: digest(fs.readFileSync(proof)),
      subject: "Exact Wasm bridge bytes and exact WGSL shader package, with composed memory-result theorems",
      hostPrecondition: "HostExecution.Ready: aligned in-bounds regions and bounded matrix sizes",
      runtimeContract: "HostExecution.contract: exact input byte snapshots, conforming WGSL dispatch and completed readback",
      hostImplementationVerified: false,
      claims: [...checked.receipt.claims, "Wasm small-step termination", "input byte transfer", "output memory correspondence",
        "memory preserved outside C (separate-profile theorem)"] };
    writeJson(path.join(checked.attempt, "bundle-verification.json"), receipt);
    console.log(`WGSL/Wasm bundle verified: ${checked.attempt}`);
    return { ...checked, hostBytes, receipt };
  } catch (error) {
    writeJson(path.join(checked.attempt, "bundle-failure.json"), { status: "error", error: error.message });
    throw error;
  }
}

// Small exact dyadic operands keep this runtime comparison independent of the
// numerical proof and give the same answer under separate and fused updates.
function exampleInputs(metadata) {
  return Object.fromEntries(["a", "b"].map((name, phase) => [name,
    Array.from({ length: metadata.buffers[name].elements }, (_, i) => ((i + phase * 3) % 7 - 3) / 16)]));
}

function executeBundle(checked) {
  const reportPath = path.join(checked.attempt, "bundle-execution.json");
  const report = { schemaVersion: 1, status: "error", hostSha256: digest(checked.hostBytes),
    shaderSha256: digest(checked.shader), manifestSha256: digest(checked.manifest),
    wasmRuntime: { node: process.version, v8: process.versions.v8 }, runtimeConformanceEstablished: false };
  try {
    const bridge = instantiate(checked.hostBytes, checked.metadata, inputs =>
      nativeDispatch(checked, inputs, path.join(checked.attempt, "host-native.log")));
    const { memory, run } = bridge.instance.exports;
    const offsets = { a: 64, b: 64 + checked.metadata.buffers.a.bytes + 32 };
    offsets.c = offsets.b + checked.metadata.buffers.b.bytes + 32;
    const end = offsets.c + checked.metadata.buffers.c.bytes + 64;
    const pages = Math.ceil(end / 65536);
    if (pages > 1) memory.grow(pages - 1);
    new Uint8Array(memory.buffer).fill(0xa5);
    const view = new DataView(memory.buffer);
    const inputs = exampleInputs(checked.metadata);
    for (const name of ["a", "b"]) inputs[name].forEach((value, i) => view.setFloat32(offsets[name] + 4 * i, value, true));
    const preserved = Buffer.from(new Uint8Array(memory.buffer));
    const status = run(offsets.a, offsets.b, offsets.c);
    requireThat(status === 0 && bridge.calls === 1, "Wasm did not make exactly one successful dispatch");
    const { rows, cols, inner } = checked.metadata.dimensions;
    let checkedElements = 0;
    for (let row = 0; row < rows; row++) for (let col = 0; col < cols; col++) {
      let expected = 0;
      for (let k = 0; k < inner; k++) expected = Math.fround(expected + Math.fround(inputs.a[row * inner + k] * inputs.b[k * cols + col]));
      const actual = view.getFloat32(offsets.c + 4 * (row * cols + col), true);
      requireThat(Object.is(actual, expected), `Wasm output differs at (${row}, ${col}): ${actual} != ${expected}`);
      checkedElements++;
    }
    const after = Buffer.from(memory.buffer);
    requireThat(after.subarray(0, offsets.c).equals(preserved.subarray(0, offsets.c)) &&
      after.subarray(offsets.c + checked.metadata.buffers.c.bytes).equals(preserved.subarray(offsets.c + checked.metadata.buffers.c.bytes)),
    "Wasm memory outside C changed");
    Object.assign(report, { status: "pass", ...bridge.last, check: { checkedElements, importedCalls: bridge.calls,
      memoryOutsideCPreserved: true, reference: "small dyadic inputs; exact separate/fused binary32 results" } });
    writeJson(reportPath, report);
    console.log(`Wasm → WGSL → Wasm passed: ${checkedElements} outputs; ${reportPath}`);
    return reportPath;
  } catch (error) {
    report.error = error.message;
    writeJson(reportPath, report);
    throw error;
  }
}

async function generateBundle(directory, dimensions) {
  directory = await generate(directory, dimensions);
  fs.copyFileSync(path.join(root, "test/wgsl/host/host.wasm"), path.join(directory, "host.wasm"), fs.constants.COPYFILE_EXCL);
}

async function corpus(directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(path.dirname(directory), { recursive: true });
  fs.mkdirSync(directory);
  const cases = JSON.parse(fs.readFileSync(path.join(__dirname, "corpus.json"), "utf8"));
  const results = [];
  for (const item of cases.positive) {
    const selected = path.join(directory, item.name);
    await generateBundle(selected, item.dimensions);
    const checked = await checkBundle(selected);
    results.push({ name: item.name, status: "pass", verification: path.join(checked.attempt, "bundle-verification.json"),
      execution: executeBundle(checked) });
  }
  for (const item of cases.bundleNegative) {
    const altered = path.join(directory, item.name);
    fs.mkdirSync(altered);
    for (const file of ["kernel.wgsl", "manifest.json"]) fs.copyFileSync(path.join(directory, item.base, file), path.join(altered, file));
    const host = fs.readFileSync(path.join(directory, item.base, "host.wasm"));
    host[host.length - item.byteOffsetFromEnd] = item.value;
    write(path.join(altered, "host.wasm"), host);
    let failure;
    try { await checkBundle(altered); } catch (error) { failure = error.message; }
    requireThat(failure && failure.includes(item.failure), `negative bundle ${item.name} did not fail as expected: ${failure}`);
    results.push({ name: item.name, status: "rejected", failure });
  }
  writeJson(path.join(directory, "corpus.json"), { status: "pass", results });
  console.log(`WGSL/Wasm corpus passed: ${results.length} cases; ${directory}`);
}

async function main([command, directory, ...rest]) {
  if (command === "wgsl-bundle-build") {
    await generateBundle(directory, rest);
    executeBundle(await checkBundle(directory));
  } else if (command === "wgsl-bundle-check" || command === "wgsl-bundle-run") {
    requireThat(rest.length === 0, "unexpected arguments");
    const checked = await checkBundle(directory);
    if (command === "wgsl-bundle-run") executeBundle(checked);
  } else if (command === "wgsl-bundle-corpus") {
    requireThat(rest.length === 0, "unexpected arguments");
    await corpus(directory);
  } else throw new Error(`unknown bundle command: ${command}`);
}

module.exports = { main, checkBundle, executeBundle };
