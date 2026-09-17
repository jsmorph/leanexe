"use strict";

// Verify the six delivered shader texts, without generating replacements or
// running an inference implementation. The selected arithmetic profile is a
// theorem premise; this command does not certify a native/browser GPU driver.
const fs = require("node:fs");
const path = require("node:path");
const crypto = require("node:crypto");
const { isDeepStrictEqual } = require("node:util");
const { checkPackage } = require("../package");
const root = path.resolve(__dirname, "../../..");
const hash = bytes => crypto.createHash("sha256").update(bytes).digest("hex");
const need = (ok, message) => { if (!ok) throw Error(message); };
const write = (file, value) => fs.writeFileSync(file, JSON.stringify(value, null, 2) + "\n", { flag: "wx" });
const shapes = [[768,2304],[768,768],[768,3072],[3072,768],[768,25129],[768,25128]]
  .map(([inner,cols], i) => ({ inner, cols, shader: `kernel-${i}.wgsl` }));

async function check(directory) {
  directory = path.resolve(directory);
  const manifestBytes = fs.readFileSync(path.join(directory, "manifest.json"));
  const manifest = JSON.parse(manifestBytes);
  need(manifest.schemaVersion === 2 && isDeepStrictEqual(manifest.shapes, shapes), "unexpected GPT-2 shader plan");
  const snapshots = shapes.map(shape => {
    const bytes = fs.readFileSync(path.join(directory, shape.shader));
    need(bytes.length === manifest.sizes[shape.shader] && hash(bytes) === manifest.sha256[shape.shader], `${shape.shader}: bundle identity mismatch`);
    return bytes;
  });
  const parent = path.join(root, "build/gpt2/shader-checks");
  fs.mkdirSync(parent, { recursive: true });
  const attempt = fs.mkdtempSync(path.join(parent, "check-"));
  fs.writeFileSync(path.join(attempt, "bundle-manifest.json"), manifestBytes, { flag: "wx" });
  const results = [];
  try {
    for (const [index, shape] of shapes.entries()) {
      const selected = path.join(attempt, String(index));
      fs.mkdirSync(selected);
      fs.writeFileSync(path.join(selected, "kernel.wgsl"), snapshots[index], { flag: "wx" });
      // Construct the requested semantic contract; the kernel checker must
      // independently establish that every field matches the parsed shader.
      write(path.join(selected, "manifest.json"), {
        schemaVersion: 1, kernel: "gemm_f32", entryPoint: "gemm_f32", wgslRevision: "2026-08-17",
        profile: { id: "leanexe-f32-rne-separate-v1", revision: 1 },
        dimensions: { rows: 1, inner: shape.inner, cols: shape.cols },
        bindings: { group: 0, a: 0, b: 1, c: 2 },
        buffers: Object.fromEntries([["a",shape.inner],["b",shape.inner*shape.cols],["c",shape.cols]]
          .map(([name,elements]) => [name, { elements, bytes: elements*4 }])),
        workgroupSize: [8,8,1], dispatchWorkgroups: [Math.ceil(shape.cols/8),1,1],
      });
      const checked = await checkPackage(selected, { wordsOnly: true });
      need(checked.shader.equals(snapshots[index]), "proof identified different shader bytes");
      results.push({ shader: shape.shader, dimensions: checked.metadata.dimensions,
        shaderSha256: checked.receipt.shaderSha256, verification: path.join(checked.attempt, "verification.json") });
    }
    need(fs.readFileSync(path.join(directory, "manifest.json")).equals(manifestBytes), "bundle manifest changed during checking");
    for (const [index,shape] of shapes.entries())
      need(fs.readFileSync(path.join(directory,shape.shader)).equals(snapshots[index]), "delivered shader changed during checking");
    write(path.join(attempt, "verification.json"), { status: "pass", bundleManifestSha256: hash(manifestBytes),
      subject: "Six delivered GPT-2 WGSL shaders implement the selected Lean binary32 GEMM",
      profile: "leanexe-f32-rne-separate-v1", numericalErrorTolerance: null,
      runtimeConformanceEstablished: false, modelCompositionEstablished: false,
      scope: "Shader parsing, dimensions, binding ABI, dispatch safety and word equality; no weights, Wasm, host schedule or driver proof",
      results });
    console.log(`GPT-2 WGSL fidelity: all six shaders verified; ${attempt}`);
    return { attempt, results };
  } catch (error) {
    write(path.join(attempt,"failure.json"), { status: "error", error: error.message, results });
    throw error;
  }
}
module.exports = { check };
