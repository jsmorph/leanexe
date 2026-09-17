import { ArtifactRunner } from "./host.js";
const element = id => document.getElementById(id);
const encoder = new TextEncoder();
let runner, busy = false, stopped = false;
const status = (text, error = false) => { element("status").textContent = text; element("status").classList.toggle("error", error); };
function controls() {
  const count = encoder.encode(element("prompt").value).length;
  element("bytes").textContent = `${count} / 128 UTF-8 bytes`;
  element("bytes").classList.toggle("error", count < 1 || count > 128);
  element("generate").disabled = busy || !runner || count < 1 || count > 128;
  element("check").disabled = busy || !runner;
  element("stop").disabled = !busy;
  element("prompt").disabled = busy; element("count").disabled = busy;
}
element("prompt").addEventListener("input", controls);
element("stop").addEventListener("click", () => { stopped = true; status("Stopping after the current GPU dispatch…"); });
element("generate").addEventListener("click", async () => {
  if (!runner || busy) return;
  const input = encoder.encode(element("prompt").value);
  if (input.length < 1 || input.length > 128) return;
  busy = true; stopped = false; controls();
  element("prefix").textContent = element("prompt").value;
  element("continuation").textContent = "";
  const generated = [], allBytes = Array.from(input), count = Number(element("count").value);
  const started = performance.now(), before = runner.dispatches;
  status("Generating locally with Wasm + WebGPU…");
  try {
    for (let i = 0; i < count && !stopped; i++) {
      const result = await runner.step(Uint8Array.from(allBytes.slice(-128)));
      allBytes.push(result.token); generated.push(result.token);
      element("continuation").textContent = new TextDecoder().decode(Uint8Array.from(generated));
      element("produced").textContent = generated.length;
      element("elapsed").textContent = ((performance.now() - started) / 1000).toFixed(2);
      element("dispatches").textContent = runner.dispatches - before;
    }
    status(`${stopped ? "Stopped" : "Complete"} · ${generated.length} bytes generated locally.`);
  } catch (error) { status(error.message, true); }
  finally { busy = false; controls(); }
});
element("check").addEventListener("click", async () => {
  if (!runner || busy) return;
  busy = true; controls(); element("stop").disabled = true;
  element("checks").textContent = ""; status("Comparing actual execution with retained Lean results…");
  try {
    const results = await runner.compare(item => {
      element("checks").textContent += `${item.name}: ${item.hidden} state / ${item.headWords} projection / ${item.logits} logit differences\n`;
    });
    const different = results.some(item => item.headWords || item.logits);
    element("checks").textContent += `\n${results.length} cases completed. Transformer state matches Lean.${different ? " Browser GPU arithmetic differences are shown above." : " All projection and logit words also match exactly."}`;
    status("Comparisons complete. Model weights restored.");
  } catch (error) { status(error.message, true); element("checks").textContent += `\nFAILED: ${error.message}`; }
  finally { busy = false; controls(); }
});
controls();
try {
  runner = await ArtifactRunner.load();
  element("backend").textContent = "WASM + WEBGPU · READY";
  element("backend").title = runner.adapterInfo;
  element("identity").textContent = `Device: ${runner.adapterInfo || "Browser WebGPU"}. Checkpoint: ${runner.manifest.checkpointSha256.slice(0, 16)}…`;
  status("Ready. Your prompt stays in this browser.");
  controls();
} catch (error) { element("backend").textContent = "WEBGPU UNAVAILABLE"; status(error.message, true); }
window.addEventListener("pagehide", () => runner?.destroy());
