import { GpuHost, WasmHost, Sampler, runLines, parse } from "./hosts.js";

const $ = id => document.getElementById(id);
const CHUNKS = 4;

let gpu = null;
let wasm = null;
let sampler = null;
let resetLines = [];
let stopping = false;
const log = [];

function note(text) {
  log.push(text);
  $("report").value = log.join("\n");
}

async function api(path) {
  const response = await fetch(path, { cache: "no-store" });
  if (!response.ok) throw Error(`${path}: ${await response.text()}`);
  return response.json();
}

/** The index of the first largest score, as `greedy32` chooses. */
function greedy(chunks) {
  let best = 0;
  let bestValue = chunks[0][0];
  let i = 0;
  for (const chunk of chunks) {
    for (const x of chunk) {
      if (bestValue < x) { best = i; bestValue = x; }
      i++;
    }
  }
  return best;
}

function compare(a, b) {
  let differ = 0;
  let largest = 0;
  let scale = 0;
  for (let c = 0; c < a.length; c++) {
    const x = a[c], y = b[c];
    const xb = new Uint32Array(x.buffer), yb = new Uint32Array(y.buffer);
    for (let i = 0; i < x.length; i++) {
      if (xb[i] !== yb[i]) differ++;
      largest = Math.max(largest, Math.abs(x[i] - y[i]));
      scale = Math.max(scale, Math.abs(x[i]));
    }
  }
  return { differ, relative: scale > 0 ? largest / scale : largest };
}

async function scores(host) {
  const out = [];
  for (let c = 0; c < CHUNKS; c++) out.push(await host.floats(`z${c}`));
  return out;
}

async function load() {
  $("load").disabled = true;
  $("generate").disabled = true;
  gpu?.close();
  wasm?.close();
  gpu = null;
  wasm = null;
  log.length = 0;
  const mode = $("mode").value;
  try {
    if (mode !== "wasm") {
      $("status").textContent = "Requesting the adapter";
      gpu = await GpuHost.open($("power").value);
      note(`WGSL: ${gpu.describe()}`);
    }
    if (mode !== "gpu") {
      wasm = await WasmHost.open("gpt32.wasm");
    }
    sampler = await Sampler.open("sampler.wasm");
    note(`user agent: ${navigator.userAgent}`);
    const lines = await api("api/setup");
    resetLines = lines.filter(l => parse(l).command === "words");
    let bytes = 0;
    const started = performance.now();
    const messages = await runLines(lines, [gpu, wasm].filter(Boolean), (name, n) => {
      bytes += n;
      $("status").textContent = `Loaded ${name}, ${(bytes / 2 ** 20).toFixed(0)} MiB`;
    });
    messages.forEach(note);
    const seconds = ((performance.now() - started) / 1000).toFixed(1);
    $("loaded").textContent = `Loaded ${(bytes / 2 ** 20).toFixed(0)} MiB in ${seconds} s` +
      (gpu ? `; WGSL on ${gpu.describe()}` : "") + (wasm ? `; ${wasm.describe()}` : "");
    note($("loaded").textContent);
    $("status").textContent = "Ready";
    $("generate").disabled = false;
  } catch (e) {
    $("status").textContent = e.message;
    $("status").className = "fail";
    note(`error: ${e.message}`);
  } finally {
    $("load").disabled = false;
  }
}

function render(prefix, continuation) {
  const text = $("text");
  const gen = document.createElement("span");
  gen.className = "gen";
  gen.textContent = continuation;
  text.replaceChildren(document.createTextNode(prefix), gen);
}

async function generate() {
  stopping = false;
  $("generate").disabled = true;
  $("load").disabled = true;
  $("stop").disabled = false;
  $("status").className = "";
  $("steps").replaceChildren();
  const hosts = [gpu, wasm].filter(Boolean);
  const n = Number($("tokens").value);
  let gpuTime = 0, wasmTime = 0, steps = 0, equal = 0, agree = 0;
  try {
    const seedText = $("seed").value.trim();
    const k = Number($("topk").value);
    const temperature = Number($("temperature").value);
    if (seedText !== "" && !/^[0-9]+$/.test(seedText)) throw Error("the seed is not a whole number");
    if (seedText !== "" && !(Number.isInteger(k) && k >= 1)) throw Error("top-k is not a positive whole number");
    if (seedText !== "" && !(temperature > 0)) throw Error("the temperature is not positive");
    let state = seedText === "" ? null : BigInt.asUintN(64, BigInt(seedText));
    // The token of `chunks`: the largest score's without a seed, else sampleTopK's from `state`.
    const choose = chunks => state === null ? { token: greedy(chunks), next: null }
      : sampler.sample(chunks, k, temperature, state);
    const prompt = await api(`api/tokenize?text=${encodeURIComponent($("prompt").value)}`);
    if (prompt.length === 0) throw Error("the prompt has no tokens");
    if (prompt.length + n > 1024) throw Error("the prompt and the tokens exceed 1,024 positions");
    const prefix = await api(`api/decode?ids=${prompt.join(",")}`);
    render(prefix, "");
    note(`prompt: ${prompt.length} tokens; ${n} to generate; ` + (state === null ? "greedy" :
      `top-k sampling with seed ${state}, k ${k}, temperature ${temperature}`));
    await runLines(resetLines, hosts);
    const ids = [...prompt];
    for (let p = 0; p < prompt.length + n - 1 && !stopping; p++) {
      $("status").textContent = `Position ${p}`;
      const lines = await api(`api/step?token=${ids[p]}&p=${p}`);
      const reading = p + 1 >= prompt.length;
      let gpuScores = null, wasmScores = null;
      // Each side runs alone, so each time is its own.
      const t0 = performance.now();
      if (gpu) {
        await runLines(lines, [gpu]);
        if (reading) gpuScores = await scores(gpu);
        else await gpu.device.queue.onSubmittedWorkDone();
        gpu.check();
      }
      const t1 = performance.now();
      if (wasm) {
        await runLines(lines, [wasm]);
        if (reading) wasmScores = await scores(wasm);
      }
      const t2 = performance.now();
      gpuTime += t1 - t0;
      wasmTime += t2 - t1;
      steps++;
      if (!reading) continue;
      const lead = wasmScores ?? gpuScores;
      const { token, next } = choose(lead);
      if (gpuScores && wasmScores) {
        const gpuToken = choose(gpuScores).token;
        const { differ, relative } = compare(wasmScores, gpuScores);
        if (differ === 0) equal++;
        if (gpuToken === token) agree++;
        const tr = document.createElement("tr");
        for (const [value, cls] of [[p, ""], [differ, differ ? "fail" : "pass"],
            [relative.toExponential(2), ""], [token, ""], [gpuToken, gpuToken === token ? "" : "fail"]]) {
          const td = document.createElement("td");
          td.textContent = String(value);
          td.className = cls;
          tr.append(td);
        }
        $("steps").append(tr);
        note(`position ${p}: ${differ} scores differ, largest relative difference ` +
             `${relative.toExponential(2)}, Wasm token ${token}, WGSL token ${gpuToken}`);
        $("equal").textContent = `${equal} of ${ids.length - prompt.length + 1}`;
        $("agree").textContent = `${agree} of ${ids.length - prompt.length + 1}`;
      }
      ids.push(token);
      if (state !== null) state = next;
      $("count").textContent = String(ids.length - prompt.length);
      if (gpu) $("perGpu").textContent = (gpuTime / 1000 / steps).toFixed(3);
      if (wasm) $("perWasm").textContent = (wasmTime / 1000 / steps).toFixed(3);
      const full = await api(`api/decode?ids=${ids.join(",")}`);
      render(prefix, full.slice(prefix.length));
    }
    const summary = `${ids.length - prompt.length} tokens in ${steps} steps` +
      (gpu ? `; WGSL ${(gpuTime / 1000 / steps).toFixed(3)} s a step` : "") +
      (wasm ? `; Wasm ${(wasmTime / 1000 / steps).toFixed(3)} s a step` : "") +
      (gpu && wasm ? `; equal scores in ${$("equal").textContent} steps, the same token in ${$("agree").textContent}` : "");
    $("status").textContent = stopping ? `Stopped: ${summary}` : summary;
    note(`tokens: ${ids.join(" ")}`);
    note(summary);
  } catch (e) {
    $("status").textContent = e.message;
    $("status").className = "fail";
    note(`error: ${e.message}`);
  } finally {
    $("generate").disabled = false;
    $("load").disabled = false;
    $("stop").disabled = true;
  }
}

$("load").addEventListener("click", load);
$("generate").addEventListener("click", generate);
$("stop").addEventListener("click", () => { stopping = true; });
// `?mode=both&power=fallback&tokens=8&seed=42&run=1` loads and generates without clicks.
const params = new URLSearchParams(location.search);
for (const key of ["mode", "power", "tokens", "seed", "topk", "temperature"]) {
  if (params.has(key)) $(key).value = params.get(key);
}
if (params.has("run")) load().then(() => { if (!$("generate").disabled) generate(); });
