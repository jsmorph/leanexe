// Runs the cases of build/wgsl/cases.txt on this browser's WebGPU.  A case line is
// `kernel|workgroups|output|inputs|expected`, as tests/wgsl/run.sh passes it to
// leanexe-webgpu-host: the output and each input are buffer specifications (`u32:W,...` or
// `u64:W,...`, least significant half first, or a word count for an output filled with
// 0x7fc00001), the inputs are bound at 0, 1, and so on with the output after them, and the
// expected words are native Lean's, in decimal.

const $ = id => document.getElementById(id);
const FILL = 0x7fc00001;

function words(spec) {
  if (spec.startsWith("u32:") || spec.startsWith("u64:")) {
    const wide = spec.startsWith("u64:");
    const out = [];
    const body = spec.slice(4);
    if (body.length > 0) {
      for (const text of body.split(",")) {
        const value = BigInt(text);
        out.push(Number(value & 0xffffffffn));
        if (wide) out.push(Number((value >> 32n) & 0xffffffffn));
      }
    }
    if (out.length === 0) out.push(0);
    return Uint32Array.from(out);
  }
  return new Uint32Array(Number(spec)).fill(FILL);
}

function parseCases(text) {
  return text.split("\n").filter(line => line.length > 0).map((line, index) => {
    const [kernel, groups, output, inputs, expected] = line.split("|");
    return { index, kernel, groups: Number(groups), output,
             inputs: inputs.length > 0 ? inputs.split(" ") : [], expected };
  });
}

const hex = w => "0x" + (w >>> 0).toString(16).padStart(8, "0");
const asFloat = w => new Float32Array(new Uint32Array([w]).buffer)[0];

async function openDevice(choice) {
  if (!globalThis.isSecureContext) {
    throw Error("This page is not a secure context, so the browser hides WebGPU. " +
                "Open it at http://127.0.0.1 or http://localhost, or through HTTPS.");
  }
  if (!navigator.gpu) throw Error("navigator.gpu is undefined: this browser has no WebGPU, or it is off.");
  const options = choice === "fallback" ? { forceFallbackAdapter: true } : { powerPreference: choice };
  const adapter = await navigator.gpu.requestAdapter(options);
  if (!adapter) throw Error(`The browser returned no adapter for "${choice}".`);
  const device = await adapter.requestDevice();
  return { adapter, device };
}

function describe(adapter) {
  const info = adapter.info ?? {};
  const limits = ["maxComputeWorkgroupsPerDimension", "maxStorageBuffersPerShaderStage",
                  "maxStorageBufferBindingSize", "maxBufferSize"];
  return [
    `user agent: ${navigator.userAgent}`,
    `adapter: vendor ${info.vendor || "?"}, architecture ${info.architecture || "?"}, ` +
      `device ${info.device || "?"}, description ${info.description || "?"}, ` +
      `fallback ${info.isFallbackAdapter ?? adapter.isFallbackAdapter ?? "?"}`,
    `adapter limits: ${limits.map(name => `${name} ${adapter.limits[name]}`).join(", ")}`,
    `features: ${[...adapter.features].sort().join(", ") || "none"}`,
  ].join("\n");
}

async function compile(device, kernel) {
  const response = await fetch(`wgsl/${kernel}.wgsl`, { cache: "no-store" });
  if (!response.ok) return { pipeline: null, messages: [], error: `cannot load wgsl/${kernel}.wgsl` };
  const code = await response.text();
  device.pushErrorScope("validation");
  const module = device.createShaderModule({ code, label: kernel });
  const info = await module.getCompilationInfo();
  const messages = info.messages.map(m => `${m.type} ${m.lineNum}:${m.linePos} ${m.message}`);
  let pipeline = null;
  let error = null;
  try {
    pipeline = await device.createComputePipelineAsync({
      label: kernel, layout: "auto", compute: { module, entryPoint: "main" } });
  } catch (e) {
    error = e.message;
  }
  const scope = await device.popErrorScope();
  if (scope && !error) error = scope.message;
  return { pipeline: error ? null : pipeline, messages, error };
}

async function runCase(device, pipeline, c) {
  const inputs = c.inputs.map(words);
  const initial = words(c.output);
  const made = [];
  const buffer = (size, usage) => {
    const b = device.createBuffer({ size, usage });
    made.push(b);
    return b;
  };
  device.pushErrorScope("out-of-memory");
  device.pushErrorScope("validation");
  const bound = inputs.map(w => {
    const b = buffer(w.byteLength, GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST);
    device.queue.writeBuffer(b, 0, w);
    return b;
  });
  const out = buffer(initial.byteLength,
                     GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC | GPUBufferUsage.COPY_DST);
  device.queue.writeBuffer(out, 0, initial);
  const read = buffer(initial.byteLength, GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST);
  const group = device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: [...bound, out].map((b, binding) => ({ binding, resource: { buffer: b } })),
  });
  const encoder = device.createCommandEncoder();
  const pass = encoder.beginComputePass();
  pass.setPipeline(pipeline);
  pass.setBindGroup(0, group);
  pass.dispatchWorkgroups(c.groups);
  pass.end();
  encoder.copyBufferToBuffer(out, 0, read, 0, initial.byteLength);
  device.queue.submit([encoder.finish()]);
  const validation = await device.popErrorScope();
  const memory = await device.popErrorScope();
  let result;
  if (validation || memory) {
    result = { error: (validation ?? memory).message };
  } else {
    await read.mapAsync(GPUMapMode.READ);
    result = { got: Array.from(new Uint32Array(read.getMappedRange())) };
    read.unmap();
  }
  made.forEach(b => b.destroy());
  return result;
}

function difference(c, got) {
  const expected = c.expected.split(",").map(Number);
  if (got.length !== expected.length) return `${got.length} words, expected ${expected.length}`;
  const wrong = [];
  for (let i = 0; i < got.length; i++) if (got[i] !== expected[i]) wrong.push(i);
  const i = wrong[0];
  let text = `${wrong.length} of ${got.length} words differ; first at word ${i}: ` +
             `${hex(got[i])}, expected ${hex(expected[i])}`;
  if (i >= 2 && i % 2 === 0) {
    text += ` (element ${(i - 2) / 2}: ${asFloat(got[i])}, expected ${asFloat(expected[i])})`;
  }
  return text;
}

let cases = [];

function renderSummary(rows) {
  const body = $("summary");
  body.replaceChildren();
  for (const row of rows) {
    const tr = document.createElement("tr");
    const cells = [row.kernel, row.cases, row.passed, row.failed,
                   row.error ? `error: ${row.error}` : row.messages.join("\n") || "none"];
    cells.forEach((value, i) => {
      const td = document.createElement("td");
      td.textContent = String(value);
      if (i === 2 && row.passed > 0) td.className = "pass";
      if (i === 3 && row.failed > 0) td.className = "fail";
      if (i === 4) td.style.whiteSpace = "pre-wrap";
      tr.append(td);
    });
    body.append(tr);
  }
}

async function run() {
  $("run").disabled = true;
  const choice = $("power").value;
  const failures = [];
  const rows = [];
  let device;
  try {
    $("status").textContent = "Requesting the adapter";
    const opened = await openDevice(choice);
    device = opened.device;
    let lost = null;
    device.lost.then(info => { lost = `device lost: ${info.reason} ${info.message}`; });
    const uncaptured = [];
    device.addEventListener("uncapturederror", e => uncaptured.push(e.error.message));
    const header = describe(opened.adapter);
    $("device").textContent = header;
    const kernels = [...new Set(cases.map(c => c.kernel))];
    const started = performance.now();
    for (const kernel of kernels) {
      const mine = cases.filter(c => c.kernel === kernel);
      $("status").textContent = `Compiling ${kernel}`;
      const compiled = await compile(device, kernel);
      const row = { kernel, cases: mine.length, passed: 0, failed: 0,
                    messages: compiled.messages, error: compiled.error };
      rows.push(row);
      for (const c of mine) {
        if (lost) throw Error(lost);
        $("status").textContent = `Running ${kernel}, case ${c.index + 1} of ${cases.length}`;
        let problem;
        if (!compiled.pipeline) {
          problem = `not compiled: ${compiled.error}`;
        } else {
          const result = await runCase(device, compiled.pipeline, c);
          if (result.error) problem = `WebGPU error: ${result.error}`;
          else if (result.got.join(",") !== c.expected) problem = difference(c, result.got);
        }
        if (problem) {
          row.failed++;
          failures.push(`${kernel}, case line ${c.index + 1}, ${c.groups} workgroups: ${problem}`);
        } else {
          row.passed++;
        }
      }
      renderSummary(rows);
    }
    const seconds = ((performance.now() - started) / 1000).toFixed(1);
    const passed = rows.reduce((n, r) => n + r.passed, 0);
    const failed = rows.reduce((n, r) => n + r.failed, 0);
    $("status").textContent = `Passed ${passed}, failed ${failed}, in ${seconds} s`;
    $("status").className = failed === 0 ? "pass" : "fail";
    $("failures").textContent = failures.length === 0 ? "None." : failures.join("\n");
    $("failures").className = failures.length === 0 ? "pass" : "fail";
    const report = [
      "WebGPU kernel tests", `adapter choice: ${choice}`, header, "",
      ...rows.map(r => `${r.kernel}: ${r.cases} cases, passed ${r.passed}, failed ${r.failed}` +
        (r.error ? `, error: ${r.error}` : "") +
        (r.messages.length ? `\n  compiler: ${r.messages.join("\n  compiler: ")}` : "")),
      `total: passed ${passed}, failed ${failed}, ${seconds} s`,
      ...(uncaptured.length ? ["", "uncaptured errors:", ...uncaptured] : []),
      ...(failures.length ? ["", `failures (up to 5 per kernel, ${failures.length} in all):`,
                             ...kernels.flatMap(k => failures.filter(f => f.startsWith(`${k}, `)).slice(0, 5))]
                          : []),
    ];
    $("report").value = report.join("\n");
  } catch (e) {
    $("status").textContent = e.message;
    $("status").className = "fail";
    $("report").value = `WebGPU kernel tests\nadapter choice: ${choice}\nerror: ${e.message}`;
  } finally {
    device?.destroy();
    $("run").disabled = false;
  }
}

async function load() {
  try {
    const response = await fetch("wgsl/cases.txt", { cache: "no-store" });
    if (!response.ok) throw Error("cannot load wgsl/cases.txt; run tests/wgsl/run.sh");
    cases = parseCases(await response.text());
    const kernels = new Set(cases.map(c => c.kernel)).size;
    $("status").textContent = `${cases.length} cases of ${kernels} kernels loaded`;
    $("run").disabled = false;
  } catch (e) {
    $("status").textContent = e.message;
    $("status").className = "fail";
  }
}

$("run").addEventListener("click", run);
// `?run=high-performance`, `?run=low-power`, or `?run=fallback` runs the cases after loading.
const start = new URLSearchParams(location.search).get("run");
load().then(() => {
  if (start && cases.length > 0) {
    $("power").value = start;
    run();
  }
});
