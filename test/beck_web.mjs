import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { once } from "node:events";
import fs from "node:fs";
import beck from "../tools/beck.js";
import { Worker } from "node:worker_threads";
import serverModule from "../tools/beck-serve.js";
import hostModule from "../tools/wasmtime-host.js";
import processModule from "../tools/run-process.js";
import { scenarios, invalidScenarios, encode, check } from "../tools/beck-web/scenarios.mjs";

const { createServer } = serverModule;
const digest = createHash("sha256").update(fs.readFileSync(beck.wasm)).digest("hex");
const server = createServer();
server.listen(0, "127.0.0.1");
await once(server, "listening");
const origin = `http://127.0.0.1:${server.address().port}`;
const bootstrap = `
  const { parentPort, workerData } = require("node:worker_threads");
  globalThis.self = { postMessage: data => parentPort.postMessage(data) };
  const nativeFetch = globalThis.fetch;
  globalThis.fetch = url => nativeFetch(new URL(url, workerData.origin));
  import(workerData.url).then(() => parentPort.on("message", data => self.onmessage({ data })));
`;

function execute(input) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(bootstrap, { eval: true, workerData: {
      origin, url: new URL("../tools/beck-web/worker.mjs", import.meta.url).href,
    } });
    const timer = setTimeout(() => finish(new Error("Browser worker timed out")), 30_000);
    const finish = (error, result) => {
      clearTimeout(timer);
      worker.terminate();
      if (error) reject(error);
      else resolve(result);
    };
    worker.once("message", result => finish(null, result));
    worker.once("error", error => finish(error));
    worker.postMessage(input);
  });
}

try {
  for (const route of ["/", "/index.html", "/style.css", "/app.mjs", "/worker.mjs", "/scenarios.mjs", "/manifest.json", "/program.wasm"]) {
    const response = await fetch(origin + route);
    assert.equal(response.status, 200, route);
    assert.equal(response.headers.get("x-content-type-options"), "nosniff");
    assert.match(response.headers.get("content-security-policy"), /wasm-unsafe-eval/);
    const bytes = Buffer.from(await response.arrayBuffer());
    if (route === "/program.wasm") {
      assert.equal(response.headers.get("content-type"), "application/wasm");
      assert.equal(createHash("sha256").update(bytes).digest("hex"), digest);
    }
    if (route === "/manifest.json") assert.equal(JSON.parse(bytes).sha256, digest);
  }
  const head = await fetch(origin, { method: "HEAD" });
  assert.equal(head.status, 200);
  assert.equal(await head.text(), "");
  assert.ok(Number(head.headers.get("content-length")) > 0);
  assert.equal((await fetch(origin + "/AGENTS.md")).status, 404);
  assert.equal((await fetch(origin, { method: "POST" })).status, 405);

  const cases = [
    ...scenarios.map(scenario => ({ ...scenario, status: 0 })),
    ...invalidScenarios,
    { input: { categories: 0, jobs: [] }, status: 0 },
    { input: { categories: 0, jobs: Array.from({ length: 6 }, () => []) }, status: 0 },
    { input: { categories: 8, jobs: Array.from({ length: 6 }, () => [7, 6, 5, 4, 3, 2, 1, 0]) }, status: 0 },
    { input: { categories: 8, jobs: Array.from({ length: 6 }, () => [7]) }, status: 0 },
    { input: { categories: 9, jobs: [] }, status: 0 },
  ];
  const host = hostModule.ensureHost();
  for (const test of cases) {
    const result = await execute(test.input);
    assert.equal(result.ok, true, result.message);
    assert.equal(result.status, test.status, JSON.stringify(test.input));
    const reference = processModule.runChecked([host, "call", beck.wasm, "compute", "array-u64", `array-u64:${encode(test.input).join(",")}`], { encoding: "utf8", timeout: 60_000 });
    assert.deepEqual(result.result, JSON.parse(reference.stdout), "Browser worker / Wasmtime agreement");
    assert.ok(Number.isFinite(result.milliseconds));
  }
  assert.equal((await execute({ categories: 1, jobs: [[-1]] })).ok, false);
  assert.equal((await execute({ categories: 1, jobs: "wrong type" })).ok, false);
  assert.throws(() => check({ categories: 1, jobs: Array.from({ length: 5 }, () => [0]) }, [0, 1, 1, 1, 1, 1, 1]), /exceeds/);
  assert.throws(() => check({ categories: 1, jobs: Array.from({ length: 5 }, () => [0]) }, [0, 2, 0, 1, 0, 1, 1]), /overlap/);
  assert.throws(() => check({ categories: 1, jobs: Array.from({ length: 5 }, () => [0]) }, [0, 1, 0, 1, 0, 1, 2]), /invalid group/);
  assert.throws(() => check({ categories: 1, jobs: Array.from({ length: 5 }, () => [0]) }, [3]), /internal failure/);
  console.log(`beck web: HTTP identity, ${cases.length} worker/Wasmtime comparisons, validation, and output checks passed`);
} finally {
  server.closeAllConnections();
  await new Promise((resolve, reject) => server.close(error => error ? reject(error) : resolve()));
}
