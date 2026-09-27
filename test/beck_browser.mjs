import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import { once } from "node:events";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import serverModule from "../tools/beck-serve.js";
import { scenarios, invalidScenarios } from "../tools/beck-web/scenarios.mjs";

const server = serverModule.createServer();
server.listen(0, "127.0.0.1");
await once(server, "listening");
const origin = `http://127.0.0.1:${server.address().port}`;
const profile = await fs.mkdtemp(path.join(os.tmpdir(), "beck-browser-"));
const browser = spawn(process.env.CHROMIUM || "chromium", ["--headless", "--disable-gpu", "--no-first-run", "--no-default-browser-check", "--remote-debugging-port=0", `--user-data-dir=${profile}`, "about:blank"], { stdio: ["ignore", "ignore", "pipe"] });
let socket;
let messages = "";
const errors = [];

try {
  const endpoint = await new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`Chromium startup timed out: ${messages}`)), 15_000);
    browser.once("error", error => { clearTimeout(timer); reject(error); });
    browser.once("exit", code => { clearTimeout(timer); reject(new Error(`Chromium exited (${code}): ${messages}`)); });
    browser.stderr.on("data", data => {
      messages += data;
      const match = messages.match(/DevTools listening on (ws:\/\/[^\s]+)/);
      if (match) { clearTimeout(timer); resolve(match[1]); }
    });
  });
  const pages = await (await fetch(new URL("/json/list", endpoint.replace("ws:", "http:")))).json();
  socket = new WebSocket(pages.find(page => page.type === "page").webSocketDebuggerUrl);
  await once(socket, "open");
  let sequence = 0;
  const pending = new Map();
  socket.addEventListener("message", event => {
    const message = JSON.parse(event.data);
    if (message.id) {
      const call = pending.get(message.id);
      if (!call) return;
      pending.delete(message.id);
      clearTimeout(call.timer);
      if (message.error) call.reject(new Error(JSON.stringify(message.error)));
      else call.resolve(message.result);
    } else if (message.method === "Runtime.exceptionThrown") errors.push(message.params.exceptionDetails);
    else if (message.method === "Log.entryAdded" && message.params.entry.level === "error") errors.push(message.params.entry);
  });
  function call(method, params = {}) {
    return new Promise((resolve, reject) => {
      const id = ++sequence;
      const timer = setTimeout(() => { pending.delete(id); reject(new Error(`Chromium command timed out: ${method}`)); }, 10_000);
      pending.set(id, { resolve, reject, timer });
      socket.send(JSON.stringify({ id, method, params }));
    });
  }
  async function evaluate(expression) {
    const result = await call("Runtime.evaluate", { expression, returnByValue: true, awaitPromise: true });
    if (result.exceptionDetails) throw new Error(JSON.stringify(result.exceptionDetails));
    return result.result.value;
  }
  async function waitFor(expression) {
    const deadline = Date.now() + 10_000;
    while (Date.now() < deadline) {
      if (await evaluate(expression)) return;
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    throw new Error(`Page condition timed out: ${expression}\n${await evaluate("document.body.innerText")}`);
  }
  async function select(id, value) {
    await evaluate(`{ const select = document.getElementById(${JSON.stringify(id)}); select.value = ${JSON.stringify(String(value))}; select.dispatchEvent(new Event('change')); }`);
  }
  const passed = "document.getElementById('status')?.dataset.state === 'passed'";
  await call("Page.enable");
  await call("Runtime.enable");
  await call("Log.enable");
  await call("Emulation.setDeviceMetricsOverride", { width: 1280, height: 1100, deviceScaleFactor: 1, mobile: false });
  await call("Page.navigate", { url: origin });
  await waitFor(passed);
  const output = path.resolve("build/beck-web");
  await fs.mkdir(output, { recursive: true });
  await fs.writeFile(path.join(output, "desktop.png"), Buffer.from((await call("Page.captureScreenshot", { format: "png" })).data, "base64"));
  for (const scenario of scenarios) {
    await select("scenario", scenario.id);
    await waitFor(passed);
    const result = await evaluate(`({ groups: ['a','b'].map(group => [...document.querySelectorAll('#group-' + group + '-jobs .job')].map(job => Number(job.textContent.slice(4)) - 1)), counts: [...document.querySelectorAll('#counts tbody tr')].map(row => [...row.querySelectorAll('td')].map(cell => cell.textContent)), overlap: Number(document.getElementById('overlap').textContent), bound: Number(document.getElementById('bound').textContent) })`);
    const overlap = Math.max(0, ...scenario.input.jobs.map(job => job.length));
    const bound = overlap ? 2 * overlap - 1 : 0;
    assert.equal(result.overlap, overlap);
    assert.equal(result.bound, bound);
    assert.deepEqual(result.groups.flat().sort((a, b) => a - b), scenario.input.jobs.map((_, index) => index));
    scenario.input.categories && assert.equal(result.counts.length, scenario.input.categories);
    result.counts.forEach((row, category) => {
      const counts = result.groups.map(jobs => jobs.filter(job => scenario.input.jobs[job].includes(category)).length);
      assert.deepEqual(row, [String(counts[0] + counts[1]), ...counts.map(String), `${Math.abs(counts[0] - counts[1])} ≤ ${bound}`]);
    });
  }
  await select("scenario", "overlap");
  await waitFor(passed);
  await evaluate("document.querySelector('input[type=checkbox]').click()");
  assert.equal(await evaluate("document.getElementById('results').hidden"), true);
  assert.equal(await evaluate("document.getElementById('scenario').value"), "custom");
  await evaluate("document.getElementById('run').click()");
  await waitFor(passed);
  await select("category-count", 0);
  await evaluate("document.getElementById('run').click()");
  await waitFor(passed);
  assert.equal(await evaluate("document.getElementById('bound').textContent"), "0");
  await select("job-count", 0);
  await evaluate("document.getElementById('run').click()");
  await waitFor(passed);
  assert.equal(await evaluate("document.querySelectorAll('.job').length"), 0);
  await evaluate("document.querySelector('.validation').open = true");
  for (let index = 0; index < invalidScenarios.length; index++) {
    await evaluate(`document.querySelectorAll('#invalid-presets button')[${index}].click(); document.getElementById('check-input').click()`);
    await waitFor("document.getElementById('validation-status').dataset.state === 'passed'");
    assert.match(await evaluate("document.getElementById('validation-status').textContent"), new RegExp(`status ${invalidScenarios[index].status}`));
  }
  await evaluate("document.getElementById('raw-input').value = '{'; document.getElementById('check-input').click()");
  assert.equal(await evaluate("document.getElementById('validation-status').dataset.state"), "error");
  await evaluate("document.querySelector('.validation').open = false");
  await select("scenario", "overlap");
  await waitFor(passed);
  await call("Emulation.setDeviceMetricsOverride", { width: 390, height: 844, deviceScaleFactor: 1, mobile: true });
  assert.equal(await evaluate("document.documentElement.scrollWidth <= window.innerWidth"), true);
  await fs.writeFile(path.join(output, "mobile.png"), Buffer.from((await call("Page.captureScreenshot", { format: "png" })).data, "base64"));
  assert.deepEqual(errors, [], "Browser errors");
  console.log(`beck browser: ${scenarios.length} scenarios, membership edits, empty inputs, rejection controls, and mobile layout passed; screenshots in ${output}`);
} finally {
  socket?.close();
  if (browser.exitCode === null) { browser.kill(); await once(browser, "exit"); }
  server.closeAllConnections();
  await new Promise((resolve, reject) => server.close(error => error ? reject(error) : resolve()));
  await fs.rm(profile, { recursive: true, force: true });
}
