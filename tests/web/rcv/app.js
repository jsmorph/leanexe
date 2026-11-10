import { boundOf, load, MODULES, Refusal, room, tabulate } from "./tabulate.js";

const $ = id => document.getElementById(id);
const number = n => n.toLocaleString("en-US");
const loaded = {};
let download = null;
let chosenFile = null;

function row(name, value) {
  const tr = document.createElement("tr");
  const th = document.createElement("th");
  const td = document.createElement("td");
  th.textContent = name;
  td.textContent = value;
  tr.append(th, td);
  $("facts").append(tr);
}

function clear() {
  $("facts").replaceChildren();
  $("outcome").textContent = "";
  $("report").textContent = "";
  $("save").hidden = true;
  if (download) URL.revokeObjectURL(download);
  download = null;
}

/** The module that the radio buttons choose: `oakland` or `maine`. */
function chosen() {
  return document.querySelector('input[name="count"]:checked').value;
}

/** Counts the recounts started, so that only the latest writes the page. */
let started = 0;

async function recount(file, name) {
  const mine = ++started;
  clear();
  const bytes = new Uint8Array(await file.arrayBuffer());
  if (mine !== started) return;
  row("File", file.name);
  row("Size", `${number(bytes.length)} bytes`);
  row("Module", MODULES[name].file);
  if (!loaded[name]) {
    $("outcome").textContent = `Refused: ${MODULES[name].file} is not loaded.`;
    return;
  }
  const bound = boundOf(bytes.length, MODULES[name].constant);
  if (bound === null) {
    $("outcome").textContent = "Refused: tabulate_bound covers files of fewer than 2^32 bytes.";
    return;
  }
  row("Bound", `${number(bound)} bytes`);
  row("Room", `${number(room(bytes.length, bound))} bytes above the fresh instance's memory`);
  try {
    const start = performance.now();
    const report = await tabulate(loaded[name].module, bytes, bound);
    if (mine !== started) return;
    row("Time", `${((performance.now() - start) / 1000).toFixed(3)} s`);
    row("Report", `${number(report.length)} bytes`);
    $("outcome").textContent = "The module returned the report.";
    $("report").textContent = new TextDecoder().decode(report);
    download = URL.createObjectURL(new Blob([report], { type: "application/octet-stream" }));
    $("save").href = download;
    $("save").download = `${file.name.replace(/\.rcv$/, "")}.${name}.report`;
    $("save").hidden = false;
  } catch (e) {
    if (mine !== started) return;
    $("outcome").textContent = e instanceof Refusal ? `Refused: ${e.message}.` :
      `Failed: ${e.message}.  Under its premises the call theorem excludes a trap, so a failure ` +
      "here comes from the browser or from this page's code.";
  }
}

async function start(name) {
  try {
    const response = await fetch(MODULES[name].file, { cache: "no-store" });
    if (!response.ok) throw Error(`${MODULES[name].file}: HTTP status ${response.status}`);
    const bytes = await response.arrayBuffer();
    loaded[name] = await load(bytes);
    $(`sha-${name}`).textContent = loaded[name].sha256;
    $(`size-${name}`).textContent = `${number(bytes.byteLength)} bytes`;
  } catch (e) {
    $(`sha-${name}`).textContent = `not loaded: ${e.message}`;
  }
}

async function startAll() {
  if (!globalThis.isSecureContext) {
    const reason = "this page is not a secure context, so the browser hides crypto.subtle, which " +
      "computes the SHA-256.  Open it at http://127.0.0.1 or http://localhost";
    for (const name of Object.keys(MODULES)) $(`sha-${name}`).textContent = `not loaded: ${reason}`;
    return;
  }
  await Promise.all(Object.keys(MODULES).map(start));
  $("file").disabled = false;
}

$("file").addEventListener("change", () => {
  chosenFile = $("file").files[0] ?? null;
  if (chosenFile) recount(chosenFile, chosen());
});
for (const input of document.querySelectorAll('input[name="count"]')) {
  input.addEventListener("change", () => {
    if (chosenFile) recount(chosenFile, chosen());
  });
}
startAll();
