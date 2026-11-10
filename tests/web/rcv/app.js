import { boundOf, load, Refusal, room, tabulate } from "./tabulate.js";

const $ = id => document.getElementById(id);
const number = n => n.toLocaleString("en-US");
let loaded = null;
let download = null;

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

async function recount(file) {
  clear();
  const bytes = new Uint8Array(await file.arrayBuffer());
  row("File", file.name);
  row("Size", `${number(bytes.length)} bytes`);
  const bound = boundOf(bytes.length);
  if (bound === null) {
    $("outcome").textContent = "Refused: tabulate_bound covers files of fewer than 2^32 bytes.";
    return;
  }
  row("Bound", `${number(bound)} bytes`);
  row("Room", `${number(room(bytes.length, bound))} bytes above the fresh instance's memory`);
  try {
    const start = performance.now();
    const report = await tabulate(loaded.module, bytes, bound);
    row("Time", `${((performance.now() - start) / 1000).toFixed(3)} s`);
    row("Report", `${number(report.length)} bytes`);
    $("outcome").textContent = "The module returned the report.";
    $("report").textContent = new TextDecoder().decode(report);
    download = URL.createObjectURL(new Blob([report], { type: "application/octet-stream" }));
    $("save").href = download;
    $("save").download = `${file.name.replace(/\.rcv$/, "")}.report`;
    $("save").hidden = false;
  } catch (e) {
    $("outcome").textContent = e instanceof Refusal ? `Refused: ${e.message}.` :
      `Failed: ${e.message}.  Under its premises the call theorem excludes a trap, so a failure ` +
      "here comes from the browser or from this page's code.";
  }
}

async function start() {
  try {
    if (!globalThis.isSecureContext) {
      throw Error("this page is not a secure context, so the browser hides crypto.subtle, which " +
                  "computes the SHA-256.  Open it at http://127.0.0.1 or http://localhost");
    }
    const response = await fetch("rcvTabulate.wasm", { cache: "no-store" });
    if (!response.ok) throw Error(`rcvTabulate.wasm: HTTP status ${response.status}`);
    const bytes = await response.arrayBuffer();
    loaded = await load(bytes);
    $("sha").textContent = loaded.sha256;
    $("size").textContent = `${number(bytes.byteLength)} bytes`;
    $("file").disabled = false;
  } catch (e) {
    $("sha").textContent = `not loaded: ${e.message}`;
  }
}

$("file").addEventListener("change", () => {
  const file = $("file").files[0];
  if (file) recount(file);
});
start();
