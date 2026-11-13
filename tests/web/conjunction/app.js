import { assess, load, PANELS } from "./assess.js";

const $ = id => document.getElementById(id);
const SVG = "http://www.w3.org/2000/svg";
const FLOATS = ["m1", "m2", "c11", "c12", "c22", "r", "t"];
const DECIMAL = /^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/;

/** Examples: the README's, two of Chan's cases, and case 4 of Alfano 2009 projected onto the
encounter plane by tests/conjunction/benchmark.py. */
const PRESETS = {
  "README: mean (300, 0), radius 20": ["300", "0", "10000", "0", "1000000", "20", "1e-4", "4096"],
  "Chan 1": ["10", "0", "2500", "0", "625", "5", "1e-4", "4096"],
  "Chan 11: probability near 1e-4": ["5000", "0", "9000000", "0", "1000000", "50", "1e-4", "4096"],
  "Chan 8: miss of 10 standard deviations along the second axis":
    ["0", "10000", "9000000", "0", "1000000", "10", "1e-4", "4096"],
  "Alfano 2009, case 4": ["134.40851351969943", "0", "11142.723603235821", "-269.97169352427227",
    "6.632970715938806", "15", "1e-4", "4096"],
};

const VERDICTS = {
  0n: "undecided: lo < t ≤ hi, so the interval does not decide",
  1n: "below: hi < t, so the model's probability is below t",
  2n: "above: t ≤ lo, so the model's probability is at least t",
};

let loaded = null;
let started = 0;

class Refusal extends Error {}

function row(name, value) {
  const tr = document.createElement("tr");
  const th = document.createElement("th");
  const td = document.createElement("td");
  th.textContent = name;
  td.textContent = value;
  tr.append(th, td);
  $("facts").append(tr);
}

function node(parent, name, attributes, text) {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attributes)) e.setAttribute(k, v);
  if (text !== undefined) e.textContent = text;
  parent.append(e);
  return e;
}

/** The entries as the doubles and the panel count that `assess` takes. */
function entries() {
  const inputs = {};
  for (const name of FLOATS) {
    const text = $(name).value.trim();
    if (!DECIMAL.test(text)) throw new Refusal(`${name} is not a decimal number`);
    inputs[name] = Number(text);
  }
  const text = $("n").value.trim();
  if (!/^\d+$/.test(text) || BigInt(text) >= 2n ** 64n) {
    throw new Refusal("n is not a whole number below 2^64");
  }
  inputs.n = BigInt(text);
  return inputs;
}

/** The covariance's eigenvalues and the angle of an eigenvector of the larger one, or null when
the matrix is not positive definite in binary64.  For c12 != 0, (c12, big - c11) is such an
eigenvector. */
function axes(c11, c12, c22) {
  const big = (c11 + c22) / 2 + Math.hypot((c11 - c22) / 2, c12);
  const small = (c11 * c22 - c12 * c12) / big;
  if (!(c11 > 0) || !(small > 0) || !Number.isFinite(big)) return null;
  const angle = c12 !== 0 ? Math.atan2(big - c11, c12) : (c11 >= c22 ? 0 : Math.PI / 2);
  return { big, small, angle };
}

/** A length of the form 1, 2, or 5 times a power of ten near `x`. */
function round(x) {
  const p = 10 ** Math.floor(Math.log10(x));
  return [5, 2, 1].map(k => k * p).find(v => v <= x) ?? p;
}

/** Draws the encounter plane: the ellipses one, two, and three standard deviations from the
mean, the mean and the miss vector, the disk of radius r about the origin, and a scale bar.  A
disk smaller than two pixels gets a dashed ring around its place, which the caption states. */
function drawPlane({ m1, m2, c11, c12, c22, r }) {
  const svg = $("plane");
  svg.replaceChildren();
  const W = 600, H = 420, pad = 36;
  const a = axes(c11, c12, c22);
  if (a === null || ![m1, m2, r].every(Number.isFinite) || !(r > 0)) {
    $("caption").textContent = "No drawing: the inputs do not give a positive definite " +
      "covariance and a positive radius in binary64.";
    return;
  }
  const sx = 3 * Math.sqrt(c11), sy = 3 * Math.sqrt(c22);
  const x0 = Math.min(-r, m1 - sx, 0), x1 = Math.max(r, m1 + sx, 0);
  const y0 = Math.min(-r, m2 - sy, 0), y1 = Math.max(r, m2 + sy, 0);
  const scale = Math.min((W - 2 * pad) / (x1 - x0), (H - 2 * pad) / (y1 - y0));
  const cx = W / 2 - scale * (x0 + x1) / 2, cy = H / 2 + scale * (y0 + y1) / 2;
  const X = x => cx + scale * x, Y = y => cy - scale * y;
  node(svg, "line", { class: "axis", x1: 0, y1: Y(0), x2: W, y2: Y(0) });
  node(svg, "line", { class: "axis", x1: X(0), y1: 0, x2: X(0), y2: H });
  node(svg, "text", { x: W - 4, y: Y(0) - 4, "text-anchor": "end", class: "muted" }, "first axis");
  node(svg, "text", { x: X(0) + 4, y: 12, class: "muted" }, "second axis");
  const degrees = -a.angle * 180 / Math.PI;
  for (const k of [1, 2, 3]) {
    node(svg, "ellipse", {
      class: "ellipse", cx: X(m1), cy: Y(m2), rx: k * Math.sqrt(a.big) * scale,
      ry: k * Math.sqrt(a.small) * scale, transform: `rotate(${degrees} ${X(m1)} ${Y(m2)})`,
      "stroke-opacity": 1 - 0.25 * (k - 1),
    });
  }
  node(svg, "line", { class: "miss", x1: X(0), y1: Y(0), x2: X(m1), y2: Y(m2) });
  node(svg, "circle", { class: "mean", cx: X(m1), cy: Y(m2), r: 3 });
  node(svg, "circle", { class: "disk", cx: X(0), cy: Y(0), r: r * scale });
  const tiny = r * scale < 2;
  if (tiny) node(svg, "circle", { class: "marker", cx: X(0), cy: Y(0), r: 8 });
  const bar = round((W - 2 * pad) / scale / 4);
  node(svg, "line", { class: "axis", x1: pad, y1: H - 12, x2: pad + bar * scale, y2: H - 12 });
  node(svg, "text", { x: pad, y: H - 18 }, `${bar}`);
  const sd = `${Math.sqrt(a.big).toPrecision(4)} and ${Math.sqrt(a.small).toPrecision(4)}`;
  $("caption").textContent = `The ellipses lie one, two, and three standard deviations from ` +
    `the mean, and the principal standard deviations are ${sd}.  The dashed line is the miss ` +
    `vector, and ` +
    `the disk of radius ${r} lies about the origin` +
    (tiny ? `, smaller than two pixels at this scale, inside the dashed ring.` : `.`) +
    `  The bar at the lower left has length ${bar}.`;
}

/** Draws [lo, hi] and t on a base-10 logarithmic scale. */
function drawInterval(lo, hi, t) {
  const svg = $("interval");
  svg.replaceChildren();
  const values = [lo, hi, t].filter(v => v > 0 && Number.isFinite(v));
  if (values.length === 0) return;
  const W = 600, pad = 40;
  const e0 = Math.floor(Math.log10(Math.min(...values))) - 1;
  const e1 = Math.ceil(Math.log10(Math.max(...values)));
  const X = v => pad + (W - 2 * pad) * (Math.log10(v) - e0) / Math.max(e1 - e0, 1);
  node(svg, "line", { class: "axis", x1: pad, y1: 30, x2: W - pad, y2: 30 });
  const step = Math.max(1, Math.ceil((e1 - e0) / 8));
  for (let e = e0; e <= e1; e += step) {
    node(svg, "line", { class: "axis", x1: X(10 ** e), y1: 26, x2: X(10 ** e), y2: 34 });
    node(svg, "text", { x: X(10 ** e), y: 50, "text-anchor": "middle", class: "muted" }, `1e${e}`);
  }
  const left = lo > 0 ? X(lo) : pad;
  node(svg, "line", { class: "interval", x1: left, y1: 30, x2: Math.max(X(hi), left + 2), y2: 30 });
  if (t > 0) {
    node(svg, "line", { class: "threshold", x1: X(t), y1: 16, x2: X(t), y2: 44 });
    node(svg, "text", { x: X(t), y: 12, "text-anchor": "middle" }, "t");
  }
  node(svg, "text", { x: left, y: 66, class: "muted" }, lo > 0 ? "[lo, hi]" : "[0, hi]");
}

/** Shows the result of `assess` on the encounter-plane inputs, which the form gives. */
async function show(inputs) {
  const mine = ++started;
  $("facts").replaceChildren();
  $("outcome").textContent = "";
  $("interval").replaceChildren();
  drawPlane(inputs);
  row("Arguments", `m1 = ${inputs.m1}, m2 = ${inputs.m2}, c11 = ${inputs.c11}, ` +
    `c12 = ${inputs.c12}, c22 = ${inputs.c22}, r = ${inputs.r}, t = ${inputs.t}, n = ${inputs.n}`);
  if (inputs.n < 1n || inputs.n > PANELS) row("Note", "assess rejects n outside 1 to 1,048,576");
  try {
    const start = performance.now();
    const { status, lo, hi, verdict } = await assess(loaded.module, inputs);
    if (mine !== started) return;
    row("Time", `${((performance.now() - start) / 1000).toFixed(3)} s`);
    row("Status", status === 0n ? "0, accepted" : `${status}, rejected`);
    if (status !== 0n) {
      $("outcome").textContent = "Rejected: a value is not finite, c11 or r is not positive, n " +
        "lies outside its range, an interval operation overflowed, or the outward-rounded " +
        "arithmetic did not show a positive conditional variance c22 - c12²/c11.";
      return;
    }
    row("lo", `${lo}`);
    row("hi", `${hi}`);
    row("hi - lo", `${hi - lo}` + (lo > 0 ? `, ${((hi - lo) / lo).toPrecision(3)} of lo` : ""));
    row("Verdict", `${verdict}, ${VERDICTS[verdict]}`);
    $("outcome").textContent = `The model's probability lies in [${lo}, ${hi}].`;
    drawInterval(lo, hi, inputs.t);
  } catch (e) {
    if (mine !== started) return;
    $("outcome").textContent = `Failed: ${e.message}.  Under its premises the theorem excludes ` +
      "a trap, so a failure here comes from the browser or from this page's code.";
  }
}

function fill(name) {
  PRESETS[name].forEach((v, i) => { $([...FLOATS, "n"][i]).value = v; });
}

function run() {
  if (loaded === null) return;
  let inputs;
  try {
    inputs = entries();
  } catch (e) {
    if (!(e instanceof Refusal)) throw e;
    started++;
    for (const id of ["facts", "interval", "plane"]) $(id).replaceChildren();
    $("caption").textContent = "";
    $("outcome").textContent = `Refused: ${e.message}.`;
    return;
  }
  show(inputs);
}

async function start() {
  for (const name of Object.keys(PRESETS)) {
    const option = document.createElement("option");
    option.value = option.textContent = name;
    $("preset").append(option);
  }
  const names = Object.keys(PRESETS);
  const index = Number(new URLSearchParams(location.search).get("example") ?? 0);
  const chosen = names[index] ?? names[0];
  $("preset").value = chosen;
  fill(chosen);
  $("preset").addEventListener("change", () => { fill($("preset").value); run(); });
  $("run").addEventListener("click", run);
  if (!globalThis.isSecureContext) {
    $("sha").textContent = "not loaded: this page is not a secure context, so the browser hides " +
      "crypto.subtle, which computes the SHA-256.  Open it at http://127.0.0.1 or http://localhost";
    return;
  }
  try {
    const response = await fetch("conjunction.wasm", { cache: "no-store" });
    if (!response.ok) throw Error(`conjunction.wasm: HTTP status ${response.status}`);
    const bytes = await response.arrayBuffer();
    loaded = await load(bytes);
    $("sha").textContent = loaded.sha256;
    $("size").textContent = `${bytes.byteLength.toLocaleString("en-US")} bytes`;
  } catch (e) {
    $("sha").textContent = `not loaded: ${e.message}`;
    return;
  }
  $("run").disabled = false;
  run();
}

start();
