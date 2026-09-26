"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../../tools/run-process");
const { ensureHost } = require("../../tools/wasmtime-host");

const root = path.resolve(__dirname, "../..");
const wasm = path.resolve(process.argv[2] || path.join(root, "build/drone-report/program.wasm"));
const figures = path.join(__dirname, "figures");
const evidence = path.join(__dirname, "evidence");
fs.mkdirSync(figures, { recursive: true });
fs.mkdirSync(evidence, { recursive: true });
const cases = [
  { id: "example", title: "Five-station example", terrain: [0, 20, 80, 40, 0] },
  { id: "flat", title: "Flat terrain", terrain: Array(15).fill(0) },
  { id: "plateau", title: "Broad plateau", terrain: [0, 0, 0, 20, 60, 100, 100, 100, 100, 100, 60, 20, 0, 0, 0] },
  { id: "hill", title: "Rounded hill", terrain: [0, 0, 10, 30, 60, 100, 130, 140, 130, 100, 60, 30, 10, 0, 0] },
  { id: "ridges", title: "Repeated ridges", terrain: [0, 0, 50, 110, 40, 0, 80, 140, 70, 0, 60, 120, 50, 0, 0] },
];
const host = ensureHost();
const run = (args, timeout = 120000) => runChecked(args, { cwd: root, encoding: "utf8", timeout });
const records = [];

for (const item of cases) {
  const compiled = run([host, "call", wasm, "compute", "array-u64", `array-u64:${item.terrain.join(",")}`]);
  const native = run(["lake", "env", "lean", "--run", "test/DroneNative.lean", ...item.terrain.map(String)]);
  const output = JSON.parse(compiled.stdout);
  const nativeOutput = JSON.parse(native.stdout);
  assert.deepEqual(output, nativeOutput, `${item.id}: native/WASM mismatch`);
  assert.equal(output.length, 2 * item.terrain.length);
  if (item.id === "example") assert.deepEqual(output, [0, 0, 145, 10, 180, 15, 165, 10, 0, 0]);
  const floor = item.terrain.map((h, i) => h + (i > 0 && i + 1 < item.terrain.length ? 100 : 0));
  const segments = [];
  const samples = ["x,z,t"];
  let elapsed = 0;
  for (let i = 0; i + 1 < item.terrain.length; i++) {
    const [z0, u, z1, v] = output.slice(2 * i, 2 * i + 4);
    const d = Math.abs(z1 - z0);
    const duration = u + v > 0 ? 200 / (u + v) : Math.max(25, Math.ceil(3 * d / 40), Math.ceil(Math.sqrt(Math.ceil(3 * d / 2))));
    const ticks = u + v > 0 ? 33600 / ((u + v) / 5) : 840 * duration;
    assert(Number.isInteger(ticks));
    segments.push({ durationSeconds: duration, ticks });
    for (let j = 0; j <= 100; j++) {
      const s = j / 100;
      const p = 3 * s * s - 2 * s * s * s;
      const q = u + v > 0 ? (2 * u * s + (v - u) * s * s) / (u + v) : p;
      const x = 100 * (i + q);
      const z = z0 + (z1 - z0) * p;
      const corridor = floor[i] + (floor[i + 1] - floor[i]) * q;
      assert(z + 1e-8 >= corridor, `${item.id}: sampled clearance`);
      samples.push(`${x.toFixed(9)},${z.toFixed(9)},${(elapsed + s * duration).toFixed(9)}`);
    }
    elapsed += duration;
  }
  const ticks = segments.reduce((sum, segment) => sum + segment.ticks, 0);
  const excess = floor.reduce((sum, r, i) => sum + output[2 * i] - r, 0);
  const record = { ...item, output, nativeOutput, nativeMatchesWasm: true, segments, totalTicks: ticks, totalSeconds: ticks / 840, excess };
  records.push(record);
  fs.writeFileSync(path.join(figures, `${item.id}-path.csv`), samples.join("\n") + "\n");
  fs.writeFileSync(path.join(figures, `${item.id}-terrain.csv`), ["x,terrain,corridor,altitude", ...item.terrain.map((h, i) => `${100 * i},${h},${floor[i]},${output[2 * i]}`)].join("\n") + "\n");
  fs.writeFileSync(path.join(evidence, `${item.id}-native.log`), native.stdout + native.stderr);
  fs.writeFileSync(path.join(evidence, `${item.id}-wasm.log`), compiled.stdout + compiled.stderr);
  const plot = String.raw`\begin{tikzpicture}
\begin{axis}[
  width=16cm,height=7.2cm,
  title={${item.title}},title style={font=\large},
  xlabel={Horizontal position (distance units)},ylabel={Elevation (distance units)},
  xmin=0,xmax=${100 * (item.terrain.length - 1)},ymin=0,ymax=${item.id === "example" ? 210 : 380},
  scaled ticks=false,axis lines=left,tick align=outside,
  xmajorgrids=false,ymajorgrids=true,grid style={gray!15},
  legend style={at={(0.5,-0.25)},anchor=north,legend columns=3,draw=none,font=\small},
  tick label style={font=\small},label style={font=\small},
  no markers,clip=true]
\addplot[draw=gray!65,fill=gray!18,thick] table[x=x,y=terrain,col sep=comma]{${item.id}-terrain.csv} \closedcycle;
\addlegendentry{Terrain}
\addplot[gray!75,dashed,thick] table[x=x,y=corridor,col sep=comma]{${item.id}-terrain.csv};
\addlegendentry{Required corridor}
\addplot[blue!55!black,line width=1.2pt] table[x=x,y=z,col sep=comma]{${item.id}-path.csv};
\addlegendentry{Drone elevation}
\addplot[blue!55!black,only marks,mark=*,mark size=1.6pt,forget plot] table[x=x,y=altitude,col sep=comma]{${item.id}-terrain.csv};
\end{axis}
\end{tikzpicture}
`;
  fs.writeFileSync(path.join(figures, `${item.id}.tex`), String.raw`\documentclass[border=5pt]{standalone}
\usepackage[T1]{fontenc}
\usepackage{lmodern,pgfplots}
\pgfplotsset{compat=1.18}
\begin{document}
` + plot + "\\end{document}\n");
  console.log(`${item.id}: native and WASM agree; ${ticks} ticks; altitude excess ${excess}`);
}
fs.writeFileSync(path.join(evidence, "runs.json"), JSON.stringify({ date: "2026-09-26", engine: "Wasmtime 44.0.0", sourceRevision: "820b39589a66732ae76e05cde6ee4ffbd08e1e69", cases: records }, null, 2) + "\n");
