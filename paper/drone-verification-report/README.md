# Verified Terrain-Following Flight Planning in LeanExe

This report describes the earlier compiler at its recorded source revision.  Its reproduction commands require that revision.  [The current compiler manuals](../../README.md#documentation) describe the merged system.

The report opens with the goal of end-to-end verification for practical applications and the repeated-ridges run.  It describes the drone planner's finite-graph optimum, continuous point-mass safety, and generated-WASM-model execution proof.  Its stand-alone LeanExe section includes the scalar and bounded-loop compiler-correctness results on main.

The drone proofs come from [one source revision](https://github.com/jsmorph/leanexe/commit/820b39589a66732ae76e05cde6ee4ffbd08e1e69), and the LeanExe overview and compiler theorem from [another](https://github.com/jsmorph/leanexe/commit/8dbb8e8a70a8b0f54d3899db5b6dac8ce2d62c18).  The report distinguishes the generated drone model from an exact-byte artifact theorem and states the physical and heap assumptions.

- [Accepted marXiv version](main.pdf)
- [Editorial review](submission-04/review.txt)
- [Report source](main.tex)
- [Report PDF](main.pdf)
- [Bibliography](references.bib)
- [Review record](review-notes.md)
- [Actual-run inputs and outputs](evidence/runs.json)
- [Principal theorem axiom audit](evidence/axioms.log)

Build from this directory with the installed TeX tools:

```sh
uv run build.py
```

At the recorded revision, the proof check uses:

```sh
tools/leanrun --timeout 15m lake -q -d proofs/talos/lean build Project.Drone.Spec Project.Drone.SourceChecks
```

The five figures use fresh Wasmtime results, each compared with native Lean.  The figure driver saves complete inputs, outputs, timing derived from the returned words, and plotting samples.  It uses the repository's Wasmtime host and routes native Lean through the resource runner.  Reproduce the runs from the repository root after creating `build/drone-report`:

```sh
tools/leanrun --timeout 15m lake -q build lean-wasm LeanExe.Demos.Drone
tools/leanrun --timeout 2m .lake/build/bin/lean-wasm compile --module LeanExe.Demos.Drone --entry LeanExe.Demos.Drone.compute --out build/drone-report/program.wasm
node paper/drone-verification-report/run-figures.js
uv run paper/drone-verification-report/build.py
```

Individual vector figures: [five-station example](figures/example.pdf), [flat terrain](figures/flat.pdf), [broad plateau](figures/plateau.pdf), [rounded hill](figures/hill.pdf), and [repeated ridges](figures/ridges.pdf).

marXiv accepted version 4 on September 26, 2026.  It uses one LeanExe background reference from morphism.com/marxiv and three external references.  The five actual-run plots show terrain, the clearance corridor, and drone elevation.  The opening context is on page 1, and the repeated-ridges graph is at the top of page 2.
