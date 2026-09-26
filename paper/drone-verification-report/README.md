# Verified Terrain-Following Flight Planning in LeanExe

This report describes the drone planner's finite-graph optimum, continuous point-mass safety, and generated-WASM-model execution proof.  Its stand-alone LeanExe section includes the scalar and bounded-loop compiler-correctness results on main.

The drone proof subject is revision `820b3958`.  The LeanExe overview and compiler theorem use main at `8dbb8e8a`.  The report distinguishes the generated drone model from an exact-byte artifact theorem and states the physical and heap assumptions.

- [Accepted marXiv version](http://127.0.0.1:8405/abs/2609.00019v3)
- [Editorial review](submission-03/review.txt)
- [Report source](main.tex)
- [Report PDF](main.pdf)
- [Bibliography](references.bib)
- [Review record](review-notes.md)
- [Actual-run inputs and outputs](evidence/runs.json)
- [Principal theorem axiom audit](evidence/axioms.log)

Build from this directory with the installed TeX tools:

```sh
python3 build.py
```

The proof check uses the current drone checkout:

```sh
tools/leanrun --timeout 15m lake -q -d proofs/talos/lean build Project.Drone.Spec Project.Drone.SourceChecks
```

The five figures use fresh Wasmtime results, each compared with native Lean.  The figure driver saves complete inputs, outputs, timing derived from the returned words, and plotting samples.  It uses the repository's Wasmtime host and routes native Lean through the resource runner.  Reproduce the runs from the repository root after creating `build/drone-report`:

```sh
tools/leanrun --timeout 15m lake -q build lean-wasm LeanExe.Examples.Drone
tools/leanrun --timeout 2m .lake/build/bin/lean-wasm compile --module LeanExe.Examples.Drone --entry LeanExe.Examples.Drone.compute --out build/drone-report/program.wasm
node paper/drone-verification-report/run-figures.js
python3 paper/drone-verification-report/build.py
```

Individual vector figures: [five-station example](figures/example.pdf), [flat terrain](figures/flat.pdf), [broad plateau](figures/plateau.pdf), [rounded hill](figures/hill.pdf), and [repeated ridges](figures/ridges.pdf).

marXiv accepted version 3 on September 26, 2026.  It uses one LeanExe background reference from morphism.com/marxiv and three external references.  The five actual-run plots show terrain, the clearance corridor, and drone elevation.
