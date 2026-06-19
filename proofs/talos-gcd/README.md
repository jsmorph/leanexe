# Talos Proofs

This directory proves properties of WASM generated from LeanExe examples.
Talos’s verifier expects a project with `rust/` and `lean/` directories, so the
compiled LeanExe artifacts live under `rust/build/<name>/program.wasm`.  The
source programs are Lean, and the `tools/check-talos-*.sh` scripts rebuild the
artifacts from that source before checking the corresponding Talos proof.

The proof uses Talos revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`.  The
Lean proof project pins that revision through Lake.  Regenerating `Program.lean`
uses Talos’s verifier emitter, which decodes `program.wat` through Talos’s WAT
decoder and writes a Lean representation of the parsed module.
