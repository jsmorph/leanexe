# Talos GCD Proof

This directory proves the WASM generated from `LeanExe.Examples.TalosGcd.gcd`.
Talos’s verifier expects a project with `rust/` and `lean/` directories, so the
compiled LeanExe artifact lives at `rust/build/gcd/program.wasm`.  The source
program is Lean, and `tools/check-talos-gcd.sh` rebuilds the artifact from that
source before checking the Talos proof.

The proof uses Talos revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`.  The
Lean proof project pins that revision through Lake.  Regenerating `Program.lean`
uses Talos’s verifier emitter, which decodes `program.wat` through Talos’s WAT
decoder and writes a Lean representation of the parsed module.
