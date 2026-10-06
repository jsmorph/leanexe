# LeanExe

The Smalltalk VM and collector are written in Lean and compiled to WASM.
`tests/smalltalk/run.sh` passes 136 native executions and 181 WASM checks,
including 136 exact arena comparisons. The emitted module is 25,208 bytes.
For a valid heap, Lean proves that the concrete collector preserves reachable
payloads and frees exactly the unreachable cells. Arena initialization,
allocation, pointer writes, frame updates, reservation, return control with
possible collection, and fuel properties are also checked.
Full VM correctness remains unproved: VM boot, method lookup, and the
remaining instruction properties still need proofs. The source compiler and
emitted WASM are tested but not proved correct.
See [smalltalk-vm.md](smalltalk-vm.md) for commands, formats, collection, tests,
and proof limits, and [smalltalk-compilers.md](smalltalk-compilers.md) for compiler
options and the unimplemented CSOM adapter.

LeanExe compiles Lean functions to WebAssembly. Correctness proofs are checked
separately; compilation alone does not establish correctness. The compiler
translates a Lean definition to an intermediate instruction form (IR) during
elaboration and records hints for the prover. `compile` translates the IR to a module of
Talos, a WebAssembly interpreter written in Lean, and `encode` produces the
bytes.  A proof per function establishes `Implements`: from any store that
satisfies the runtime invariant, the exported function either traps at
`unreachable` or returns the Lean function's value, and `decode_encode` carries
the result to the bytes.  For the Euler solvers and the drone planner,
`ImplementsA` with a memory budget also proves that the call returns, within a
stated number of pages.

Compiler rules are verified one at a time.  A verified rule, such as
`Func.tail_implements` for tail recursion, reduces each program's proof to the
parts the rule does not cover, and it enters the LTG knowledge base in `ltg/`.
The trusted base is Lean's kernel, Talos's semantics, and the binary decoder,
which is tested against the official WebAssembly testsuite.

[The user manual](docs/manual.md) describes the dialect the compiler accepts,
the commands that compile and run a program, the theorems and the rules that
prove them, the tests, and the examples.  `deslop.md` records the design, the
decisions, the status, and the plan, and `devnotes.md` is the development
journal.

## Layout

| Path | Contents |
|---|---|
| `LeanExe/` | The example programs in `Examples/`, the combinators `LeanExe.loop`, `LeanExe.build`, and `LeanExe.repeatWhile`, and the binary32 and binary64 wrappers the float proofs use. |
| `Project/Compiler/` | The compiler and the `leanexe_compile` command. |
| `Project/IR/` | The IR, `compile`, the statement and template rules, and the `Live` invariant of composite bodies. |
| `Project/Runtime/` | The code of the runtime functions `alloc` and `release`, and the free-list layout. |
| `Project/Pipeline/` | `Implements` and `ImplementsA`, the runtime heap invariant, the allocation and release specifications, the memory budget, and `Emit.lean`. |
| `Project/Encoding/` | The encoder, the decoder, `decode_encode`, and the testsuite runner. |
| `Project/ProofKit/` | General lemmas: memory, arrays, allocation, and binary32 and binary64 arithmetic and enclosures. |
| `Project/Scale/`, `Gcd/`, `SumArray/`, `PairSum/`, `SumCount/`, `Axpy/`, `ScaledHypot/`, `Piecewise/`, `SumSquares/`, `Mean/`, `Bucket/`, `Prng/`, `Bools/`, `Calc/`, `Shape/`, `Lists/`, `Words/`, `Trees/`, `Updates/`, `Clob/`, `Grids/`, `Binary32/`, `Gpt/`, `Euler/`, `Drone/` | Each example's module and theorems. |
| `Project/EulerReal/` | The real-number Euler mathematics that the solvers' hyperbolicity theorems use. |
| `Project/WGSL/` | The WGSL subset, its printer, parser, and semantics, and the proved translation of IR kernels into WGSL. |
| `Project/Gpt32/` | GPT-2 in binary32: the kernels' dispatch theorems, the host programs with their theorem `generate_host`, and the Lean driver. |
| `Project/LTG/` | The checker of the LTG entries. |
| `ltg/` | The LTG knowledge base. |
| `tools/` | The resource-limited Lean runner, the Wasmtime and WebGPU hosts and their build scripts, and the Euler and GPT-2 command-line tools. |
| `tests/` | Module, GPT, drone, PRNG, WGSL, and GPT-2 tests, and the WebGPU pages of `tests/web/`. |
| `data/`, `paper/` | Records of runs and reports. |

## Commands

Run every Lean or Lake command through `tools/leanrun`, as `AGENTS.md`
requires.  The commands below build and check `gcd`: they build its proof, write
its bytes, validate them, run them in Wasmtime, and check the LTG entries.  The
manual lists the tests and the full check.

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Gcd.Module Project.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
tools/leanrun --timeout 10m lake env lean --run Project/LTG/Check.lean ltg/entries
```

`tools/build-wasmtime-host.sh` builds the Wasmtime host after
`tools/download-wasmtime.sh` fetches the pinned C API.  `tests/modules/run.sh`
compares every module except `gpt`, `gpt32`, and `prng` with native Lean on the
cases of `tests/modules/Cases.lean`, and `tests/gpt/run.sh` does the same for
`gpt.wasm`.  Both read the modules from `build/NAME/NAME.wasm`.

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/: one runs
the WGSL kernel tests on a browser's WebGPU, and one runs GPT-2 with its kernels
on WebGPU, in WebAssembly, or on both, compared.  `tests/web/README.md` describes
the pages, their setup, and what is proved about what they run.  The GPT-2 page
needs the binary32 weights that `uv run tests/gpt32/generate.py --export` writes.
