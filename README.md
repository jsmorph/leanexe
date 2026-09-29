# LeanExe

LeanExe compiles Lean functions to WebAssembly and proves, for each compiled
program, that the bytes compute exactly the Lean function.  A compiler, which is
not trusted, translates a Lean definition to a small IR during elaboration and
records hints for the prover.  `compile` translates the IR to a module of Talos,
a WebAssembly interpreter written in Lean, and `encode` produces the bytes.  A
per-program proof establishes `Implements`: from any store that satisfies the
runtime invariant, the exported function terminates and returns the Lean
function's value.  `decode_encode` carries the result to the bytes.

Compiler rules are verified one at a time.  A verified rule, such as
`Func.tail_implements` for tail recursion, reduces each program's proof to the
parts the rule does not cover, and it enters the LTG knowledge base in `ltg/`.
The trusted base is Lean's kernel, Talos's semantics, and the binary decoder,
which is tested against the official WebAssembly testsuite.  `deslop.md` records
the design, decisions, status, and plan, and `devnotes.md` is the development
journal.

## Layout

| Path | Contents |
|---|---|
| `LeanExe/` | Source programs and the binary32 wrappers the float proofs use. |
| `Project/IR/` | The IR, `compile`, the statement rules, and rule lemmas. |
| `Project/Compiler/` | The compiler and the `leanexe_compile` command. |
| `Project/Pipeline/` | `Implements`, the runtime heap invariant, allocation lemmas, and `Emit.lean`. |
| `Project/Encoding/` | The encoder, decoder, `decode_encode`, and the testsuite runner. |
| `Project/ProofKit/` | General lemmas: memory, arrays, allocation, and binary32 arithmetic. |
| `Project/Scale/`, `Project/Gcd/` | Compiled programs with their theorems. |
| `ltg/` | The LTG knowledge base. |
| `tools/` | The resource-limited Lean runner and the Wasmtime host builder. |

## Commands

Run every Lean or Lake command through `tools/leanrun`, as `AGENTS.md`
requires.  The commands below build and check `gcd`: they build its proof, write
its bytes, validate them, run them in Wasmtime, and check the LTG entries.

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
`tools/download-wasmtime.sh` fetches the pinned C API.
