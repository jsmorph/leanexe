# LeanExe

LeanExe compiles Lean functions to WebAssembly and proves, for each compiled function, that the
bytes compute the Lean function.  The compiler, which is not trusted, translates a Lean definition
to a small IR during elaboration and records hints for the prover.  `compile` translates the IR to
a module of Talos, a WebAssembly interpreter written in Lean, and `encode` produces the bytes.  A
proof per function establishes `Implements`: from any store that satisfies the runtime invariant,
the exported function either traps at `unreachable` or returns the Lean function's value.
`decode_encode` gives the same theorem for the module that the decoder reads from the bytes.  For
the Euler solvers, the drone planner, and the increment example, `ImplementsA` with a memory budget
also proves that the call returns within a stated number of pages.

Each compiler rule has its own theorem.  A rule's theorem, such as `Func.tail_implements` for tail
recursion, reduces each program's proof to the parts the rule does not cover, and an entry of
[the LTG knowledge base](ltg/README.md) describes it.  The trusted base is Lean's kernel, Talos's
semantics, and the binary decoder, which the official WebAssembly testsuite tests.

[The user manual](docs/manual.md) describes the dialect the compiler accepts, the commands that
compile and run a program, the theorems and the rules that prove them, the tests, and the examples.
[The design record](docs/design.md) holds the design, the decisions, the status, and the plan, and
[the development journal](devnotes.md) records the work.

## Layout

| Path | Contents |
|---|---|
| [`LeanExe/`](LeanExe/) | The system, the library `LeanExe`. |
| [`LeanExe/Dialect/`](LeanExe/Dialect/) | The modules a program may import: the combinators `LeanExe.loop`, `LeanExe.build`, and `LeanExe.repeatWhile`, and `LeanExe.Float32.nearest`. |
| [`LeanExe/Compiler/`](LeanExe/Compiler/) | The compiler and the `leanexe_compile` command. |
| [`LeanExe/IR/`](LeanExe/IR/) | The IR, `compile`, the statement and template rules, and the `Live` invariant of composite bodies. |
| [`LeanExe/Runtime/`](LeanExe/Runtime/) | The code of the runtime functions `alloc` and `release`, and the free-list layout. |
| [`LeanExe/Pipeline/`](LeanExe/Pipeline/) | `Implements` and `ImplementsA`, the runtime heap invariant, the allocation and release specifications, and the memory budget. |
| [`LeanExe/Encoding/`](LeanExe/Encoding/) | The encoder, the decoder, and `decode_encode`. |
| [`LeanExe/ProofKit/`](LeanExe/ProofKit/) | General lemmas: memory, arrays, allocation, binary32 and binary64 arithmetic and enclosures, and the raw-bit float wrappers that the float proofs state their results about. |
| [`LeanExe/WGSL/`](LeanExe/WGSL/) | The WGSL subset, its printer, parser, and semantics, and the proved translation of IR kernels into WGSL. |
| [`Examples/`](Examples/) | The library `Examples`: one directory per example, with a README, the program, the specification where there is one, the module, the proofs, the module cases, and the request and run records where there are any.  [The manual's list of examples](docs/manual.md#worked-examples) names them all. |
| [`docs/`](docs/) | [The user manual](docs/manual.md) and [the design record](docs/design.md). |
| [`ltg/`](ltg/) | The LTG knowledge base and its checker, `Check.lean`. |
| [`.claude/skills/verified-executable/`](.claude/skills/verified-executable/SKILL.md) | The skill that takes a request in English to a program and a theorem about its bytes. |
| [`tools/`](tools/) | The resource-limited Lean runner, `Emit.lean` and `EmitWgsl.lean`, which write modules and kernels, the Wasmtime and WebGPU hosts and their build scripts, the checker `demo-check`, and the Euler and GPT-2 command-line tools. |
| [`tests/`](tests/) | Module, decoder, GPT, drone, PRNG, WGSL, and GPT-2 tests, and the WebGPU pages of [`tests/web/`](tests/web/). |
| [`data/`](data/), [`paper/`](paper/) | Records of runs, and reports. |

## Commands

Run every Lean or Lake command through [`tools/leanrun`](tools/leanrun), as [the repository
instructions](AGENTS.md) require.  The commands below build the project, write the bytes of `gcd`,
validate them, run them in Wasmtime, and check the LTG entries.  The manual lists the tests and the
full check.

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Gcd.Module Examples.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
tools/leanrun --timeout 10m lake env lean --run ltg/Check.lean ltg/entries
```

[`tools/build-wasmtime-host.sh`](tools/build-wasmtime-host.sh) builds the Wasmtime host after
[`tools/download-wasmtime.sh`](tools/download-wasmtime.sh) fetches the pinned C API.
[`tests/modules/run.sh`](tests/modules/run.sh) compares every module except `gpt`, `gpt32`, and
`prng` with native Lean on the cases in each example's `Cases.lean`, which
[`tests/modules/Cases.lean`](tests/modules/Cases.lean) runs in turn, and
[`tests/gpt/run.sh`](tests/gpt/run.sh) does the same for `gpt.wasm`.  Both read the modules from
`build/NAME/NAME.wasm`.

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  One runs the WGSL kernel
tests on a browser's WebGPU, and the other runs GPT-2 with its kernels on WebGPU, in WebAssembly,
or on both and compares them.  [The description of the pages](tests/web/README.md) covers their
setup and what is proved about what they run.  The GPT-2 page needs the binary32 weights that
`uv run tests/gpt32/generate.py --export` writes.
