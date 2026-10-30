# WebGPU Pages

[`tests/web/serve.py`](serve.py) serves two pages that run this project's WGSL kernels on a
browser's WebGPU.  The kernel test page runs the cases that [`tests/wgsl/run.sh`](../wgsl/run.sh)
writes and compares every output word with native Lean's.  The GPT-2 page runs GPT-2 124M in
binary32, with each kernel on WebGPU, in `gpt32.wasm` on the CPU, or on both with their scores
compared.  By default the pages run the verified compiler's kernels and modules, and with
`--leanexe` the LeanExe compiler's.  They use only standard WebGPU and WebAssembly and have been run
in Chromium 145 and Chrome 152.  The server needs `uv` and this repository's Lean
toolchain, and its first start downloads `transformers` and the GPT-2 tokenizer.

## Running

The GPT-2 page needs the weights of the pinned `openai-community/gpt2` checkpoint as binary32
files, 949 MiB in `build/gpt2-32`, which `generate.py --export` writes.  The server then starts on
127.0.0.1, port 8000:

```sh
export PATH="$HOME/.elan/bin:$PATH"
uv run tests/gpt32/generate.py --export
uv run tests/web/serve.py
```

The address http://127.0.0.1:8000/ links to both pages.  At start, the server writes what is missing
from `build/`.  When `build/wgsl` lacks a kernel text that the pages load or `cases.txt`, it runs
`tests/wgsl/run.sh --emit-only`, which writes the verified compiler's kernels and the cases of
[`tests/wgsl/Cases.lean`](../wgsl/Cases.lean) and of [the verified GPT-2
corpus](../../Demos/Gpt32/VerifiedCases.lean).  It also writes the verified modules
`build/verified/gpt32.wasm` and `build/verified/gpt.wasm`, the sampler's module, and builds the
program printer `gpt32-lines`.  With `--leanexe`, the server uses `tests/wgsl/run.sh --leanexe`,
which writes the LeanExe compiler's kernels under the same names to `build/wgsl-leanexe`, and the
LeanExe modules `build/gpt32/gpt32.wasm` and `build/gpt/gpt.wasm`.  The server writes only missing
files, so after a change to a kernel, to the cases, or to the GPT-2 programs, run
[`tests/wgsl/run.sh`](../wgsl/run.sh), which rewrites the kernel directory, or delete the affected
files before starting it.  The pages serve what the kernel directory holds: after
`tests/wgsl/run.sh --verified`, the kernel page runs that option's cases, and
[`tests/gpt32/generate.py`](../gpt32/generate.py) writes the LeanExe compiler's GPT-2 kernels to
`build/wgsl` under the names of the verified ones.

Browsers expose WebGPU only to secure contexts, which include http://127.0.0.1 and
http://localhost but not a plain-HTTP address of another machine.  To use a browser on another
machine, forward the port with `ssh -L 8000:127.0.0.1:8000 HOST` and open http://127.0.0.1:8000/
there.  Alternatively, start the server with `--host 0.0.0.0` and, in Chrome, add the address, such
as `http://10.211.55.3:8000`, to `chrome://flags/#unsafely-treat-insecure-origin-as-secure`.
`--port` chooses another port.

## Kernel tests: `/kernels/`

The page runs the cases of `cases.txt` on the kernels that the cases name.  By default these are
the 694 cases of [`tests/wgsl/Cases.lean`](../wgsl/Cases.lean) and of [the verified GPT-2
corpus](../../Demos/Gpt32/VerifiedCases.lean), on the verified compiler's kernels of [the binary32
example](../../Examples/Binary32/Compiled.lean) under the names `scale`, `axpyArray`, `matVec`, and
`condMix`, and of [the binary32 GPT-2 compilation](../../Demos/Gpt32/Verified.lean).  With
`--leanexe` they are the 474 cases of `tests/wgsl/Cases.lean`, on the LeanExe compiler's kernels of
[`Examples/Binary32/Wgsl.lean`](../../Examples/Binary32/Wgsl.lean),
[`Demos/Gpt32/Kernels.lean`](../../Demos/Gpt32/Kernels.lean), and
[`Demos/Gpt32/Specs.lean`](../../Demos/Gpt32/Specs.lean).  The page binds and dispatches each case
as `leanexe-webgpu-host run` does for [`tests/wgsl/run.sh`](../wgsl/run.sh), reads the output
buffer, and compares each word with native Lean's.  The cases include subnormal values, infinities,
NaNs, and arrays of up to 4,096 elements.

| Control or section | Contents |
|---|---|
| Adapter | `high-performance`, `low-power`, or `fallback`, the browser's software adapter |
| Device | Browser, vendor and architecture of the adapter, its limits, and its features |
| Results | Cases, passes, and failures for each kernel, with the shader compiler's messages, which are Tint's in Chrome |
| Failures | Each failing case's line in `cases.txt` and its first differing word, as bits and as a binary32 value |
| Report | Plain text of the run, with up to five failures for each kernel |

A device passes every case when its arithmetic meets the strict binary32 profile on these inputs:
each operation rounded to nearest even, subnormal values kept, and no fused or reordered
operations.  WGSL does not require this profile.  Chrome 152 on an Apple GPU, for example, failed
132 cases, because it flushes subnormal values to zero and fuses multiplications with additions,
both of which WGSL permits (sections 15.7.2 and 15.7.5).  `?run=high-performance`,
`?run=low-power`, or `?run=fallback` starts the run when the page loads.

## GPT-2: `/gpt2/`

The page tokenizes the prompt on the server and runs one step of GPT-2 for each position.  For each
step it fetches the host commands that `gpt32-lines` prints from
[`Demos/Gpt32/HostProgram.lean`](../../Demos/Gpt32/HostProgram.lean) and runs them, after
loading the weights with the setup commands.  The commands are those of the theorem
`Demos.Gpt32.generate_host`.  `hosts.js` runs them on WebGPU, as the C host does, or in
`gpt32.wasm`, the same kernels compiled to WebAssembly, whose arrays have the words of the host's
buffers.

| Control | Effect |
|---|---|
| Kernels | `WGSL and Wasm, compared` runs every step on both, compares the scores bit for bit, and follows Wasm's tokens.  `WGSL on WebGPU` and `gpt32.wasm on the CPU` run one |
| Adapter | WebGPU adapter, as on the kernel page |
| Load | Loads the weights into each kind of kernel and compiles the WGSL kernels |
| Tokens | Number of tokens to generate.  The prompt and the tokens may take up to 1,024 positions |
| Seed | Empty: each token is the first largest score's, as `greedy32` chooses.  A whole number: each token is drawn by top-k sampling, starting from the seed as the generator's state |
| Top-k, Temperature | `k` of the sampling, 50 by default, and its temperature, 1.0 by default |

Sampling calls `sampleTopK` of `gpt.wasm`, the binary64 model's module, with the scores widened
to binary64.  It keeps the tokens whose scores are at least the k-th largest and draws one with
weight `exp((score - max) / temperature)` from one SplitMix64 step.  In the compared mode, the
comparison table shows, for each step, the scores that differ in their bits, the largest
difference relative to the largest score, and the token each side chooses from the same state.
The page also reports the seconds per step of each kind of kernel and a plain-text report.  The
address takes the controls as parameters, such as
`?mode=both&power=high-performance&tokens=32&seed=42&run=1`, where `run=1` loads and generates
without clicks.

## Theorems and device results

Under its shape, token, loaded-weight, and device assumptions, `Demos.Gpt32.Verified.generate_host`
proves that the setup and step commands, run with the verified kernels, leave the bits of native
`step32` in the score buffers and that every dispatch is race-free, and `Demos.Gpt32.generate_host`
proves the same for the LeanExe compiler's kernels.  [The program](../../Demos/Gpt32/Program.lean)
defines that binary32 GPT-2 step.  `compiled.sampleTopK.implements` of `Demos.Gpt.Verified` proves
that `sampleTopK` in the verified `gpt.wasm` computes the Lean function of the same name, and
`sampleTopK_implements` proves it for the LeanExe module.  The verified `gpt32.wasm` has the Wasm
execution theorems of [the verified compilation](../../Demos/Gpt32/README.md#verified-compiler),
and the LeanExe compiler's `gpt32.wasm` has none.  The JavaScript hosts, the generation loop, the
server, the tokenizer, and the browser's WebGPU implementation remain outside those proofs.  The
compared mode measures differences between the page's GPU and Wasm results.

These browser measurements used the shared translation before arithmetic-NaN normalization:

| Device | Kernel tests | GPT-2, compared mode |
|---|---|---|
| Headless Chromium 145, SwiftShader (development machine) | 474 passed, 0.8 s | Scores equal at every step.  About 0.17 s a step on each side |
| Chrome 152, Apple GPU through Metal | 342 passed, 132 failed | 32 tokens from "The meaning of life is": no step with equal scores, the largest difference 5.2e-5 of the largest score, the same token at all 32 steps.  0.081 s a step with WGSL and 0.157 with Wasm |

After the pages moved to the verified compiler's kernels and modules, headless Chromium 145 with SwiftShader on an AArch64 machine gave these results:

| Server | Kernel tests | GPT-2, compared mode |
|---|---|---|
| Default, verified compiler's kernels and modules | 694 passed, 0.9 s | 16 greedy tokens from "The meaning of life is": scores equal at every step, 0.313 s a step with WGSL and 0.177 with Wasm.  8 tokens sampled from seed 42: scores equal at every step |
| `--leanexe`, LeanExe compiler's kernels and modules | 474 passed, 0.8 s | 8 tokens sampled from seed 42: scores equal at every step, and the same tokens as with the verified modules |

## Files

| Path | Contents |
|---|---|
| [`tests/web/serve.py`](serve.py) | Server: page files, kernel texts, Wasm modules, weights, and requests below |
| [`tests/web/index.html`](index.html) | Page that links to both pages |
| [`tests/wgsl/browser/`](../wgsl/browser) | Kernel test page |
| [`tests/gpt32/browser/`](../gpt32/browser) | GPT-2 page: `app.js` for the controls and the generation loop, `hosts.js` for the WebGPU and Wasm hosts and the sampler |
| [`Demos/Gpt32/Lines.lean`](../../Demos/Gpt32/Lines.lean) | `gpt32-lines`, the native program that prints the setup and step commands |

| Request | Answer |
|---|---|
| `/gpt2/api/tokenize?text=TEXT` | Token ids of `TEXT`, as JSON |
| `/gpt2/api/decode?ids=I,J,...` | Text of the token ids, as JSON |
| `/gpt2/api/setup` | Shader commands and setup commands, as a JSON list of lines |
| `/gpt2/api/step?token=T&p=P` | Commands of the step of token `T` at position `P`, as a JSON list of lines |
