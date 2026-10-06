# WebGPU Pages

[`tests/web/serve.py`](serve.py) serves two pages that run this project's WGSL kernels on a
browser's WebGPU.  The kernel test page runs the cases of
[`tests/wgsl/Cases.lean`](../wgsl/Cases.lean) and compares every output word with native Lean's.
The GPT-2 page runs GPT-2 124M in binary32, with each kernel on WebGPU, in `gpt32.wasm` on the CPU,
or on both with their scores compared.  The pages use only standard WebGPU and WebAssembly and have
been run in Chromium 145 and Chrome 152.  The server needs `uv` and this repository's Lean
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
from `build/`: the seventeen kernel texts and `cases.txt` in `build/wgsl`, `gpt32.wasm`, the
sampler's module `gpt.wasm`, and the program printer `gpt32-lines`.  From nothing this took about
four minutes on the development machine.  The server writes only missing files, so after a change to
a kernel, to the cases, or to the GPT-2 programs, run [`tests/wgsl/run.sh`](../wgsl/run.sh) (which
rewrites `build/wgsl`) or delete the affected files before starting it.

Browsers expose WebGPU only to secure contexts, which include http://127.0.0.1 and
http://localhost but not a plain-HTTP address of another machine.  To use a browser on another
machine, forward the port with `ssh -L 8000:127.0.0.1:8000 HOST` and open http://127.0.0.1:8000/
there.  Alternatively, start the server with `--host 0.0.0.0` and, in Chrome, add the address, such
as `http://10.211.55.3:8000`, to `chrome://flags/#unsafely-treat-insecure-origin-as-secure`.
`--port` chooses another port.

## Kernel tests: `/kernels/`

The page runs 474 cases of seventeen kernels: `scale`, `axpyArray`, `matVec`, and `condMix` of
[`Examples/Binary32/Wgsl.lean`](../../Examples/Binary32/Wgsl.lean), `exp` of
[`Examples/Gpt32/Kernels.lean`](../../Examples/Gpt32/Kernels.lean), and the twelve GPT-2 kernels of
[`Examples/Gpt32/Specs.lean`](../../Examples/Gpt32/Specs.lean).  It binds and dispatches each case
as `leanexe-webgpu-host run` does for [`tests/wgsl/run.sh`](../wgsl/run.sh), reads the output
buffer, and compares each word with native Lean's.  The cases include subnormal values, infinities,
NaNs, and arrays of up to 4,096 elements.

| Control or section | Contents |
|---|---|
| Adapter | `high-performance`, `low-power`, or `fallback`, the browser's software adapter |
| Device | The browser, the adapter's vendor and architecture, its limits, and its features |
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
[`Examples/Gpt32/HostProgram.lean`](../../Examples/Gpt32/HostProgram.lean) and runs them, after
loading the weights with the setup commands.  The commands are those of the theorem
`Examples.Gpt32.generate_host`.  `hosts.js` runs them on WebGPU, as the C host does, or in
`gpt32.wasm`, the same kernels compiled to WebAssembly, whose arrays have the words of the host's
buffers.

| Control | Effect |
|---|---|
| Kernels | `WGSL and Wasm, compared` runs every step on both, compares the scores bit for bit, and follows Wasm's tokens.  `WGSL on WebGPU` and `gpt32.wasm on the CPU` run one |
| Adapter | The WebGPU adapter, as on the kernel page |
| Load | Loads the weights into each kind of kernel and compiles the WGSL kernels |
| Tokens | The number of tokens to generate.  The prompt and the tokens may take up to 1,024 positions |
| Seed | Empty: each token is the first largest score's, as `greedy32` chooses.  A whole number: each token is drawn by top-k sampling, starting from the seed as the generator's state |
| Top-k, Temperature | The sampling's `k`, 50 by default, and its temperature, 1.0 by default |

Sampling calls `sampleTopK` of `gpt.wasm`, the binary64 model's module, with the scores widened
to binary64.  It keeps the tokens whose scores are at least the k-th largest and draws one with
weight `exp((score - max) / temperature)` from one SplitMix64 step.  In the compared mode, the
comparison table shows, for each step, the scores that differ in their bits, the largest
difference relative to the largest score, and the token each side chooses from the same state.
The page also reports the seconds per step of each kind of kernel and a plain-text report.  The
address takes the controls as parameters, such as
`?mode=both&power=high-performance&tokens=32&seed=42&run=1`, where `run=1` loads and generates
without clicks.

## What Is Proved

`generate_host` proves that, on a device with strict binary32 arithmetic, the commands of the setup
and of each step leave in the score buffers exactly the bits of `step32`, the binary32 GPT-2 step of
[`Examples/Gpt32/Program.lean`](../../Examples/Gpt32/Program.lean).  `sampleTopK_implements` proves
that `sampleTopK` in `gpt.wasm` computes the Lean function of the same name.  The JavaScript hosts,
the generation loop, the server, the tokenizer, and the browser's WebGPU implementation are
unproved, and the kernels of `gpt32.wasm` have no WebAssembly theorem.  On a device outside the
strict profile, no theorem applies, and the compared mode measures the difference.

| Device | Kernel tests | GPT-2, compared mode |
|---|---|---|
| Headless Chromium 145, SwiftShader (development machine) | 474 passed, 0.8 s | Scores equal at every step.  About 0.17 s a step on each side |
| Chrome 152, Apple GPU through Metal | 342 passed, 132 failed | 32 tokens from "The meaning of life is": no step with equal scores, the largest difference 5.2e-5 of the largest score, the same token at all 32 steps.  0.081 s a step with WGSL and 0.157 with Wasm |

## Files

| Path | Contents |
|---|---|
| [`tests/web/serve.py`](serve.py) | The server: page files, kernel texts, Wasm modules, weights, and the requests below |
| [`tests/web/index.html`](index.html) | The page that links to both pages |
| [`tests/wgsl/browser/`](../wgsl/browser/) | The kernel test page |
| [`tests/gpt32/browser/`](../gpt32/browser/) | The GPT-2 page: `app.js` for the controls and the generation loop, `hosts.js` for the WebGPU and Wasm hosts and the sampler |
| [`Examples/Gpt32/Lines.lean`](../../Examples/Gpt32/Lines.lean) | `gpt32-lines`, the native program that prints the setup and step commands |

| Request | Answer |
|---|---|
| `/gpt2/api/tokenize?text=TEXT` | The token ids of `TEXT`, as JSON |
| `/gpt2/api/decode?ids=I,J,...` | The text of the token ids, as JSON |
| `/gpt2/api/setup` | The shader commands and the setup commands, as a JSON list of lines |
| `/gpt2/api/step?token=T&p=P` | The commands of the step of token `T` at position `P`, as a JSON list of lines |
