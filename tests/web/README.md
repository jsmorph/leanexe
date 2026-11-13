# Browser pages

[`tests/web/serve.py`](serve.py) serves pages that run this project's WGSL kernels on a browser's
WebGPU and its verified modules in the browser's WebAssembly engine.  The kernel test page runs the
cases that [`tests/wgsl/run.sh`](../wgsl/run.sh) writes and compares every output word with native
Lean's.  The GPT-2 page runs GPT-2 124M in binary32, with each kernel on WebGPU, in `gpt32.wasm` on
the CPU, or on both with their scores compared.  The recount page recounts a ranked-choice contest
from a canonical ballot file on the reader's computer with the tabulator's Oakland module
`rcvTabulate.wasm` or its Maine module `rcvMaine.wasm`.  The conjunction page computes an interval
that contains the probability of collision of an encounter with the module `conjunction.wasm` and
draws the encounter plane.  The pages run the verified compiler's
kernels and modules.  They use only standard WebGPU and WebAssembly.
The server needs `uv` and this repository's Lean toolchain, and its first start downloads
`transformers` and the GPT-2 tokenizer.

## Running

The GPT-2 page needs the weights of the pinned `openai-community/gpt2` checkpoint as binary32 files,
949 MiB in `build/gpt2-32`.  `uv run tests/gpt32/generate.py --export` writes them.  The server
starts on 127.0.0.1, port 8000, with `elan`'s toolchain on the search path:

```sh
uv run tests/gpt32/generate.py --export
uv run tests/web/serve.py
```

The address http://127.0.0.1:8000/ links to the pages.  At start, the server writes what is missing
from `build/`.  When `build/wgsl` lacks a kernel text that the pages load or `cases.txt`, it runs
`tests/wgsl/run.sh --emit-only`, which writes the verified compiler's kernels and the cases of
[`tests/wgsl/Cases.lean`](../wgsl/Cases.lean) and of [the verified GPT-2
corpus](../../Demos/Gpt32/VerifiedCases.lean).  It also writes the verified modules
`build/verified/gpt32.wasm`, the sampler's module `build/verified/gpt.wasm`, and the tabulator's
modules `build/verified/rcvTabulate.wasm` and `build/verified/rcvMaine.wasm`, and the conjunction
program's module `build/verified/conjunction.wasm`, whose builds and emissions it runs under
`tools/leanrun` with 8 GiB of memory and two hours each, and it builds the
program printer `gpt32-lines`.  The server
writes only missing files.  After a change to a kernel, to the cases, or to the GPT-2 programs,
[`tests/wgsl/run.sh`](../wgsl/run.sh) rewrites the kernel directory, and the server writes again
any file that has been deleted.  The pages serve what the kernel directory holds: after
`tests/wgsl/run.sh --verified`, the kernel page runs that option's cases.
[`tests/gpt32/generate.py`](../gpt32/generate.py) writes the texts of the verified GPT-2 kernels to
`build/wgsl` under the names that `tests/wgsl/run.sh` gives them.

Browsers expose WebGPU only to secure contexts, which include http://127.0.0.1 and http://localhost
but not a plain-HTTP address of another machine.  A browser on another machine reaches the pages at
http://127.0.0.1:8000/ through a forwarded port, such as that of `ssh -L 8000:127.0.0.1:8000 HOST`.
With `--host 0.0.0.0` the server listens on every interface, and Chrome treats its address, such as
`http://ADDRESS:8000`, as secure when `chrome://flags/#unsafely-treat-insecure-origin-as-secure`
lists it.  `--port` chooses another port.

## Kernel tests: `/kernels/`

The page runs the cases of `cases.txt` on the kernels that the cases name.  These are the 694
cases of [`tests/wgsl/Cases.lean`](../wgsl/Cases.lean) and of [the verified GPT-2
corpus](../../Demos/Gpt32/VerifiedCases.lean), on the verified compiler's kernels of [the binary32
example](../../Examples/Binary32/Compiled.lean) under the names `scale`, `axpyArray`, `matVec`, and
`condMix`, and of [the binary32 GPT-2 compilation](../../Demos/Gpt32/Verified.lean).  The page
binds and dispatches each case as `leanexe-webgpu-host run` does for
[`tests/wgsl/run.sh`](../wgsl/run.sh), reads the output buffer, and compares each word with native
Lean's.  The cases include subnormal values, infinities, NaNs, and arrays of up to 4,096 elements.

| Control or section | Contents |
|---|---|
| Adapter | `high-performance`, `low-power`, or `fallback`, the browser's software adapter |
| Device | Browser, vendor and architecture of the adapter, its limits, and its features |
| Results | Cases, passes, and failures for each kernel, with the shader compiler's messages, which are Tint's in Chrome |
| Failures | Each failing case's line in `cases.txt` and its first differing word, as bits and as a binary32 value |
| Report | Plain text of the run, with up to five failures for each kernel |

A device passes every case when its arithmetic meets the strict binary32 profile on these inputs:
each operation rounded to nearest even, subnormal values kept, and no fused or reordered operations.
WGSL permits a device to flush subnormal values and to fuse
multiplications with additions (sections 15.7.2 and 15.7.5), and a device that does either fails
cases.  `?run=high-performance`, `?run=low-power`, or `?run=fallback` starts the run when the page
loads.

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
| Kernels | `WGSL and Wasm, compared` runs every step on both, compares the scores bit for bit, and continues with Wasm's tokens.  `WGSL on WebGPU` and `gpt32.wasm on the CPU` run one |
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

## RCV recount: `/rcv/`

The page recounts a ranked-choice contest from a canonical ballot file that the reader chooses on
their computer, under Oakland City Charter §1105 with the export `tabulate` of
`build/verified/rcvTabulate.wasm` or under 21-A M.R.S. §723-A with that of
`build/verified/rcvMaine.wasm`.  Two radio buttons choose the module, and a change of the choice
recounts the chosen file.  The browser reads the file with the File API and sends nothing to the
server.  The page shows each module's SHA-256, size, export, and bound, the file's size and the
bound of the call, the report as text, and a link that saves the report's bytes.  It needs a
secure context, as WebGPU does, for `crypto.subtle`, which computes the SHA-256.
[`tabulate.js`](rcv/tabulate.js) makes the call, and [`app.js`](rcv/app.js) runs the page.  [The
tabulator's README](../../Demos/Rcv/README.md#the-browser-page) and [the Maine module's
README](../../Demos/Rcv/Maine/README.md#the-browser-page) state the call theorems and the bounds,
the premises that the page establishes, the code that the page trusts, and the tests of the call.

Headless Chromium 145 on an AArch64 machine loaded the page, which showed both modules' SHA-256.
For each of the 19 contests of the Oakland corpus with the Oakland module and each of the 6
contests of the Maine corpus with the Maine module, chosen through the file input, and for the
Oakland worked example under both modules, the page's text and its saved file equal the
reference's report.  The largest file of each corpus took the page 0.035 s with the Oakland module,
the 2024 at-large council contest of 4,696,262 bytes with a bound of 409,403,869 bytes, and 0.052 s
with the Maine module, the 2024 contest for Representative to Congress, District 2, of 8,262,002
bytes with a bound of 694,918,189 bytes.

## Conjunction: `/conjunction/`

The page computes the two-dimensional probability of collision from the quantities of the
encounter plane that the reader enters: the mean miss vector `m1 m2`, its covariance
`c11 c12 c22`, the combined radius `r`, the threshold `t`, and the number of panels `n`.  A menu
fills the fields with an example: the README's, Chan's cases 1, 8, and 11, and Alfano's case 4 as
[the differential test](../../Demos/Conjunction/README.md#published-cases) projects it.  The page
converts each decimal entry to the nearest double, refuses an empty or malformed entry and a panel
count of 2^64 or more, and calls the export `assess` of `build/verified/conjunction.wasm` on a
fresh instance.  It shows the arguments, the status, `lo`, `hi`, the width, and the verdict, draws
`[lo, hi]` and `t` on a logarithmic scale, and draws the plane with the covariance ellipses at
one, two, and three standard deviations, the mean, the miss vector, and the disk.  A dashed ring
marks a disk smaller than two pixels at the drawing's scale, and the caption says so.
[`assess.js`](conjunction/assess.js) makes the call, and [`app.js`](conjunction/app.js) runs the
page and draws.

`compiled.assess.implements` of
[the conjunction program's compilation](../../Demos/Conjunction/Verified.lean) states that the
export, called from a store with the allocator's invariant that holds the table of `exp`, returns
without a trap the words of `Demos.Conjunction.assess`, and the generated `compiled.initial` states
that a fresh instance's store is such a store.  `assess_sound` and `pc_enclosure` of
[the soundness proofs](../../Demos/Conjunction/Soundness.lean) give the meaning of the result,
and [the conjunction README](../../Demos/Conjunction/README.md#theorems) states them.  The page's
JavaScript, its conversion of the entries, and its drawing lie outside the theorems.  The page has
a hidden section for the conjunction-message form, which will take two states and two covariances
in each object's RTN frame.

`node tests/conjunction/page.mjs CASES` runs `assess.js` under Node on the lines of the export
`assess` among the module cases that `verified-cases-conjunction` prints, 650 calls, and requires
each status, endpoint, and verdict to equal native Lean's bit for bit.

## Theorems and device results of the GPU pages

Under its shape, token, loaded-weight, and device assumptions, `Demos.Gpt32.Verified.generate_host`
proves that the setup and step commands, run with the verified kernels, leave the bits of native
`step32` in the score buffers and that every dispatch is race-free and meets the statement of the
Vulkan memory model.  It instantiates `Demos.Gpt32.generate_host`, which states the same for any
device with a backend.  [The program](../../Demos/Gpt32/Program.lean) defines that binary32 GPT-2 step.
`compiled.sampleTopK.implements` of `Demos.Gpt.Verified` proves that `sampleTopK` in the verified
`gpt.wasm` computes the Lean function of the same name.  The verified `gpt32.wasm` has the Wasm
execution theorems of [the verified compilation](../../Demos/Gpt32/README.md#verified-compiler).
The JavaScript hosts, the generation loop, the
server, the tokenizer, and the browser's WebGPU implementation are not covered by those proofs.  The
compared mode measures differences between the page's GPU and Wasm results.

Headless Chromium 145, with its SwiftShader adapter on an AArch64 machine, ran the pages with the
verified compiler's kernels and modules.  The kernel page passed all 694 cases.  In compared mode,
16 greedy tokens from "The meaning of life is" and 8 tokens sampled from seed 42 gave equal scores
at every step.

| Server | Kernel tests | GPT-2, compared mode |
|---|---|---|
| Default, verified compiler's kernels and modules | 694 passed, 0.9 s | 16 greedy tokens from "The meaning of life is": scores equal at every step, 0.313 s a step with WGSL and 0.177 with Wasm.  8 tokens sampled from seed 42: scores equal at every step |

## Files

| Path | Contents |
|---|---|
| [`tests/web/serve.py`](serve.py) | Server: page files, kernel texts, Wasm modules, weights, and requests below |
| [`tests/web/index.html`](index.html) | Page that links to the pages |
| [`tests/wgsl/browser/`](../wgsl/browser) | Kernel test page |
| [`tests/gpt32/browser/`](../gpt32/browser) | GPT-2 page: `app.js` for the controls and the generation loop, `hosts.js` for the WebGPU and Wasm hosts and the sampler |
| [`tests/web/rcv/`](rcv) | Recount page: `tabulate.js` for the call of the tabulator's modules, `app.js` for the page |
| [`tests/web/conjunction/`](conjunction) | Conjunction page: `assess.js` for the call of the module, `app.js` for the page and the drawing |
| [`Demos/Gpt32/Lines.lean`](../../Demos/Gpt32/Lines.lean) | `gpt32-lines`, the native program that prints the setup and step commands |

| Request | Answer |
|---|---|
| `/gpt2/api/tokenize?text=TEXT` | Token ids of `TEXT`, as JSON |
| `/gpt2/api/decode?ids=I,J,...` | Text of the token ids, as JSON |
| `/gpt2/api/setup` | Shader commands and setup commands, as a JSON list of lines |
| `/gpt2/api/step?token=T&p=P` | Commands of the step of token `T` at position `P`, as a JSON list of lines |
