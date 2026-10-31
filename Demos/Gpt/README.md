# Gpt: GPT-2 in binary64

## The model, cached generation, and sampling

[The program](Program.lean) is the GPT-2 language model in Lean `Float`, binary64: token and
position embeddings, a loop over transformer blocks of multi-head causal attention and an MLP with
GELU, a final layer norm, and the scores of every vocabulary token.  It has two ways to run:
`forward` computes the scores of all positions at once, and `step` and `scores` compute one position
at a time from a cache of keys and values, which is how a host generates text.  `sampleTopK` draws a
token by top-k sampling, with SplitMix64 from [`Prng`](../../Library/Random/SplitMix64/README.md)
as its generator.  Shared vector and matrix operations come from [the binary64 linear-algebra
library](../../Library/Numerics/LinearAlgebra/README.md), and the model-specific approximations,
normalization, attention, and sampling remain in the demo.  `exp` and `tanh` are Lean definitions,
since Lean's `Float.exp` is opaque, and tests compare `exp` with the C library's, with no theorem
bounding its error.

## The compiled module and its theorems

[The verified compilation](Verified.lean) compiles the model's functions, from `dot` to
`sampleTopK`, with `verified_compile`, and `tests/verified/run.sh` writes the module to
`build/verified/gpt.wasm`.  For each function `f`, the generated theorem `compiled.f.implements`
states that the module computes `f` bit for bit, unless the call stops at `unreachable`, and
`compiled.f.trapFree` excludes the stop when `top` can rise by the allocation bound
`compiled.f.bound` within the memory cap.  [The verified compiler
manual](../../docs/verified-manual.md#the-implements-and-trapfree-theorems) states both forms and
the conditions under which a call stops.  `forward_causal` and `steps_exact` concern the Lean model
alone: the first states that row `i` of the scores depends only on tokens `0` to `i`, and the
second that the cached steps give `forward`'s rows bit for bit.  The `#print axioms`
commands of `Verified.lean` and [`VerifiedGeneration.lean`](VerifiedGeneration.lean), whose
theorems use `steps_exact`, report no axiom beyond `propext`, `Classical.choice`, and
`Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `compiled.f.implements` | For each compiled function `f`, a call on arguments that represent `x` returns the representation of `f x`, with the bits of every float, unless it stops at `unreachable`. |
| `compiled.f.trapFree` | Under room for `top` to rise by `compiled.f.bound` on the arguments within the memory cap, which the theorem requires only of a function that can stop, the call returns `f` of its arguments without a trap and raises `top` by at most the bound. |
| `compiled.bytes` | `encode` succeeds on `compiled.module`, `decode` reads the bytes back as the module, and the module implements every compiled function. |
| `gpt_file`, `gpt_file_decode` | `build/verified/gpt.wasm` holds `encode compiled.module` and decodes to `compiled.module`.  [`VerifiedFile.lean`](VerifiedFile.lean) checks both after the file is written. |
| `forward_causal` | Under bounds on the dimensions, two token sequences that agree up to position `i` give scores that agree up to row `i`. |
| `steps_exact` | Under bounds on the dimensions, `step` run on tokens `0` to `p` from an empty cache, then `scores`, equals row `p` of `forward` on any number of tokens above `p`, bit for bit. |

## Generation theorems

[The generation theorems](VerifiedGeneration.lean) state the host's calls of `step` and `scores` on
`compiled.module` with [the host's definitions](Host.lean) of the weights, their pointers, the cache
after `p` tokens, and the arguments of the calls.  `Generating heap store` describes a store between
the calls: the weights are borrowed at their pointers, and the cache of the first `p` tokens is
owned at `pc`, apart from them.  It names `heap`, the allocator's state, so that a premise can state
room for `top` to rise from it.  The theorems rest on `compiled.step.implements` and
`compiled.scores.implements`, which allow a stop at `unreachable`, and on `compiled.step.trapFree`
and `compiled.scores.trapFree`, which exclude it under room for the generated bounds
`compiled.step.bound` and `compiled.scores.bound`.

| Theorem | Statement |
|---------|-----------|
| `generating_start`, `generating_step`, `generating_scores` | In the host's sequence of calls, `step` per token with the cache handed over and then `scores` return row `p` of `forward`, unless a call stops at `unreachable`.  `scores` leaves a store of the generation, with the cache and the weights in place. |
| `generating_step_trapFree` | From a store of the generation after `p` tokens in which `top` can rise by the bound of `step` on its arguments within the memory cap, `step` returns without a trap the cache of `p + 1` tokens in a store of the generation.  It keeps the memory caps and raises `top` by at most the bound. |
| `generating_scores_trapFree` | From a store of the generation after `p + 1` tokens in which `top` can rise by the bound of `scores` on its arguments within the memory cap, `scores` returns without a trap row `p` of `forward`, under the bounds of `steps_exact`.  It leaves a store of the generation, keeps the memory caps, and raises `top` by at most the bound. |

`scores` leaves the cache in its block and the weights borrowed because the generated theorem keeps
every region of the heap that the call does not consume, and `scores` consumes nothing.  The
trap-free forms keep the memory caps and bound the rise of `top`, so room for the sum of the bounds
before the first call gives room for each later call by `Heap.Within.after`.  The theorems cover a
host that calls `step` again after `scores` and keeps the scores array.
[`tools/gpt2.py`](../../tools/gpt2.py) releases that array between the calls, after reading it or
passing it to `sampleTopK`, and no generation theorem covers the release or the call of
`sampleTopK`.  No theorem gives the bounds in closed form.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Demos.Gpt.Causal Demos.Gpt.Exact \
  Demos.Gpt.VerifiedGeneration
tests/verified/run.sh --cases gpt
uv run tests/gpt/gpt2_compare.py
uv run tools/gpt2.py --output-tokens 8 --prompt "It was a dark and stormy night"
```

The commands build the proofs, write and test the module, compare it with Hugging Face's model, and
generate text, with the setup of [the repository README](../../README.md#commands).
`tests/verified/run.sh --cases gpt` writes the module, validates it with `wasm-tools`, and runs
[`tests/gpt/run.sh`](../../tests/gpt/run.sh), which compares the module with native Lean on the
2,733 cases of [`tests/gpt/Cases.lean`](../../tests/gpt/Cases.lean), and
[`tests/gpt/sessions.sh`](../../tests/gpt/sessions.sh), which checks that sessions free every
allocation.  Without `--cases`, the driver also checks `VerifiedFile.lean` against the file it
wrote and requires both file theorems to report no axiom beyond `propext`, `Classical.choice`, and
`Quot.sound`.

[`tests/gpt/gpt2_compare.py`](../../tests/gpt/gpt2_compare.py) downloads the pinned GPT-2 124M
checkpoint, writes its weights to `build/gpt2-124m/`, about 1.0 GB, and compares `forward` and the
cached generation with Hugging Face's `GPT2LMHeadModel` in float64.  It fails if a score differs
from Hugging Face's by more than 1e-12 of the largest score, if a cached step's score differs from
`forward`'s, or if a generated token differs from Hugging Face's choice.
[`tools/gpt2.py`](../../tools/gpt2.py) then generates text: the command above printed "It was a
dark and stormy night. The wind was blowing, and the", and `--top-k`, `--temperature`, and `--seed`
select top-k sampling.  The scripts of `tests/gpt/` and `tools/gpt2.py` read the module from
`build/verified/gpt.wasm`.

## Related examples

[`Gpt32`](../Gpt32/README.md) is GPT-2 in binary32 on WGSL kernels, and [its GPT-2 browser
page](../../tests/web/README.md) samples tokens with this module's `sampleTopK`, with the binary32
scores widened to binary64.  [`Prng`](../../Library/Random/SplitMix64/README.md) compiles
SplitMix64, the generator of `sampleTopK`, into a module of its own, `prng.wasm`.  The VKB entry
[`region-frame`](../../VKB/entries/region-frame/README.md) describes the region clause of
`Implements` and the lemmas `Heap.Borrowed.keepIn` and `Heap.Owned.keepIn`, which the generation
proofs use to keep the weights borrowed and the cache owned across the calls.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019, and the repository
  [openai/gpt-2](https://github.com/openai/gpt-2).
- A. Vaswani et al., "Attention Is All You Need," *Advances in Neural Information Processing
  Systems* 30, 2017.
- J. L. Ba, J. R. Kiros, and G. E. Hinton, "Layer Normalization,"
  [arXiv:1607.06450](https://arxiv.org/abs/1607.06450), 2016.
- D. Hendrycks and K. Gimpel, "Gaussian Error Linear Units (GELUs),"
  [arXiv:1606.08415](https://arxiv.org/abs/1606.08415), 2016.
- A. Fan, M. Lewis, and Y. Dauphin, "Hierarchical Neural Story Generation," *Proceedings of ACL
  2018*.
- Hugging Face Transformers, [GPT-2](https://huggingface.co/docs/transformers/model_doc/gpt2),
  `GPT2LMHeadModel`.
- Hugging Face, [openai-community/gpt2](https://huggingface.co/openai-community/gpt2).
