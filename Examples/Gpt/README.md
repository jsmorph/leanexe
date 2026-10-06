# Gpt: GPT-2 in binary64

## What it is

[The program](Program.lean) is the GPT-2 language model in Lean `Float`, binary64: token and
position embeddings, a loop over transformer blocks of multi-head causal attention and an MLP with
GELU, a final layer norm, and the scores of every vocabulary token.  It has two ways to run:
`forward` computes the scores of all positions at once, and `step` and `scores` compute one position
at a time from a cache of keys and values, which is how text is generated.  `sampleTopK` draws a
token by top-k sampling, with SplitMix64 from [`Prng`](../Prng/README.md) as its generator.  [The
module definition](Module.lean) compiles 48 functions into the 14,141-byte `gpt.wasm`, which runs
the GPT-2 124M weights.

## What it shows

Every function of the module, from `dot` to `sampleTopK`, has an `Implements` theorem, so the bytes
compute the Lean model bit for bit, including the cached generation.  `Live` carries the proofs of
the functions that call others and release temporaries, and
[`tools/gpt_composites.py`](../../tools/gpt_composites.py) generates those proofs in
[`Composites.lean`](Composites.lean) from a description of each function's calls.  Two theorems
concern the Lean model alone: `forward_causal` states that row `i` of the scores depends only on
tokens `0` to `i`, and `steps_exact` states that the cached steps give `forward`'s rows bit for bit.
`exp` and `tanh` are written in Lean, since Lean's `Float.exp` is opaque, so the model differs
slightly from a library implementation.

| Theorem | Statement |
|---------|-----------|
| `gpt_bytes` | `encode` succeeds on `gpt.module`, and the module that `decode` reads from the bytes implements all 48 functions, functions 2 to 49. |
| `gpt_file` | The file `build/gpt/gpt.wasm` that `Emit.lean` writes holds the bytes of `gpt_bytes`.  [`File.lean`](File.lean) checks it after the file is written. |
| `forward_causal` | Under bounds on the dimensions, two token sequences that agree up to position `i` give scores that agree up to row `i`. |
| `steps_exact` | `step` run on tokens `0` to `p` from an empty cache, then `scores`, equals row `p` of `forward` on any number of tokens above `p`, bit for bit. |
| `generating_start`, `generating_step`, `generating_scores` | The host's sequence of calls, `step` per token with the cache handed over and then `scores`, returns row `p` of `forward`, unless a call stops at `unreachable`. |

The proofs are in [`Verify.lean`](Verify.lean), [`Composites.lean`](Composites.lean),
[`StepVerify.lean`](StepVerify.lean), [`SampleVerify.lean`](SampleVerify.lean),
[`Causal.lean`](Causal.lean), [`Exact.lean`](Exact.lean), [`Generation.lean`](Generation.lean), and
[`Bytes.lean`](Bytes.lean), and they use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.  `Implements` allows a stop at `unreachable`, and no theorem bounds the memory of a
generation.  [The design document](../../docs/design.md#proved) gives the construction of each
function.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Gpt.Bytes Examples.Gpt.Causal Examples.Gpt.Exact \
  Examples.Gpt.Generation
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Gpt.Module Examples.Gpt.gpt.module build/gpt/gpt.wasm
tools/leanrun --timeout 20m lake env lean Examples/Gpt/File.lean
tests/gpt/run.sh
uv run tests/gpt/gpt2_compare.py
uv run tools/gpt2.py --output-tokens 8 --prompt "It was a dark and stormy night"
```

The commands build the proofs, write the module, check that the file holds the proved bytes, and run
the tests and a generation, with the setup of [the repository README](../../README.md#commands).
[`tests/gpt/run.sh`](../../tests/gpt/run.sh) compares every export with native Lean on the 2,733
cases of [`tests/gpt/Cases.lean`](../../tests/gpt/Cases.lean), and
[`tests/gpt/sessions.sh`](../../tests/gpt/sessions.sh) checks that sessions free every allocation.
[`tests/gpt/gpt2_compare.py`](../../tests/gpt/gpt2_compare.py) downloads the pinned GPT-2 124M
checkpoint, writes its weights to `build/gpt2-124m/`, about 1.0 GB, and compares `forward` and the
cached generation with Hugging Face's `GPT2LMHeadModel` in float64, where the scores agree within
about 1e-13 of the largest score.  [`tools/gpt2.py`](../../tools/gpt2.py) then generates text: the
command above printed "It was a dark and stormy night. The wind was blowing, and the" in about 11
seconds, and `--top-k`, `--temperature`, and `--seed` select top-k sampling.

## Related examples

[`Gpt32`](../Gpt32/README.md) is GPT-2 in binary32 on WGSL kernels.  [`Prng`](../Prng/README.md)
supplies the sampler's generator, and [`SumSquares`](../SumSquares/README.md) and
[`Clob`](../Clob/README.md) show the fold and `Live` rules at a small scale.  The LTG entries
[`array-state-loop`](../../ltg/entries/array-state-loop/README.md),
[`function-call`](../../ltg/entries/function-call/README.md),
[`release-temporary`](../../ltg/entries/release-temporary/README.md), and
[`region-frame`](../../ltg/entries/region-frame/README.md) use this example's proofs as worked
examples.

## References

- A. Radford, J. Wu, R. Child, D. Luan, D. Amodei, and I. Sutskever, "Language Models are
  Unsupervised Multitask Learners," OpenAI, 2019, and the code at
  [github.com/openai/gpt-2](https://github.com/openai/gpt-2).
- A. Vaswani et al., "Attention Is All You Need," *Advances in Neural Information Processing
  Systems* 30, 2017.
- J. L. Ba, J. R. Kiros, and G. E. Hinton, "Layer Normalization,"
  [arXiv:1607.06450](https://arxiv.org/abs/1607.06450), 2016.
- D. Hendrycks and K. Gimpel, "Gaussian Error Linear Units (GELUs),"
  [arXiv:1606.08415](https://arxiv.org/abs/1606.08415), 2016.
- A. Fan, M. Lewis, and Y. Dauphin, "Hierarchical Neural Story Generation," *Proceedings of ACL
  2018*, which introduced top-k sampling for text generation.
- Hugging Face Transformers,
  [`GPT2LMHeadModel`](https://huggingface.co/docs/transformers/model_doc/gpt2), and the checkpoint
  [`openai-community/gpt2`](https://huggingface.co/openai-community/gpt2).
