**Yes—there is good research on the components of this problem, though I did not find a paper establishing a useful GPT-2 logit-error bound from only an entrywise weight bound.** Your adversarial weights are consistent with a real obstacle: bounding individual parameters does not tightly control the network’s sensitivity to rounding errors.

I’m assuming you mean absolute error between the f32 execution and exact-real evaluation of the same stored parameters.

The papers I would start with are:

1. **Beuzeville, Buttari, Gratton & Mary, “Deterministic and probabilistic rounding error analysis of neural networks in floating-point arithmetic,” *IMA Journal of Numerical Analysis*, 2026.** This is the closest general numerical-analysis reference: forward and backward errors, conditioning, and deterministic versus probabilistic rounding models. Its setting is feed-forward networks; it does not supply a complete GPT-2 analysis. Particularly relevant are §2.3 on conditioning and §4.4 on the assumptions needed for sharper probabilistic bounds. Those assumptions cannot simply be applied to adversarial weights under deterministic round-to-nearest. [Journal article](https://doi.org/10.1093/imanum/draf130) · [Author-hosted manuscript](https://tmary.perso.lip6.fr/doc/BEA_NN.pdf)

2. **Castin, Ablin & Peyré, “How Smooth Is Attention?”, ICML 2024.** Probably the most useful transformer-specific paper for your problem. It studies attention’s sensitivity on bounded domains, including normalization, causal masking, and experiments with **GPT-2**. Its bounds depend on weight operator norms and activation bounds, with matching lower-bound constructions in certain regimes. See §2.3, Theorem 3.3, and §§4–5. This analyzes amplification of perturbations in real arithmetic; you would combine it with bounds on the rounding errors injected by your implementation. [Paper](https://proceedings.mlr.press/v235/castin24a.html)

3. **Blanchard, Higham & Higham, “Accurately computing the log-sum-exp and softmax functions,” *IMA Journal of Numerical Analysis*, 2021.** The key reference for softmax’s own floating-point error. It distinguishes conditioning from algorithmic stability and analyzes shifted implementations. Useful for avoiding unnecessary pessimism from separately bounding exponentials and denominators. It does not bound the preceding computation of attention scores or subsequent network amplification. [Paper](https://doi.org/10.1093/imanum/draa038)

4. **Jia & Rinard, “Exploiting Verified Neural Networks via Floating Point Numerical Error,” SAS 2021.** Especially relevant to your adversarial examples: they construct network architectures and weights that exploit numerical errors to defeat verification claims. This is evidence that floating-point problems can be deliberately engineered, although it does not establish your particular bounded-weight GPT-2 result. [Paper](https://arxiv.org/abs/2003.03021)

5. **Murray, “Lipschitz-Based Robustness Certification Under Floating-Point Execution,” 2026 preprint.** A useful formal-methods complement: compositional bounds relating floating-point and real execution, overflow conditions, and a Rocq formalization. The developed results target feed-forward ReLU networks; extending them to LayerNorm, attention, and GELU requires additional work. [Paper](https://arxiv.org/abs/2603.13334)

Here is my mathematical interpretation of why your single-bound approach struggles.

**First, entrywise bounds allow large amplification.** For a $d\times d$ matrix,

$$
|W_{ij}|\le M \quad\Longrightarrow\quad \|W\|_2\le Md,
$$

and this is attainable by rank-one matrices. At $d=768$, a bound near $M=4$ permits an operator norm near $3072$. Multiple projections and residual branches can therefore make products of worst-case sensitivity bounds enormous. This observation alone does not prove that actual rounding errors attain those bounds.

**Second, LayerNorm bounds activation magnitude while permitting substantial sensitivity.** For the usual real-valued definition,

$$
\operatorname{LN}(x)
=\gamma\odot\frac{x-\bar x\mathbf1}{\sqrt{v(x)+\varepsilon}}+\beta,
$$

direct differentiation gives

$$
\|D\operatorname{LN}(x)\|_2
\le
\frac{\|\gamma\|_\infty}{\sqrt{v(x)+\varepsilon}}
\le
\frac{\|\gamma\|_\infty}{\sqrt{\varepsilon}}.
$$

If $\varepsilon=10^{-5}$ and $\|\gamma\|_\infty\le4$, the latter is approximately **1265**. A parameter-magnitude bound does not exclude nearly constant residual vectors, where the small-variance problem occurs. This is sensitivity of the mathematical function, before accounting for errors in computing its mean and variance.

There is an important qualification: **this is about obtaining a small, useful error bound—not necessarily the existence of any finite bound.** Positive LayerNorm epsilon removes the zero-variance singularity; a final LayerNorm and bounded unembedding also bound exact logit magnitudes. Floating-point exceptions still need separate treatment.

For a useful certificate, I would investigate **certified operator norms, lower bounds on LayerNorm variance over reachable states, and bounds on amplification from each rounding site to the logits**. Those carry information that a single maximum-weight bound discards. Probabilistic rounding assumptions can help with typical behavior, but change the guarantee.

One distinction would determine the next step: **do your adversarial weights produce large actual f32-versus-high-precision logit differences, or do they only make your computed upper bound explode?** The former supplies lower-bound evidence against the desired guarantee; the latter may still be fixable by preserving correlations and tightening propagation.
