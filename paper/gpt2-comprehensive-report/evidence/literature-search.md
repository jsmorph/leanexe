# Verification of GPT-style inference: literature search

Search date: 19 September 2026.  The task was to identify work comparable to a proof-assistant-checked theorem connecting a complete executable GPT inference module to its source algorithm.

## Method and limits

Queries combined GPT-2, transformer, and LLM inference with formal verification, executable, binary, Lean, Coq/Rocq, Isabelle, CompCert, CakeML, and verified compilation.  Follow-up searches examined claimed verification results and their primary papers or repository definitions.  The comparison records the proof subject, arithmetic, quantified domain, translation boundary, and checking method.  Independent proof rebuilding and complete dependency audits remain outside this source review.

## Primary sources

| Source | Inspected evidence | Comparison |
|--------|-------------------|------------|
| [TorchLean, v2](https://arxiv.org/html/2602.22631v2) | Table 3, Appendix B forward-compilation theorem, Appendix D.1 runtime correspondence. | Source/IR and arithmetic proofs.  Target-runtime connection is future work. |
| [HLS transformation verification](https://www.csl.cornell.edu/~zhiruz/pdfs/hls-verify-fpga2024.pdf) | Introduction's synthesis assumption, Section 7.2 BERT layer. | C/C++ equivalence before HLS. |
| [Compact Proofs of Model Performance](https://arxiv.org/pdf/2406.11779) | Abstract, Max-of-K scope, Appendix A.7 real/floating-point boundary. | Accuracy property of small trained transformers. |
| [Lean Verified Transformers](https://github.com/srush/lean-transformer/blob/main/Transformer.lean) | Rational vectors, `softmax_like`, ordered/tiled attention equalities. | Source-level transformer invariants. |
| [Rocq Transformer](https://github.com/jwiegley/rocq-transformer) | Documented structural implementations and numerical parameters. | Shapes and architecture with abstract numerical operations. |
| [Verifiable Transformers](https://github.com/neelsomani/verifiable-transformers) | Fixed 1,280-prompt quote-closing result and stated architecture changes. | SMT task-decision guarantees. |
| [zkLLM](https://arxiv.org/html/2404.16109v1) | Protocol and soundness section, quantization/attention tolerances, model evaluation. | Cryptographic certificates for inference evaluations. |
| [zkGPT](https://www.usenix.org/system/files/usenixsecurity25-qu-zkgpt.pdf) | GPT-2 implementation, arithmetic encoding, Section 9.3 quantization limitation. | Complete quantized inference proof system. |
| [DeepProve](https://github.com/Lagrange-Labs/deep-prove/blob/master/zkml/README.md) | Full-model commands, quantization, proving and verification description. | Current implemented cryptographic LLM inference proofs. |
| [LAProof](https://www.cs.princeton.edu/~appel/papers/LAProof.pdf) | Numerical accuracy results and verified C sparse matrix-vector case. | Verified floating-point implementation precedent. |

## Assessment

The inspected sources establish related results at the model, source, transformation, numerical-kernel, or individual-evaluation level.  The search found no earlier result matching the complete frozen-binary-to-source GPT inference theorem.  The report uses a qualified “to our knowledge” priority statement and names the formal WebAssembly execution boundary.  Its WGSL statement retains the explicit host and strict shader-arithmetic premises.  Complete cryptographic inference certificates predate the report and receive a separate comparison.
