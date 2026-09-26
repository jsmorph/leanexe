# Quantized GPT-2 report review

Accept the final report.  No unresolved substantive or style findings remain.

Reviewed PDF: `paper/gpt2-quantized-report/main.pdf`, 20 pages, 392,080 bytes, SHA-256 `6f5156e663a24b7938d13d1b949a5991bfbd47eceb7b0f3d9614742a70b9d250`.  Review date: 2026-09-24.  Submission and archive review belong to the root agent.

## Review scope

This independent review checks all nine manuscript sections, bibliography, complete extracted PDF text, submission metadata, and evidence inventory against the source arithmetic, cached-session and artifact theorem declarations, retained evaluation JSON, numerical theorem assumptions, and the current marXiv standards and style manual retrieved on 2026-09-24.  It ran no Lean build, inference experiment, or certificate evaluator.  Root inspected the rendered pages.

## Checked evidence

| Subject | Primary evidence and result |
|---|---|
| Quantization | `LeanExe/Models/Gpt2/Quantized/Kernel.lean` uses finite FP32 input words, FP32 maximum-magnitude division by 127, a minimum scale of `2^-126`, scale one for all-zero rows, saturation to `[-127,127]`, and nearest-even rounding. |
| Group order | `LeanExe/Models/Gpt2/Quantized/Grouped.lean` uses contiguous groups of 64, signed-byte products, an integer group sum, FP32 scale multiplication, FP32 rescaling, and ordered FP32 addition from positive zero.  Bias is added once. |
| Integer range | `Gpt2QuantizedGroupedRows.Numerics.group_integer_conversion_exact` uses the bound `64 * 127^2 = 1,032,256` and proves exact signed-integer-to-FP32 conversion. |
| Session scope | `Gpt2QuantizedCached.Spec.gpt2_128_exact` assumes a 127,695,972-byte weight array and at most 128 UInt32 tokens.  Its session specification covers reset, allocation, byte loading, validation, calls, failure termination, and releases. |
| Artifact | `ArtifactTranslation.artifact_gpt2_128_exact` connects the embedded 28,315-byte artifact to decoding, grammar membership, validation, CoreValid, and the complete session property.  External file equality remains a tool/runtime assumption. |
| Weights | The export record checks 123,532,032 signed coefficients, 133,201 scales, and 907,776 retained FP32 words.  Total file storage falls from 497,759,232 to 127,695,972 bytes. |
| Controlled benchmark | One warmup trace and three measured 128-prefix traces give median durations 27.286732966662385 s and 97.93591100571211 s.  The ratio is approximately 3.589.  Warm linear-memory maxima are 747,110,400 and 1,144,848,384 bytes.  The comparison uses the repository's serial FP32 WASM implementation. |
| Bitwise checks | The retained 128-prefix run checks 6,432,896 logits and complete caches against the grouped reference.  Nine compiled completions reproduce the grouped reference token streams. |
| Greedy choices | The retained fixed trace contributes 120/128, nine prompt-prefix sequences contribute 85/101, and six later held-out prompts contribute 58/73.  The sum 263/302 counts evaluated positions, with overlap between prefix sets. |
| Observed certificates | The raw-margin checks accept 119 + 26 = 145 positions.  Common-offset checks accept 183 + 49 = 232 positions.  These use measured output differences and do not certify complete generated continuations. |
| Forward bounds | The source numerical theorem assumes arithmetic ranges, reconstruction inequalities, source-intermediate identity, valid shapes/tokens, successful quantized steps, and the stated cache relation.  Native Lean computes retained natural-number bounds.  All 302 bounds exceed `2^129`; no forward token certificate succeeds. |
| Bound magnitudes | Retained bounds range from about `1.515968e601` to `8.124149e61429`; held-out bounds range from about `1.515968e601` to `2.353630e7765`. |
| Release state | Quantized source/artifact checks are distinct from unfinished repository-wide release checks.  The paper must preserve that distinction. |

## Preliminary corrections sent to the author

The paper must distinguish position observations from distinct prefixes, state the exact FP32 rescaling order, state model-size and token-count assumptions, and describe the failure/release branches.  The fixed trace repeats token subsequences after its opening.  Its benchmark and quality measurements have that workload scope.  The performance comparison is against the repository's serial FP32 WASM implementation.  The 232 observed-logit certificates and zero forward certificates are separate results.

## Draft verdict

The final report supports its core claims and states the proof and evaluation limitations.  It distinguishes the exact execution theorem, finite reference comparisons, observed-logit certificates, and conditional forward bounds.  The abstract and body state zero successful forward token certificates.  The text explains overlapping position observations, the repetitive fixed trace, the serial FP32 comparison, native checker execution, the captured-operand identity premise, and unfinished repository-wide release checks.  FP32 remains the default.

## Required corrections sent during drafting

| Severity | Location at review | Correction and evidence |
|---|---|---|
| Medium: exact operation order | `sections/03-proof.tex:38` | The first wording reversed the formal release order.  `Session/State.lean:38–39` releases the previous cache before the output-logit buffer.  The author has corrected this in the current source. |
| Low: count interpretation | `sections/06-runtime.tex:31` | Closing the session releases its remaining live objects.  The final counters show cumulative freeing of all 45,569 allocations, or 182,273 across four traces.  The final text now states that the allocator has freed all allocations by close. |
| Low: arithmetic procedure | `sections/07-numerical.tex:38` | Exponential reduction performs up to six conditional halvings and the corresponding number of squarings.  `LeanExe/Models/Gpt2/Numerics.lean:25–36` does not always execute six halvings or six squarings.  The final text states the upper limit. |
| Low: missing premise detail | `sections/04-export.tex:16` | State the scalar division exponent limits `24 ≤ b ≤ 275`.  The author has added these limits. |
| Build defect | `main.tex:20` | The initial title contained a literal escaped newline and plus sign.  The author has replaced them with the intended line break. |
| Style | `sections/01-scope.tex:8` | Delete the announcement “The work has three different conclusions.”  The author has removed it. |
| Style and extent | Abstract | Replace “including six fresh prompts” with “including prefixes of six held-out prompts.”  The author has made this change. |
| Style: repeated values | `sections/06-runtime.tex:4,8,17,25` | Keep exact storage counts and runtime values in the table, and use surrounding prose for interpretation.  The author removed the duplicate exact counts and ratio. |
| Low: executable command text | `main.tex`, PDF pages 3 and 19 | Typewriter ligatures initially rendered ASCII double hyphens as en dashes in command flags.  The final PDF preserves `--quantized`, `--scheme`, `--grouped`, `--wasm`, and `--repetitions` after whitespace normalization. |

Every required correction above is resolved in the reviewed PDF.

## Static source checks

All 71 repository links resolve to paths present at the cited revision `c655d35b5011c1703dfd22bcceaec4e5bee17088`.  The named supporting declarations exist in the linked modules.  All 67 inventory entries match the exact byte lengths and SHA-256 hashes of objects at that revision, including documentation with unrelated working-tree changes.  A scan for the style manual's listed filler terms, emphatic markup, em-dashes, and prose semicolons found no additional occurrences.  Mathematical notation and ordinary negative limitations were read in context.

## PDF and metadata checks

Direct extraction from the final PDF succeeds.  After whitespace normalization, its title and entire 1,801-character abstract equal `evidence/metadata.json`.  The author is Jamie Stephens in the PDF and metadata.  The 20-page comment matches `pdfinfo`.  Primary classification `cs.PL` and secondary classification `cs.CL` fit the paper.  The related-paper descriptions fit the cited earlier reports.  The PDF hash and byte length match `evidence/build-result.json`.

The retained JSON independently gives 302 position observations, 263 equal greedy winners, 145 accepted raw-margin checks, 232 accepted common-offset checks, and zero forward certificates.  Direct recomputation gives 74.3458355384155% weight-storage reduction, median runtime ratio 3.5891402288931213, and 34.74154216039842% warm linear-memory reduction.  The displayed rounding agrees with these values.  The manuscript's remaining numerical tables, bounds, model dimensions, cache sizes, and identities match the cited evidence or source definitions.

The related-work descriptions agree with the primary records for [integer-only quantization](https://arxiv.org/abs/1712.05877), [LLM.int8()](https://arxiv.org/abs/2208.07339), [SmoothQuant](https://arxiv.org/abs/2211.10438), and [QEBVerif](https://arxiv.org/abs/2212.02781).  QEBVerif's volume, pages, and publication year agree with the [publisher record](https://link.springer.com/chapter/10.1007/978-3-031-37703-7_20).  The earlier GPT report titles and authors agree with the local marXiv records.

## Remarks

No remaining remarks.
