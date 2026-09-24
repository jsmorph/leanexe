# Quantized GPT-2 report review

## Evidence and theorem review

The drafter read the current marXiv requirements and style manual before writing and preserved both served documents.  Repository review started with `AGENTS.md`, the root README, and the paper inventory.  The report's source and evidence snapshot is `c655d35b5011c1703dfd22bcceaec4e5bee17088`.

The arithmetic review checked `Kernel.lean`, `Grouped.lean`, `Format.lean`, and `Cached.lean`, plus the signed-dot, scalar-reconstruction, and rescaling proof declarations.  It verified the scale floor, all-zero rule, division/clipping/nearest-even order, rejection of byte `0x80`, scale-product rounding before accumulator rescaling, ordered partial additions, and one final bias addition.  The integer bound covers every prefix.  The group accumulator also converts to binary32 exactly.

The execution review read the complete specification, exact-binary translation, session state, loop, close, export relation, and numerical session declarations.  It checked the distinction between arbitrary same-length weights with status-dependent termination and measured successful inference of the pinned checkpoint.  It also checked the formal release order: old cache before output logits.  Report wording was corrected to match that order.

The evidence review recomputed the 302 observation count, 263 greedy agreements, 145 raw certificates, 232 common-offset certificates, zero forward certificates, storage reduction, median timing ratio, and warm-memory reduction.  The script reads both inventory files and measurement JSON from the fixed git revision.  It passes in the active checkout despite unrelated documentation edits.  It also verifies the frozen quantized binary's length and digest.

The report states the overlap between evaluated prefix sets and the repetition in the fixed trace.  It distinguishes terminal first-trace memory from repeated warm memory, separates Wasm capacity from process RSS, and identifies the serial binary32 Wasm comparison.  It retains the first quantizer's text failure, grouped completion differences, held-out failures, and the absence of a semantic-quality benchmark.

The numerical review checked the native checkpoint/checker boundary, captured-operand identity premise, raw arithmetic range conditions, source-stage theorem scope, and the distinction between measured-logit certificates and propagated bounds.  It corrected exponential reduction wording to “up to six halvings and corresponding squarings.”  The report does not infer complete text preservation from individual accepted margin checks.

An independent review agent examined the source sections as they were drafted, verified every repository link against the cited revision, checked bibliography metadata against primary sources and prior marXiv records, and reviewed the extracted PDF.  Root reviewed the complete extracted PDF and rendered pages 1, 5, 10, 13, and 17.  Those pages were legible and unclipped.  The independent reviewer identified command-option ligatures.  Disabling typewriter ligatures corrected the PDF extraction to preserve ASCII `--`.

## Editorial and build review

Two prose passes checked the archive's banned constructions, unsupported claims, repeated numerical claims, paragraph openings, and scope qualifiers.  The draft removed a content-free introductory sentence and unnecessary contrast clauses.  Tables retain exact values where they support reproduction, while prose reports interpretation and measurement scope.  All substantive experimental limitations remain explicit.

The compiled PDF has twenty pages, extractable text, resolved citations and references, no overfull boxes, and no BibTeX warnings.  Three underfull-paragraph diagnostics remain.  The title and abstract in the metadata were extracted from the PDF, bounded by the author line and the Contents heading.  The abstract stays below the archive's 3,000-character limit.  The build-result record supplies the PDF digest and command results.

The first compilation exposed a literal title escape and a fragile sequence-splitting command in a caption.  Both were corrected.  BibTeX rejected an absolute output path under its `openout_any=p` setting.  Running BibTeX in the temporary output directory with the report directory in `BIBINPUTS` succeeded.  No dependency was added, and no Lean, Lake, compiler, or inference job ran during report production.

## Submission boundary

The report is ready for root's submission cycle.  The source revision remains fixed.  Current quantized proofs and retained measurements are complete at the stated component boundary.  Repository-wide aggregate, execution, conformance, and clean-checkout release checks remain pending.  Root owns submission, archive review, any revision requested by the archive, publication records, commit, and push.
