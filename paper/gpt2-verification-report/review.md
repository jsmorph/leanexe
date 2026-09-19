# GPT-2 verification report review

## Technical review

The report describes source revision `f4d412b709a13bb2649fe23be267ec9928838064`.  The review traced `gpt2_128_exact` through the source recurrence, initialization, token-step composition, ownership preservation, and allocation budget.  The public theorem assumes the weight byte length, vocabulary token range, and token-count limit.  The report distinguishes the mathematical input copy from the native host implementation and specifies the order of cache observation, old-cache release, logit observation, and logit release.

The arithmetic claims refer to Lean's logical `Float32` semantics and the all-word equalities for addition, subtraction, multiplication, division, and square root.  The numerical-method description preserves the finite-input qualification for the exponential and GELU cutoffs.  The report names Wasmtime's canonical-NaN configuration and the trusted translation and runtime components.  Exact-byte closure, real-arithmetic bounds, and cached/full-prefix algorithm equivalence remain outside its formal claim.

The memory review distinguishes the charged heap-top bound of 2.5 GiB, the formal page-count bound of 4 GiB, and the recorded runtime memory size.  The runtime figures come from the canonical-mode test record.  The PyTorch comparison covers all logits for one 128-token sequence and its prefixes.  It establishes the reported test tolerance for those inputs.  The stochastic completion commands use different generators despite sharing the same seed option.

The source-driven proof check regenerated the artifact, matched the tracked Talos module, and passed the complete proof import using cached proof objects.  The public axiom reports contain `propext`, `Classical.choice`, and `Quot.sound`.  The first attempt failed because the sandbox prevented inspecting the materialized dependency revision.  The authorized retry passed.  Both logs are retained.  The source-identity record checks all cited repository paths and both artifact hashes.

## Editorial and PDF review

The first pass checked the central claim against the theorem statement, the bibliography against the cited files and primary documentation, and the distinction between proved equalities and empirical numerical agreement.  It removed unnecessary contrastive wording and a redundant transition.  The second pass reread the complete text for unsupported claims, notation, repetition, and the archive's style requirements.

Visual review covered all nine pages, including both tables and the theorem display.  The command examples initially rendered double hyphens as dashes.  Verbatim typesetting and the installed `upquote` package now preserve their ASCII syntax.  Text extraction checks all five complete commands.  The final two LaTeX passes report no undefined references, citation warnings, or overfull or underfull boxes.  Title, authors, and abstract in the submission request were extracted from the compiled PDF.

## Submission

The first submission uses primary category `cs.PL`, secondary category `cs.LG`, and a related-work link to the LeanExe subset report.  Its directory retains the exact PDF, source, and metadata.  The archive's standards and style manual are retained in the evidence directory.
