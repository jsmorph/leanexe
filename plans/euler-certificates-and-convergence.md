# Euler certificates, completion, and convergence

This plan expands phase 13 of the root development plan.  The user authorized the sequence on 15 September 2026 after merging the completed Euler branch into `main`.  The order is numerical certificates, successful completion, and continuum convergence.  Each stage starts with source review and mathematical research before Lean execution.

## 1. Numerical conservation and rounding certificates

For conserved component `i`, the existing `physical_trace_balance` theorem gives

\[
M_i^{\mathrm{final}}-M_i^{\mathrm{initial}}=B_i+R_i.
\]

Here `M` is the exact decoded cell total divided by `n²`, `B` is the sum of accepted durations times physical Rusanov boundary flux divided by `n`, and `R` is the defined accumulated physical residual.  The physical flux uses the decoded reconstructed states and the selected executable speed.  Both directional sweeps enter the boundary sum.  Rejected trials contribute zero accepted duration.

If checked intervals enclose the initial total, final total, and boundary sum, then

\[
R_i\in[M_{i,L}^{\mathrm{final}}-M_{i,U}^{\mathrm{initial}}-B_{i,U},\;
M_{i,U}^{\mathrm{final}}-M_{i,L}^{\mathrm{initial}}-B_{i,L}].
\]

The maximum of the negative lower endpoint and the upper endpoint bounds the absolute net residual.  The user selected the net residual certificate first.  A later assessment will determine whether to add the sum of local error bounds before cancellation.

The existing `F64Outward` operations compute a nearest-rounded result and then its adjacent endpoint.  Their checked theorems establish enclosure, including underflow, and expose rejection for nonfinite endpoints.  A certificate must preserve this status information and account for rounding in its own accumulation.  Exact rational constants in the physical reference, including `2/5`, need enclosing constructions from exact integer words.

The proposed observer keeps the numerical recurrence and accepted-grid sequence equal to the current solver.  It accumulates accepted boundary contributions with bounded storage, calculates initial and final totals for all four conserved components, and returns certificate endpoints with an explicit certificate status.  Its proof must connect those endpoints to the same accepted trace as the solver.  The observer's success conditions remain explicit until proved or checked for a production instance.

The binary64 time word and the sum of decoded timestep durations are separate quantities.  This certificate uses the durations in the existing physical-balance theorem.  A later continuum argument must account for rounded time accumulation.

- [x] Merge the completed branch into `main`, push, and verify the fetched identity.
- [x] Read the existing physical trace, step, row, outward-arithmetic, and error definitions.
- [x] Research outward interval inclusion and accumulation, including dependency overestimation.
- [x] Retrieve existing array-fold LTG guidance and identify applicable scalar support.
- [x] Resolve the certificate scope with the user: net conservation error first.
- [x] Prove shared residual-enclosure and accumulation results.
- [x] Specify the executable certificate and its relation to the unchanged numerical recurrence.
- [x] Prove the scalar arithmetic, totals, boundary evaluation, accepted-step observer, and complete observer recurrence.
- [x] Inspect compiler output and reuse checked regions, fold guidance, and allocation theorems where their premises match.
- [x] Prove exact generated execution and store preservation for grid totals, boundary reads, reconstructed face fluxes, the boundary fold, and physical timestep scaling.
- [x] Prove exact trial and retry execution, all failure paths, heap reservations, and interval results.
- [x] Prove complete outer-loop and enclosing-run execution through initialization, final totals, and residual intervals.
- [x] Prove complete generated execution, allocation, exact output, the 512 MiB memory bound, and certificate inclusion.  Pass the focused source-artifact gate and public axiom audits.
- [ ] Prove exact-byte behavior.  Run independent package checking and axiom audits.
- [ ] Run and inspect the proved certificate at 192, then at 800, with the standard one-process runner limits.  Preserve both earlier datasets.
- [ ] Publish the certificate values, meanings, widths, run measurements, and proof references.

## 2. Successful completion

Begin after the first certificate stage.  Review the existing guard-acceptance results, timestep-progress lemmas, and the recorded failure of the old `StateBounds 8` preservation claim.  State the exact quantified success claim before proof construction.  Investigate whether suitable bounds follow from this initial grid through every accepted step and whether retries accept before binary64 time loses positive progress.  Preserve any counterexample and use it to determine the achievable statement.  Changes to the numerical method require a design discussion.

- [ ] Research the invariant and progress argument.
- [ ] Establish the proposed invariant or a counterexample to it.
- [ ] Prove the supported completion statement and compose it with the exact artifact theorem.

## 3. Continuum convergence

Begin after the completion investigation.  Identify a precise solution concept, boundary condition, and convergence statement for this two-dimensional problem.  Examine an entropy inequality for the complete reconstructed and directionally split update.  Develop the required uniform estimates, consistency, limit argument, and treatment of finite precision.  A numerical-method change or a weaker target theorem requires a design discussion before implementation.

- [ ] Research applicable entropy and convergence results for the exact numerical method.
- [ ] Establish an entropy inequality or a counterexample for the proposed claim.
- [ ] State the justified convergence target and its additional hypotheses.
- [ ] Formalize the resulting argument and its connection to finite executable instances.

## Sources and proof construction

[Rump, Verification methods: Rigorous results using floating-point arithmetic](https://www.tuhh.de/ti3/rump/intlab/ActaNumerica2010.pdf), Sections 4–6, gives outward summation, interval inclusion, and examples of dependency overestimation.  The application here encloses aggregates of the defined discrete trace.  The Lean statements and existing binary64 semantics remain the proof authority.

[Feireisl, Lukáčová-Medvid’ová, and Mizerová](https://arxiv.org/abs/1803.08401) gives a reference for the later convergence investigation.  Its hypotheses and limiting solution concept must be compared with the reconstructed split scheme before adopting an argument.

The source basis is `EulerReconstructed.PhysicalTrace`, `PhysicalStep`, `TraceBalance`, and `RatioResidual`, together with `ProofKit.F64OutwardAccepted`, `F64RoundingResidual`, and `F64ErrorPropagation`.  The retrieved `array-fold-prefix` and `fixed-array-fold-body` entries supply accumulator invariants and generated-region composition.  Their applicability to the new compiler output will be checked after the executable specification is fixed.

The checked foundation comprises `ProofKit.RealBalanceEnclosure`, `ProofKit.F64OutwardAccumulation`, and `EulerReconstructed.PhysicalEnclosure`.  Their eight theorems cover real residual bounds, directed addition and subtraction, sequential rounded accumulation, rounded residual endpoints, and application to the existing Euler trace.  Every public axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The scalar certificate implementation has source soundness and generated-WASM execution proofs.  `ProofKit.F64Interval` provides checked addition, subtraction, multiplication by a decoded word, and division by a positive decoded word.  `EulerCertificate.Flux` composes them into pressure, physical flux, and Rusanov interface bounds.  `EulerCertificateFlux.Spec` proves exact output and componentwise enclosure whenever the corresponding status is zero.  Its 5,741-byte generated module reuses the existing outward arithmetic through a checked function-region renaming.  The focused source-artifact gate passes.

The complete observer now has source proofs.  `Totals.physical_encloses_grid` relates the two normalized array folds to the existing physical total.  `Boundary.physicalStep_encloses_trace` uses the same reconstructed faces and selected speeds as the two directional sweeps.  `Control.advance_base` proves numerical projection equality, and `Control.advance_trace` proves boundary inclusion along that same accepted trace.  `Solve.run_enclosure` composes these results with physical conservation.  `Solve.solve_toList` proves the previous solver output is the exact prefix, followed by four status/lower/upper triples.  The triples represent mass, x-momentum, y-momentum, and energy in that order.  All source audits use standard axioms.  The complete observer's generated execution, allocation, exact output, and 512 MiB memory bound now pass, together with the focused source-artifact gate.  Exact-byte verification remains open.
