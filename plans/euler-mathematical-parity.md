# Euler mathematical parity

The user authorized review, a detailed plan, and implementation on 2026-09-14.
The target is the current four-component, two-dimensional ideal-gas problem
with exact gamma 7/5, followed through the complete LeanExe-generated WASM
calculation.  Each completed numerical claim must describe decoded output
from the exact binary, including the effect of rounding and rejection.

On 2026-09-14 the user authorized implementation of this detailed plan,
including outward-rounded speed bounds and the common-factor positivity
limiter.  These choices are approved for the new numerical implementation.

## Reviewed claims and existing evidence

The [Euler article](https://lanyon.ai/research/euler-equations/) and its
[2D proof source](https://github.com/lanyonai/CompressibleEuler/blob/a736aa5f8b17efd225c4692404e2442361d06729/proofs/compressible_euler_2d.lean)
define the comparison.  The GitHub API confirmed that upstream main still
names this revision on 2026-09-14.  The proof source covers hyperbolicity,
speed estimates, zero physical diffusion, wave consistency and state-jump
decomposition, flux conservation, and reconstruction consistency, linearity,
and reflection symmetry.  The article reports positive numerical examples
and discusses entropy behavior.  It describes Roe development as later work
and identifies the cylinder boundary representation as unverified.

| Claim | Present evidence | Completion target |
|---|---|---|
| Physical flux derivative and complete real eigenbasis | The 2D directional theorem and exact-binary connection pass. | Retain these results and add the sharp characteristic-speed bound. |
| Left eigenvectors | The right eigenvector matrix is invertible. | Check its inverse, the left eigenrelation, and the decomposition identities used by subsequent mathematics. |
| Executable speed bound | The present quantitative theorem gives velocity plus half the sound speed. | Bound every physical left/right characteristic speed by the selected decoded speed. |
| Wave consistency and state jump | The production solver evaluates the Rusanov flux. | Prove its two-wave representation, zero waves for equal states, and sum equal to the state jump. |
| Flux jump and conservation | Fixed 1D balance certificates and local 2D error bounds exist. | Prove the real flux-jump identity, local rounding residuals, and grid/time boundary-flux balance. |
| Reconstruction | The production solver uses cell averages as face states. | Prove minmod constants, componentwise linear profiles, and reflection symmetry, then connect a positivity-preserving reconstruction to WASM. |
| Positive density and pressure | Accepted states, sweep intermediates, and terminal arrays are safe. | Preserve this property through reconstructed faces, corrected speeds, and the complete revised solver. |

Universal status-zero completion and convergence to a continuous entropy
solution remain separate mathematical questions.  Each new theorem will
state its domain.  The proof inventory will distinguish a property of the
real scheme, a conditional numerical estimate, and a property established
for every accepted execution.

## 1. Characteristic speeds and the existing binary

- [x] Prove max(|u-c|, |u+c|) = |u|+c for c >= 0 and characterize a bound on all four eigenvalues.
- [x] Apply the result to the directional eigenvalues in the existing hyperbolicity theorem.
- [x] Prove the inverse eigenvector identities, left eigenrelation, and reconstruction of a characteristic decomposition.
- [x] Check the existing executable speed against that target and preserve a Lean-checked counterexample.
- [x] Connect the counterexample to function 22 of the exact frozen WASM binary.
- [x] Record the conditions in the existing interface error bound and distinguish them from accepted-state safety.

For density 1, both momenta 0, and total energy 1, Lean kernel evaluation
checks accepted status and speed word `3fe7f254dab9cc3a`.  Its decoded
value is strictly below the exact sound speed sqrt(14/25).  The source
certificate concerns an admissible helper input.  Reachability of that
input from the production quadrants is a separate question.  The checked
`SpeedCounterexample.artifact_underestimate` theorem also establishes
the result for function 22 after decoding and validating the frozen bytes.

The existing `Numerics.interface_reference_error` bounds each flux
component by 304 * 2^-52 * M^5.  Its `Numerics.StateBounds M` premise
requires finite input words, 1/M <= rho <= M, absolute momenta and energy
at most M, a true state guard, and internal energy at least
24 * 2^-52 * M^3, with 1 <= M <= 2^100.  Accepted side execution proves
finiteness, the state guard, and positive real density and internal energy.
The quantitative M bounds and margin are additional assumptions.  The
accepted-state theorem returns `Euler2DConservative.Guard.StateBounds`,
a distinct predicate that has no M parameter.  A complete trace theorem
must prove any quantitative premise it uses or state that premise explicitly.

## 2. Corrected numerical speed and CFL

The proposed computation carries outward bounds through velocity, kinetic
energy, pressure, and sound speed.  A pressure upper bound uses a lower
kinetic-energy bound.  The final speed bounds the absolute exact normal
velocity plus the exact sound speed.  The implementation must account for
rounded constants, signed zero, subnormal results, and finite-range exits.
The user approved this arithmetic design for the executable changes.

- [ ] Specify outward arithmetic using the existing integer-bit interface and IEEE64 model.
- [x] Implement adjacent-value operations and prove their exact spacing and ordering for both signs.
- [ ] Prove endpoint enclosure for the required operations, with explicit overflow and invalid-input returns.
- [ ] Prove the side-speed bound under conditions established by acceptance.
- [ ] Prove that interface and grid maxima retain both directional bounds.
- [ ] Prove an exact-real CFL inequality from the executable timestep test, including multiplication and division rounding.
- [ ] Compile the revised numerical helper and inspect compiler annotations and emitted operations.
- [ ] Prove its exact-WASM execution, rejection behavior, and speed theorem.

The original frozen binary and production data remain preserved.  A changed
speed produces a new binary and a separately identified numerical recurrence.

## 3. Wave and flux identities

For states L and R, physical directional flux F, and a positive interface
speed a, define dU = R-L and dF = F(R)-F(L).  The mathematical waves are
Wminus = (dU-dF/a)/2 and Wplus = (dU+dF/a)/2, with speeds -a and a.

- [x] Prove Wminus+Wplus = dU and -a*Wminus+a*Wplus = dF.
- [x] Prove zero waves and numerical-flux consistency for identical states.
- [x] Prove equivalence between these fluctuations and the real Rusanov reference formula.
- [x] Prove directional flux reversal and connect the physical flux in the numerical-error modules to the differentiated flux.
- [ ] Derive exact residual equations for the computed interface flux and cell update, reusing existing componentwise bounds.
- [ ] Establish finite, stated bounds for every residual claimed by the accepted-execution theorem.

The mathematical wave representation explains the flux that the solver
computes.  The execution theorem continues to follow that flux computation.

## 4. Grid and time conservation

- [x] Prove generic sweep telescoping and time accumulation with explicit residuals.
- [ ] Instantiate cancellation of shared internal face fluxes in each solver sweep.
- [ ] Express total mass, both momenta, and energy changes as boundary fluxes plus the sum of local rounding residuals.
- [ ] Compose x and y sweeps using their respective intermediate states.
- [ ] Compose accepted timesteps with their computed durations and boundary states.
- [ ] Derive the final-array balance from the complete solver trace and attach it to the exact binary theorem.

Open boundaries contribute physical flux.  Rejected trials preserve the
last accepted grid, and their discarded values contribute no accepted-step
balance.  A useful error theorem must bound the residuals using established
conditions or retain their exact recorded values.

## 5. Reconstruction and positivity

First prove scalar minmod properties, then lift them componentwise to
the four conserved fields.  Use a separate slope for each component when
stating preservation of a linear profile.  Define face states U +/- D/2.

- [x] Prove preservation of constants, linear profiles, reflection symmetry, and cell-average symmetry for the real reconstruction.
- [x] Prove component bounds and retain an exact counterexample to unconditional pressure preservation.
- [x] Review a common-factor positivity limiter for both faces.  The approved limiter reduces the complete slope together and has an explicit zero-slope terminal case.
- [ ] Prove admissibility of both returned faces and preservation of the unrestricted reconstruction when its checks pass.
- [ ] State linear-profile preservation with the precise limiter-inactive and representability conditions required by execution.
- [ ] Define and prove the rounded reconstruction, including branch selection, finite intermediate results, and rounding residuals.
- [ ] Prove the generated WASM helper and its complete source-model correspondence.

The positivity check belongs at reconstructed faces before flux evaluation.
Reducing the timestep alone leaves those face states unchanged.  The user
approved the limiter design and its conditional reconstruction properties
for integration.

The checked counterexample has conserved states [1,0,0,1/8],
[1,1,0,5/8], and [1,2,0,17/8].  Each has internal energy 1/8.
The center's reconstructed right face is [1,3/2,0,7/8], with internal
energy -1/4 and pressure -1/10.  Componentwise bounds therefore do not
establish admissibility of the reconstructed state.

## 6. Complete revised solver and data

- [ ] Integrate accepted face states, certified speeds, and the checked CFL rule into the existing directional traversal.
- [ ] Reprove allocation, ownership, termination, complete failure behavior, and the full memory bound for the changed call graph.
- [ ] Reuse compiler-described scalar and array regions, existing ProofKit lemmas, and relevant LTG entries.  Inspect generated equalities before repeating local instruction proofs.
- [ ] Freeze the new artifact and prove complete decoding, validation, Talos translation, and all registered behavior theorems.
- [ ] Check the independent package and all public/transitive axiom audits.
- [ ] Run the new 192-grid calculation, require status zero at time 0.8, and produce density and pressure figures.
- [ ] Run the new 800-grid calculation under the same acceptance conditions and produce its figures.
- [ ] Update the short article with the claim-to-theorem table, explicit conditions, rounding statements, and comparison with the preserved data.

## Gates and work order

Begin with the speed characterization and counterexample, then the real
wave/flux and reconstruction lemmas that are independent of numerical design.
Arithmetic and limiter choices are approved.  Complete
local IEEE64 proofs before generated execution composition.  Complete the
exact-binary gate before either production calculation.

All Lean and Lake work uses standard local `tools/leanrun`, one process and
one thread.  Small proof modules receive focused three-minute checks and
standard-axiom audits.  An unchanged target is never retried after a timeout.
The final focused source/artifact gates follow the changed boundaries.
Existing aggregate CLOB and cold-release work retain their recorded deferred
status.  Each checkpoint records proof structure, reused support, compiler
evidence, failures, and timings in the journal, then commits and publishes
the reviewed paths.  No new dependency is planned.
