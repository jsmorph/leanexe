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

- [x] Specify outward arithmetic using the existing integer-bit interface and IEEE64 model.
- [x] Implement adjacent-value operations and prove their exact spacing and ordering for both signs.
- [x] Prove endpoint enclosure for the required operations, with explicit overflow and invalid-input returns.
- [x] Prove the side-speed bound under conditions established by acceptance.
- [x] Prove that interface and grid maxima retain both directional bounds at source level.
- [x] Prove interface maximum selection and mesh CFL helpers in generated WASM.
- [x] Close the interface maximum helper over its exact binary bytes.
- [x] Close the mesh CFL helper over its exact binary bytes.
- [x] Prove grid-fold execution with exact output, termination, store preservation, and both directional speed bounds.
- [x] Close the grid-fold helper over its exact binary bytes.
- [x] Combine the certified speed with physical side-flux arithmetic and prove source safety and residual bounds.
- [x] Compose both revised sides into the scalar interface flux and prove source safety and residual bounds.
- [x] Prove the revised side/interface's generated execution, rejection behavior, store preservation, and numerical bounds.
- [x] Prove the revised interface's exact-byte behavior.
- [x] Compose the revised interfaces with conservative advancement and prove source safety, physical-reference error bounds, and exact-real face CFL bounds.
- [x] Prove the scalar face-step's generated execution, complete rejection behavior, and numerical specifications.
- [ ] Close the scalar face-step over its exact binary bytes.
- [ ] Compose maximum/CFL checks with the revised solver stages.
- [x] Prove an exact-real CFL inequality from the executable timestep test, including multiplication and division rounding.
- [x] Compile the revised numerical helper and inspect compiler annotations and emitted operations.
- [x] Prove its exact-WASM execution, rejection behavior, and speed theorem.

Finite integer packing, local half-step error, and signed neighboring-value
enclosure now pass focused checks for all five arithmetic operations.
The checked helpers either return the rejected status/value record or a
finite directed bound with valid inputs.  Boundary certificates cover
signed zero, underflow, invalid inputs, and finite-range exits.  LeanExe
compiles the checked division helper to scalar, allocation-free WASM with
direct-call annotations.  The separate Euler speed helper now has a complete
rejection-or-accepted source theorem.  Acceptance establishes a finite positive
bound on all four exact characteristic speeds, using the existing physical
state guard without an extra quantitative headroom premise.  Its compiler
diagnostic has 35 reachable scalar functions and 102 direct-call annotations.
The checked ratio bounds both decoded dt/spacing and its returned ratio
times alpha.  A downward spacing bound connects acceptance to exact
unit-domain spacing and proves dt*n*alpha at most one half.  The ratio
and mesh helpers have complete rejection behavior and checked boundary
cases.  The generated speed module now has complete terminating execution,
exact rejection behavior, and a public real characteristic-speed bound.
The focused source-driven and independent exact-byte gates pass.  The
4,936-byte speed artifact has complete decoding, validation, translation,
and explicit execution and physical-speed theorems.  Accepted interface
selection now bounds both states.  The grid fold bounds every cell in both
directions, including finite rejection behavior and the empty-grid zero
seed.  Its composition with the mesh test gives dt*n*abs(lambda_i) at most
one half for every member cell.  The interface helper compiles to 5,260 bytes
with 106 direct-call annotations.  Its generated-WASM specification proves
exact output, rejection, store preservation, and the positive finite bound
for both interface states.  The mesh CFL specification covers every raw
UInt64 grid-size input, including rejection outside 2..800.  Accepted output
bounds dt*n from above and its product with alpha by one half.  Its
integer-to-binary64 conversion reuses the existing execution theorem through
checked function renaming, extended to cover i64 shift and OR.  Both public
specifications pass focused checks with standard axioms.  The maximum's
5,260-byte package now has complete decoding, validation, translation,
exact-output, and physical-speed theorems.  Its independent package check
passes with standard axioms.  The 2,557-byte CFL package also has complete
decoding, validation, translation, exact-output, and numerical behavior
proofs.  Its independent check passes with standard axioms.  The generated
grid fold now proves terminating exact output and complete store preservation
for every represented grid.  Acceptance bounds every member's characteristic
speeds in both directions.  The proof uses the compiler-generated fold-region
equality and shared fold-prefix and memory-access lemmas.  Its source gate
passes.  Complete decoding, validation, exact output, and physical-speed
bounds now hold for the 5,728-byte grid artifact, with standard-axiom audits
and an accepted independent package check.  Timestep controller integration
remains open.

The separate revised side computation now returns the certified outward
speed with positive pressure and finite physical-flux intermediates.
Its source theorem bounds all four characteristic speeds and each physical
flux error.  Both the preserved and revised computations use one shared
arithmetic theorem with physical-state and finite-intermediate premises.
The preserved side's exact-byte residual theorem still passes.  The revised
interface now has complete source and generated-WASM exact-output, safety,
and residual proofs.  Function-region transport reuses the speed and
Rusanov component code, while the new proofs follow both side calls and
all four component calls.  The eight-input, six-result module has 7,175
bytes and no reachable memory operations.  Its exact-byte package now
has complete decoding, validation, translation, exact-output, safety,
and residual theorems.  Independent verification and all standard-axiom
audits pass.  The decoder proof reuses checked byte lookup and explicit
instruction-sequence boundaries.  All body and section targets passed
on their first attempts.

The scalar face-step source now advances a center average using the two
certified interfaces between four supplied face states.  Acceptance proves
physical output-state bounds and positive pressure, bounds all four faces'
characteristic speeds, and bounds each characteristic Courant number by
one half.  The mesh-ratio theorem transfers the bound to exact dt*n on the
unit domain.  The four-component update certificate and physical-reference
error bound derive their premises from acceptance.  A shared conservative
reference lemma adds the two flux errors to the update residual.  These
source proofs pass with standard axioms.  The generated-WASM entry now
has complete termination, exact output, store preservation, accepted safety,
characteristic-CFL, and physical-reference residual proofs.  Its 9,077-byte
module uses 50 reachable scalar functions and 168 direct-call annotations.
The advancement proof takes 57 seconds, the entry composition 4.3 seconds,
and the public specification 1.7 seconds.  The exact-byte package and
complete solver integration remain open.

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
- [x] Prove signed operation-error certificates and bounds for accepted conservative updates and Rusanov components, including exact-byte execution.
- [x] Bound physical side-flux error from accepted status alone, including the rounded pressure coefficient, and transfer the bound to exact bytes.
- [x] Compose a scalar Rusanov arithmetic bound with explicit errors in its two side fluxes.
- [x] Instantiate the physical reference bound for all four components of the accepted interface call and connect it to exact bytes.
- [x] Derive all four conservative-update certificates and balance bounds from accepted complete-cell execution, including exact bytes.
- [x] Establish conservative-update residual bounds throughout the complete accepted solver trace.

The mathematical wave representation explains the flux that the solver
computes.  The execution theorem continues to follow that flux computation.

The new local bounds use neighboring-value rounding radii and derive finite
inputs and intermediates from accepted status.  The side-flux proof includes
the stored pressure coefficient's difference from exact 2/5.  It requires
no quantitative M bound or extra internal-energy margin.  Functions 22, 46,
and 58 of the preserved binary now carry physical-side, Rusanov-arithmetic,
and conservative-update residual theorems.  The scalar reference composition
adds one half of the sum of the two side-flux error bounds.
The four-component interface theorem now applies that bound to function 54.
The complete cell theorem transfers all four update certificates and balance
bounds through function 65.  Both exact-byte transfers pass standard-axiom
audits.

## 4. Grid and time conservation

- [x] Prove generic sweep telescoping and time accumulation with explicit residuals.
- [x] Instantiate a row of rounded updates with one shared flux sequence and bound its accumulated update residual under accepted status.
- [x] Prove equality of neighboring recomputed row fluxes and derive balance for accepted complete Euler-cell outputs.
- [x] Instantiate cancellation of shared internal face fluxes in each solver sweep.
- [x] Express total mass, both momenta, and energy changes as computed boundary fluxes plus the sum of local rounding residuals.
- [x] Compose x and y sweeps using their respective intermediate states.
- [x] Compose accepted timesteps with their computed ratios and boundary states.
- [x] Derive the final-grid balance from the complete solver trace and attach it to the exact binary theorem.
- [x] Express the area-weighted balance using duration-weighted physical boundary fluxes, including spacing, ratio, and boundary-flux rounding errors.

The source line, grid, two-sweep, and accepted-trace theorems pass focused
checks.  The complete solve_balance and artifact_solve_balance theorems
attach both computed-flux and physical-flux balances to the preserved
21,767-byte solver with its original termination, memory, exact-output,
and accepted-state guarantees.  The physical balance uses cell area
1/n squared and face-length/time factor dt/n.  It bounds errors from cell
updates, both endpoint flux evaluations, spacing division, and timestep
ratio division.  The y contribution uses the x-sweep result.  Its source
and exact-byte checks pass, including the strengthened independent package
check.  The balance covers each conserved component in the final
internal grid.  Serialized output continues to contain density and
pressure.  These statements will require the corresponding instantiation
for the revised reconstruction and outward-CFL solver.

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
- [x] Prove source-level admissibility of both returned faces and preservation of the unrestricted reconstruction when its checks pass.
- [x] State source-level linear-profile preservation with the precise limiter-inactive and representability conditions required by execution.
- [x] Define and prove the rounded reconstruction source, including branch selection, finite accepted intermediates, and rounding residuals.
- [x] Prove the generated WASM helper and its complete source-model correspondence.
- [x] Prove reconstruction decoding, validation, and behavior for the exact frozen bytes.
- [x] Prove that rounded halving is nonincreasing and every returned factor is finite and in [0, 1/2], including exact-byte execution.

The positivity check belongs at reconstructed faces before flux evaluation.
Reducing the timestep alone leaves those face states unchanged.  The user
approved the limiter design and its conditional reconstruction properties
for integration.

The checked source computes finite rounded differences and exact minmod
selection on their binary64 values.  It tests both faces, halves one common
factor after rejection, and returns the center state when the trial budget
is exhausted.  Acceptance proves both faces admissible.  The source proof
identifies the selected halving count, bounds every component's error against
the exact-real minmod slope, and bounds the face-average residual.  The
linear-profile theorem states exact subtraction, scaling, and face-operation
premises together with acceptance of the unrestricted candidate.  The
counterexample rejects factors 1/2 and 1/4 and accepts 1/8.  LeanExe emits a
5,619-byte registered artifact with a bounded loop and no reachable memory
operations.  Complete generated execution, termination, exact-word output,
safety, and accuracy specifications pass the source regeneration gate.
The exact-byte decoder, validator, execution transfer, and independent package
check pass for digest 0fd762b3c1596a995438259ea909dc30fc0eca4137c79d1d8cf6bbb3678ed6f9.
The production trial budget and stage integration remain open.

The shared halving theorem proves finite, nonnegative, nonincreasing output
for each factor step, including subnormal rounding and zero.  The source
iteration proof and selected-candidate certificate imply a returned factor
in [0, 1/2] for every input and budget.  The complete generated-WASM and
exact-byte factor theorems pass, along with the strengthened independent
package check.  These theorems retain the existing numerical computation.

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
