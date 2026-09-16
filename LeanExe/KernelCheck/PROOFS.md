# Correctness evidence and next proof milestones

Executable milestones and formal proof coverage are different statuses.
M0.0–M0.10 have source tests and WASM/standard-Lean comparisons. They do **not**
establish overall checker soundness or correctness of the emitted WASM.
The user clarified the current priority: this is a PoC of what LeanExe can
execute; some source proofs may be deferred, and there is no WASM proof work
now. Keep useful small source proofs without blocking executable milestones.

## Proved source properties

Run from the repository root, under its normal authorized runner environment:

```sh
node test/kernel_proofs.js
```

This builds the proof modules with pinned Lean and audits the transitive axioms
of all ten public theorems. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. No `sorryAx`, additional axioms, or native-evaluation trust axiom
is admitted. These are universally quantified Lean proofs, not finite tests.

| Increment | Mathematical statement | Source theorem coverage |
|---|---|---|
| P0: sort typing | Accept iff the claimed natural level is the mathematical successor; reject iff the successor fits and the claim is wrong; overflow iff the successor does not fit | `SortProofs.lean`: three iff theorems, for every pair of UInt64 inputs |
| P1: concrete universes | Word-level max/imax map exactly to unbounded Nat max/imax; acceptance and rejection exactly characterize those specifications; unknown operations return unsupported | `UniverseProofs.lean`: seven public theorems, for every relevant UInt64 input |

The specifications use `UInt64.toNat`. In particular, sort correctness connects
machine addition to mathematical succession and proves that wraparound cannot
be accepted. `imaxNat` separately states the impredicative zero-codomain rule.

## Still unproved

| Boundary | Current evidence | Required theorem |
|---|---|---|
| Graph validation and internal reads | Malformed-input and boundary tests | Successful validation implies every accessed record/reference is in bounds and decodes to an admitted acyclic term; internal word address calculations do not wrap within the ABI size bound |
| Scope and shifting | Exact-result tests, including nested/shared binders | The graph operations refine binder-aware mathematical operations, including scope preservation and absence of capture |
| Substitution | Exact-result tests with lifting/index adjustment | Graph instantiation refines capture-avoiding binder removal; establish substitution and lifting laws needed by typing |
| Contexts and inference | Positive/negative typing tests | Admitted contexts are well formed; successful inference establishes declarative typing |
| Conversion | Beta, capture, negative, eta-inconclusive and exhaustion tests | A successful comparison establishes declarative definitional equality; reductions preserve typing |
| Checking | Closed proof and corrupt-proof tests | Acceptance implies the decoded proof has the decoded claimed type in the admitted context |
| Emitted WASM | Wasmtime execution and comparison with ordinary Lean | An exact-artifact behavior/refinement theorem connects the frozen binary to the proved source property |

A theorem about a separate model alone does not prove the implementation.
The graph-to-model refinement lemmas are required. Likewise, a theorem about
one successful fixture is not a theorem about every accepted input.

## Deferred source proof checkpoints

1. **P2a: node reads and validation entry checks.** State the representation/ABI
   size bound. Prove address arithmetic and root/record access safety for the
   actual helpers, plus the validator's root/alignment implications. Keep this
   first graph proof narrow; it does not establish the entire validator yet.
2. **P2b: full graph validation refinement.** Define the decoded admitted-form
   syntax and prove that every successful validation satisfies the backward
   reference and canonical-field invariants, including unreachable records.
3. **P3a: scope.** Prove the explicit traversal invariant at each occurrence;
   sharing does not imply identical binder depth. Connect success to the
   mathematical well-scoped predicate. Exhaustion is not rejection.
4. **P3b: shifting.** Prove the reconstruction-stack invariant, valid output
   IDs, exact index transformation, and bound-variable preservation. Relate
   overflow to the finite representation rather than to invalid Lean syntax.
5. **P4: substitution.** Prove capture avoidance and index decrement against
   the decoded model, then the substitution lemma needed by typing. Split the
   model law and implementation refinement into separate reviewable commits.
6. **P5: contexts, sorts and Pi formation.** Define declarative typing for the
   admitted concrete-universe fragment. Prove context lookup lifting and the
   inference-machine invariant, starting with Sort/bvar and then Pi.
7. **P6: lambda/application inference and checking.** Extend the invariant and
   prove success soundness for the existing executable fragment.
8. **P7: beta conversion.** Prove the reducer's stack invariant, typing
   preservation, and successful comparison soundness. Missing eta and proof
   irrelevance remain explicit incompleteness, not assumed rules.
Exact-WASM proofs are explicitly outside current work. The binary refinement
row above records an unproved boundary, not an active PoC task.

For each proof increment, retain the theorem statement, its source connection,
axiom audit, executable regression command, remaining gaps, and a commit/push.
Revise source structure when needed to support tractable invariants; recheck
its observable WASM behavior after each such change. Continue M0.10–M0.11 now; defer larger source obligations openly rather than
treating tested coverage as already proved.
