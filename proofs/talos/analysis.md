# CLOB Verification Analysis

This document records a critical review of the CLOB proof work as of 2026-07-18, when the `clob_depth` proof completed.  It states what the theorems establish, what remains trusted, where the premises limit applicability, and where the proofs carry engineering debt.  The [proof inventory](README.md) lists the completed theorems, and the [development journal](../../devnotes.md) records the dated build evidence.

## What the Theorems Establish

The exported theorems are input-generic total-correctness statements over the decoded WASM.  `ClobDepth.Func7.func7_terminates` states that for every represented order array meeting the premises, the depth export terminates and the two returned pointers own level arrays representing the exact source `depthSideL` folds for both sides, with the exact three allocator globals, page equality, and byte preservation below the initial heap top.  The other CLOB exports (`quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`) carry statements of the same shape, each quantified over represented inputs rather than fixed samples.

The semantic chain runs from instruction-level weakest preconditions through branch adapters to the source model: the level-update branches conclude in one `addLevelL` result, the per-side fold concludes in `depthSideL`, and the export concludes in `depthL`.  Source-level corollaries then apply: exact modular per-price aggregation and, under an explicit no-overflow bound, its natural-number interpretation.  Because the proof tool regenerates WASM, WAT, and the decoded model from the current source and compiler before Lean checks a specification, the compiler stays outside the trusted base.

## Trusted Base

The trusted components are Talos's WASM semantics, the WAT decoder, `wasm-tools print`, the Lean kernel, and the handwritten representation predicates.  The representation predicates deserve emphasis: `OrdersAt` and `LevelsAt` are the ABI claim.  They state the stride, field order, and header layout that the host is assumed to write and read.  If they mis-state the layout the host actually uses, every downstream theorem is about the wrong memory, and nothing inside Lean checks them against a real host.  Differential execution tests are the only evidence tying the predicates to observed behavior.

## Premise Limits

Two premises limit where the depth theorem applies.  The empty free-list premise requires global 1 to be zero at entry.  The generated depth code never releases, so emptiness is preserved internally, but a caller that runs depth after free-list-populating operations has no coverage from this theorem.

The heap budget premise is quadratic in the order count: `g0 + 224 + 2 * N * (56 + 16 * N)` bytes must fit in linear memory.  The quadratic term is a consequence of the compiled code, which bump-allocates a fresh level array on every matching order and frees none of the intermediates.  The stated budget is also coarser than the code requires: each call's capacity depends on the number of distinct prices seen so far, and the premise bounds that count by the order count.  A book with many orders at few prices needs far less memory than the premise demands.  Sharpening the budget would mean carrying a distinct-price count through the fold invariant.

The quantity fields are modular `UInt64` sums.  The natural-number reading holds only under the caller-supplied bound in `Spec.result_qtyAt_nat`; without it, the theorem does not rule out wrapped quantities.

## Generated-Code Observations

The proof documents behavior; it does not certify efficiency.  The verified depth code allocates two initial empty arrays of which the owner-side one is dead weight, reallocates the whole level array on every matching order, tests a loop-exit flag that can never fire, and keeps scratch locals live across regions, which forced those locals into the continuation frames of the proofs.  These are properties of the compiler output that the theorems faithfully carry.

## Proof-Engineering Observations

The found-price branch is largely a clone of the missing-price branch with one index, one length, or one local changed.  `FoundCopyInvariant`, `FoundStoreFacts`, and `FoundBranchFacts` are near-duplicates of their missing counterparts.  This follows the recorded rule against parameterizing shared theorems over generated locals, and the pieces that were cheap to share are shared: the empty free-list search theorem is frame-generic and serves both branches, the copy cursor frame and loop measure are reused, and the replacement store reuses `appendLevelStore` with the matched index as its slot.  A consolidation pass could plausibly merge the two branch-facts modules over a capacity-and-length parameter.

Two cosmetic debts remain.  `missingSearchProg_empty` serves both branches from a module still named `MissingSearch`.  `Func7.Result.global2` states the allocation counter as `g2 + 2 + m0 + 2 + m1` in unassociated form, which is exact but awkward for consumers.

## Fragility

The recurring maintenance cost in this codebase is closing simplification sets coupled to definition internals.  Both `ClobPostOnly` failures recorded by the previous aggregate run were exactly that: shared allocation definitions moved their header writes behind `fixedArrayHeaderMem`, and two `simpa only` lists stopped unfolding far enough.  Each repair was one definition added to a closing set.

The new fold modules carry the same exposure.  The loop body's frame-field proofs resolve twenty-element local-set chains by simplification under a raised step limit, and a change to the default simp set or to the `Locals` internals would break them in the same pattern.  Read-interface lemmas that state each definition's reads once would decouple the proofs from definition shape; that work belongs in the consolidation phase.

## Verification State

Every depth module and the focused depth gate pass under the resource policy with warnings failing the build.  The largest focused builds are the fold loop body at 10 seconds and the empty-allocation adapter at 9.1 seconds.  At the time of writing, the aggregate proof gate had regenerated all twenty artifacts and was still building the aggregate `Project` target, and the execution suite had not been rerun since the depth work; neither result is in evidence, and the plan's stable point cannot be claimed until both gates pass.  The four modules with recorded no-diagnostic timeouts (`Validate.Spec`, `SharedPair.Spec`, `LebU32.Iter`, `LebU32.NegIter`) remain to divide.
