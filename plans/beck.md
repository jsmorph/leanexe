# Beck–Fiala partitioner

## Scope and completion

Implement two groups with unweighted category counts.  The first capacity target is six jobs and eight categories.  Each supported input must have a universal source theorem and an exact-binary execution theorem before the example is described as complete.  Capacity increases follow the same gate.

The executable starts at zero, preserves every category with more than the maximum overlap in undecided jobs, selects a deterministic kernel direction, and moves to a boundary.  Source proofs must establish progress, termination, the discrepancy bound, exact arithmetic, and sufficient helper fuel.  The binary theorem must establish termination, agreement, and sufficient allocation under stated caller assumptions.

## Interface

The runner accepts `{"categories": m, "jobs": [[category IDs], ...]}`.  IDs are integers in `[0,m)`.  Membership order has no semantic meaning.  Repeated membership within a job is invalid.  Separate categories may contain identical sets of jobs.

The WASM entry accepts an `Array UInt64` containing `[n,m,k0,ids0...,k1,ids1...,...]`.  It checks counts, lengths, IDs, and duplicates.  Success returns `[0,t,group0,...]`, with groups zero and one and `t` computed from the input.  Empty jobs return `[0,0]`.  Zero-overlap jobs enter group one.  Invalid input returns `[1]`, and capacity overflow returns `[2]`.  Internal arithmetic or fuel failure must be unreachable on supported inputs.

Use integer cofactor directions and signed `UInt64` numerators with a shared denominator.  Scan rows, columns, and boundary candidates in ascending index order.  The capacity target becomes a published guarantee only after the arithmetic proof passes.

## Work and evidence

- [x] Create `beck` from local `main` at `8dbb8e8a` in a separate worktree.
- [x] Read repository instructions, compiler and verification documentation, and the drone source and final theorem statements.
- [x] Compile and run the entry and native comparison.
- [x] Prove exact arithmetic under the incidence assumptions.
- [x] Prove preserving-direction construction and rounding progress.
- [x] Prove discrepancy and sufficient rounding fuel for supported incidence inputs.
- [x] Prove input validation establishes the incidence assumptions and exact maximum row count.
- [x] Prove complete correspondence between accepted inputs and the membership encoding.
- [x] Prove allocation and WASM resource bounds.
- [x] Check the identified binary and its independent proof package.
- [x] Add exhaustive small tests, edge cases, and an overlapping demonstration.
- [ ] Increase capacity with the complete theorem and execution tests preserved.

Repository references: [source language and ABI](../docs/spec.md), [development checks](../DEVELOPING.md), [verification procedure](../docs/verifying.md), and [artifact format](../docs/artifact-format.md).  The mathematical reference is Beck and Fiala, [“Integer-making” theorems](https://doi.org/10.1016/0166-218X(81)90022-6), *Discrete Applied Mathematics* 3 (1981), 1–8.

## Approved arithmetic change

The user approved replacing Gaussian elimination on separate reduced fractions with integer cofactor directions and one denominator shared by all coordinates.  With six jobs, a direction can use minors of order at most five.  The elementary determinant bound is `5! = 120`, so a shared denominator grows by at most 120 per rounding round.  These bounds replace the need to bound intermediate rational Gaussian elimination and separately reduced coordinate denominators.  The cost is additional small-determinant computation.

## Approved capacity generalization

The user approved a theorem quantified over job count, category count, and overlap, with arithmetic storage and allocation bounds derived from those dimensions.  The implementation will construct directions by exact elimination and use multiword integer arithmetic.  The executable must check a proved resource condition and return capacity rejection when it fails.  Every accepted valid input must terminate with the discrepancy guarantee in the exact-binary theorem.  Capacity will follow from the resource analysis and performance measurements.

- [x] Generalize rounding and arithmetic lemmas to symbolic bounds.
- [x] Compile and exercise multiword operations through the new partitioner entry as they are introduced.
- [ ] Implement and prove exact elimination, preserving directions, and rounding.
- [ ] Derive indexing, helper termination, and allocation bounds from input dimensions.
- [ ] Check the replacement binary's universal execution theorem and independent package.
- [ ] Measure larger overlapping cases and update the browser demo to the verified replacement.

The six-job artifact and its proofs remain a checked reference during this work.  The earlier 256-job, 64-category suggestion had no derived resource bound or performance evidence and is superseded by this plan.

The replacement entry is `LeanExe.Examples.BeckExact.compute`.  It uses base-2^32 integer limbs and fraction-free elimination.  The current 609 native/WASM comparisons pass, including a 64-job, 16-category input with overlap three.  That input exposed repeated evaluation of nested loops in the compiler.  Materializing the monadic loop body before projecting its status and result removed the observed memory failure.  The full ownership-report test passes.  The replacement's arithmetic proofs cover limb operations, normalization, addition, and subtraction.  Its complete source and artifact theorems remain open.
