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
- [ ] Prove complete correspondence between accepted inputs and the membership encoding.
- [ ] Prove allocation and WASM resource bounds.
- [ ] Check the identified binary and its independent proof package.
- [x] Add exhaustive small tests, edge cases, and an overlapping demonstration.
- [ ] Increase capacity with the complete theorem and execution tests preserved.

Repository references: [source language and ABI](../docs/spec.md), [development checks](../DEVELOPING.md), [verification procedure](../docs/verifying.md), and [artifact format](../docs/artifact-format.md).  The mathematical reference is Beck and Fiala, [“Integer-making” theorems](https://doi.org/10.1016/0166-218X(81)90022-6), *Discrete Applied Mathematics* 3 (1981), 1–8.

## Approved arithmetic change

The user approved replacing Gaussian elimination on separate reduced fractions with integer cofactor directions and one denominator shared by all coordinates.  With six jobs, a direction can use minors of order at most five.  The elementary determinant bound is `5! = 120`, so a shared denominator grows by at most 120 per rounding round.  These bounds replace the need to bound intermediate rational Gaussian elimination and separately reduced coordinate denominators.  The cost is additional small-determinant computation.
