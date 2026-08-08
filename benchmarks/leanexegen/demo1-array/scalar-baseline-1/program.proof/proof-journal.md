# Proof Journal

The initial prescribed build failed before checking `Behavior.lean`.  Lake attempted to rebuild `Project.ProofKit.FixedArraySearch` in the read-only Project dependency and could not remove its existing `.ltar` artifact.  The starter imports several search modules that do not match this prime-factor-count artifact.  I will reduce the imports to the modules supported by the artifact structure, which should keep Lake from selecting the stale search target and expose the theorem goal.

The frozen program has three reachable functions.  Function 0 implements the factor-count loop, function 1 handles the zero-and-one case and calls function 0, and exported function 2 checks for a singleton input, loads its element, calls function 1, and constructs the singleton result through the standard fourteen-local allocator and singleton suffix.  I replaced the unrelated search imports with `Control` and `FixedArraySingleton`; `Array` remains for the ABI facts.

The next prescribed build reached `Behavior.lean` and exposed the starter's intended goal: the public `TerminatesWith` postcondition after the `RuntimeReady` decomposition.  The named input length, input-bound, allocator-global, memory-fit, and page facts are all present.  The operational failure is resolved because the smaller import set no longer selects the stale search module.

I began the application proof with four facts about `Nat.primeFactorsList`.  Its length is bounded by the represented number; division by a trial divisor equal to the least prime factor removes one list element; a quotient below the current trial value proves primality; and advancing from two to three or from an odd value to the next odd value preserves the bound by `minFac`.  These facts state the semantic transitions needed by function 0 without mentioning WebAssembly locals.

The first check of those facts found three presentation errors: the positive-product fact had the strict form, rewriting the product equation also rewrote the argument of `primeFactorsList`, and the recursive length equation ended with commuted addition.  I changed the product proof to a directed calculation and closed the arithmetic forms explicitly.

The follow-up check accepted the directed calculations and requested an explicit conversion from the element lower bound `2 ≤ y` to the strict positivity premise of `List.prod_pos`.  I added that conversion locally.

That edit used a Unicode double-arrow token unsupported by this Lean parser.  The diagnostic was syntactic; I replaced it with the ordinary lambda arrow.

All application lemmas now compile.  I represented only the four changing parameters, result local, done local, local-list length, and operand stack in `FactorFrame`; the fourteen scratch locals remain abstract because every scratch read follows a write in the same iteration.  `FactorFacts` carries the factor-count equation, trial-divisor facts, remaining-number bound, fuel inequality, and completed-result equation.  The loop measure is twice the fuel plus one while the done flag is zero, which decreases both when fuel falls and when an iteration sets the done flag.

The first loop check exposed the interpreter's top-first argument convention: `TerminatesWith` reverses the supplied four-value list when it builds the callee frame.  I changed function 0's public argument list to `[count, p, n, fuel]`, which yields generated parameters `[fuel, n, p, count]`.  I also replaced reductions of `UInt64.toNat` literals with proof terms and began the loop step by unpacking its abstract frame.

The frame now initializes in the intended parameter order.  The remaining initialization diagnostics were reflexive arithmetic and an impossible zero-equals-one premise.  The local symbolic-execution macro must be opened from `Project.Common`; namespace qualification is not valid tactic syntax for this macro.

`Project.Common` is not imported by the selected proof-kit modules, and the allowed import list does not include it.  I retained the smaller imports and defined a local symbolic-execution macro with the same checked `wp_simp` and local-frame reductions needed for this sixteen-local loop.

The local macro now reaches the first structured conditional.  I split the fuel-zero exit, derived `n ≤ 1` from `n + 2 ≤ fuel + p`, `p ≤ minFac n`, and `minFac n ≤ n`, and split the Boolean done flag before executing the block exit and result epilogue.

The epilogue reduction needed proof-carrying local reads rather than optional reads.  I now convert the result and done `getElem?` facts once.  In the unfinished branch, `n ≤ 1` makes the remaining factor list empty, so the factor-count equation identifies `count` with the expected result; in the finished branch, `doneResult` already identifies the result local.

The fuel-zero epilogue now reduces to one missing projection of the factor-count equation, which I named explicitly.  For nonzero fuel, I split the done flag first.  A set done flag exits through the same proved epilogue; an unset flag reaches the application branch beginning with the `n ≤ 1` test.

The fuel-zero and already-completed paths now compile.  In the active path, I split the represented comparison `n ≤ 1`; its true branch derives the same count equation as the exhausted-fuel path, selects the generated completion arm, and reaches the loop-invariant reconstruction goal.

I reconstructed the completion invariant with the result local and done flag updated and proved the one-bit decrease in the loop measure.  The `n > 1` branch now selects the generated negative arm, proves the trial divisor nonzero from `2 ≤ p`, and reaches the quotient-versus-divisor comparison after the checked division sequence.

The `n ≤ 1` completion branch compiles.  I split the quotient comparison over `toNat`.  When `n / p < p`, the trial-divisor bound proves `n` prime, so the remaining factor-list length is one and the generated `count + 1` equals the expected total without wrapping.  That branch now reconstructs the completed invariant and decreases the done-bit measure; the other branch reaches the remainder computation.

The no-wrap proof for the primality completion now rewrites the factor-count equation with the proved one-element length before reducing `UInt64` addition.  In the continuing quotient branch, I selected the nonzero-divisor remainder arm and split divisibility by the exact `toNat` remainder equation.

The generated remainder predicate passes through two Boolean-normalization conditionals before selecting division or trial advance.  I followed both exact paths: a zero remainder reaches the division update after its checked divisor branch, while a nonzero remainder reaches the trial-advance program.

For division, the zero remainder supplies `p ∣ n`.  The least-factor invariant makes the factor-list length drop by one; divisors of `n / p` remain divisors of `n`, preserving the lower bound on its next least factor.  I derived no-wrap equations for `count + 1` and `fuel - 1`, preserved the fuel inequality using `n / p < n`, and reconstructed the running invariant.

The exact check found four local omissions in that reconstruction.  I rewrote the saved factor-count equation with the division step before deriving the increment bound, reused the proof-carrying reads for locals zero and one, and used the positive-fuel fact to close the measure decrease after simplification.  These changes preserve the invariant chosen for the loop rather than changing its statement to accommodate the generated frame.

The next check showed that `Nat.div_lt_self` needed the named `2 ≤ p` projection and that the updated scratch-local list required simplification before applying the original optional reads.  I supplied both facts.  The nonzero-remainder path now splits the generated `p = 2` decision, which will expose the remaining Boolean normalization and the concrete next-candidate frame in each arm.

The diagnostic revealed one omitted normalization conditional before the trial-divisor decision; the attempted `p = 2` split had therefore selected the division arm.  I added that exact outer conditional, followed all three generated conditionals for the divisor decision, and reconstructed both next states.  The two case proofs use `next_trial_le`: two advances to three, while an odd divisor advances by two after proving that the machine addition does not wrap.

Both trial-advance frames and their measure decreases compile.  The remaining function-zero goal is the fuel inequality in the two-to-three case, where Lean retained `UInt64.toNat 3` as an opaque arithmetic term.  I stated that goal in its reduced natural-number form so `omega` can combine it with the previous fuel bound.

Function 0 now compiles in full.  I added a function-one theorem that returns zero when the input is at most one and invokes the proved loop theorem otherwise.  Its callee postcondition preserves the complete store, which is the property the exported wrapper needs before allocating the result array.

Function 1 also compiles in full.  I split the exported wrapper on the represented array size.  The non-singleton branch returns the original pointer after relating the frozen `expected` match to `input`, while the singleton branch performs the checked first-element load, calls function 1, normalizes the fixed capacity to sixteen bytes, and hands the exact remaining instruction region to `FixedArraySingleton.region_result_spec`.

The first exported-wrapper check reached both semantic branches.  The generated element load uses the normalized `UInt32.ofNat` address supplied by `generatedElement`, so I retained that read alongside `firstElementRead_add`; the latter records the checked direct-address form.  The unchanged branch reduced to the unfolded array representation, which I now close from the original `UInt64Array.At` fact after the instruction proof returns the input pointer.

The unchanged branch now compiles.  The singleton branch reached the allocator-region change, but destructuring the callee equality with two reflexive patterns caused Lean to eliminate the name `initial`.  I now name the store equality and substitute the callee store, preserving `initial` for the fixed-array theorem's arguments.

The call-store substitution now works.  The subsequent symbolic reduction consumed the first three allocator instructions and stopped at the free-list global read, so the remaining program no longer matched the complete cataloged region.  I removed that reduction and apply the region theorem directly after selecting the false capacity-normalization arm.

After selecting the empty capacity-normalization branch, the goal still contains `wp` for that empty branch, whose continuation begins the allocator.  General symbolic reduction crosses both boundaries and consumes allocator instructions.  I reduce only `Wasm.wp_nil`, leaving the complete allocator region folded for the cataloged theorem.

The complete allocator and singleton-result theorem now applies and discharges every region obligation.  Its continuation contains the theorem's abstract `resultFrame`, whose combined local four holds the returned root.  I unfold that frame transformer only after the region proof, then reuse the theorem's `UInt64Array.At` fact for the formal postcondition.

The prescribed build completed successfully for both `Behavior` and `ArtifactResult`.  The exported theorem covers the unchanged-input branch for every non-singleton array and the allocated-result branch for every singleton array, including zero and one through function 1.  I will now run the required final build without changing the candidate afterward.
