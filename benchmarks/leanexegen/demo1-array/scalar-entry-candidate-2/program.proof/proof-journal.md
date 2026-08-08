# Proof Journal

The initial required build failed in `Behavior.lean` after the deterministic starter rewrote function 2 to `AnnotationMatches.function_2_singleton_wrapper_0`.  The remaining goal is exactly `FixedArraySingletonWrapper.wrapperProgram_spec`'s whole-wrapper boundary: `wp module function_2_singleton_wrapper_0 (FixedArrayPairResult.publicPost (FormalSpec.expected input)) initial (FixedArraySingletonWrapper.entryFrame inputPtr) env`.  This confirms that the complete singleton-wrapper composition matches and that the proof should establish the store-preserving scalar callee instead of expanding the array loader or allocator.

The first declaration probe confirmed `Nat.primeFactorsList_zero`, `Nat.primeFactorsList_one`, `Nat.prod_primeFactorsList`, `Nat.mem_primeFactorsList`, and `Nat.primeFactorsList_unique`.  The guessed declarations `primeFactorsList_eq_cons`, `primeFactorsList_div`, and `primeFactorsList_mul` do not exist.  `primeFactorsList_unique` provides a direct way to prove the one-prime-factor length recurrence by constructing `p :: (n / p).primeFactorsList`, proving its product and primality, and taking lengths across the resulting permutation.

The second probe confirmed the useful minimum-factor API: `Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.minFac_pos`, `Nat.minFac_le`, and `Nat.minFac_sq_le_self`.  It also confirmed the exact `UInt64.toNat_div`, `UInt64.toNat_mod`, `UInt64.toNat_add`, and `UInt64.toNat_sub` equations.  The absent guesses `primeFactorsList_of_prime`, `primeFactorsList_cons`, and `eq_prime_of_minFac_eq` will not be used.

The third probe confirmed `Nat.minFac_le_of_dvd`, `Nat.Prime.eq_two_or_odd`, `Nat.div_dvd_of_dvd`, `Nat.mul_div_cancel'`, `Nat.div_lt_self`, `Nat.mod_add_div`, `UInt64.toNat_lt`, `UInt64.ofNat_toNat`, `UInt64.ofNat_add`, and `List.Perm.length_eq`.  There is no `UInt64.eq_iff_toNat_eq`; word equalities can instead use `UInt64.ofNat_toNat` after proving equality of `toNat` values, or use `UInt64.ofNat_add` for additions.

The first helper-lemma check reduced the remaining errors to two local proof details.  Membership in a cons list needs an explicit `List.mem_cons` simplification before case analysis, and the `UInt64` decrement equation needs an explicit rewrite of `(2^64 - 1 + n) % 2^64` as `(2^64 + (n - 1)) % 2^64`; `omega` did not normalize that modular expression by itself.

The prime-factor helper lemmas now compile.  The decrement proof reached only the bound `n - 1 < 2^64`; deriving it by transitivity from `n - 1 ≤ n` avoids numeral normalization inside `omega`.

Lean's simplifier normalizes `2^64` to its decimal numeral before applying `Nat.mod_eq_of_lt`, while the stored bound retained the power notation.  Normalizing the bound once before the final simplification should make the terms syntactically identical.

The number-theoretic helper lemmas and the `factorCore`, `factorInv`, and `factorMeasure` definitions compile.  `factorCore` tracks the remaining prime-factor count, candidate parity and minimum-factor bound, and enough fuel to prevent a premature exit.  `factorMeasure` reads the generated fuel and done locals, matching the compiler's administrative done-setting iteration.

The first `whileProgram_spec` application exposed the function-entry argument convention before reaching the loop.  `TerminatesWith` receives the operand stack in reverse parameter order for this four-parameter function, so function 0's public argument list must be `[count, candidate, remaining, fuel]`; the entry normalization then produces the generated state `[fuel, remaining, candidate, count]` required by `function_0_while_loop_0_entry_to_loop`.

The full scalar-loop application now reaches each semantic branch.  The remaining diagnostics identify normalization facts rather than invariant defects: checked division and remainder retain their zero-divisor alternatives until supplied `candidate ≠ 0`; generated evaluator equations need that fact to reduce `Option.map`; and the post-loop suffix needs another `wp_run` after each normalized conditional.  Two arithmetic obligations also need explicit rewrites for `UInt64.toNat 1`, the selected next-candidate branch, and the already-proved decrement equation.

After adding the zero-divisor fact, every body evaluator reduced except the nondivisible candidate update, whose final conditional requires a case split on the word equality `candidate = 2`.  The fuel proof becomes simpler when stated through the strict increase from `candidate` to `nextCandidate`, avoiding separate arithmetic for the two candidate forms.  The suffix diagnostics show that the first simplification reached a non-`wp` residual goal, so the additional unconditional `wp_run` calls were removed pending the exact residual.

All active loop branches now compile.  One indentation error made the nonzero-fuel branch look like a third subgoal of the zero-fuel tuple; dedenting that bullet restores the intended `by_cases` branch.  The completed-state suffix stops at its false post-loop conditional and needs one further `wp_run` after simplification.

The corrected branch structure leaves three control-normalization goals.  Both suffixes have reached `wp` at an `iff` with a known `i32` condition, so `Wasm.wp_iff_cons` with the explicit positive or negative rewrite handles them.  In the nondivisible `candidate = 2` evaluator branch, substituting the candidate into the quotient and remainder hypotheses before simplification removes the remaining checked conditionals.

The completed-state suffix now closes.  The zero-fuel suffix reaches its nested unsigned comparison and needs the word equality `remaining = 1` before selecting the false branch.  The nondivisible body evaluator rewrites `¬q < candidate` into `candidate ≤ q`; passing `not_lt_of_ge` explicitly lets the simplifier select the intended branch.

Both suffixes compile.  `UInt64`'s unsigned order does not use the generic `Preorder` instance expected by `not_lt_of_ge`, but the original `hQuotientWord` already has the exact negated comparison required by the evaluator.  Preserving that hypothesis while simplifying only the remainder fact avoids the incompatible order conversion.

Function 0 now compiles in full.  Function 1 reaches only final local-list reductions in both its small-value branch and its call branch; unfolding `func1Def` in those final simplifications exposes the six zero-initialized locals and their generated updates.

Function 1 now compiles and supplies the store-preserving scalar theorem required by `FixedArraySingletonWrapper.wrapperProgram_spec`.  The final composition will pass the existing memory, page, allocator-global, and input-representation facts directly, leaving only the two equations that characterize `FormalSpec.expected` on singleton and nonsingleton arrays.

The complete artifact build succeeded after applying `FixedArraySingletonWrapper.wrapperProgram_spec`.  The scalar premise is `func1_correct`; the invalid-length equation follows because a singleton `toList` would force `input.size = 1`; and the valid-length equation obtains the unique singleton element from `List.length_eq_one_iff`.  The proof imports only the frozen generated modules, `FixedArraySingletonWrapper`, and `Control`, and contains no `sorry` or added axiom.
