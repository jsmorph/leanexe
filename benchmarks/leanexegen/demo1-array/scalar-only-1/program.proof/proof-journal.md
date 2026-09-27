# Proof Journal

The initial resource-limited build failed in `Behavior.lean` at the starter's intended continuation.  The starter has already decomposed `RuntimeReady` into the allocator globals, input representation, length read, address bound, input address normalization, and memory/page bounds.  The remaining goal is the exact `TerminatesWith` execution theorem for exported function 2.

The first declaration query confirmed the zero and one equations, product theorem, membership characterization, and factorization API for `Nat.primeFactorsList`.  Guessed cons-equation names do not exist.  I will express one-factor removal through the checked uniqueness or factorization API instead of depending on a recursive equation name.

`Nat.primeFactorsList_unique` gives the needed one-factor removal result: the list formed by a prime divisor and the quotient's prime factors has the right product and contains only primes, so it is a permutation of the original factor list.  The scalar invariant can therefore track `count + primeFactorsList.length` while trial division updates the current number.

The initial arithmetic lemmas exposed four local proof errors: one permutation equation needed symmetry, cons membership needed explicit simplification, a proper divisor needed a separate positivity argument before `omega`, and the parity proof for the next candidate used the wrong divisibility identity.  None changes the invariant or proof boundary.

The number-theoretic support now checks.  `prime_of_trial` proves that the current remainder is prime once its quotient by the candidate falls below the candidate, and `no_factor_next` preserves the excluded-divisor range when the loop advances from 2 to 3 or between odd candidates.

The first function-entry diagnostic confirmed that `TerminatesWith` supplies multi-value WebAssembly arguments in operand-stack order: the four scalar arguments must be written as `[count, candidate, remaining, fuel]`, which the entry rule reverses into local-parameter order.  The store introduced by `wp_entry` remains unchanged through this scalar function.

The loop rule requires a decrease on the completion iteration, where the artifact sets the done flag without decrementing fuel.  I changed the measure from fuel alone to `2 * fuel + running-bit`; a factor or candidate-advance step decreases fuel, while a completion step clears the running bit.

All three scalar body cases are now present in the proof.  The latest check found only representation-level issues before those obligations: UInt64 order needs explicit `toNat` conversion, and the epilogue should use the ordinary `wp_run` tactic once its literal frame and branch Boolean are exposed.

The complete scalar function now elaborates through its loop body.  Remaining failures concern quotient abbreviation rewriting, explicit Boolean facts for the nondivisible evaluator branch, and presenting the decreasing measure without asking `omega` to process unrelated UInt64 division hypotheses.

Function 0 now checks completely, including fuel exhaustion, completion, factor removal, and candidate advance.  Its theorem preserves the store and returns the encoded length of `primeFactorsList`; function 1 can therefore split at `x ≤ 1` and use the direct-call rule in its other branch.

Function 1 also reaches its intended composition: zero and one use the empty factor-list equations, while larger inputs call function 0 and preserve the store.  I am now exposing function 2's singleton-length dispatch before applying the complete fixed-array singleton result theorem.

Function 1 now checks.  Function 2's header load also checks with the prepared array facts and leaves the compiler's normalized singleton comparison, represented by the expected sequence of Boolean `iff` nodes.

The next check reduced the singleton branch to the indexed element loader and the other branch to its return.  The loader exposes its memory bound before the checked branch, so the proof now supplies `generatedLengthBound` and normalizes the loaded length through `lengthRead`.  The non-singleton Boolean normalization needed a proof that zero is not nonzero, rather than the equivalent equality passed to `if_neg`.

The checked non-singleton branch has reached its final representation obligation.  A small semantic lemma now reduces `expected input` to `input` from the failed size-one test, allowing the original array representation to discharge that branch.  I also isolated the size-one array identity needed to relate the loaded first element to the formal singleton result in the allocating branch.

The semantic helper lemmas elaborate, but the prior edit placed the non-singleton representation proof before the wrapper's last conditional.  Moving it after the last negative branch preserves the exact Program structure.  The singleton loader now enters its positive checked branch using the representation's generated payload bound and read equation.

The non-singleton branch now checks completely.  The checked payload load also reduces to `input[0]`, leaving the direct call to function 1 with the original store.  The proof composes that call with `func1_spec` before approaching the capacity normalization and singleton allocator suffix.

The scalar call composition checks and leaves the computed factor count in combined local 2.  The capacity expression reduces to 16, and its negative normalization branch begins the exact `FixedArrayAllocator.region 1 ++ FixedArraySingleton.resultSuffix` sequence.  The proof now applies `region_result_spec` with the RuntimeReady memory and global facts and relates its singleton array to the formal expected value.

Two reduction details blocked the first region application.  Rewriting the complete array inside a dependent `getElem` expression produced an ill-typed rewrite motive, so the expected-value proof now rewrites only the nondependent `toList` scrutinee.  The empty capacity-normalization branch also requires `wp_nil` before the continuation exposes the allocator region.

The region equality now succeeds after the empty branch reduction.  Lean still retained an unreduced continuation frame when the theorem inferred that frame, which prevented closed proofs of its length and local-index premises.  The proof now names the exact one-parameter, fourteen-local allocator-entry frame and supplies each structural premise by reduction.

The complete `ArtifactResult` target now builds.  The final proof uses the scalar loop invariant for multiplicity counting, preserves the input representation on every non-singleton length, and applies the checked singleton allocator theorem after the function 1 call.  I will now run the prescribed import check and target rebuild once more without changing `Behavior.lean` afterward.
