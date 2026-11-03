import Mathlib.Data.Nat.Prime.Defs

/-! The specification of the primes below a word `N`: the numbers `p < N` with `Nat.Prime p`,
Mathlib's primality, in increasing order, as words.  Every number below `N` is below `2^64`, so each
prime is its own word.  For `N` of 0, 1, and 2 the result is empty.  The specification names the
result and not the sieve, and the program text shows the method.  The theorems of the module read
"allocate only the flags and the result" as a call that raises the heap's `top` by at most the
blocks of `N` flags and of the result, which `primes_implements` and `primes_bound` state.  That
reading is weaker than the request's: allocations from free blocks below `top` do not raise it, and
no theorem states that the call releases the flags.  They read "a call stack that does not grow" as
theorems with no call-depth premise, which rests on the compiler's rule that the verified compiler's
manual states and no theorem states: the compiler translates recognized tail recursion and loops
into loops and gives every other recursive function and its callers a call depth, which their
theorems carry as a premise. -/

namespace Library.Numerics.Arithmetic.Sieve

def expected (N : UInt64) : Array UInt64 :=
  (((List.range N.toNat).filter fun p => decide (Nat.Prime p)).map UInt64.ofNat).toArray

end Library.Numerics.Arithmetic.Sieve
