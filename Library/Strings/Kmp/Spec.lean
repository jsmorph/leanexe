import Library.Bytes.Packed

/-! The specification of the occurrences of a pattern in a text, both byte strings held eight bytes
to a word as `Library.Bytes` states.  `OccursAt pat m txt n i` states that the `m` bytes of the
pattern equal the bytes `i` to `i + m - 1` of the text of `n` bytes, which requires `i + m ≤ n`, and
a byte past the end of an array reads as zero, as `byteAt` states.  `expected` is the list of these
positions in increasing order, an array of words, so the empty pattern gives every position from 0
to `n`, and a pattern longer than the text gives none.  The specification names the result and not
the method, and the program text shows the algorithm of Knuth, Morris, and Pratt in two scans of the
text, one that counts the occurrences and one that records them.  The theorems of the module read
"allocate only the table of lengths and the result" as a rise of the heap's `top` by at most those
two blocks, which `occurrences_bound` states and which allocations from free blocks below `top` do
not raise, and they read "a call stack that does not grow" as theorems with no call-depth premise,
which rests on the compiler's rule, which the verified compiler's manual states and no theorem
states, that it translates recognized tail recursion and loops into loops. -/

namespace Library.Strings.Kmp

open Library.Bytes

/-- The pattern of `m` bytes occurs in the text of `n` bytes at position `i`. -/
def OccursAt (pat : Array UInt64) (m : Nat) (txt : Array UInt64) (n i : Nat) : Prop :=
  i + m ≤ n ∧ ∀ k < m, byteAt txt (i + k) = byteAt pat k

instance (pat : Array UInt64) (m : Nat) (txt : Array UInt64) (n i : Nat) :
    Decidable (OccursAt pat m txt n i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The positions of the occurrences in increasing order. -/
def expected (pat : Array UInt64) (m : UInt64) (txt : Array UInt64) (n : UInt64) : Array UInt64 :=
  (((List.range (n.toNat + 1)).filter fun i => decide (OccursAt pat m.toNat txt n.toNat i)).map
    UInt64.ofNat).toArray

end Library.Strings.Kmp
