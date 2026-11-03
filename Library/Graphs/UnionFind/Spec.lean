import Mathlib.Logic.Relation
import Mathlib.Order.Bounds.Defs

/-! The specification of equivalence classes.  The count `n` is a word, and `LeastLabels` takes its
value as a natural number.  Pair `t`, for `t` below the lengths of both arrays, relates `js[t]` and
`ks[t]` when both are below `n`, as unsigned numbers, and a pair with an element of `n` or more
relates nothing.  Words past the length of the shorter array belong to no pair.  `Equivalent` is
the least equivalence relation on the natural numbers that relates the elements of each pair, so
every element below `n` is equivalent to itself, and an element equivalent to a different element
is below `n`.  `LeastLabels n js ks r` states that `r` holds `n` words and that word `i` is the
least element of the class of `i`, which determines `r`.  The specification does not distinguish
Algorithm E from other methods that find the classes, such as one that links the roots the other
way, and the program text shows the method.  The theorems require room in memory for three arrays
of `n` words and say nothing for a larger `n`.  The specification reads "in place" as the update
of the array of parent links in its own block, which depends on the compiler's rule that the code
updates an owned array at its last use in place, a rule that the verified compiler's manual states
and no theorem states.  The theorems bound the rise of the heap's `top` by three arrays of `n`
words for any number of pairs, which the generated bound, charging every copy, supports.  It reads
"a call stack that does not grow" as theorems with no call-depth premise, which depends on another
rule of the manual that no theorem states: the compiler translates recognized tail recursion into
loops and gives every other recursive function and its callers a call depth, which their theorems
take as a premise. -/

namespace Library.Graphs.UnionFind

/-- Pair `t` relates `a` and `b`: they are `js[t]` and `ks[t]`, and both are below `n`. -/
def Paired (n : Nat) (js ks : Array UInt64) (a b : Nat) : Prop :=
  ∃ t, t < js.size ∧ t < ks.size ∧ js[t]!.toNat = a ∧ ks[t]!.toNat = b ∧ a < n ∧ b < n

/-- The least equivalence relation that relates the elements of each pair. -/
def Equivalent (n : Nat) (js ks : Array UInt64) : Nat → Nat → Prop :=
  Relation.EqvGen (Paired n js ks)

/-- `r` holds `n` words, and word `i` is the least element of the class of `i`. -/
def LeastLabels (n : Nat) (js ks r : Array UInt64) : Prop :=
  r.size = n ∧ ∀ i < n, IsLeast {j | Equivalent n js ks i j} r[i]!.toNat

end Library.Graphs.UnionFind
