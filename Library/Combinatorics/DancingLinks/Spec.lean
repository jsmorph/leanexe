import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-! The specification of exact cover.  The first word of the input is the number of items `N`, read
as `x.getD 0 0`, so the empty array has no items.  The options are the maximal runs of nonzero words
after the first word: `List.splitOn 0` cuts the rest at each zero, and the empty runs are removed,
those that consecutive, leading, or trailing zeros leave and the one that `List.splitOn` returns
when nothing follows the first word, so they add no option, and a last run without a zero after it
is an option.  Option `k`, counted from 0, is the run at index `k`, so two
equal runs are two options.  An input is valid when `N ≤ 998`, every item of every option lies in
`1..N`, and no option repeats an item.  A cover is a set of option indices that contains, for each
item of `1..N`, exactly one option holding that item, and `countSpec` is the number of covers
modulo `2^64`.  On a valid input every option lies inside `1..N` and holds each of its items once,
so the covers are the exact covers of the request.  With `N = 0` and no options, the empty set is
the one cover, and the count is 1.  `validSpec` is 1 exactly for valid inputs.  The request fixes
the count only on valid inputs, and `countSpec` on other inputs is the same formula, which the
module's theorem does not claim. -/

namespace Library.Combinatorics.DancingLinks

/-- The number of items, the first word of the input. -/
def itemCount (x : Array UInt64) : Nat := (x.getD 0 0).toNat

/-- The options: the maximal runs of nonzero words after the first word. -/
def options (x : Array UInt64) : List (List Nat) :=
  (((x.toList.drop 1).map UInt64.toNat).splitOn 0).filter (· ≠ [])

/-- The input is valid: at most 998 items, every item of every option in `1..N`, and no option
that repeats an item. -/
def Valid (x : Array UInt64) : Prop :=
  itemCount x ≤ 998 ∧ ∀ o ∈ options x, o.Nodup ∧ ∀ j ∈ o, j ≤ itemCount x

instance (x : Array UInt64) : Decidable (Valid x) := by
  unfold Valid; infer_instance

/-- The set `S` of option indices contains exactly one option holding each item of `1..N`. -/
def IsCover (x : Array UInt64) (S : Finset Nat) : Prop :=
  ∀ i ∈ Finset.Icc 1 (itemCount x), (S.filter fun k => i ∈ (options x)[k]!).card = 1

instance (x : Array UInt64) (S : Finset Nat) : Decidable (IsCover x S) := by
  unfold IsCover; infer_instance

/-- The number of covers: the sets of option indices that are covers. -/
def coverCount (x : Array UInt64) : Nat :=
  ((Finset.range (options x).length).powerset.filter (IsCover x)).card

def countSpec (x : Array UInt64) : UInt64 := UInt64.ofNat (coverCount x)

def validSpec (x : Array UInt64) : UInt64 := if Valid x then 1 else 0

end Library.Combinatorics.DancingLinks
