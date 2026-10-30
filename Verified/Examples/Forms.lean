import Verified.Reflect.Command

/-! Array literals with elements, and conjunctions and disjunctions of propositions in conditions.
The reflector reads `#[a₁, …, aₙ]` as `((#[].push a₁).push …).push aₙ`, and `if p ∧ q` and
`if p ∨ q`, in ordinary code and in tail loops, as tests of `decide p && decide q` and
`decide p || decide q`.  The kernel checks each reading. -/

namespace Verified.Examples.Forms

/-- A literal of two words. -/
def pair (a b : UInt64) : Array UInt64 := #[a, b]

/-- A literal of one computed word. -/
def single (a : UInt64) : Array UInt64 := #[a + 1]

/-- A literal of binary64 values. -/
def floats (x : Float) : Array Float := #[x, x * 2.0, -x]

/-- A literal of `Bool`s, the last the decision of a conjunction. -/
def flags (a b : UInt64) : Array Bool := #[a < b, a == b, decide (a ≤ b ∧ b ≤ 100)]

/-- A literal whose elements read an array, past its end included. -/
def window (xs : Array UInt64) (i : UInt64) : Array UInt64 :=
  #[xs[i.toNat]!, xs[(i + 1).toNat]!, xs.size.toUInt64]

/-- A loop whose state is a literal built at each step. -/
def lastTwo (n : UInt64) : Array UInt64 :=
  LeanExe.loop n #[0, 0] fun i s => #[s[(1 : UInt64).toNat]!, i]

/-- 1 when `lo ≤ a < hi`, and 0 otherwise. -/
def inside (a lo hi : UInt64) : UInt64 := if lo ≤ a ∧ a < hi then 1 else 0

/-- 1 when `a < lo` or `hi ≤ a`, and 0 otherwise. -/
def outside (a lo hi : UInt64) : UInt64 := if a < lo ∨ hi ≤ a then 1 else 0

/-- The middle word when the three are strictly ordered in either direction, and 0 otherwise. -/
def ordered (a b c : UInt64) : UInt64 :=
  if (a < b ∧ b < c) ∨ (c < b ∧ b < a) then b else 0

/-- `x` when it lies in `[lo, hi]`, and 0 otherwise. -/
def within (x lo hi : Float) : Float := if lo ≤ x ∧ x ≤ hi then x else 0.0

/-- Decisions of a conjunction and of a disjunction as `Bool` values. -/
def decided (a b : UInt64) : Bool := decide (a < b ∧ b ≠ 0) || decide (a = b ∨ b = 7)

/-- A conjunction in each element of a build. -/
def marks (xs : Array UInt64) (lo hi : UInt64) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => if lo ≤ xs[i.toNat]! ∧ xs[i.toNat]! ≤ hi then 1 else 0

/-- A tail recursion that stops on a disjunction. -/
def countDown (n acc : UInt64) : UInt64 :=
  if n = 0 ∨ acc = 1000 then acc else countDown (n - 1) (acc + 1)
termination_by n.toNat
decreasing_by
  rename_i h
  have hn : n.toNat ≠ 0 := fun e => h (Or.inl (UInt64.toNat_inj.mp (by simpa using e)))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp
  omega

/-- A tail recursion that continues on a conjunction. -/
def climb (n acc : UInt64) : UInt64 :=
  if n ≠ 0 ∧ acc < 50 then climb (n - 1) (acc + 3) else acc
termination_by n.toNat
decreasing_by
  rename_i h
  have hn : n.toNat ≠ 0 := fun e => h.1 (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp
  omega

verified_compile compiled := [pair, single, floats, flags, window, lastTwo, inside, outside,
  ordered, within, decided, marks, countDown, climb]

/-- A literal of one word allocates an empty block and grows it once: 152 bytes. -/
theorem single_bound (a : UInt64) : compiled.single.bound a = 152 := by
  rw [compiled.single.bound_eq]
  decide

/-- A literal of two words allocates an empty block, grows it once, and pushes onto the paid
result once more: 232 bytes. -/
theorem pair_bound (a b : UInt64) : compiled.pair.bound (a, b) = 232 := by
  rw [compiled.pair.bound_eq]
  decide

#print axioms compiled.bytes
#print axioms pair_bound

end Verified.Examples.Forms
