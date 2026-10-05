import Project.ProofKit.F64Outward
import Project.ProofKit.F64MulEnclosure
import Project.ProofKit.F64DivEnclosure
import Project.ProofKit.F64SqrtEnclosure

namespace Project.ProofKit.F64Outward
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Adjacent
set_option exponentiation.threshold 4096

def Sound (up : Bool) (result : Checked) (x : ℝ) : Prop :=
  result.status = 0 ∧ Finite result.value ∧
    if up then x ≤ value result.value else value result.value ≤ x

theorem guarded_behavior (ok : Bool) (result : Checked) (P : Checked → Prop)
    (h : ok = true → result = rejected ∨ P result) :
    (if ok then result else rejected) = rejected ∨ P (if ok then result else rejected) := by
  cases ok <;> simp_all

theorem endpoint_behavior (up : Bool) (rounded : UInt64) (x : ℝ)
    (he : Finite rounded → value (nextDown rounded) ≤ x ∧ x ≤ value (nextUp rounded)) :
    endpoint up rounded = rejected ∨ Sound up (endpoint up rounded) x := by
  unfold endpoint
  refine guarded_behavior _ _ (fun result => Sound up result x) ?_
  intro hf
  refine guarded_behavior _ _ (fun result => Sound up result x) ?_
  intro hn
  right
  refine ⟨rfl, (finiteBits_iff _).mp hn, ?_⟩
  have he := he ((finiteBits_iff _).mp hf)
  cases up
  · exact he.1
  · exact he.2

theorem binary_behavior (op : UInt64 → UInt64 → UInt64) (f : ℝ → ℝ → ℝ)
    (he : ∀ (a b : UInt64), Finite a → Finite b → Finite (op a b) →
      value (nextDown (op a b)) ≤ f (value a) (value b) ∧
      f (value a) (value b) ≤ value (nextUp (op a b)))
    (up : Bool) (a b : UInt64) :
    let result := if finiteBits a && finiteBits b then endpoint up (op a b) else rejected
    result = rejected ∨ Finite a ∧ Finite b ∧ Sound up result (f (value a) (value b)) := by
  refine guarded_behavior _ _
    (fun result => Finite a ∧ Finite b ∧ Sound up result (f (value a) (value b))) ?_
  intro hg
  have hg : finiteBits a = true ∧ finiteBits b = true := by simpa using hg
  obtain ⟨ha, hb⟩ := hg
  have ha := (finiteBits_iff _).mp ha
  have hb := (finiteBits_iff _).mp hb
  exact (endpoint_behavior up (op a b) _ (he a b ha hb)).imp_right
    (fun h => ⟨ha, hb, h⟩)

theorem add_behavior (up : Bool) (a b : UInt64) :
    add up a b = rejected ∨ Finite a ∧ Finite b ∧ Sound up (add up a b) (value a+value b) :=
  binary_behavior Wasm.IEEE64.add (·+·) add_enclosure up a b

theorem sub_behavior (up : Bool) (a b : UInt64) :
    sub up a b = rejected ∨ Finite a ∧ Finite b ∧ Sound up (sub up a b) (value a-value b) :=
  binary_behavior Wasm.IEEE64.sub (·-·) sub_enclosure up a b

theorem mul_behavior (up : Bool) (a b : UInt64) :
    mul up a b = rejected ∨ Finite a ∧ Finite b ∧ Sound up (mul up a b) (value a*value b) :=
  binary_behavior Wasm.IEEE64.mul (·*·) mul_enclosure up a b

theorem magnitude_ne_zero (a : UInt64) (ha : absBits a ≠ 0) :
    Wasm.IEEE64.scaledMagnitude a ≠ 0 := by
  rw [scaledMagnitude_abs]
  intro hz
  unfold unsignedScaled at hz
  split at hz
  · rename_i he
    have hnat : (absBits a).toNat = 0 := by
      have := Nat.div_add_mod' (absBits a).toNat (2^52)
      omega
    exact ha (UInt64.toNat_inj.mp hnat)
  · have hp : 0 < (2^52+(absBits a).toNat%2^52)*2^((absBits a).toNat/2^52-1) := by
      positivity
    omega

theorem nonnegative_word (a : UInt64) (ha : a ≤ 0x8000000000000000) : 0 ≤ value a := by
  have hraw : a.toNat ≤ 2^63 := UInt64.le_iff_toNat_le.mp ha
  by_cases hz : a = 0x8000000000000000
  · subst a
    rw [value, show Wasm.IEEE64.scaledValue 0x8000000000000000 = 0 by decide +kernel]
    simp
  · have hne : a.toNat ≠ 2^63 := fun h => hz (UInt64.toNat_inj.mp h)
    have hs : Wasm.IEEE64.sign a = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
      omega
    simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Int.cast_natCast]
    positivity

theorem div_behavior (up : Bool) (a b : UInt64) :
    div up a b = rejected ∨ Finite a ∧ Finite b ∧ Wasm.IEEE64.scaledMagnitude b ≠ 0 ∧
      Sound up (div up a b) (value a/value b) := by
  unfold div
  refine guarded_behavior _ _
    (fun result => Finite a ∧ Finite b ∧ Wasm.IEEE64.scaledMagnitude b ≠ 0 ∧
      Sound up result (value a/value b)) ?_
  intro hg
  have hg : (finiteBits a = true ∧ finiteBits b = true) ∧ 0 < absBits b := by simpa using hg
  have ha := (finiteBits_iff _).mp hg.1.1
  have hb := (finiteBits_iff _).mp hg.1.2
  have hz := magnitude_ne_zero b (by intro hz; simpa [hz] using hg.2)
  exact (endpoint_behavior up (Wasm.IEEE64.div a b) _ (div_enclosure a b ha hb hz)).imp_right
    (fun h => ⟨ha, hb, hz, h⟩)

theorem sqrt_behavior (up : Bool) (a : UInt64) :
    sqrt up a = rejected ∨ Finite a ∧ 0 ≤ value a ∧
      Sound up (sqrt up a) (Real.sqrt (value a)) := by
  unfold sqrt
  refine guarded_behavior _ _
    (fun result => Finite a ∧ 0 ≤ value a ∧ Sound up result (Real.sqrt (value a))) ?_
  intro hg
  have hg : finiteBits a = true ∧ a ≤ 0x8000000000000000 := by simpa using hg
  have ha := (finiteBits_iff _).mp hg.1
  have hx := nonnegative_word a hg.2
  exact (endpoint_behavior up (Wasm.IEEE64.sqrt a) _ (sqrt_enclosure a ha hx)).imp_right
    (fun h => ⟨ha, hx, h⟩)

#print axioms add_behavior
#print axioms sub_behavior
#print axioms mul_behavior
#print axioms div_behavior
#print axioms sqrt_behavior
end Project.ProofKit.F64Outward
