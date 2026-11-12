import Library.Numerics.Bounds.Compiled
import Library.Numerics.Bounds.Proof
import Verified.Master

namespace Library.Numerics.Bounds

open LeanExe.ProofKit
open LeanExe.ProofKit.F64Adjacent (nextUp nextDown)
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-- The checked value `c` holds the word `w` moved one step up for `up` and one step down
otherwise, it is accepted exactly when `ok` holds and `w` and the moved word are finite, and an
accepted `c` lies at or above the real `x` for `up` and at or below it otherwise. -/
def Outward (up : Bool) (ok : Prop) (w : UInt64) (x : ℝ) (c : Checked) : Prop :=
  (c.status = 0 ↔ ok ∧ Finite w ∧ Finite (F64Outward.neighbor up w)) ∧
    (c.status = 0 → c.value.toBits = F64Outward.neighbor up w ∧
      if up then x ≤ value c.value.toBits else value c.value.toBits ≤ x)

theorem Outward.lower {ok : Prop} {w : UInt64} {x : ℝ} {c : Checked} (o : Outward false ok w x c) :
    ((c.status = 0 ↔ ok ∧ Finite w ∧ Finite (nextDown w)) ∧
      (c.status = 0 → c.value.toBits = nextDown w)) ∧ (c.status = 0 → value c.value.toBits ≤ x) :=
  ⟨⟨o.1, fun h => (o.2 h).1⟩, fun h => (o.2 h).2⟩

theorem Outward.upper {ok : Prop} {w : UInt64} {x : ℝ} {c : Checked} (o : Outward true ok w x c) :
    ((c.status = 0 ↔ ok ∧ Finite w ∧ Finite (nextUp w)) ∧
      (c.status = 0 → c.value.toBits = nextUp w)) ∧ (c.status = 0 → x ≤ value c.value.toBits) :=
  ⟨⟨o.1, fun h => (o.2 h).1⟩, fun h => (o.2 h).2⟩

/-! ### Words -/

theorem abs_eq_absBits (x : UInt64) : Wasm.IEEE64.abs x = absBits x := by
  apply UInt64.toNat_inj.mp
  rw [show absBits x = F64Order.absBits x from rfl, F64Order.absBits_toNat]
  have hx := x.toNat_lt
  simp only [Wasm.IEEE64.abs, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, Bool.false_eq_true, ite_false, Nat.zero_add, UInt64.toNat_ofNat']
  omega

theorem value_abs (x : UInt64) : value (Wasm.IEEE64.abs x) = |value x| := by
  have ht : (Wasm.IEEE64.abs x).toNat = x.toNat % 2 ^ 63 := by
    rw [abs_eq_absBits]
    exact F64Order.absBits_toNat x
  have hs : Wasm.IEEE64.sign (Wasm.IEEE64.abs x) = false := by
    have := Nat.mod_lt x.toNat (by norm_num : 0 < 2 ^ 63)
    simp only [Wasm.IEEE64.sign, ht, decide_eq_false_iff_not, not_le]
    omega
  have he : Wasm.IEEE64.exponent (Wasm.IEEE64.abs x) = Wasm.IEEE64.exponent x := by
    simp only [Wasm.IEEE64.exponent, ht]
    omega
  have hf : Wasm.IEEE64.fraction (Wasm.IEEE64.abs x) = Wasm.IEEE64.fraction x := by
    simp only [Wasm.IEEE64.fraction, ht]
    omega
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.abs x) = Wasm.IEEE64.scaledMagnitude x := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf]
  have habs : |(Wasm.IEEE64.scaledValue x : ℝ)| = Wasm.IEEE64.scaledMagnitude x := by
    simp [Wasm.IEEE64.scaledValue]
    split <;> simp
  unfold CodeLib.IEEE64.value
  rw [abs_div, habs, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  simp only [Wasm.IEEE64.scaledValue, hs, hm, Bool.false_eq_true, ite_false, Int.cast_natCast]

theorem unsignedScaled_eq_zero (n : Nat) : F64Order.unsignedScaled n = 0 ↔ n = 0 := by
  unfold F64Order.unsignedScaled
  split
  · constructor <;> intro <;> omega
  · rename_i h
    have hp : 0 < (2 ^ 52 + n % 2 ^ 52) * 2 ^ (n / 2 ^ 52 - 1) := by positivity
    constructor
    · intro h0
      exact absurd h0 hp.ne'
    · intro h0
      subst h0
      simp at h

/-- A word's magnitude field is nonzero exactly when its value is nonzero. -/
theorem absBits_pos_iff (b : UInt64) : 0 < F64Order.absBits b ↔ value b ≠ 0 := by
  have hv : value b ≠ 0 ↔ Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    rw [← CodeLib.IEEE64.natAbs_scaledValue, Int.natAbs_ne_zero]
    unfold CodeLib.IEEE64.value
    rw [div_ne_zero_iff, Int.cast_ne_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, by positivity⟩⟩
  rw [hv, F64Order.scaledMagnitude_abs, Ne, unsignedScaled_eq_zero, UInt64.lt_iff_toNat_lt]
  simp only [UInt64.reduceToNat]
  exact ⟨fun h => by omega, fun h => by omega⟩

/-- A word lies at or below the word of `-0` exactly when its value is not negative. -/
theorem le_negZero_iff (a : UInt64) : a ≤ 0x8000000000000000 ↔ 0 ≤ value a := by
  refine ⟨F64Outward.nonnegative_word a, fun h => ?_⟩
  by_contra hn
  have hlt : 2 ^ 63 < a.toNat := by
    have := mt UInt64.le_iff_toNat_le.mpr hn
    simp only [UInt64.reduceToNat, not_le] at this
    omega
  have hp : 0 < F64Order.unsignedScaled (a.toNat - 2 ^ 63) :=
    Nat.pos_of_ne_zero fun h0 => by
      have := (unsignedScaled_eq_zero _).mp h0
      omega
  rw [F64Adjacent.negative_word_value a hlt.le] at h
  have hneg : -(F64Order.unsignedScaled (a.toNat - 2 ^ 63) : ℝ) / (2 : ℝ) ^ 1074 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (by exact_mod_cast hp)) (by positivity)
  linarith

theorem nextUpBits_eq (x : UInt64) : nextUpBits x = nextUp x := by
  simp [nextUpBits, nextUp]

theorem nextDownBits_eq (x : UInt64) : nextDownBits x = nextDown x := by
  simp [nextDownBits, nextDown]

/-! ### Checked endpoints -/

theorem endpoint_status_word (up : Bool) (w : UInt64) :
    (F64Outward.endpoint up w).status = 0 ↔ Finite w ∧ Finite (F64Outward.neighbor up w) := by
  rw [← F64Order.finiteBits_iff, ← F64Order.finiteBits_iff]
  by_cases hf : F64Order.finiteBits w = true
  · by_cases hn : F64Order.finiteBits (F64Outward.neighbor up w) = true
    · simp only [F64Outward.endpoint, hf, hn, ite_true, and_self, iff_self]
    · simp only [F64Outward.endpoint, hf, hn, ite_true, Bool.false_eq_true, ite_false,
        and_false, iff_false]
      exact fun h => absurd h (by decide)
  · simp only [F64Outward.endpoint, hf, Bool.false_eq_true, ite_false, false_and, iff_false]
    exact fun h => absurd h (by decide)

theorem endpoint_value_word {up : Bool} {w : UInt64} (h : (F64Outward.endpoint up w).status = 0) :
    (F64Outward.endpoint up w).value = F64Outward.neighbor up w := by
  obtain ⟨hf, hn⟩ := (endpoint_status_word up w).mp h
  rw [← F64Order.finiteBits_iff] at hf hn
  simp only [F64Outward.endpoint, hf, hn, ite_true]

theorem guarded_status (g up : Bool) (w : UInt64) :
    (if g then F64Outward.endpoint up w else F64Outward.rejected).status = 0 ↔
      g = true ∧ Finite w ∧ Finite (F64Outward.neighbor up w) := by
  cases g
  · simp only [Bool.false_eq_true, ite_false, false_and, iff_false]
    exact fun h => absurd h (by decide)
  · simp only [ite_true, true_and]
    exact endpoint_status_word up w

theorem guarded_value {g up : Bool} {w : UInt64}
    (h : (if g then F64Outward.endpoint up w else F64Outward.rejected).status = 0) :
    (if g then F64Outward.endpoint up w else F64Outward.rejected).value =
      F64Outward.neighbor up w := by
  cases g
  · simp only [Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)
  · simp only [ite_true] at h ⊢
    exact endpoint_value_word h

theorem endpoint_spec (up : Bool) (r : Float) :
    ((endpoint up r).status = 0 ↔ Finite r.toBits ∧ Finite (F64Outward.neighbor up r.toBits)) ∧
      ((endpoint up r).status = 0 →
        (endpoint up r).value.toBits = F64Outward.neighbor up r.toBits ∧
          if up then value r.toBits < value (endpoint up r).value.toBits
          else value (endpoint up r).value.toBits < value r.toBits) := by
  have hw := endpoint_word up r
  have hs : (endpoint up r).status = (F64Outward.endpoint up r.toBits).status :=
    congrArg F64Outward.Checked.status hw
  have hv : (endpoint up r).value.toBits = (F64Outward.endpoint up r.toBits).value :=
    congrArg F64Outward.Checked.value hw
  refine ⟨by rw [hs]; exact endpoint_status_word up r.toBits, fun h => ?_⟩
  have h' : (F64Outward.endpoint up r.toBits).status = 0 := hs.symm.trans h
  have hf := ((endpoint_status_word up r.toBits).mp h').1
  rw [hv, endpoint_value_word h']
  refine ⟨rfl, ?_⟩
  cases up
  · exact F64Adjacent.nextDown_lt _ hf
  · exact F64Adjacent.nextUp_lt _ hf

theorem outAdd_outward (up : Bool) (a b : Float) :
    Outward up (Finite a.toBits ∧ Finite b.toBits) (Wasm.IEEE64.add a.toBits b.toBits)
      (value a.toBits + value b.toBits) (outAdd up a b) := by
  have hw := outAdd_word up a b
  unfold F64Outward.add at hw
  have hs := congrArg F64Outward.Checked.status hw
  have hv := congrArg F64Outward.Checked.value hw
  change (outAdd up a b).status = _ at hs
  change (outAdd up a b).value.toBits = _ at hv
  refine ⟨?_, fun h => ⟨?_, (outAdd_accepted h).2.2.2.2⟩⟩
  · rw [hs, guarded_status]
    simp only [Bool.and_eq_true, F64Order.finiteBits_iff, iff_self]
  · rw [hv]
    exact guarded_value (hs.symm.trans h)

theorem outSub_outward (up : Bool) (a b : Float) :
    Outward up (Finite a.toBits ∧ Finite b.toBits) (Wasm.IEEE64.sub a.toBits b.toBits)
      (value a.toBits - value b.toBits) (outSub up a b) := by
  have hw := outSub_word up a b
  unfold F64Outward.sub at hw
  have hs := congrArg F64Outward.Checked.status hw
  have hv := congrArg F64Outward.Checked.value hw
  change (outSub up a b).status = _ at hs
  change (outSub up a b).value.toBits = _ at hv
  refine ⟨?_, fun h => ⟨?_, (outSub_accepted h).2.2.2.2⟩⟩
  · rw [hs, guarded_status]
    simp only [Bool.and_eq_true, F64Order.finiteBits_iff, iff_self]
  · rw [hv]
    exact guarded_value (hs.symm.trans h)

theorem outMul_outward (up : Bool) (a b : Float) :
    Outward up (Finite a.toBits ∧ Finite b.toBits) (Wasm.IEEE64.mul a.toBits b.toBits)
      (value a.toBits * value b.toBits) (outMul up a b) := by
  have hw := outMul_word up a b
  unfold F64Outward.mul at hw
  have hs := congrArg F64Outward.Checked.status hw
  have hv := congrArg F64Outward.Checked.value hw
  change (outMul up a b).status = _ at hs
  change (outMul up a b).value.toBits = _ at hv
  refine ⟨?_, fun h => ⟨?_, (outMul_accepted h).2.2.2.2⟩⟩
  · rw [hs, guarded_status]
    simp only [Bool.and_eq_true, F64Order.finiteBits_iff, iff_self]
  · rw [hv]
    exact guarded_value (hs.symm.trans h)

theorem outDiv_outward (up : Bool) (a b : Float) :
    Outward up (Finite a.toBits ∧ Finite b.toBits ∧ value b.toBits ≠ 0)
      (Wasm.IEEE64.div a.toBits b.toBits) (value a.toBits / value b.toBits) (outDiv up a b) := by
  have hw := outDiv_word up a b
  unfold F64Outward.div at hw
  have hs := congrArg F64Outward.Checked.status hw
  have hv := congrArg F64Outward.Checked.value hw
  change (outDiv up a b).status = _ at hs
  change (outDiv up a b).value.toBits = _ at hv
  refine ⟨?_, fun h => ⟨?_, (outDiv_accepted h).2.2.2.2.2⟩⟩
  · rw [hs, guarded_status]
    simp only [Bool.and_eq_true, F64Order.finiteBits_iff, decide_eq_true_eq, absBits_pos_iff,
      and_assoc, iff_self]
  · rw [hv]
    exact guarded_value (hs.symm.trans h)

theorem outSqrt_outward (up : Bool) (a : Float) :
    Outward up (Finite a.toBits ∧ 0 ≤ value a.toBits) (Wasm.IEEE64.sqrt a.toBits)
      (Real.sqrt (value a.toBits)) (outSqrt up a) := by
  have hw := outSqrt_word up a
  unfold F64Outward.sqrt at hw
  have hs := congrArg F64Outward.Checked.status hw
  have hv := congrArg F64Outward.Checked.value hw
  change (outSqrt up a).status = _ at hs
  change (outSqrt up a).value.toBits = _ at hv
  refine ⟨?_, fun h => ⟨?_, (outSqrt_accepted h).2.2.2.2⟩⟩
  · rw [hs, guarded_status]
    simp only [Bool.and_eq_true, F64Order.finiteBits_iff, decide_eq_true_eq, le_negZero_iff,
      iff_self]
  · rw [hv]
    exact guarded_value (hs.symm.trans h)

/-! ### Exports -/

theorem absBits_export :
    ({ name := "absBits", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem finite_export :
    ({ name := "finite", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem nextUpBits_export :
    ({ name := "nextUpBits", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem nextDownBits_export :
    ({ name := "nextDownBits", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem endpoint_export :
    ({ name := "endpoint", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outAdd_export :
    ({ name := "outAdd", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outSub_export :
    ({ name := "outSub", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outMul_export :
    ({ name := "outMul", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outDiv_export :
    ({ name := "outDiv", funcIdx := 10 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outSqrt_export :
    ({ name := "outSqrt", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-! ### Master theorems -/

/-- The export `absBits`, called on a word, returns the word of IEEE 754 `abs`, whose value is the
absolute value of the word's value. -/
theorem absBits_master :
    Verified.Master compiled.module compiled.tables "absBits" compiled.absBits.bound
      (fun _ => True)
      (fun (x : UInt64) (y : UInt64) => y = Wasm.IEEE64.abs x ∧ value y = |value x|) :=
  .of_trapFree (.ofA compiled.absBits.trapFree) nofun absBits_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨(abs_eq_absBits x).symm, by rw [← abs_eq_absBits]; exact value_abs x⟩

#print axioms absBits_master

/-- The export `finite`, called on a float, returns `true` exactly when the float is finite. -/
theorem finite_master :
    Verified.Master compiled.module compiled.tables "finite" compiled.finite.bound (fun _ => True)
      (fun (x : Float) (y : Bool) => y = true ↔ Finite x.toBits) :=
  .of_trapFree (.ofA compiled.finite.trapFree) nofun finite_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => F64Order.finiteBits_iff x.toBits

#print axioms finite_master

/-- The export `nextUpBits`, called on a word, returns the next word above it in value, whose
value exceeds the value of a finite word. -/
theorem nextUpBits_master :
    Verified.Master compiled.module compiled.tables "nextUpBits" compiled.nextUpBits.bound
      (fun _ => True)
      (fun (x : UInt64) (y : UInt64) => y = nextUp x ∧ (Finite x → value x < value y)) :=
  .of_trapFree (.ofA compiled.nextUpBits.trapFree) nofun nextUpBits_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨nextUpBits_eq x, fun h => by rw [nextUpBits_eq]; exact F64Adjacent.nextUp_lt x h⟩

#print axioms nextUpBits_master

/-- The export `nextDownBits`, called on a word, returns the next word below it in value, whose
value lies below the value of a finite word. -/
theorem nextDownBits_master :
    Verified.Master compiled.module compiled.tables "nextDownBits" compiled.nextDownBits.bound
      (fun _ => True)
      (fun (x : UInt64) (y : UInt64) => y = nextDown x ∧ (Finite x → value y < value x)) :=
  .of_trapFree (.ofA compiled.nextDownBits.trapFree) nofun nextDownBits_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨nextDownBits_eq x, fun h => by rw [nextDownBits_eq]; exact F64Adjacent.nextDown_lt x h⟩

#print axioms nextDownBits_master

/-- The export `endpoint`, called on a direction `up` and a float `r`, accepts exactly when `r`
and the word one step from it, up for `up` and down otherwise, are finite, and then returns that
word, whose value lies above the value of `r` for `up` and below it otherwise. -/
theorem endpoint_master :
    Verified.Master compiled.module compiled.tables "endpoint" compiled.endpoint.bound
      (fun _ => True)
      (fun (x : Bool × Float) (y : Checked) =>
        (y.status = 0 ↔ Finite x.2.toBits ∧ Finite (F64Outward.neighbor x.1 x.2.toBits)) ∧
          (y.status = 0 → y.value.toBits = F64Outward.neighbor x.1 x.2.toBits ∧
            if x.1 then value x.2.toBits < value y.value.toBits
            else value y.value.toBits < value x.2.toBits)) :=
  .of_trapFree (.ofA compiled.endpoint.trapFree) nofun endpoint_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => endpoint_spec x.1 x.2

#print axioms endpoint_master

/-- The export `outAdd`, called on a direction `up` and floats `a` and `b`, returns the IEEE 754
sum of `a` and `b` moved one step up for `up` and one step down otherwise, accepted exactly when
`a`, `b`, the sum, and the moved sum are finite, and bounding `a + b` from above for `up` and from
below otherwise. -/
theorem outAdd_master :
    Verified.Master compiled.module compiled.tables "outAdd" compiled.outAdd.bound (fun _ => True)
      (fun (x : Bool × Float × Float) (y : Checked) =>
        Outward x.1 (Finite x.2.1.toBits ∧ Finite x.2.2.toBits)
          (Wasm.IEEE64.add x.2.1.toBits x.2.2.toBits)
          (value x.2.1.toBits + value x.2.2.toBits) y) :=
  .of_trapFree (.ofA compiled.outAdd.trapFree) nofun outAdd_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => outAdd_outward x.1 x.2.1 x.2.2

#print axioms outAdd_master

/-- The export `outSub`, called on a direction `up` and floats `a` and `b`, returns the IEEE 754
difference of `a` and `b` moved one step up for `up` and one step down otherwise, accepted exactly
when `a`, `b`, the difference, and the moved difference are finite, and bounding `a - b` from
above for `up` and from below otherwise. -/
theorem outSub_master :
    Verified.Master compiled.module compiled.tables "outSub" compiled.outSub.bound (fun _ => True)
      (fun (x : Bool × Float × Float) (y : Checked) =>
        Outward x.1 (Finite x.2.1.toBits ∧ Finite x.2.2.toBits)
          (Wasm.IEEE64.sub x.2.1.toBits x.2.2.toBits)
          (value x.2.1.toBits - value x.2.2.toBits) y) :=
  .of_trapFree (.ofA compiled.outSub.trapFree) nofun outSub_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => outSub_outward x.1 x.2.1 x.2.2

#print axioms outSub_master

/-- The export `outMul`, called on a direction `up` and floats `a` and `b`, returns the IEEE 754
product of `a` and `b` moved one step up for `up` and one step down otherwise, accepted exactly
when `a`, `b`, the product, and the moved product are finite, and bounding `a * b` from above for
`up` and from below otherwise. -/
theorem outMul_master :
    Verified.Master compiled.module compiled.tables "outMul" compiled.outMul.bound (fun _ => True)
      (fun (x : Bool × Float × Float) (y : Checked) =>
        Outward x.1 (Finite x.2.1.toBits ∧ Finite x.2.2.toBits)
          (Wasm.IEEE64.mul x.2.1.toBits x.2.2.toBits)
          (value x.2.1.toBits * value x.2.2.toBits) y) :=
  .of_trapFree (.ofA compiled.outMul.trapFree) nofun outMul_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => outMul_outward x.1 x.2.1 x.2.2

#print axioms outMul_master

/-- The export `outDiv`, called on a direction `up` and floats `a` and `b`, returns the IEEE 754
quotient of `a` by `b` moved one step up for `up` and one step down otherwise, accepted exactly
when `a` and `b` are finite, the value of `b` is not zero, and the quotient and the moved quotient
are finite, and bounding `a / b` from above for `up` and from below otherwise. -/
theorem outDiv_master :
    Verified.Master compiled.module compiled.tables "outDiv" compiled.outDiv.bound (fun _ => True)
      (fun (x : Bool × Float × Float) (y : Checked) =>
        Outward x.1 (Finite x.2.1.toBits ∧ Finite x.2.2.toBits ∧ value x.2.2.toBits ≠ 0)
          (Wasm.IEEE64.div x.2.1.toBits x.2.2.toBits)
          (value x.2.1.toBits / value x.2.2.toBits) y) :=
  .of_trapFree (.ofA compiled.outDiv.trapFree) nofun outDiv_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => outDiv_outward x.1 x.2.1 x.2.2

#print axioms outDiv_master

/-- The export `outSqrt`, called on a direction `up` and a float `a`, returns the IEEE 754 square
root of `a` moved one step up for `up` and one step down otherwise, accepted exactly when `a` is
finite with a value that is not negative and the root and the moved root are finite, and bounding
`√a` from above for `up` and from below otherwise. -/
theorem outSqrt_master :
    Verified.Master compiled.module compiled.tables "outSqrt" compiled.outSqrt.bound (fun _ => True)
      (fun (x : Bool × Float) (y : Checked) =>
        Outward x.1 (Finite x.2.toBits ∧ 0 ≤ value x.2.toBits) (Wasm.IEEE64.sqrt x.2.toBits)
          (Real.sqrt (value x.2.toBits)) y) :=
  .of_trapFree (.ofA compiled.outSqrt.trapFree) nofun outSqrt_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => outSqrt_outward x.1 x.2

#print axioms outSqrt_master

end Library.Numerics.Bounds
