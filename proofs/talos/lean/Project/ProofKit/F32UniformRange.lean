import Project.ProofKit.F32DotRanges

namespace Project.ProofKit.F32UniformRange
open CodeLib.IEEE32

def productMagnitude (bound : Nat) : Nat := (2 ^ bound + 2 ^ (bound - 25)) / 2 ^ 149

theorem product_magnitude (a b : UInt32) (bound : Nat)
    (hLower : 173 ≤ bound) (hUpper : bound ≤ 425)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hProduct : Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.mulBits a b) ∧
      (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits a b)).natAbs ≤ productMagnitude bound := by
  have h := F32MultiplicationBounds.mul_scaled_error a b bound hLower hUpper ha hb hProduct
  rw [← F32Mul.mul_eq] at h
  have he : (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits a b) * (2 : Int) ^ 149 -
      Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b).natAbs ≤ 2 ^ (bound - 25) := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h.2
  have hp : (Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound := by
    simpa only [Int.natAbs_mul, natAbs_scaledValue] using hProduct
  have ht := Int.natAbs_add_le
    (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits a b) * (2 : Int) ^ 149 -
      Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b)
    (Wasm.IEEE32.scaledValue a * Wasm.IEEE32.scaledValue b)
  rw [sub_add_cancel, Int.natAbs_mul, Int.natAbs_pow] at ht
  refine ⟨h.1, (Nat.le_div_iff_mul_le (by positivity)).mpr ?_⟩
  change (Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits a b)).natAbs * 2 ^ 149 ≤ _
  omega

theorem sum_prefix (input : Nat → UInt32) (count bound magnitude : Nat)
    (hUpper : bound ≤ 276) (hFinite : ∀ i < count, CodeLib.IEEE32.Finite (input i))
    (hMagnitude : ∀ i < count, (Wasm.IEEE32.scaledValue (input i)).natAbs ≤ magnitude)
    (hFits : count * (magnitude + 2 ^ (bound - 25)) < 2 ^ bound) :
    CodeLib.IEEE32.Finite (F32SumError.sumPrefix input count) ∧
      (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count)).natAbs ≤
        count * (magnitude + 2 ^ (bound - 25)) := by
  induction count with
  | zero =>
    norm_num [F32SumError.sumPrefix, CodeLib.IEEE32.Finite, Wasm.IEEE32.isFinite,
      Wasm.IEEE32.exponent, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
      Wasm.IEEE32.fraction, Wasm.IEEE32.sign]
  | succ count ih =>
    have hp := ih (fun i hi => hFinite i (by omega)) (fun i hi => hMagnitude i (by omega))
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ count)) hFits)
    have hSum := Int.natAbs_add_le (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count))
      (Wasm.IEEE32.scaledValue (input count))
    have hi := hMagnitude count (by omega)
    have hRange : (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count) +
        Wasm.IEEE32.scaledValue (input count)).natAbs < 2 ^ bound := by
      apply lt_of_le_of_lt (hSum.trans (Nat.add_le_add hp.2 hi))
      apply lt_of_le_of_lt _ hFits
      rw [Nat.succ_mul]
      exact Nat.add_le_add_left (Nat.le_add_right magnitude (2 ^ (bound - 25))) _
    have ha := F32AdditionBounds.add_spec (F32SumError.sumPrefix input count) (input count) bound
      hUpper hp.1 (hFinite count (by omega)) hRange
    rw [← F32Add.add_eq, ← F32SumError.sumPrefix_succ] at ha
    have he : (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input (count + 1)) -
        (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count) + Wasm.IEEE32.scaledValue (input count))).natAbs ≤
          2 ^ (bound - 25) := by
      rw [← Int.natCast_natAbs] at ha
      exact_mod_cast ha.2
    have ht := Int.natAbs_add_le
      (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input (count + 1)) -
        (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count) + Wasm.IEEE32.scaledValue (input count)))
      (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input count) + Wasm.IEEE32.scaledValue (input count))
    rw [sub_add_cancel] at ht
    refine ⟨ha.1, ?_⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem sum_ranges (input : Nat → UInt32) (count bound magnitude : Nat)
    (hUpper : bound ≤ 276) (hFinite : ∀ i < count, CodeLib.IEEE32.Finite (input i))
    (hMagnitude : ∀ i < count, (Wasm.IEEE32.scaledValue (input i)).natAbs ≤ magnitude)
    (hFits : count * (magnitude + 2 ^ (bound - 25)) < 2 ^ bound) :
    ∀ i < count, (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input i) +
      Wasm.IEEE32.scaledValue (input i)).natAbs < 2 ^ bound := by
  intro i hi
  have hp := sum_prefix input i bound magnitude hUpper (fun j hj => hFinite j (by omega))
    (fun j hj => hMagnitude j (by omega)) (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega : i ≤ count)) hFits)
  have ht := Int.natAbs_add_le (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input i))
    (Wasm.IEEE32.scaledValue (input i))
  have hm := hMagnitude i hi
  have hc := Nat.mul_le_mul_right (magnitude + 2 ^ (bound - 25)) (show i + 1 ≤ count by omega)
  rw [Nat.add_mul, Nat.one_mul] at hc
  apply lt_of_le_of_lt (ht.trans (Nat.add_le_add hp.2 hm))
  apply lt_of_le_of_lt _ hFits
  exact (Nat.add_le_add_left (Nat.le_add_right magnitude (2 ^ (bound - 25))) _).trans hc

theorem dot_ranges (x w : Nat → UInt32) (count mulBound addBound : Nat)
    (hMulLower : 173 ≤ mulBound) (hMulUpper : mulBound ≤ 425) (hAddUpper : addBound ≤ 276)
    (hx : ∀ i < count, CodeLib.IEEE32.Finite (x i)) (hw : ∀ i < count, CodeLib.IEEE32.Finite (w i))
    (hProduct : ∀ i < count, Wasm.IEEE32.scaledMagnitude (x i) * Wasm.IEEE32.scaledMagnitude (w i) < 2 ^ mulBound)
    (hFits : count * (productMagnitude mulBound + 2 ^ (addBound - 25)) < 2 ^ addBound) :
    F32DotError.Ranges x w count ⟨fun _ => mulBound, fun _ => addBound⟩ := by
  have hp (i : Nat) (hi : i < count) := product_magnitude (x i) (w i) mulBound hMulLower hMulUpper (hx i hi) (hw i hi) (hProduct i hi)
  exact ⟨hx, hw, fun _ _ => hMulLower, fun _ _ => hMulUpper, hProduct, fun _ _ => hAddUpper,
    sum_ranges _ count addBound (productMagnitude mulBound) hAddUpper (fun i hi => (hp i hi).1)
      (fun i hi => (hp i hi).2) hFits⟩

#print axioms product_magnitude
#print axioms sum_prefix
#print axioms sum_ranges
#print axioms dot_ranges
end Project.ProofKit.F32UniformRange
