import Examples.Below100.Program
import Examples.Below100.Spec
import LeanExe.IR.Combinators

/-! The program equals the specification, a fact about the Lean definitions that the theorems of
the verified compilation use. -/

namespace Examples.Below100

theorem keep_eq (xs : Array UInt64) (i : UInt64) (out : Array UInt64) :
    keep xs i out = (i + 1, if xs[i.toNat]! < 100 then out.push xs[i.toNat]! else out) := by
  by_cases h : xs[i.toNat]! < 100 <;> simp [keep, h]

/-- `keep` repeated from index `i` until `count` filters the first `count` elements. -/
theorem keep_go (xs : Array UInt64) (count : UInt64) (hc : count.toNat ≤ xs.size) :
    ∀ (k : Nat) (i : UInt64) (out : Array UInt64), i.toNat ≤ count.toNat →
      count.toNat - i.toNat ≤ k →
      out.toList = (xs.toList.take i.toNat).filter (fun e => decide (e < 100)) →
      (LeanExe.repeatWhile.go (fun (s : UInt64 × Array UInt64) => decide (s.1 < count))
        (fun s => keep xs s.1 s.2) k (i, out)).2.toList =
        (xs.toList.take count.toNat).filter (fun e => decide (e < 100)) := by
  have hcount := count.toNat_lt
  intro k
  induction k with
  | zero =>
    intro i out hi hk hout
    have : i.toNat = count.toNat := by omega
    simp only [LeanExe.repeatWhile.go]
    rw [hout, this]
  | succ k ih =>
    intro i out hi hk hout
    simp only [LeanExe.repeatWhile.go]
    by_cases hlt : i < count
    · have hlt' : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hix : i.toNat < xs.toList.length := by simp; omega
      have hx : xs[i.toNat]! = xs.toList[i.toNat] := by
        rw [getElem!_pos xs i.toNat (by omega)]; simp
      simp only [hlt, decide_true, ite_true]
      show (LeanExe.repeatWhile.go _ _ k (keep xs i out)).2.toList = _
      rw [keep_eq xs i out]
      refine ih (i + 1) _ (by omega) (by omega) ?_
      rw [hi1, List.take_add_one, List.filter_append, ← hout, List.getElem?_eq_getElem hix, hx]
      generalize xs.toList[i.toNat] = v
      by_cases h : v < 100 <;> simp [h]
    · have hge : count.toNat ≤ i.toNat :=
        Nat.le_of_not_lt fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      have : i.toNat = count.toNat := by omega
      simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      rw [hout, this]

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  by_cases hs : xs.size ≤ 8
  · have hle : xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_true, hs]
    apply Array.toList_inj.mp
    have := keep_go xs xs.size.toUInt64 (by rw [hn]) 8 0 #[] (by simp) (by rw [hn]; simp; omega)
      (by simp)
    rw [hn, List.take_of_length_le (by simp)] at this
    rw [Array.toList_filter, ← this]
    rfl
  · have hle : ¬ xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_false, hs]
    rfl

end Examples.Below100
