import Project.RunningSum.Order

namespace Project.RunningSum

def compareDigits (a b : ByteArray) : List Nat → Option Bool
  | [] => none
  | i :: rest => if a[i]! != b[i]! then some (a[i]! < b[i]!) else compareDigits a b rest

theorem compareDigits_forIn (a b : ByteArray) (indices : List Nat) :
    (forIn indices (none, ()) (fun i (_ : Option Bool × Unit) =>
      if a[i]! != b[i]! then pure (.done (some (decide (a[i]! < b[i]!)), ()))
      else pure (.yield (none, ()))) : Id (Option Bool × Unit)) =
      (compareDigits a b indices, ()) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.forIn_cons, compareDigits]
    split_ifs
    · rfl
    · simpa using ih

theorem compareDigits_correct (a b : ByteArray) (ha : AsciiDigits a) (hb : AsciiDigits b)
    (hs : a.size = b.size) (start count : Nat) (hsize : start + count = a.size)
    (hprefix : ∀ i, i < start → a[i]! = b[i]!) :
    (compareDigits a b (List.range' start count)).getD false = decide (magnitude a < magnitude b) := by
  induction count generalizing start with
  | zero =>
    have he : magnitude a = magnitude b := magnitude_eq_of_bytes a b hs (by
      intro i hi
      exact hprefix i (by omega))
    simp [compareDigits, he]
  | succ count ih =>
    rw [List.range'_succ, compareDigits]
    by_cases he : a[start]! = b[start]!
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false]
      apply ih (start + 1) (by omega)
      intro i hi
      by_cases hi' : i < start
      · exact hprefix i hi'
      · have hindex : i = start := by omega
        simpa [hindex] using he
    · have hflag : (a[start]! != b[start]!) = true := by simp [he]
      simp only [hflag, ite_true, Option.getD_some]
      congr 1
      exact propext (first_difference_lt a b ha hb hs start (by omega) hprefix he).symm

theorem magnitudeLess_correct (a b : ByteArray) (ha : Canonical a) (hb : Canonical b) :
    LeanExe.Examples.RunningSum.magnitudeLess a b = decide (magnitude a < magnitude b) := by
  by_cases hs : a.size = b.size
  · simp only [LeanExe.Examples.RunningSum.magnitudeLess, hs, bne_self_eq_false,
      Bool.false_eq_true, ite_false, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      compareDigits_forIn, Id.run]
    change (compareDigits a b (List.range' 0 b.size)).getD false = _
    exact compareDigits_correct a b ha.1 hb.1 hs 0 b.size (by omega) (by omega)
  · have hflag : (a.size != b.size) = true := by simp [hs]
    simp only [LeanExe.Examples.RunningSum.magnitudeLess, hflag, ite_true, Id.run, pure]
    by_cases hlt : a.size < b.size
    · have hm := magnitude_lt_of_size a b ha hb hlt
      simp [hlt, hm]
    · have hm := magnitude_lt_of_size b a hb ha (by omega)
      simp [hlt, Nat.not_lt.mpr (Nat.le_of_lt hm)]

#print axioms magnitudeLess_correct

end Project.RunningSum
