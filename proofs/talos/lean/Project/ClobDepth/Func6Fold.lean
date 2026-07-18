import Project.ClobDepth.Func6Alloc

/-!
# Fold state for function 6

The per-side fold consumes one order per iteration and calls the level
update for orders on the selected side.  These definitions give the exact
represented levels, match count, heap top, result root, owner local, and
result capacity after any prefix, together with the bounds the loop
invariant carries.
-/

namespace Project.ClobDepth.Func6Fold

open Project.Clob Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Properties

def foldLevels (os : List OrderL) (side : UInt64) (k : Nat) : List LevelL :=
  depthSideL (os.take k) side

def matchCount (os : List OrderL) (side : UInt64) (k : Nat) : Nat :=
  (os.take k).countP (fun order => order.oside == side)

def stepBytes (count : Nat) : Nat :=
  56 + 16 * count

def foldTop (os : List OrderL) (side : UInt64) (g0 : Nat) : Nat → Nat
  | 0 => g0 + 112
  | k + 1 =>
      if os[k]!.oside = side then
        foldTop os side g0 k + 48 +
          fixedArrayBytes (foldLevels os side (k + 1)).length 2
      else
        foldTop os side g0 k

def foldRoot (os : List OrderL) (side : UInt64) (g0 : Nat) : Nat → Nat
  | 0 => g0 + 104
  | k + 1 =>
      if os[k]!.oside = side then foldTop os side g0 k + 48
      else foldRoot os side g0 k

def foldOwner (os : List OrderL) (side : UInt64) (g0 : Nat) : Nat → Nat
  | 0 => g0 + 48
  | k + 1 =>
      if os[k]!.oside = side then foldTop os side g0 k + 48
      else foldOwner os side g0 k

def foldCap (os : List OrderL) (side : UInt64) : Nat → Nat
  | 0 => 8
  | k + 1 =>
      if os[k]!.oside = side then
        fixedArrayBytes (foldLevels os side (k + 1)).length 2
      else foldCap os side k

theorem foldLevels_zero (os : List OrderL) (side : UInt64) :
    foldLevels os side 0 = [] := rfl

theorem foldLevels_succ (os : List OrderL) (side : UInt64) (k : Nat)
    (hk : k < os.length) :
    foldLevels os side (k + 1) =
      if os[k]!.oside = side then
        addLevelL (foldLevels os side k) os[k]!.oprice os[k]!.oqty
      else foldLevels os side k := by
  unfold foldLevels depthSideL
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [Project.Common.getBang_eq hk]

theorem matchCount_succ (os : List OrderL) (side : UInt64) (k : Nat)
    (hk : k < os.length) :
    matchCount os side (k + 1) =
      matchCount os side k + if os[k]!.oside = side then 1 else 0 := by
  unfold matchCount
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.countP_append, List.countP_cons,
    List.countP_nil]
  rw [Project.Common.getBang_eq hk]
  by_cases h : os[k].oside = side
  · simp [h]
  · simp [h]

theorem matchCount_le (os : List OrderL) (side : UInt64) (k : Nat) :
    matchCount os side k ≤ k := by
  calc
    matchCount os side k ≤ (os.take k).length := List.countP_le_length
    _ ≤ k := by simp

theorem addLevelL_length_le (levels : List LevelL) (price qty : UInt64) :
    (addLevelL levels price qty).length ≤ levels.length + 1 := by
  induction levels with
  | nil => simp [addLevelL]
  | cons level levels ih =>
      by_cases h : level.lprice = price
      · simp [addLevelL, h]
      · rw [show addLevelL (level :: levels) price qty =
          level :: addLevelL levels price qty by simp [addLevelL, h]]
        simpa using ih

theorem foldLevels_length_le (os : List OrderL) (side : UInt64) (k : Nat)
    (hk : k ≤ os.length) :
    (foldLevels os side k).length ≤ matchCount os side k := by
  induction k with
  | zero => simp [foldLevels_zero, matchCount]
  | succ k ih =>
      have hk' : k < os.length := by omega
      rw [foldLevels_succ os side k hk', matchCount_succ os side k hk']
      have hPrev := ih (by omega)
      by_cases h : os[k]!.oside = side
      · rw [if_pos h, if_pos h]
        calc
          (addLevelL (foldLevels os side k) os[k]!.oprice
              os[k]!.oqty).length ≤
              (foldLevels os side k).length + 1 :=
            addLevelL_length_le _ _ _
          _ ≤ matchCount os side k + 1 := by omega
      · rw [if_neg h, if_neg h]
        omega

theorem foldLevels_full (os : List OrderL) (side : UInt64) :
    foldLevels os side os.length = depthSideL os side := by
  unfold foldLevels
  rw [List.take_of_length_le (le_refl _)]

theorem foldRoot_add_cap (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) :
    foldRoot os side g0 k + foldCap os side k ≤ foldTop os side g0 k := by
  induction k with
  | zero => simp [foldRoot, foldCap, foldTop]
  | succ k ih =>
      simp only [foldRoot, foldCap, foldTop]
      by_cases h : os[k]!.oside = side
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h]
        exact ih

theorem foldTop_mono (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) :
    foldTop os side g0 k ≤ foldTop os side g0 (k + 1) := by
  simp only [foldTop]
  by_cases h : os[k]!.oside = side
  · rw [if_pos h]
    omega
  · rw [if_neg h]

theorem foldTop_ge (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) : g0 + 112 ≤ foldTop os side g0 k := by
  induction k with
  | zero => simp [foldTop]
  | succ k ih =>
      have hMono := foldTop_mono os side g0 k
      omega

theorem foldRoot_le_top (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) :
    foldRoot os side g0 k ≤ foldTop os side g0 k := by
  have h := foldRoot_add_cap os side g0 k
  omega

theorem foldRoot_ge (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) :
    g0 + 104 ≤ foldRoot os side g0 k := by
  induction k with
  | zero => simp [foldRoot]
  | succ k ih =>
      simp only [foldRoot]
      by_cases h : os[k]!.oside = side
      · rw [if_pos h]
        have hRoot := foldRoot_le_top os side g0 k
        have hCap := foldRoot_add_cap os side g0 k
        omega
      · rw [if_neg h]
        exact ih

theorem foldOwner_ge (os : List OrderL) (side : UInt64) (g0 : Nat)
    (k : Nat) :
    g0 + 48 ≤ foldOwner os side g0 k := by
  induction k with
  | zero => simp [foldOwner]
  | succ k ih =>
      simp only [foldOwner]
      by_cases h : os[k]!.oside = side
      · rw [if_pos h]
        have hRoot := foldRoot_le_top os side g0 k
        have hCap := foldRoot_add_cap os side g0 k
        have hGe := foldRoot_ge os side g0 k
        omega
      · rw [if_neg h]
        exact ih

theorem foldCap_bytes (os : List OrderL) (side : UInt64) (k : Nat) :
    fixedArrayBytes (foldLevels os side k).length 2 ≤ foldCap os side k := by
  induction k with
  | zero =>
      rw [foldLevels_zero]
      unfold foldCap fixedArrayBytes
      simp
  | succ k ih =>
      by_cases hk : k < os.length
      · rw [foldLevels_succ os side k hk]
        unfold foldCap
        by_cases h : os[k]!.oside = side
        · rw [if_pos h, if_pos h]
          rw [foldLevels_succ os side k hk, if_pos h]
        · rw [if_neg h, if_neg h]
          exact ih
      · have hLevels : foldLevels os side (k + 1) = foldLevels os side k := by
          unfold foldLevels
          rw [List.take_of_length_le (by omega),
            List.take_of_length_le (by omega)]
        simp only [foldCap]
        rw [hLevels]
        by_cases h : os[k]!.oside = side
        · rw [if_pos h]
        · rw [if_neg h]
          exact ih

theorem foldTop_le (os : List OrderL) (side : UInt64) (g0 : Nat)
    (count k : Nat) (hk : k ≤ count) (hos : count ≤ os.length) :
    foldTop os side g0 k ≤ g0 + 112 + k * stepBytes count := by
  induction k with
  | zero => simp [foldTop]
  | succ k ih =>
      have hStep : fixedArrayBytes
          (foldLevels os side (k + 1)).length 2 ≤ 8 + 16 * count := by
        have hLen := foldLevels_length_le os side (k + 1) (by omega)
        have hMatch := matchCount_le os side (k + 1)
        unfold fixedArrayBytes
        omega
      simp only [foldTop]
      by_cases h : os[k]!.oside = side
      · rw [if_pos h]
        have hPrev := ih (by omega)
        unfold stepBytes at hPrev ⊢
        rw [Nat.succ_mul]
        omega
      · rw [if_neg h]
        have hPrev := ih (by omega)
        unfold stepBytes at hPrev ⊢
        rw [Nat.succ_mul]
        omega

end Project.ClobDepth.Func6Fold
