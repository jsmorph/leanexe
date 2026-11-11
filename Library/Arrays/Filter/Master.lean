import Library.Arrays.Filter.Compiled
import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas
import Verified.Master

namespace Library.Arrays.Filter

open LeanExe.Dialect LeanExe.Pipeline

theorem removeAll_export :
    ({ name := "removeAll", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem below_export :
    ({ name := "below", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem clearUntil_export :
    ({ name := "clearUntil", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The search loop of `removeAll` gives the index of the first element of `a` equal to `v`, or
the size of `a` when no element is. -/
theorem firstIndex_eq (a : Array UInt64) (v : UInt64) (h : a.size < 2 ^ 64) :
    LeanExe.loop a.size.toUInt64 a.size.toUInt64
        (fun j k => if k == a.size.toUInt64 && a[j.toNat]! == v then j else k) =
      UInt64.ofNat (a.toList.findIdx (· == v)) := by
  have hn := size_toUInt64 a h
  have hf : a.toList.findIdx (· == v) ≤ a.size := by
    simpa using List.findIdx_le_length (p := (· == v)) (xs := a.toList)
  have hl := loop_induction (n := a.size.toUInt64) (init := a.size.toUInt64)
    (f := fun j k => if k == a.size.toUInt64 && a[j.toNat]! == v then j else k)
    (fun m k => k = if a.toList.findIdx (· == v) < m then
      UInt64.ofNat (a.toList.findIdx (· == v)) else a.size.toUInt64) (by simp)
    fun m k hm hk => by
      rw [hn] at hm
      have hml : m < a.toList.length := by simpa using hm
      have hget : a[(UInt64.ofNat m).toNat]! = a[m] := by
        rw [UInt64.toNat_ofNat_of_lt' (show m < 2 ^ 64 by omega), getElem!_pos a m hm]
      subst hk
      rw [hget]
      by_cases hlt : a.toList.findIdx (· == v) < m
      · have hne : UInt64.ofNat (a.toList.findIdx (· == v)) ≠ a.size.toUInt64 := by
          intro he
          have := congrArg UInt64.toNat he
          rw [UInt64.toNat_ofNat_of_lt' (show a.toList.findIdx (· == v) < 2 ^ 64 by omega),
            hn] at this
          omega
        simp [hlt, hne, show a.toList.findIdx (· == v) < m + 1 by omega]
      · by_cases heq : a.toList.findIdx (· == v) = m
        · have hv : a[m] = v := by simpa using ((List.findIdx_eq hml).mp heq).1
          simp [hv, heq]
        · have hv : a[m] ≠ v := by
            simpa using List.not_of_lt_findIdx (p := (· == v)) (xs := a.toList) (i := m)
              (by omega)
          simp [hlt, hv, show ¬ a.toList.findIdx (· == v) < m + 1 by omega]
  rw [hn] at hl
  rw [hl]
  by_cases hlt : a.toList.findIdx (· == v) < a.size
  · simp only [hlt, ↓reduceIte]
  · simp only [hlt, ↓reduceIte]
    rw [show a.size.toUInt64 = UInt64.ofNat a.size from rfl,
      show a.toList.findIdx (· == v) = a.size by omega]

theorem filter_erase (l : List UInt64) (v : UInt64) :
    (l.erase v).filter (· != v) = l.filter (· != v) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = v
    · subst h; simp
    · simp [h, ih]

/-- `removeAll xs v` is `xs` without the elements equal to `v`, for an array of fewer than
`2 ^ 64` elements. -/
theorem removeAll_eq (xs : Array UInt64) (v : UInt64) (h : xs.size < 2 ^ 64) :
    removeAll xs v = xs.filter (· != v) := by
  have hl : (removeAll xs v).size ≤ xs.size ∧
      (removeAll xs v).toList.filter (· != v) = xs.toList.filter (· != v) ∧
      (removeAll xs v).toList.count v = xs.toList.count v - xs.size := by
    have := loop_induction (n := xs.size.toUInt64) (init := xs)
      (f := fun _ acc =>
        let n := acc.size.toUInt64
        let k := LeanExe.loop n n fun j k => if k == n && acc[j.toNat]! == v then j else k
        LeanExe.eraseAt acc k)
      (fun m acc => acc.size ≤ xs.size ∧
        acc.toList.filter (· != v) = xs.toList.filter (· != v) ∧
        acc.toList.count v = xs.toList.count v - m) ⟨le_rfl, rfl, by simp⟩
      fun m acc _ ⟨hsz, hfil, hcnt⟩ => by
        dsimp only
        rw [firstIndex_eq acc v (by omega)]
        have hf : acc.toList.findIdx (· == v) ≤ acc.size := by
          simpa using List.findIdx_le_length (p := (· == v)) (xs := acc.toList)
        have he : (LeanExe.eraseAt acc (UInt64.ofNat (acc.toList.findIdx (· == v)))).toList =
            acc.toList.erase v := by
          rw [LeanExe.eraseAt, Array.toList_eraseIdxIfInBounds,
            UInt64.toNat_ofNat_of_lt' (show acc.toList.findIdx (· == v) < 2 ^ 64 by omega)]
          exact (List.erase_eq_eraseIdx_of_idxOf rfl).symm
        refine ⟨?_, ?_, ?_⟩
        · have := List.length_erase_le (a := v) (l := acc.toList)
          rw [← he] at this
          simp only [Array.length_toList] at this
          omega
        · rw [he, filter_erase, hfil]
        · rw [he, List.count_erase_self, hcnt]
          omega
    rw [size_toUInt64 xs h] at this
    exact this
  obtain ⟨-, hfil, hcnt⟩ := hl
  have hle := List.count_le_length (a := v) (l := xs.toList)
  simp only [Array.length_toList] at hle
  have h0 : (removeAll xs v).toList.count v = 0 := by omega
  rw [← Array.toList_inj, Array.toList_filter, ← hfil]
  symm
  apply List.filter_eq_self.mpr
  intro a ha
  have hav : a ≠ v := fun e => List.count_eq_zero.mp h0 (e ▸ ha)
  simpa using hav

theorem below_go (xs : Array UInt64) (limit count : UInt64) (h : xs.size < 2 ^ 64) :
    ∀ k (s : UInt64 × Array UInt64), s.1.toNat + k = xs.size →
      s.2.toList = (xs.toList.take s.1.toNat).filter (· < limit) → s.2.size ≤ count.toNat →
      (LeanExe.repeatWhile.go (fun s => s.2.size.toUInt64 < count)
        (fun s => (s.1 + 1, if xs[s.1.toNat]! < limit then s.2.push xs[s.1.toNat]! else s.2))
        k s).2.toList = (xs.toList.filter (· < limit)).take count.toNat := by
  intro k
  induction k with
  | zero =>
    intro s hk hs hc
    have hs' : s.2.toList = xs.toList.filter (· < limit) := by
      rw [hs, List.take_of_length_le (by simp; omega)]
    simp only [LeanExe.repeatWhile.go]
    rw [← hs', List.take_of_length_le (by simpa using hc)]
  | succ k ih =>
    intro s hk hs hc
    have hlen : s.2.size ≤ s.1.toNat := by
      have h1 := congrArg List.length hs
      have h2 := List.length_filter_le (fun a => decide (a < limit)) (xs.toList.take s.1.toNat)
      simp only [Array.length_toList, List.length_take] at h1 h2
      omega
    have h1 : (s.1 + 1).toNat = s.1.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    simp only [LeanExe.repeatWhile.go]
    split
    · next hcond =>
      have hlt : s.2.size < count.toNat := by
        have h1 : s.2.size.toUInt64 < count := by simpa using hcond
        rwa [UInt64.lt_iff_toNat_lt, size_toUInt64 s.2 (by omega)] at h1
      have hi : s.1.toNat < xs.toList.length := by simp; omega
      have hget : xs[s.1.toNat]! = xs.toList[s.1.toNat] := get_toList xs (by omega)
      apply ih
      · rw [h1]; omega
      · rw [h1, List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, ← hs, hget]
        split <;> simp_all
      · rw [hget]
        split <;> (try simp only [Array.size_push]) <;> omega
    · next hcond =>
      have hge : count.toNat ≤ s.2.size := by
        have h1 : ¬ s.2.size.toUInt64 < count := by simpa using hcond
        rw [UInt64.lt_iff_toNat_lt, size_toUInt64 s.2 (by omega)] at h1
        omega
      have hsplit : xs.toList = xs.toList.take s.1.toNat ++ xs.toList.drop s.1.toNat :=
        (List.take_append_drop _ _).symm
      rw [hsplit, List.filter_append, ← hs, List.take_append_of_le_length (by simp; omega),
        List.take_of_length_le (by simp; omega)]

/-- `below xs limit count` holds the first `count` elements of `xs` below `limit`, in order, or
all of them when fewer than `count` are below `limit`, for an array of fewer than `2 ^ 64`
elements. -/
theorem below_eq (xs : Array UInt64) (limit count : UInt64) (h : xs.size < 2 ^ 64) :
    below xs limit count = ((xs.toList.filter (· < limit)).take count.toNat).toArray :=
  Array.toList_inj.mp (below_go xs limit count h xs.size.toUInt64.toNat
    (0, LeanExe.build 0 fun i => i) (by rw [size_toUInt64 xs h]; simp)
    (by simp [LeanExe.build]) (by simp [LeanExe.build]))

theorem clearUntil_go (xs : Array UInt64) (v : UInt64) (h : xs.size < 2 ^ 64) :
    ∀ k (s : UInt64 × Array UInt64), s.1.toNat + k = xs.size →
      s.1.toNat ≤ xs.toList.findIdx (· == v) →
      s.2.toList = List.replicate s.1.toNat 0 ++ xs.toList.drop s.1.toNat →
      (LeanExe.repeatWhile.go (fun s => s.1 < s.2.size.toUInt64 && s.2[s.1.toNat]! != v)
        (fun s => (s.1 + 1, s.2.set! s.1.toNat 0)) k s).2.toList =
        List.replicate (xs.toList.findIdx (· == v)) 0 ++
          xs.toList.drop (xs.toList.findIdx (· == v)) := by
  have hf : xs.toList.findIdx (· == v) ≤ xs.size := by
    simpa using List.findIdx_le_length (p := (· == v)) (xs := xs.toList)
  intro k
  induction k with
  | zero =>
    intro s hk hi hs
    simp only [LeanExe.repeatWhile.go]
    rw [hs, show s.1.toNat = xs.toList.findIdx (· == v) by omega]
  | succ k ih =>
    intro s hk hi hs
    have hsz : s.2.size = xs.size := by
      have := congrArg List.length hs
      simp only [Array.length_toList, List.length_append, List.length_replicate,
        List.length_drop] at this
      omega
    have hil : s.1.toNat < xs.toList.length := by simp; omega
    have hget : s.2[s.1.toNat]! = xs.toList[s.1.toNat] := by
      rw [get_toList s.2 (p := s.1.toNat) (by omega)]
      simp [hs, List.getElem_append_right]
    have hlt : s.1 < s.2.size.toUInt64 := by
      rw [UInt64.lt_iff_toNat_lt, size_toUInt64 s.2 (by omega)]
      omega
    simp only [LeanExe.repeatWhile.go]
    by_cases heq : s.1.toNat = xs.toList.findIdx (· == v)
    · have hv : (xs.toList[s.1.toNat] == v) = true := ((List.findIdx_eq hil).mp heq.symm).1
      have hc : (decide (s.1 < s.2.size.toUInt64) && (s.2[s.1.toNat]! != v)) = false := by
        rw [hget]
        simp only [bne, hv, Bool.not_true, Bool.and_false]
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [hs, heq]
    · have hv : (xs.toList[s.1.toNat] == v) = false :=
        List.not_of_lt_findIdx (p := (· == v)) (xs := xs.toList) (i := s.1.toNat) (by omega)
      have hc : (decide (s.1 < s.2.size.toUInt64) && (s.2[s.1.toNat]! != v)) = true := by
        rw [hget]
        simp only [bne, hv, Bool.not_false, Bool.and_true, hlt, decide_true]
      have h1 : (s.1 + 1).toNat = s.1.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      simp only [hc, ↓reduceIte]
      apply ih
      · rw [h1]; omega
      · rw [h1]; omega
      · rw [h1, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, hs,
          List.set_append_right _ _ (by simp), List.drop_eq_getElem_cons hil]
        simp [List.replicate_succ']

/-- `clearUntil xs v` is `xs` with the elements before the first element equal to `v` set to 0,
and with every element set to 0 when no element equals `v`, for an array of fewer than `2 ^ 64`
elements. -/
theorem clearUntil_eq (xs : Array UInt64) (v : UInt64) (h : xs.size < 2 ^ 64) :
    (clearUntil xs v).toList = List.replicate (xs.toList.findIdx (· == v)) 0 ++
      xs.toList.drop (xs.toList.findIdx (· == v)) :=
  clearUntil_go xs v h xs.size.toUInt64.toNat (0, xs) (by rw [size_toUInt64 xs h]; simp)
    (by simp) (by simp)

/-- The export `removeAll`, called on an array of words that the caller moves and a word `v`,
returns the array without the elements equal to `v`. -/
theorem removeAll_master :
    Verified.Master compiled.module compiled.tables "removeAll" compiled.removeAll.bound
      (fun _ => True)
      (fun (x : Moved (Array UInt64) × UInt64) y => y = x.1.val.filter (· != x.2)) :=
  .of_trapFree (.ofA compiled.removeAll.trapFree) nofun removeAll_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => removeAll_eq x.1.val x.2 hxs.values.size_lt

#print axioms removeAll_master

/-- The export `below`, called on an array of words, a limit, and a count `c`, returns the first
`c` elements below the limit, in order, or all of them when fewer than `c` are below it. -/
theorem below_master :
    Verified.Master compiled.module compiled.tables "below" compiled.below.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64 × UInt64) y =>
        y = ((x.1.toList.filter (· < x.2.1)).take x.2.2.toNat).toArray) :=
  .of_trapFree (.ofA compiled.below.trapFree) nofun below_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => below_eq x.1 x.2.1 x.2.2 hxs.values.size_lt

#print axioms below_master

/-- The export `clearUntil`, called on an array of words that the caller moves and a word `v`,
returns the array with the elements before the first element equal to `v` set to 0, and with
every element set to 0 when no element equals `v`. -/
theorem clearUntil_master :
    Verified.Master compiled.module compiled.tables "clearUntil" compiled.clearUntil.bound
      (fun _ => True)
      (fun (x : Moved (Array UInt64) × UInt64) (y : Array UInt64) =>
        let i := x.1.val.toList.findIdx (· == x.2)
        y.toList = List.replicate i 0 ++ x.1.val.toList.drop i) :=
  .of_trapFree (.ofA compiled.clearUntil.trapFree) nofun clearUntil_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x ⟨_, _, _, ⟨_, _, hxs⟩, _⟩ _ => clearUntil_eq x.1.val x.2 hxs.values.size_lt

#print axioms clearUntil_master

end Library.Arrays.Filter
