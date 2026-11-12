import Demos.Rcv.PrintProgram
import Demos.Rcv.ReadProgramMain
import Demos.Rcv.Winner

/-!
The report's printer equals the specification's report.  Every part of the printer appends words to
an array, and `loop_append` reads a loop of such parts as the concatenation of what each pass
appends.  `pushNumber` appends the decimal form of its word through the library's `digitWords`
equations, and a mask's members print in increasing index because the members of a set of
candidates are the bit indices of its mask plus one.
-/

namespace Demos.Rcv.PrintProgram

open LeanExe Demos.Rcv Demos.Rcv.Spec Demos.Rcv.ReadProgram
open Library.Numerics.Decimal.Int64Text (digitCount digitByte digitWords digitCount_toNat
  digitByte_eq digitWords_getElem?)
open scoped List

/-! ## Loops that append -/

/-- A loop whose pass `i` appends `f i` to the array appends the passes' lists in order. -/
theorem loop_append (n : UInt64) (o : Array UInt64) (step : UInt64 → Array UInt64 → Array UInt64)
    (f : UInt64 → List UInt64) (h : ∀ i o, (step i o).toList = o.toList ++ f i) :
    (LeanExe.loop n o step).toList =
      o.toList ++ (List.range n.toNat).flatMap fun i => f (UInt64.ofNat i) := by
  unfold LeanExe.loop
  generalize n.toNat = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.fold_succ, h, ih, List.range_succ, List.flatMap_append]
    simp

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) :
    (l.flatMap fun x => [f x]) = l.map f := by
  induction l <;> simp_all

theorem pushWord_toList (o : Array UInt64) (w len : UInt64) :
    (pushWord o w len).toList = o.toList ++ wordBytes w len.toNat := by
  unfold pushWord
  rw [loop_append len o _ (fun i => [(w >>> (8 * i)) &&& 255]) (fun i o => Array.toList_push),
    flatMap_single]
  rfl

theorem pushNumber_toList (o : Array UInt64) (v : UInt64) :
    (pushNumber o v).toList = o.toList ++ (decimal v.toNat).map UInt8.toUInt64 := by
  show (LeanExe.loop (digitCount v) o fun i o =>
    o.push (digitByte v (digitCount v - 1 - i))).toList = _
  rw [loop_append (digitCount v) o _ (fun i => [digitByte v (digitCount v - 1 - i)])
    (fun i o => Array.toList_push), flatMap_single, ← digitWords_eq]
  refine congrArg (o.toList ++ ·) ?_
  have hL := digitCount_toNat v
  have hlen : (digitWords v.toNat).length ≤ 20 :=
    Library.Numerics.Decimal.Int64Text.digitWords_length_le v.toNat v.toNat_lt
  have hpos : 0 < (digitWords v.toNat).length := by
    rw [digitWords, List.length_map]; exact Nat.length_toDigits_pos
  apply List.ext_getElem?
  intro j
  rw [digitWords_getElem?, List.getElem?_map]
  by_cases hj : j < (digitWords v.toNat).length
  · rw [List.getElem?_range (by rw [hL]; exact hj), ite_eq_left hj, Option.map_some, digitByte_eq]
    have hjN : (UInt64.ofNat j).toNat = j := ofNat_toNat_small (by omega)
    have h1 : (digitCount v - 1).toNat = (digitWords v.toNat).length - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hL]; simp; omega)), hL]
      simp
    have h2 : (digitCount v - 1 - UInt64.ofNat j).toNat = (digitWords v.toNat).length - 1 - j := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hjN, h1]; omega)), h1, hjN]
    rw [h2]
  · rw [List.getElem?_eq_none (by simp only [List.length_range, hL]; omega), ite_eq_right hj]
    rfl

theorem pushRange_toList (o : Array UInt64) (b : Bytes) (_hb : b.data.size < 2 ^ 64) (s e : UInt64)
    (hse : s ≤ e) (he : e.toNat ≤ b.data.size) :
    (pushRange o b s e).toList = o.toList ++ (slice b s.toNat e.toNat).map UInt8.toUInt64 := by
  have hse' := UInt64.le_iff_toNat_le.mp hse
  unfold pushRange
  rw [loop_append _ o _ (fun i => [b.get (s + i)]) (fun i o => Array.toList_push),
    slice_eq_map he, toNat_sub_of_le' hse, flatMap_single]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have := UInt64.toNat_lt e
  simp only [Function.comp_apply, get_eq, toNat_add_ofNat (show s.toNat + i < 2 ^ 64 by omega)]

theorem toBytes_toList (o : Array UInt64) (h : o.size < 2 ^ 64) :
    bytesOf (toBytes o) = o.toList.map UInt64.toUInt8 := by
  have hs : o.size.toUInt64.toNat = o.size := ofNat_toNat_small h
  apply List.ext_getElem
  · simp [bytesOf, toBytes, Bytes.build, hs]
  · intro i h1 h2
    simp only [bytesOf, toBytes, Bytes.build, Array.getElem_toList, List.getElem_map,
      Array.getElem_ofFn]
    rw [ofNat_toNat_small (by simp at h2; omega), getElem!_pos o i (by simpa using h2)]

/-- A list of words below 256 maps back from bytes. -/
theorem map_toUInt8_toUInt64 (L : List UInt8) :
    (L.map UInt8.toUInt64).map UInt64.toUInt8 = L := by
  simp [List.map_map, Function.comp_def]

/-! ## Texts -/

theorem text_cons (l : List UInt8) (ls : List (List UInt8)) :
    text (l :: ls) = l ++ [lf] ++ text ls := by
  simp [text, lf]

theorem text_append (ls ms : List (List UInt8)) : text (ls ++ ms) = text ls ++ text ms := by
  simp [text]

theorem text_nil : text [] = [] := rfl

set_option maxRecDepth 100000 in
theorem pushHead_toList (o : Array UInt64) :
    (pushHead o).toList = o.toList ++
      (text [ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]]).map
        UInt8.toUInt64 := by
  simp only [pushHead, pushWord_toList, List.append_assoc]
  congr 1

/-! ## Sets of candidates -/

/-- A loop whose pass `i`, for `i` below its count, appends `f i`. -/
theorem loop_append' (n : UInt64) (o : Array UInt64) (step : UInt64 → Array UInt64 → Array UInt64)
    (f : Nat → List UInt64)
    (h : ∀ i, i < n.toNat → ∀ o, (step (UInt64.ofNat i) o).toList = o.toList ++ f i) :
    (LeanExe.loop n o step).toList = o.toList ++ (List.range n.toNat).flatMap f := by
  unfold LeanExe.loop
  suffices key : ∀ m, m ≤ n.toNat →
      (Nat.fold m (fun i _ s => step (UInt64.ofNat i) s) o).toList =
        o.toList ++ (List.range m).flatMap f from key _ le_rfl
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Nat.fold_succ, h m (by omega), ih (by omega), List.range_succ, List.flatMap_append]
    simp

theorem shift_bit_one (m k : UInt64) (hk : k.toNat < 64) :
    ((m >>> k) &&& 1 == 1) = m.toNat.testBit k.toNat := by
  have h : ((m >>> k) &&& 1).toNat = m.toNat / 2 ^ k.toNat % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
    simp
  have h2 : m.toNat / 2 ^ k.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
    ← UInt64.toNat_inj, h]
  simp only [UInt64.reduceToNat]

theorem sublist_range'_facts {M : List Nat} {n : Nat} (hM : M <+ List.range' 1 n) :
    M.Pairwise (· < ·) ∧ ∀ i ∈ M, 1 ≤ i ∧ i ≤ n := by
  refine ⟨List.Pairwise.sublist hM List.pairwise_lt_range', fun i hi => ?_⟩
  have := List.mem_range'_1.mp (hM.subset hi)
  omega

/-- The bits of the mask of a set of candidates are its members less one. -/
theorem mask_testBit {M : List Nat} {n : Nat} (hM : M <+ List.range' 1 n) (j : Nat) :
    (mask M).testBit j = decide (j + 1 ∈ M) := by
  obtain ⟨hs, hin⟩ := sublist_range'_facts hM
  have hL : (M.map (· - 1)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    refine hs.imp_of_mem ?_
    intro a b ha hb hab
    have := (hin a ha).1
    omega
  have hmask : mask M = ((M.map (· - 1)).map fun j => 2 ^ j).sum := by
    rw [mask, List.map_map]
    rfl
  have hb := Nat.bitIndices_sum_map_two_pow (List.sortedLT_iff_pairwise.mpr hL)
  rw [← Bool.coe_iff_coe, ← Nat.mem_bitIndices, ← hmask] at *
  rw [hb]
  simp only [List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [show i - 1 + 1 = i by have := (hin i hi).1; omega]
    exact hi
  · intro h
    exact ⟨j + 1, h, by omega⟩

theorem mask_lt {M : List Nat} {n : Nat} (hM : M <+ List.range' 1 n) : mask M < 2 ^ n := by
  obtain ⟨hs, hin⟩ := sublist_range'_facts hM
  have hL : (M.map (· - 1)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    refine hs.imp_of_mem ?_
    intro a b ha hb hab
    have := (hin a ha).1
    omega
  have : mask M = ((M.map (· - 1)).map fun j => 2 ^ j).sum := by
    rw [mask, List.map_map]
    rfl
  rw [this]
  exact sum_lt_of_bits hL (fun j hj => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := hin i hi
    omega)

theorem flatMap_filter_mem {α : Type} (M L : List Nat) (g : Nat → List α) :
    (L.flatMap fun x => if x ∈ M then g x else []) =
      (L.filter fun x => decide (x ∈ M)).flatMap g := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    by_cases hx : x ∈ M
    · simp [hx, ih]
    · simp [hx, ih]

theorem filter_mem_of_sublist {M L : List Nat} (h : M <+ L) (hL : L.Nodup) :
    L.filter (fun x => decide (x ∈ M)) = M := by
  induction h with
  | slnil => rfl
  | @cons l₁ l₂ a h ih =>
    have ha : a ∉ l₁ := fun hm => (List.nodup_cons.mp hL).1 (h.subset hm)
    rw [List.filter_cons, ite_eq_right (by simpa using ha), ih (List.nodup_cons.mp hL).2]
  | @cons_cons l₁ l₂ a h ih =>
    have ha : a ∉ l₂ := (List.nodup_cons.mp hL).1
    rw [List.filter_cons, ite_eq_left (by simp)]
    congr 1
    calc l₂.filter (fun x => decide (x ∈ a :: l₁)) = l₂.filter (fun x => decide (x ∈ l₁)) := by
          apply List.filter_congr
          intro x hx
          have : x ≠ a := fun e => ha (e ▸ hx)
          simp only [List.mem_cons, this, false_or]
      _ = l₁ := ih (List.nodup_cons.mp hL).2

/-- The indices below `n` whose successor is a member of a set of candidates, in order, give the
members in order. -/
theorem flatMap_range_mem {α : Type} {M : List Nat} {n : Nat} (hM : M <+ List.range' 1 n)
    (g : Nat → List α) :
    ((List.range n).flatMap fun i => if i + 1 ∈ M then g (i + 1) else []) = M.flatMap g := by
  have h1 : ((List.range n).flatMap fun i => if i + 1 ∈ M then g (i + 1) else []) =
      (List.range' 1 n).flatMap fun x => if x ∈ M then g x else [] := by
    rw [List.range'_eq_map_range, List.flatMap_map]
    congr 1
    funext i
    rw [Nat.add_comm]
  rw [h1, flatMap_filter_mem, filter_mem_of_sublist hM List.nodup_range']

theorem spaced_flatMap (a : List UInt8) (ms : List (List UInt8)) :
    spaced (a :: ms) = a ++ ms.flatMap fun m => sp :: m := by
  induction ms generalizing a with
  | nil => simp [spaced]
  | cons m ms ih =>
    rw [spaced_cons_cons, ih m]
    simp

/-- `pushMembers` prints a space and the index of each member of a set of candidates. -/
theorem pushMembers_toList (o : Array UInt64) {M : List Nat} {n : Nat} (hn : n ≤ 63)
    (hM : M <+ List.range' 1 n) :
    (pushMembers o (UInt64.ofNat (mask M)) (UInt64.ofNat n)).toList =
      o.toList ++ (M.flatMap fun i => sp :: decimal i).map UInt8.toUInt64 := by
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have hmN : (UInt64.ofNat (mask M)).toNat = mask M :=
    ofNat_toNat_small
      (Nat.lt_of_lt_of_le (mask_lt hM) (Nat.pow_le_pow_right (by decide) (by omega)))
  unfold pushMembers
  have hfm := flatMap_range_mem hM (fun i => (sp :: decimal i).map UInt8.toUInt64)
  rw [loop_append' _ o _ (fun i => if i + 1 ∈ M then
      (sp :: decimal (i + 1)).map UInt8.toUInt64 else []), hnN, hfm, List.map_flatMap]
  · intro i hi o
    rw [hnN] at hi
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    have hi1 : (UInt64.ofNat i + 1).toNat = i + 1 := by
      rw [UInt64.toNat_add, hiN]; simp; omega
    rw [shift_bit_one _ _ (by rw [hiN]; omega), hmN, hiN, mask_testBit hM]
    by_cases hm : i + 1 ∈ M
    · rw [decide_eq_true hm, ite_eq_left rfl, ite_eq_left hm, pushNumber_toList, Array.toList_push,
        hi1]
      simp [sp]
    · rw [decide_eq_false hm, ite_eq_right (by simp), ite_eq_right hm]
      simp

/-! ## Lines of a round -/

theorem pushLine_toList (o : Array UInt64) (w1 l1 w2 l2 v : UInt64) :
    (pushLine o w1 l1 w2 l2 v).toList =
      o.toList ++ wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat ++
        (decimal v.toNat).map UInt8.toUInt64 ++ [10] := by
  simp [pushLine, pushNumber_toList, pushWord_toList, List.append_assoc]

/-- A line of a text of two words and a number. -/
theorem pushLine_text (o : Array UInt64) (w1 l1 w2 l2 v : UInt64) (T : String)
    (hT : (ascii T ++ [sp]).map UInt8.toUInt64 = wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat) :
    (pushLine o w1 l1 w2 l2 v).toList =
      o.toList ++ (spaced [ascii T, decimal v.toNat] ++ [lf]).map UInt8.toUInt64 := by
  rw [pushLine_toList, spaced_two]
  have : (ascii T ++ sp :: decimal v.toNat ++ [lf]).map UInt8.toUInt64 =
      (ascii T ++ [sp]).map UInt8.toUInt64 ++ (decimal v.toNat).map UInt8.toUInt64 ++ [10] := by
    simp [lf]
  rw [this, hT]
  simp

/-- A line of a text of three words and a number. -/
theorem pushLine_text3 (o : Array UInt64) (w0 l0 w1 l1 w2 l2 v : UInt64) (T : String)
    (hT : (ascii T ++ [sp]).map UInt8.toUInt64 =
      wordBytes w0 l0.toNat ++ wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat) :
    (pushLine (pushWord o w0 l0) w1 l1 w2 l2 v).toList =
      o.toList ++ (spaced [ascii T, decimal v.toNat] ++ [lf]).map UInt8.toUInt64 := by
  rw [pushLine_toList, pushWord_toList, spaced_two]
  have : (ascii T ++ sp :: decimal v.toNat ++ [lf]).map UInt8.toUInt64 =
      (ascii T ++ [sp]).map UInt8.toUInt64 ++ (decimal v.toNat).map UInt8.toUInt64 ++ [10] := by
    simp [lf]
  rw [this, hT]
  simp

theorem lookup_map {S : List Nat} (hS : S.Nodup) (f : Nat → Nat) {i : Nat} (hi : i ∈ S) :
    (S.map fun j => (j, f j)).lookup i = some (f i) := by
  induction S with
  | nil => simp at hi
  | cons a S ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases hia : i = a
    · subst hia; simp
    · have : (i == a) = false := by simpa using hia
      rw [this]
      exact ih (List.nodup_cons.mp hS).2 (by simpa [hia] using hi)

/-- The votes lines of the members of `S`, each with its votes `f i`. -/
theorem pushVotes_toList (o res : Array UInt64) {S : List Nat} {n base : Nat} (hn : n ≤ 63)
    (hS : S <+ List.range' 1 n) (f : Nat → Nat) (hf : ∀ i ∈ S, f i < 2 ^ 64)
    (hbase : base + n + 9 < 2 ^ 64) (hmask : res[base]! = UInt64.ofNat (mask S))
    (hv : ∀ i < n, i + 1 ∈ S → res[base + 2 + i]! = UInt64.ofNat (f (i + 1))) :
    (pushVotes o res (UInt64.ofNat n) (UInt64.ofNat base)).toList =
      o.toList ++ (text ((S.map fun i => (i, f i)).map fun x : Nat × Nat =>
        spaced [ascii "votes", decimal x.1, decimal x.2])).map UInt8.toUInt64 := by
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have hbN : (UInt64.ofNat base).toNat = base := ofNat_toNat_small (by omega)
  have hmN : (UInt64.ofNat (mask S)).toNat = mask S :=
    ofNat_toNat_small
      (Nat.lt_of_lt_of_le (mask_lt hS) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hfm := flatMap_range_mem hS (fun i =>
    (spaced [ascii "votes", decimal i, decimal (f i)] ++ [lf]).map UInt8.toUInt64)
  unfold pushVotes
  rw [hbN, hmask]
  rw [loop_append' _ o _ (fun i => if i + 1 ∈ S then
      (spaced [ascii "votes", decimal (i + 1), decimal (f (i + 1))] ++ [lf]).map UInt8.toUInt64
      else []), hnN, hfm]
  · simp only [text, List.map_map, List.flatMap_map, List.map_flatMap]
    rfl
  · intro i hi o
    rw [hnN] at hi
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    have hi1 : (UInt64.ofNat i + 1).toNat = i + 1 := by
      rw [UInt64.toNat_add, hiN]; simp; omega
    rw [shift_bit_one _ _ (by rw [hiN]; omega), hmN, hiN, mask_testBit hS]
    by_cases hm : i + 1 ∈ S
    · have hidx : (UInt64.ofNat base + 2 + UInt64.ofNat i).toNat = base + 2 + i := by
        rw [UInt64.toNat_add, UInt64.toNat_add, hbN, hiN]; simp; omega
      rw [decide_eq_true hm, ite_eq_left rfl, ite_eq_left hm, Array.toList_push, pushNumber_toList,
        Array.toList_push, pushNumber_toList, pushWord_toList, hi1, hidx, hv i hi hm,
        ofNat_toNat_small (hf _ hm)]
      have hw : wordBytes 0x207365746f76 6 = (ascii "votes ").map UInt8.toUInt64 := by decide
      rw [show (6 : UInt64).toNat = 6 from rfl, hw, spaced_cons_cons, spaced_two]
      simp [sp]
      rfl
    · rw [decide_eq_false hm, ite_eq_right (by simp), ite_eq_right hm]
      simp

/-! ## Eliminations -/

/-- The words of an elimination in a round's words: its code and the masks of the eliminated
candidates and of the tied set. -/
def elimWords : Option Elimination → List Nat
  | none => [0, 0, 0]
  | some (.lowest i) => [1, mask [i], 0]
  | some (.order tied i) => [2, mask [i], mask tied]
  | some (.batch members) => [3, mask members, 0]

/-- The members of an elimination are candidates from 1 to `n` in increasing order. -/
def ElimOk (n : Nat) : Option Elimination → Prop
  | none => True
  | some (.lowest i) => [i] <+ List.range' 1 n
  | some (.order tied i) => tied <+ List.range' 1 n ∧ [i] <+ List.range' 1 n
  | some (.batch members) => members <+ List.range' 1 n

/-- The lines of an elimination, or none. -/
def elimLines : Option Elimination → List (List UInt8)
  | some e => eliminationLines e
  | none => []

theorem members_line (o : Array UInt64) (w1 l1 w2 l2 : UInt64) (T : String)
    (hT : (ascii T).map UInt8.toUInt64 = wordBytes w1 l1.toNat ++ wordBytes w2 l2.toNat)
    {M : List Nat} {n : Nat} (hn : n ≤ 63) (hM : M <+ List.range' 1 n) :
    ((pushMembers (pushWord (pushWord o w1 l1) w2 l2) (UInt64.ofNat (mask M))
      (UInt64.ofNat n)).push 10).toList =
      o.toList ++ (spaced (ascii T :: M.map decimal) ++ [lf]).map UInt8.toUInt64 := by
  rw [Array.toList_push, pushMembers_toList _ hn hM, pushWord_toList, pushWord_toList,
    spaced_flatMap, List.flatMap_map]
  simp only [List.map_append, hT, List.append_assoc]
  rfl

theorem pushElimination_toList (o : Array UInt64) {n : Nat} (hn : n ≤ 63) (e : Option Elimination)
    (he : ElimOk n e) :
    (pushElimination o (UInt64.ofNat ((elimWords e).getD 0 0))
      (UInt64.ofNat ((elimWords e).getD 1 0)) (UInt64.ofNat ((elimWords e).getD 2 0))
      (UInt64.ofNat n)).toList = o.toList ++ (text (elimLines e)).map UInt8.toUInt64 := by
  have hEL : ∀ T : String, ∀ w l, (ascii T).map UInt8.toUInt64 =
      wordBytes 0x74616e696d696c65 8 ++ wordBytes w l → True := fun _ _ _ _ => trivial
  clear hEL
  cases e with
  | none =>
    simp only [elimWords, List.getD_cons_zero, pushElimination]
    simp [elimLines, text]
  | some e =>
    cases e with
    | lowest i =>
      simp only [elimWords, List.getD_cons_zero, List.getD_cons_succ, pushElimination]
      rw [ite_eq_left (by rfl)]
      rw [members_line o _ 8 _ 8 "eliminate lowest" (by decide) hn he]
      simp [elimLines, eliminationLines, text, lf]
    | order tied i =>
      obtain ⟨ht, hi⟩ := he
      simp only [elimWords, List.getD_cons_zero, List.getD_cons_succ, pushElimination]
      rw [ite_eq_right (by decide), ite_eq_left (by rfl)]
      rw [members_line _ _ 8 _ 7 "eliminate order" (by decide) hn hi]
      have htie : ((pushMembers (pushWord o 0x656974 3) (UInt64.ofNat (mask tied))
          (UInt64.ofNat n)).push 10).toList =
          o.toList ++ (spaced (ascii "tie" :: tied.map decimal) ++ [lf]).map UInt8.toUInt64 := by
        rw [Array.toList_push, pushMembers_toList _ hn ht, pushWord_toList, spaced_flatMap,
          List.flatMap_map]
        simp only [List.map_append, List.append_assoc]
        rw [show wordBytes 0x656974 (3 : UInt64).toNat = (ascii "tie").map UInt8.toUInt64 by decide]
        rfl
      rw [htie]
      simp [elimLines, eliminationLines, text, lf]
    | batch members =>
      simp only [elimWords, List.getD_cons_zero, List.getD_cons_succ, pushElimination]
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by rfl)]
      rw [members_line o _ 8 _ 7 "eliminate batch" (by decide) hn he]
      simp [elimLines, eliminationLines, text, lf]

/-! ## Rounds -/

theorem roundWords_eq (n : Nat) (rd : Round) :
    roundWords n rd = [mask (rd.tally.votes.map fun x : Nat × Nat => x.1), rd.tally.continuing] ++
      (List.range' 1 n).map (fun i : Nat => (rd.tally.votes.lookup i).getD 0) ++
      [rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
      elimWords rd.elimination := by
  unfold roundWords elimWords
  rcases rd with ⟨t, e⟩
  rcases e with _ | e
  · rfl
  · cases e <;> rfl

theorem roundWords_length (n : Nat) (rd : Round) : (roundWords n rd).length = n + 9 := by
  rw [roundWords_eq]
  rcases rd with ⟨t, e⟩
  rcases e with _ | e
  · simp [elimWords]
  · cases e <;> (simp [elimWords]; try omega)

/-- The words of round `rd` stand at position `base` of `res`. -/
def RoundAt (res : Array UInt64) (base n : Nat) (rd : Round) : Prop :=
  ∀ j < n + 9, res[base + j]! = UInt64.ofNat ((roundWords n rd).getD j 0)

theorem getD_round_head (n : Nat) (rd : Round) :
    (roundWords n rd).getD 0 0 = mask (rd.tally.votes.map fun x : Nat × Nat => x.1) ∧
      (roundWords n rd).getD 1 0 = rd.tally.continuing := by
  rw [roundWords_eq]
  simp [List.getD_eq_getElem?_getD]

theorem getD_round_vote (n : Nat) (rd : Round) (i : Nat) (hi : i < n) :
    (roundWords n rd).getD (2 + i) 0 = (rd.tally.votes.lookup (i + 1)).getD 0 := by
  rw [roundWords_eq, List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
  simp [Nat.add_comm, hi]

theorem getD_round_tail (n : Nat) (rd : Round) (j : Nat) :
    (roundWords n rd).getD (n + 2 + j) 0 =
      ([rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
        elimWords rd.elimination).getD j 0 := by
  rw [roundWords_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  congr 2
  simp
  omega

theorem lookup_getD {S : List Nat} (hS : S.Nodup) (f : Nat → Nat) (i : Nat) (hi : i ∈ S) :
    ((S.map fun j => (j, f j)).lookup i).getD 0 = f i := by
  rw [lookup_map hS f hi]
  rfl

/-- `pushRoundLines` prints the lines of round `r`. -/
theorem pushRoundLines_toList (o res : Array UInt64) {n base r : Nat} (hn : n ≤ 63) (rd : Round)
    (S : List Nat) (f : Nat → Nat) (hvotes : rd.tally.votes = S.map fun i => (i, f i))
    (hS : S <+ List.range' 1 n) (hf : ∀ i ∈ S, f i < 2 ^ 64)
    (hcounts : rd.tally.continuing < 2 ^ 64 ∧ rd.tally.blank < 2 ^ 64 ∧
      rd.tally.uncounted < 2 ^ 64 ∧ rd.tally.overvote < 2 ^ 64 ∧ rd.tally.exhausted < 2 ^ 64)
    (he : ElimOk n rd.elimination) (hbase : base + n + 9 < 2 ^ 64) (hr : r < 2 ^ 64)
    (hres : RoundAt res base n rd) :
    (pushRoundLines o res (UInt64.ofNat n) (UInt64.ofNat base) (UInt64.ofNat r)).toList =
      o.toList ++ (text (roundLines r rd)).map UInt8.toUInt64 := by
  obtain ⟨hT, hbl, hun, hov, hex⟩ := hcounts
  have hSnd : S.Nodup := (List.Pairwise.sublist hS List.pairwise_lt_range').nodup
  have hbN : (UInt64.ofNat base).toNat = base := ofNat_toNat_small (by omega)
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have hrN : (UInt64.ofNat r).toNat = r := ofNat_toNat_small hr
  have hkeys : rd.tally.votes.map (fun x : Nat × Nat => x.1) = S := by
    rw [hvotes, List.map_map]
    exact List.map_id' S
  have idx : ∀ c : UInt64, c.toNat ≤ 8 → (UInt64.ofNat base + c).toNat = base + c.toNat := by
    intro c hc
    rw [UInt64.toNat_add, hbN]
    omega
  have idxn : ∀ c : UInt64, c.toNat ≤ 8 → (UInt64.ofNat base + c + UInt64.ofNat n).toNat =
      base + c.toNat + n := by
    intro c hc
    rw [UInt64.toNat_add, idx c hc, hnN]
    omega
  have at_ : ∀ j < n + 9, res[base + j]! = UInt64.ofNat ((roundWords n rd).getD j 0) := hres
  -- the words of the round
  have w0 : res[base]! = UInt64.ofNat (mask S) := by
    have := at_ 0 (by omega)
    rw [Nat.add_zero, (getD_round_head n rd).1, hkeys] at this
    exact this
  have w1 : res[base + 1]! = UInt64.ofNat rd.tally.continuing := by
    have := at_ 1 (by omega)
    rw [(getD_round_head n rd).2] at this
    exact this
  have wv : ∀ i < n, i + 1 ∈ S → res[base + 2 + i]! = UInt64.ofNat (f (i + 1)) := by
    intro i hi hm
    have := at_ (2 + i) (by omega)
    rw [getD_round_vote n rd i hi, hvotes, lookup_getD hSnd f _ hm, ← Nat.add_assoc] at this
    exact this
  have wt : ∀ j < 7, res[base + 2 + n + j]! = UInt64.ofNat
      (([rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
        elimWords rd.elimination).getD j 0) := by
    intro j hj
    have := at_ (n + 2 + j) (by omega)
    rw [getD_round_tail] at this
    rw [show base + 2 + n + j = base + (n + 2 + j) by omega]
    exact this
  unfold pushRoundLines
  simp only []
  -- reads of the words
  rw [show (UInt64.ofNat base + 1).toNat = base + 1 from idx 1 (by decide), w1,
    show (UInt64.ofNat base + 2 + UInt64.ofNat n).toNat = base + 2 + n from idxn 2 (by decide),
    show (UInt64.ofNat base + 3 + UInt64.ofNat n).toNat = base + 2 + n + 1 by
      rw [idxn 3 (by decide)]; simp; omega,
    show (UInt64.ofNat base + 4 + UInt64.ofNat n).toNat = base + 2 + n + 2 by
      rw [idxn 4 (by decide)]; simp; omega,
    show (UInt64.ofNat base + 5 + UInt64.ofNat n).toNat = base + 2 + n + 3 by
      rw [idxn 5 (by decide)]; simp; omega,
    show (UInt64.ofNat base + 6 + UInt64.ofNat n).toNat = base + 2 + n + 4 by
      rw [idxn 6 (by decide)]; simp; omega,
    show (UInt64.ofNat base + 7 + UInt64.ofNat n).toNat = base + 2 + n + 5 by
      rw [idxn 7 (by decide)]; simp; omega,
    show (UInt64.ofNat base + 8 + UInt64.ofNat n).toNat = base + 2 + n + 6 by
      rw [idxn 8 (by decide)]; simp; omega]
  rw [show base + 2 + n = base + 2 + n + 0 from rfl, wt 0 (by omega), wt 1 (by omega),
    wt 2 (by omega), wt 3 (by omega), wt 4 (by omega), wt 5 (by omega), wt 6 (by omega)]
  have hel : ([rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
      elimWords rd.elimination).getD 4 0 = (elimWords rd.elimination).getD 0 0 ∧
      ([rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
      elimWords rd.elimination).getD 5 0 = (elimWords rd.elimination).getD 1 0 ∧
      ([rd.tally.blank, rd.tally.uncounted, rd.tally.overvote, rd.tally.exhausted] ++
      elimWords rd.elimination).getD 6 0 = (elimWords rd.elimination).getD 2 0 := by
    simp [List.getD_eq_getElem?_getD]
  rw [hel.1, hel.2.1, hel.2.2, pushElimination_toList _ hn _ he]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, Option.getD_some]
  rw [pushLine_text3 _ _ _ _ _ _ _ _ "inactive exhausted" (by decide),
    pushLine_text3 _ _ _ _ _ _ _ _ "inactive overvote" (by decide),
    pushLine_text3 _ _ _ _ _ _ _ _ "inactive uncounted" (by decide),
    pushLine_text _ _ _ _ _ _ "inactive blank" (by decide),
    pushVotes_toList _ res hn hS f hf (by omega) w0 wv,
    pushLine_text _ _ _ _ _ _ "continuing" (by decide),
    pushLine_text _ _ _ _ _ _ "round" (by decide)]
  rw [ofNat_toNat_small hT, ofNat_toNat_small hbl, ofNat_toNat_small hun, ofNat_toNat_small hov,
    ofNat_toNat_small hex, hrN]
  simp only [roundLines, text_append, text_cons, text_nil, List.map_append, List.append_assoc,
    hvotes, elimLines]
  rcases rd.elimination with _ | e <;> simp [text]

/-! ## Facts of the count that the printer needs -/

open Demos.Rcv.Rounds in
/-- The candidates that an elimination of `rule` names are members of the round's continuing set,
in its order. -/
theorem elimOk_of_rule {order : List Nat} {t : Tally} {e : Elimination} {n : Nat}
    (hS : (t.votes.map fun x : Nat × Nat => x.1) <+ List.range' 1 n)
    (h : rule order t = .eliminate e) : ElimOk n (some e) := by
  obtain ⟨hpos, -, hcases⟩ := rule_eq_eliminate h
  have hsub : ∀ p : Nat × Nat → Bool,
      ((t.votes.filter p).map fun x : Nat × Nat => x.1) <+ List.range' 1 n :=
    fun p => (List.filter_sublist.map _).trans hS
  rcases hcases with ⟨s, hs, rfl⟩ | ⟨-, ⟨z, hz, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨-, ⟨x, -, -, rfl⟩, -⟩ := batch_some hs
    exact hsub _
  · show [z] <+ List.range' 1 n
    rw [← hz]
    exact hsub _
  · have hne : ruleTied t.votes ≠ [] := by
      rw [ruleTied_eq_fewest]
      exact fewest_ne_nil (votes_ne_nil hpos)
    refine ⟨hsub _, ?_⟩
    exact List.singleton_sublist.mpr ((hsub _).subset (latest_mem hne))

open Demos.Rcv.Rounds in
/-- The rounds of the count of `n` candidates: each holds the votes of its continuing set, a set of
candidates from 1 to `n` in increasing order, and names in its elimination only such candidates. -/
theorem count_round_facts (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    ∀ rd ∈ (count kinds order ballots).rounds, ∃ S : List Nat,
      rd.tally.votes = S.map (fun i => (i, (ballots.map (interpret kinds S)).count (.counts i))) ∧
      S <+ List.range' 1 kinds.length ∧ ElimOk kinds.length rd.elimination ∧
      rd.tally.continuing ≤ ballots.length ∧ rd.tally.blank ≤ ballots.length ∧
      rd.tally.uncounted ≤ ballots.length ∧ rd.tally.overvote ≤ ballots.length ∧
      rd.tally.exhausted ≤ ballots.length := by
  intro rd hrd
  obtain ⟨htally, hsub, helim⟩ := (count_trace kinds order ballots).mem rd hrd
  have hS : continuingSet rd <+ List.range' 1 kinds.length := hsub.trans (countedSet_sublist kinds)
  have hnd : (continuingSet rd).Nodup := (List.Pairwise.sublist hS List.pairwise_lt_range').nodup
  refine ⟨continuingSet rd, ?_, hS, ?_, ?_⟩
  · rw [htally]
    rfl
  · cases he : rd.elimination with
    | none => trivial
    | some e =>
      have hkeys : (rd.tally.votes.map fun x : Nat × Nat => x.1) = continuingSet rd := rfl
      exact elimOk_of_rule (by rw [hkeys]; exact hS) (helim e he)
  · have hsum := tally_sum (interpret kinds) (continuingSet rd) ballots hnd
      (fun ps i h => interpret_counts h)
    rw [← htally] at hsum
    have : rd.tally.continuing = (rd.tally.votes.map fun x : Nat × Nat => x.2).sum := rfl
    omega

open Demos.Rcv.Rounds in
theorem trace_winner {interp : List Nat → List UInt64 → Outcome} {order : List Nat}
    {ballots : List (List UInt64)} {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp (rule order) ballots C rds w) : ∀ i, w = some i → i ∈ C := by
  induction h with
  | @last C w hr =>
    intro i hi
    rcases rule_eq_winner hr with ⟨x, hx, -, hw⟩ | ⟨-, hw⟩
    · rw [hi] at hw
      cases hw
      have := List.mem_map_of_mem (f := fun x : Nat × Nat => x.1) hx
      rwa [tally_votes_fst] at this
    · rw [hi] at hw; cases hw
  | @step C e rds w hr _ ih =>
    intro i hi
    exact (List.mem_filter.mp (ih i hi)).1

open Demos.Rcv.Rounds in
/-- The winner of the count of `n` candidates, when there is one, is a candidate from 1 to `n`. -/
theorem count_winner (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    (i : Nat) (h : (count kinds order ballots).winner = some i) : 1 ≤ i ∧ i ≤ kinds.length :=
  mem_countedSet (trace_winner (count_trace kinds order ballots) i h)

/-! ## The header lines -/

theorem prefix_unique {c : UInt8} :
    ∀ {a a' r r' : List UInt8}, c ∉ a → c ∉ a' → a ++ c :: r = a' ++ c :: r' → a = a'
  | [], [], _, _, _, _, _ => rfl
  | [], x :: a', _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | x :: a, [], _, _, h, _, hh => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hh
    exact absurd (hh.1 ▸ List.mem_cons_self) h
  | x :: a, y :: a', r, r', h, h', hh => by
    simp only [List.cons_append, List.cons.injEq] at hh
    rw [hh.1, prefix_unique (fun m => h (List.mem_cons_of_mem x m))
      (fun m => h' (List.mem_cons_of_mem y m)) hh.2]

/-- The position that `findByte` finds when the bytes from `p` are a line and its LF. -/
theorem findByte_line (b : Bytes) (p e : UInt64) (hpe : p ≤ e) (he : e.toNat ≤ b.data.size)
    {l rest : List UInt8} (hl : lf ∉ l) (hs : slice b p.toNat e.toNat = l ++ lf :: rest) :
    (findByte b 10 p e).toNat = p.toNat + l.length := by
  obtain ⟨q1, q2, hnot, hsplit⟩ := findByte_slice b 10 lf rfl p e hpe he
  have q1' := UInt64.le_iff_toNat_le.mp q1
  have q2' := UInt64.le_iff_toNat_le.mp q2
  rw [hs] at hsplit
  by_cases hq : findByte b 10 p e < e
  · rw [ite_eq_left hq] at hsplit
    have := prefix_unique hl hnot hsplit
    rw [this, slice_length (q2'.trans he)]
    omega
  · rw [ite_eq_right hq, List.append_nil] at hsplit
    exact absurd (hsplit ▸ List.mem_append_right l List.mem_cons_self) hnot

theorem text_length_take (L : List (List UInt8)) (k : Nat) (hk : k < L.length) :
    (text (L.take (k + 1))).length = (text (L.take k)).length + L[k].length + 1 := by
  rw [List.take_add_one, text_append, List.getElem?_eq_getElem hk]
  simp [text]
  omega

theorem text_drop (L : List (List UInt8)) (k : Nat) :
    (text L).drop (text (L.take k)).length = text (L.drop k) := by
  conv_lhs => rw [← List.take_append_drop k L, text_append]
  simp

/-- After `m` passes, the loop of `printReport` stands after the LF of line `m`. -/
theorem header_loop (b : Bytes) (hb : b.data.size < 2 ^ 64) (L : List (List UInt8))
    (hL : ∀ l ∈ L, lf ∉ l) (hw : bytesOf b = text L) (m : UInt64) (hm : m.toNat ≤ L.length) :
    (LeanExe.loop m (0 : UInt64) fun _ p => findByte b 10 p b.size + 1).toNat =
      (text (L.take m.toNat)).length := by
  have hsz := size_toNat b hb
  have htext : (text L).length = b.data.size := by rw [← hw]; simp
  have key := LeanExe.Dialect.loop_induction (n := m) (init := (0 : UInt64))
    (f := fun _ p => findByte b 10 p b.size + 1)
    (fun k p => p.toNat = (text (L.take k)).length) (by simp [text])
    (by
      intro k p hk hp
      have hkL : k < L.length := by omega
      have hle : (text (L.take k)).length + L[k].length + 1 ≤ b.data.size := by
        rw [← text_length_take L k hkL, ← htext]
        have := text_append (L.take (k + 1)) (L.drop (k + 1))
        rw [List.take_append_drop] at this
        rw [this, List.length_append]
        omega
      have hp' : p ≤ b.size := UInt64.le_iff_toNat_le.mpr (by rw [hp, hsz]; omega)
      have hs : slice b p.toNat b.data.size = L[k] ++ lf :: text (L.drop (k + 1)) := by
        rw [slice_end, hw, hp, text_drop, List.drop_eq_getElem_cons hkL, text_cons]
        simp
      have hf := findByte_line b p b.size hp' (by rw [hsz]) (hL _ (List.getElem_mem hkL)) (by
        rw [hsz]; exact hs)
      show (findByte b 10 p b.size + 1).toNat = _
      rw [UInt64.toNat_add, hf, text_length_take L k hkL, hp]
      simp
      omega)
  exact key

/-! ## The result words -/

theorem getElem!_toArray_eq (l : List UInt64) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  rw [getElem!_def, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_toArray]
  cases l[i]? <;> rfl

theorem getD_flatMap_block {m : Nat} (f : Round → List Nat) (hf : ∀ x, (f x).length = m) :
    ∀ (rds : List Round) (r j : Nat) (hr : r < rds.length), j < m →
      (rds.flatMap f).getD (r * m + j) 0 = (f rds[r]).getD j 0
  | [], r, j, hr, _ => by simp at hr
  | x :: rds, r, j, hr, hj => by
    rw [List.flatMap_cons]
    cases r with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [hf]; exact hj)]
    | succ r =>
      simp only [List.getElem_cons_succ, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hf]; rw [Nat.succ_mul]; omega), hf,
        show (r + 1) * m + j - m = r * m + j by rw [Nat.succ_mul]; omega]
      have := getD_flatMap_block f hf rds r j (by simp at hr; omega) hj
      simpa [List.getD_eq_getElem?_getD] using this

theorem resultWords_toList (n : Nat) (k : Count) :
    resultWords n k = ([1, k.rounds.length] ++ k.rounds.flatMap (roundWords n) ++
      [k.winner.getD 0]).map Nat.toUInt64 := rfl

theorem resultWords_rounds (n : Nat) (k : Count) :
    (resultWords n k).toArray[1]! = UInt64.ofNat k.rounds.length := by
  rw [getElem!_toArray_eq, resultWords_toList]
  rfl

theorem flatMap_roundWords_length (n : Nat) (rds : List Round) :
    (rds.flatMap (roundWords n)).length = rds.length * (n + 9) := by
  induction rds with
  | nil => simp
  | cons x rds ih => simp [List.flatMap_cons, roundWords_length, ih]; ring

theorem resultWords_round (n : Nat) (k : Count) (r j : Nat) (hr : r < k.rounds.length)
    (hj : j < n + 9) :
    (resultWords n k).toArray[2 + r * (n + 9) + j]! =
      UInt64.ofNat ((roundWords n k.rounds[r]).getD j 0) := by
  have hlen := flatMap_roundWords_length n k.rounds
  have hlt : r * (n + 9) + j < k.rounds.length * (n + 9) := by
    have : (r + 1) * (n + 9) ≤ k.rounds.length * (n + 9) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    omega
  have h2 : [1, k.rounds.length].length ≤ 2 + r * (n + 9) + j := by
    simp only [List.length_cons, List.length_nil]; omega
  have h3 : 2 + r * (n + 9) + j - [1, k.rounds.length].length = r * (n + 9) + j := by
    simp only [List.length_cons, List.length_nil]; omega
  rw [getElem!_toArray_eq, resultWords_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.append_assoc, List.getElem?_append_right h2, h3,
    List.getElem?_append_left (by rw [hlen]; exact hlt)]
  have := getD_flatMap_block (roundWords n) (roundWords_length n) k.rounds r j hr hj
  rw [List.getD_eq_getElem?_getD] at this
  have hlt' : r * (n + 9) + j < (k.rounds.flatMap (roundWords n)).length := by rw [hlen]; omega
  rw [List.getElem?_eq_getElem hlt'] at this ⊢
  simp only [Option.getD_some] at this
  simp only [Option.map_some, Option.getD_some, this]

theorem resultWords_winner (n : Nat) (k : Count) :
    (resultWords n k).toArray[2 + k.rounds.length * (n + 9)]! = UInt64.ofNat (k.winner.getD 0) := by
  have hlen := flatMap_roundWords_length n k.rounds
  have h2 : ([1, k.rounds.length] ++ k.rounds.flatMap (roundWords n)).length =
      2 + k.rounds.length * (n + 9) := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
  rw [getElem!_toArray_eq, resultWords_toList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_right (Nat.le_of_eq h2), h2, Nat.sub_self]
  rfl

/-! ## The rounds -/

theorem flatMap_range_zipIdx (L : List Round) (d : Round) (G : Nat → Round → List UInt64) :
    ((List.range L.length).flatMap fun i => G (i + 1) (L.getD i d)) =
      (L.zipIdx 1).flatMap fun p => G p.2 p.1 := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      List.zipIdx_append, List.flatMap_append]
    congr 1
    · rw [← ih]
      apply List.flatMap_congr
      intro i hi
      have hi := List.mem_range.mp hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · simp only [List.getD_eq_getElem?_getD]
      simp [Nat.add_comm]

/-! ## The report -/

theorem text_flatMap {α : Type} (l : List α) (g : α → List (List UInt8)) :
    text (l.flatMap g) = l.flatMap fun a => text (g a) := by
  simp [text, List.flatMap_assoc]

/-- The default round, which `List.getD` takes past the end. -/
def noRound : Round := ⟨⟨[], 0, 0, 0, 0⟩, none⟩

/-- The printer prints the report of a structure that meets the constraints from its file and the
result words of its count, provided the report has fewer than `2 ^ 64` bytes. -/
theorem printReport_eq (b : Bytes) (hb : b.data.size < 2 ^ 64) (c : Contest) (hc : c.WellFormed)
    (hw : bytesOf b = write c) (hlen : (report c).length < 2 ^ 64) :
    bytesOf (printReport b (UInt64.ofNat c.candidates.length)
      (resultWords c.candidates.length (countContest c)).toArray) = report c := by
  have hn : c.candidates.length ≤ 63 := hc.2.2.2.1
  have hN : c.ballots.length ≤ maxBallots := hc.2.2.2.2.1
  have hNb : c.ballots.length < 2 ^ 64 := by simp [maxBallots] at hN; omega
  have hrep : report c =
      text ([ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++
        headerLines c ++ (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat =>
          roundLines p.2 p.1) ++ [winnerLine (countContest c).winner]) := rfl
  have hfacts := count_round_facts (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hwin := count_winner (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hRle := Demos.Rcv.Winner.rounds_le (kindsOf c) c.order
    (c.ballots.map fun b : Ballot => b.positions)
  have hkl : (kindsOf c).length = c.candidates.length := by simp [kindsOf]
  have hcs := Demos.Rcv.Rounds.countedSet_sublist (kindsOf c)
  have hcsl : (countedSet (kindsOf c)).length ≤ c.candidates.length := by
    have := hcs.length_le; rw [List.length_range', hkl] at this; exact this
  have hdef : count (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions) =
      countContest c := rfl
  rw [hdef, hkl] at hfacts hwin
  rw [hdef] at hRle
  -- The header lines
  set L := (ascii "rcv-ballots 1" :: headerLines c) ++ c.ballots.map ballotLine with hL
  have hwL : bytesOf b = text L := by rw [hw]; rfl
  have hLn : ∀ l ∈ L, lf ∉ l := lines_no_lf hc
  have hhl : (headerLines c).length = 5 + c.candidates.length := by
    simp only [headerLines, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_zipIdx]
    omega
  have hLlen : 6 + c.candidates.length ≤ L.length := by simp [hL, hhl]; omega
  generalize hnn : c.candidates.length = n at *
  have hnN : (UInt64.ofNat n).toNat = n := ofNat_toNat_small (by omega)
  have h6 : (6 + UInt64.ofNat n).toNat = 6 + n := by
    rw [UInt64.toNat_add, hnN]; simp; omega
  have hh := header_loop b hb L hLn hwL (6 + UInt64.ofNat n) (by rw [h6]; exact hLlen)
  rw [h6] at hh
  have htake : L.take (6 + n) = ascii "rcv-ballots 1" :: headerLines c := by
    rw [hL, List.cons_append, show 6 + n = (5 + n) + 1 by omega, List.take_succ_cons,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  rw [htake] at hh
  have hsize := size_toNat b hb
  have htextL : (text L).length = b.data.size := by rw [← hwL]; simp
  have hl1 : (ascii "rcv-ballots 1" ++ [lf]).length = 14 := rfl
  have hfile : text L = (ascii "rcv-ballots 1" ++ [lf]) ++
      (text (headerLines c) ++ text (c.ballots.map ballotLine)) := by
    rw [hL, List.cons_append, text_cons, text_append, List.append_assoc]
  have h14 : (text (ascii "rcv-ballots 1" :: headerLines c)).length =
      14 + (text (headerLines c)).length := by
    rw [text_cons, List.length_append, hl1]
  generalize hH : LeanExe.loop (6 + UInt64.ofNat n) (0 : UInt64)
      (fun _ p => findByte b 10 p b.size + 1) = H at hh
  have hl1' : (ascii "rcv-ballots 1").length + [lf].length = 14 := rfl
  have hHle : H.toNat ≤ b.data.size := by
    rw [hh, h14, ← htextL, hfile, List.length_append, List.length_append, List.length_append]
    omega
  have h14le : (14 : UInt64) ≤ H := by
    rw [UInt64.le_iff_toNat_le, hh, h14]; simp
  have hslice : slice b 14 H.toNat = text (headerLines c) := by
    rw [hh, h14, slice, hwL, hfile, List.drop_left' hl1, Nat.add_sub_cancel_left,
      List.take_left' rfl]
  -- The program
  unfold printReport
  simp only []
  rw [hH]
  rw [show ((1 : UInt64).toNat) = 1 from rfl, resultWords_rounds]
  have ho1 := pushRange_toList (pushHead #[]) b hb 14 H h14le hHle
  rw [show (14 : UInt64).toNat = 14 from rfl, hslice, pushHead_toList] at ho1
  generalize pushRange (pushHead #[]) b 14 H = o1 at ho1
  -- The rounds
  set R := (countContest c).rounds.length with hR
  have hR64 : R ≤ 64 := by have := hRle; omega
  have hRN : (UInt64.ofNat R).toNat = R := ofNat_toNat_small (by omega)
  have hloop := loop_append' (UInt64.ofNat R) o1
    (fun r o => pushRoundLines o (resultWords n (countContest c)).toArray (UInt64.ofNat n)
      (2 + r * (UInt64.ofNat n + 9)) (r + 1))
    (fun i => (text (roundLines (i + 1) ((countContest c).rounds.getD i noRound))).map
      UInt8.toUInt64) (by
      intro i hi o
      rw [hRN] at hi
      have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
      have hprod : i * (n + 9) ≤ 64 * 72 := Nat.mul_le_mul (by omega) (by omega)
      have hbase : (2 + UInt64.ofNat i * (UInt64.ofNat n + 9) : UInt64) =
          UInt64.ofNat (2 + i * (n + 9)) := by
        apply UInt64.toNat_inj.mp
        rw [ofNat_toNat_small (by omega), UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_add,
          hiN, hnN]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (show n + 9 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show i * (n + 9) < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 2 + i * (n + 9) < 2 ^ 64 by omega)]
      have hr1 : (UInt64.ofNat i + 1 : UInt64) = UInt64.ofNat (i + 1) := by
        apply UInt64.toNat_inj.mp
        rw [ofNat_toNat_small (by omega), UInt64.toNat_add, hiN]
        simp only [UInt64.reduceToNat]
        omega
      have hmem : (countContest c).rounds[i] ∈ (countContest c).rounds := List.getElem_mem hi
      obtain ⟨S, hvotes, hS, helim, hT, hbl, hun, hov, hex⟩ := hfacts _ hmem
      rw [hbase, hr1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      simp only [List.length_map] at hT hbl hun hov hex
      exact pushRoundLines_toList o _ hn _ S _ hvotes hS
        (fun j _ => Nat.lt_of_le_of_lt List.count_le_length (by simp; omega))
        ⟨by omega, by omega, by omega, by omega, by omega⟩ helim (by omega) (by omega)
        (fun j hj => resultWords_round n (countContest c) i j hi hj))
  rw [hRN, flatMap_range_zipIdx _ noRound (fun r rd => (text (roundLines r rd)).map
    UInt8.toUInt64)] at hloop
  generalize LeanExe.loop (UInt64.ofNat R) o1 _ = o2 at hloop
  -- The winner
  have hidx : (2 + UInt64.ofNat R * (UInt64.ofNat n + 9) : UInt64).toNat = 2 + R * (n + 9) := by
    have hprod : R * (n + 9) ≤ 64 * 72 := Nat.mul_le_mul (by omega) (by omega)
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_add, hRN, hnN]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (show n + 9 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show R * (n + 9) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 + R * (n + 9) < 2 ^ 64 by omega)]
  rw [hidx, resultWords_winner]
  have hfinal : ∀ o : Array UInt64, o.toList = (report c).map UInt8.toUInt64 →
      bytesOf (toBytes o) = report c := by
    intro o ho
    have hs : o.size < 2 ^ 64 := by
      have := congrArg List.length ho
      simp at this
      omega
    rw [toBytes_toList o hs, ho, map_toUInt8_toUInt64]
  apply hfinal
  rw [hrep, text_append, text_append, text_append, text_flatMap]
  cases hwk : (countContest c).winner with
  | none =>
    simp only [Option.getD_none]
    rw [ite_eq_left (by rfl), pushWord_toList, pushWord_toList, hloop, ho1]
    have hw0 : wordBytes 0x6e2072656e6e6977 (8 : UInt64).toNat ++
        wordBytes 0xa656e6f (4 : UInt64).toNat = (text [winnerLine none]).map UInt8.toUInt64 := by
      decide
    simp only [List.map_append, List.append_assoc, ← hw0, List.map_flatMap]
    simp
  | some i =>
    simp only [Option.getD_some]
    obtain ⟨hi1, hin⟩ := hwin i hwk
    have hiN : (UInt64.ofNat i).toNat = i := ofNat_toNat_small (by omega)
    rw [ite_eq_right (by
      intro h
      have := congrArg UInt64.toNat (beq_iff_eq.mp h)
      rw [hiN] at this
      simp at this
      omega), Array.toList_push, pushNumber_toList, pushWord_toList, hloop, ho1, hiN]
    have hw7 : wordBytes 0x2072656e6e6977 (7 : UInt64).toNat =
        (ascii "winner" ++ [sp]).map UInt8.toUInt64 := by
      decide
    rw [hw7]
    simp only [List.map_append, List.append_assoc, winnerLine, text, spaced_two, List.map_flatMap]
    simp [sp]

end Demos.Rcv.PrintProgram
