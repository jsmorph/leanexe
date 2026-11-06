import LeanExe.A64.Gen

/-!
The area's bytes past its prefix are 0.  The module's initial memory starts as `Mem.empty`, whose
bytes are 0, and each data segment with an offset writes only the bytes from its offset below its
end, so every byte at or past `dataEnd` keeps the value 0.  `areaByte` reads the memory's byte
`j - 4096` for `j` at or past 4096, so every byte of the area from `areaPrefix` on is 0.
-/

namespace LeanExe.A64

open Wasm

theorem le_foldl_segEnd (segs : List DataSegment) (acc : Nat) : acc ≤ segs.foldl segEnd acc := by
  induction segs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons seg segs ih =>
      simp only [List.foldl_cons, segEnd]
      split
      · exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      · exact ih _

theorem end_le_foldl_segEnd (segs : List DataSegment) (acc : Nat) {seg : DataSegment}
    (hs : seg ∈ segs) {off : UInt32} (ho : seg.offset = some off) :
    off.toNat + seg.bytes.length ≤ segs.foldl segEnd acc := by
  induction segs generalizing acc with
  | nil => cases hs
  | cons s segs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hs with rfl | hs
      · have : segEnd acc seg = max acc (off.toNat + seg.bytes.length) := by
          simp only [segEnd, ho]
        rw [this]
        exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_segEnd _ _)
      · exact ih _ hs

/-- A fold whose every step keeps the byte at `i` keeps it. -/
theorem foldl_bytes {f : Mem → DataSegment → Mem} (segs : List DataSegment) (m0 : Mem) (i : Nat)
    (hf : ∀ acc seg, seg ∈ segs → (f acc seg).bytes i = acc.bytes i) :
    (segs.foldl f m0).bytes i = m0.bytes i := by
  induction segs generalizing m0 with
  | nil => rfl
  | cons seg segs ih =>
      simp only [List.foldl_cons]
      rw [ih _ fun acc s hs => hf acc s (List.mem_cons_of_mem _ hs), hf _ _ List.mem_cons_self]

/-- Every byte of the initial memory of `m` at or past `dataEnd m` is 0. -/
theorem initialStore_bytes (m : Module) (i : Nat) (hi : dataEnd m ≤ i) :
    (m.initialStore : Store Unit).mem.bytes i = 0 := by
  unfold Module.initialStore
  unfold dataEnd at hi
  cases hm : m.memory with
  | none => rfl
  | some d =>
      rw [hm] at hi
      simp only at hi ⊢
      rw [foldl_bytes]
      · rfl
      · intro acc seg hs
        split
        · rename_i off ho
          have hle := Nat.le_trans (end_le_foldl_segEnd d.data 0 hs ho) hi
          split
          · split
            · simp only [Mem.writeBytes]
              rw [dif_neg (by omega)]
            · rfl
          · rfl
        · rfl

/-- Every byte of the area of `m` from `areaPrefix m` on is 0. -/
theorem areaByte_tail (m : Module) (j : Nat) (hj : areaPrefix m ≤ j) :
    areaByte m.initialStore j = 0 := by
  have h1 : 4096 + dataEnd m ≤ areaPrefix m := by
    unfold areaPrefix roundUp
    omega
  unfold areaByte
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact initialStore_bytes m _ (by omega)

end LeanExe.A64
