import Project.Smalltalk.ConstructionValues
import Project.Smalltalk.Loops
import Project.Smalltalk.Worklist

namespace Project.Smalltalk.FillLoop
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes Project.Smalltalk.ConstructionValues

def filling (s : Array UInt64) (count : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.repeatWhile count ((0 : UInt64), write s 19 0)
    (fun st => decide (st.1 < count)) (fun st => (st.1 + 1, fillOne st.2))

structure Progress (original : Array UInt64) (cap limit : Nat) (st : UInt64 × Array UInt64) : Prop where
  heap : Heap.Valid st.2 cap
  typed : PointerTypes.Valid st.2 cap
  index : st.1.toNat ≤ limit
  values : Values st.2 cap (read st.2 19) (List.replicate st.1.toNat 1)
  count : (read st.2 9).toNat + st.1.toNat = (read original 9).toNat
  previous : ∀ h, Handle cap h → field original h 0 ≠ 0 → ∀ k : UInt64, k.toNat < 8 →
    field st.2 h k = field original h k
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read st.2 r = read original r

theorem free_count_bound {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap) : (read s 9).toNat ≤ cap := by
  rcases valid.2 with ⟨nodes, free⟩
  rw [free.2.1]
  exact Worklist.handles_length (FreeList.chain_nodup free.1) (fun _ member => FreeList.chain_handle free.1 member)

theorem initial {s : Array UInt64} {cap limit : Nat} (valid : Heap.Valid s cap)
    (typed : PointerTypes.Valid s cap) : Progress s cap limit (0, write s 19 0) := by
  refine ⟨HeapWrite.write_register_valid valid (show (19 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by intro root; simp at root),
    PointerTypes.write_register_valid valid.1.1 typed (show (19 : UInt64).toNat < 24 by decide),
    by simp, ?_, ?_, ?_, ?_⟩
  · rw [read_write_same _ _ _ (register_bound valid.1.1 (show (19 : UInt64).toNat < 24 by decide))]
    exact .nil
  · rw [read_write_other _ _ _ _ (show (19 : UInt64) ≠ 9 by decide)]
    rfl
  · intro h handle _ k bound
    exact field_write_register valid.1.1 handle bound (show (19 : UInt64).toNat < 24 by decide)
  · intro r _ _ _ _ _ _ notScratch
    exact read_write_other _ _ _ _ (Ne.symm notScratch)

theorem next_progress {original s : Array UInt64} {cap limit : Nat} {i : UInt64}
    (progress : Progress original cap limit (i, s)) (limitBound : limit ≤ 1048576)
    (budget : limit + 1 ≤ (read original 9).toNat) (active : i.toNat < limit) :
    Progress original cap limit (i + 1, fillOne s) := by
  have increment := successor_toNat (i := i) (by omega)
  have enough : (1 : UInt64) ≤ read s 9 := by
    apply UInt64.le_iff_toNat_le.mpr
    change 1 ≤ (read s 9).toNat
    have count : (read s 9).toNat + i.toNat = (read original 9).toNat := progress.count
    omega
  have effect : Construction.Effect s (fillOne s) cap 1 :=
    Construction.fillOne_effect progress.heap progress.typed (head_matches progress.values) enough
  refine ⟨effect.heap, effect.typed, ?_, ?_, ?_, ?_, ?_⟩
  · change (i + 1).toNat ≤ limit
    rw [increment]; omega
  · rw [increment, List.replicate_succ]
    exact prepend_values effect progress.values
  · change (read (fillOne s) 9).toNat + (i + 1).toNat = (read original 9).toNat
    rw [increment]
    have before : (read s 9).toNat + i.toNat = (read original 9).toNat := progress.count
    have after := effect.count
    omega
  · intro h handle allocated k bound
    have currentAllocated : field s h 0 ≠ 0 := by rw [progress.previous h handle allocated 0 (by decide)]; exact allocated
    exact (effect.previous h handle currentAllocated k bound).trans (progress.previous h handle allocated k bound)
  · intro r bound h8 h9 h10 h13 h17 h19
    exact (effect.registers r bound h8 h9 h10 h13 h17 h19).trans (progress.registers r bound h8 h9 h10 h13 h17 h19)

theorem filling_progress {s : Array UInt64} {cap : Nat} {count : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (budget : count.toNat + 1 ≤ (read s 9).toNat) : Progress s cap count.toNat (filling s count) := by
  have limitBound : count.toNat ≤ 1048576 := by
    have free := free_count_bound valid
    have capBound := valid.1.1.2.1
    omega
  unfold filling
  apply Loops.repeat_invariant (Progress s cap count.toNat)
  · intro st progress active
    rcases st with ⟨i, t⟩
    exact next_progress progress limitBound budget
      (UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true active))
  · exact initial valid typed

theorem filling_index {s : Array UInt64} {cap : Nat} {count : UInt64}
    (valid : Heap.Valid s cap) (budget : count.toNat + 1 ≤ (read s 9).toNat) :
    (filling s count).1.toNat = count.toNat := by
  have limitBound : count.toNat ≤ 1048576 := by
    have free := free_count_bound valid
    have capBound := valid.1.1.2.1
    omega
  simpa only [filling, LeanExe.repeatWhile, UInt64.reduceToNat, Nat.zero_add] using
    Loops.counted_index (fun t _ => fillOne t) count limitBound count.toNat 0 (write s 19 0) (by simp)

theorem filling_values {s : Array UInt64} {cap : Nat} {count : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (budget : count.toNat + 1 ≤ (read s 9).toNat) :
    Values (filling s count).2 cap (read (filling s count).2 19) (List.replicate count.toNat 1) := by
  have values := (filling_progress valid typed budget).values
  rw [filling_index valid budget] at values
  exact values

theorem filling_eq_pair (s : Array UInt64) (count : UInt64) :
    filling s count = LeanExe.repeatWhile count ((0 : UInt64), write s 19 0)
      (fun (i, _) => i < count) (fun (i, t) => fillNext t i) := by
  unfold filling
  congr 1 <;> funext st <;> cases st <;> rfl

end Project.Smalltalk.FillLoop
