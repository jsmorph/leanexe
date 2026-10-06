import Project.Smalltalk.BindingPreservation
import Project.Smalltalk.FillLoop

namespace Project.Smalltalk.BindingLoop
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes Project.Smalltalk.ConstructionValues
open Project.Smalltalk.ArgumentBinding Project.Smalltalk.BindingPreservation

def slotValues (s : Array UInt64) (args arity receiver : UInt64) (start : Nat) : Nat → List UInt64
  | 0 => []
  | n + 1 => slotValue s args arity receiver start.toUInt64 :: slotValues s args arity receiver (start + 1) n

theorem slotValues_length (s : Array UInt64) (args arity receiver : UInt64) (start count : Nat) :
    (slotValues s args arity receiver start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [slotValues, List.length_cons, ih]

theorem slotValues_index (s : Array UInt64) (args arity receiver : UInt64) (start count index : Nat)
    (within : index < count) :
    (slotValues s args arity receiver start count)[index]? =
      some (slotValue s args arity receiver (start + index).toUInt64) := by
  induction count generalizing start index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp only [slotValues, List.getElem?_cons_zero, Nat.add_zero]
    | succ index =>
      simp only [slotValues, List.getElem?_cons_succ]
      rw [ih (start + 1) index (by omega)]
      have same : start + 1 + index = start + (index + 1) := by omega
      rw [same]

def binding (s : Array UInt64) (args arity locals receiver : UInt64) : UInt64 × Array UInt64 :=
  LeanExe.repeatWhile (arity + locals) ((0 : UInt64), write s 19 0)
    (fun st => decide (st.1 < arity + locals))
    (fun st => (st.1 + 1, bindOne st.2 args arity locals receiver st.1))

structure Progress (original : Array UInt64) (cap : Nat) (args arity locals receiver : UInt64)
    (st : UInt64 × Array UInt64) : Prop where
  heap : Heap.Valid st.2 cap
  typed : PointerTypes.Valid st.2 cap
  index : st.1.toNat ≤ arity.toNat + locals.toNat
  values : Values st.2 cap (read st.2 19)
    (slotValues original args arity receiver (arity.toNat + locals.toNat - st.1.toNat) st.1.toNat)
  count : (read st.2 9).toNat + st.1.toNat = (read original 9).toNat
  previous : Preserved original st.2 cap
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 → r ≠ 19 →
    read st.2 r = read original r

theorem total_toNat {arity locals : UInt64} (bound : arity.toNat + locals.toNat ≤ 1048576) :
    (arity + locals).toNat = arity.toNat + locals.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem selected_index {arity locals i : UInt64}
    (bound : arity.toNat + locals.toNat ≤ 1048576) (active : i.toNat < arity.toNat + locals.toNat) :
    arity + locals - 1 - i = (arity.toNat + locals.toNat - (i.toNat + 1)).toUInt64 := by
  have total := total_toNat bound
  have one : (1 : UInt64) ≤ arity + locals := UInt64.le_iff_toNat_le.mpr (by rw [total]; change 1 ≤ arity.toNat + locals.toNat; omega)
  have first : (arity + locals - 1).toNat = arity.toNat + locals.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ one, total]; rfl
  have second : i ≤ arity + locals - 1 := by apply UInt64.le_iff_toNat_le.mpr; rw [first]; omega
  have small : arity.toNat + locals.toNat - (i.toNat + 1) < UInt64.size := by
    change arity.toNat + locals.toNat - (i.toNat + 1) < 18446744073709551616
    omega
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ second, first, UInt64.toNat_ofNat_of_lt' small]
  omega

theorem initial {s : Array UInt64} {cap : Nat} {args arity locals receiver : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) :
    Progress s cap args arity locals receiver (0, write s 19 0) := by
  have initialized := FillLoop.initial valid typed (limit := arity.toNat + locals.toNat)
  exact ⟨initialized.heap, initialized.typed, initialized.index,
    by simpa only [UInt64.reduceToNat, slotValues, List.replicate_zero] using initialized.values,
    initialized.count, initialized.previous, initialized.registers⟩

theorem next_progress {original s : Array UInt64} {cap : Nat} {args arity locals receiver i : UInt64}
    (originalValid : Heap.Valid original cap) (originalTyped : PointerTypes.Valid original cap)
    (inputs : Inputs original cap args arity receiver)
    (progress : Progress original cap args arity locals receiver (i, s))
    (budget : arity.toNat + locals.toNat + 1 ≤ (read original 9).toNat)
    (active : i.toNat < arity.toNat + locals.toNat) :
    Progress original cap args arity locals receiver (i + 1, bindOne s args arity locals receiver i) := by
  have bound : arity.toNat + locals.toNat ≤ 1048576 := by
    have free := FillLoop.free_count_bound originalValid
    have capBound := originalValid.1.1.2.1
    omega
  have increment := successor_toNat (i := i) (by omega)
  have before : (read s 9).toNat + i.toNat = (read original 9).toNat := progress.count
  have enough : (1 : UInt64) ≤ read s 9 := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ (read s 9).toNat; omega)
  have valueSame := slotValue_transfer originalValid.1.1 progress.heap.1.1 originalTyped progress.previous inputs
    (arity + locals - 1 - i)
  have selected : HeapWrite.Value s cap (slotValue s args arity receiver (arity + locals - 1 - i)) := by
    rw [valueSame]
    exact value_transfer progress.previous (slotValue_valid originalValid.1 inputs _)
  have effect : Construction.Effect s (bindOne s args arity locals receiver i) cap
      (slotValue s args arity receiver (arity + locals - 1 - i)) :=
    bindOne_effect progress.heap progress.typed (head_matches progress.values) selected enough
  refine ⟨effect.heap, effect.typed, ?_, ?_, ?_, ?_, ?_⟩
  · change (i + 1).toNat ≤ arity.toNat + locals.toNat
    rw [increment]; omega
  · change Values _ cap _ (slotValues original args arity receiver
      (arity.toNat + locals.toNat - (i + 1).toNat) (i + 1).toNat)
    rw [increment, slotValues]
    have start : arity.toNat + locals.toNat - (i.toNat + 1) + 1 = arity.toNat + locals.toNat - i.toNat := by omega
    rw [start]
    have built := prepend_values effect progress.values
    rw [valueSame, selected_index bound active] at built
    exact built
  · change (read (bindOne s args arity locals receiver i) 9).toNat + (i + 1).toNat = (read original 9).toNat
    rw [increment]
    have after := effect.count
    omega
  · intro h handle allocated k offset
    have allocatedNow : field s h 0 ≠ 0 := by rw [progress.previous h handle allocated 0 (by decide)]; exact allocated
    exact (effect.previous h handle allocatedNow k offset).trans (progress.previous h handle allocated k offset)
  · intro r offset h8 h9 h10 h13 h17 h19
    exact (effect.registers r offset h8 h9 h10 h13 h17 h19).trans (progress.registers r offset h8 h9 h10 h13 h17 h19)

theorem binding_progress {s : Array UInt64} {cap : Nat} {args arity locals receiver : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (inputs : Inputs s cap args arity receiver)
    (budget : arity.toNat + locals.toNat + 1 ≤ (read s 9).toNat) :
    Progress s cap args arity locals receiver (binding s args arity locals receiver) := by
  have bound : arity.toNat + locals.toNat ≤ 1048576 := by
    have free := FillLoop.free_count_bound valid
    have capBound := valid.1.1.2.1
    omega
  unfold binding
  apply Loops.repeat_invariant (Progress s cap args arity locals receiver)
  · intro st progress active
    rcases st with ⟨i, t⟩
    have natural := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true active)
    rw [total_toNat bound] at natural
    exact next_progress valid typed inputs progress budget natural
  · exact initial valid typed

theorem binding_index {s : Array UInt64} {cap : Nat} {args arity locals receiver : UInt64}
    (valid : Heap.Valid s cap) (budget : arity.toNat + locals.toNat + 1 ≤ (read s 9).toNat) :
    (binding s args arity locals receiver).1.toNat = arity.toNat + locals.toNat := by
  have bound : arity.toNat + locals.toNat ≤ 1048576 := by
    have free := FillLoop.free_count_bound valid
    have capBound := valid.1.1.2.1
    omega
  have total := total_toNat bound
  have counted := Loops.counted_index (fun t i => bindOne t args arity locals receiver i)
    (arity + locals) (by rw [total]; exact bound) (arity + locals).toNat 0 (write s 19 0) (by simp)
  simpa only [binding, LeanExe.repeatWhile, UInt64.reduceToNat, Nat.zero_add, total] using counted

theorem binding_values {s : Array UInt64} {cap : Nat} {args arity locals receiver : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (inputs : Inputs s cap args arity receiver)
    (budget : arity.toNat + locals.toNat + 1 ≤ (read s 9).toNat) :
    Values (binding s args arity locals receiver).2 cap
      (read (binding s args arity locals receiver).2 19)
      (slotValues s args arity receiver 0 (arity.toNat + locals.toNat)) := by
  have values := (binding_progress valid typed inputs budget).values
  rw [binding_index valid budget, Nat.sub_self] at values
  exact values

theorem binding_eq_pair (s : Array UInt64) (args arity locals receiver : UInt64) :
    binding s args arity locals receiver =
      LeanExe.repeatWhile (arity + locals) ((0 : UInt64), write s 19 0)
        (fun (i, _) => i < arity + locals) (fun (i, t) => bindNext t args arity locals receiver i) := by
  unfold binding
  congr 1 <;> funext st <;> cases st <;> rfl

end Project.Smalltalk.BindingLoop
