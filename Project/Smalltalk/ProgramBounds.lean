import Project.Smalltalk.ProgramChecks

namespace Project.Smalltalk.ProgramBounds
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
open Project.Smalltalk.ProgramChecks

structure Header (p : Array UInt64) : Prop where
  classesPositive : 0 < (read p 0).toNat
  classesBound : (read p 0).toNat ≤ 1048576
  methodsPositive : 0 < (read p 1).toNat
  methodsBound : (read p 1).toNat ≤ 1048576
  codePositive : 0 < (read p 2).toNat
  codeBound : (read p 2).toNat ≤ 1048576
  entryPositive : 0 < (read p 3).toNat
  entryBound : (read p 3).toNat ≤ (read p 1).toNat
  sizeWord : p.size.toUInt64 = 8 + 4 * read p 0 + 6 * read p 1 + 4 * read p 2

theorem header {p : Array UInt64} (valid : programValid p = true) : Header p := by
  have shaped := (checks valid).1
  have all : 0 < (read p 0).toNat ∧ (read p 0).toNat ≤ 1048576 ∧
      0 < (read p 1).toNat ∧ (read p 1).toNat ≤ 1048576 ∧
      0 < (read p 2).toNat ∧ (read p 2).toNat ≤ 1048576 ∧
      0 < (read p 3).toNat ∧ (read p 3).toNat ≤ (read p 1).toNat ∧
      p.size.toUInt64 = 8 + 4 * read p 0 + 6 * read p 1 + 4 * read p 2 := by
    simpa only [shape, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat] using shaped
  rcases all with ⟨n0, n, m0, m, c0, c, e0, e, size⟩
  exact ⟨n0, n, m0, m, c0, c, e0, e, size⟩

theorem table_count {p : Array UInt64} (bounds : Header p) :
    (read p 0 + read p 1).toNat = (read p 0).toNat + (read p 1).toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have n := bounds.classesBound; have m := bounds.methodsBound; omega)]

theorem class_checked {p : Array UInt64} {c : UInt64} (valid : programValid p = true)
    (positive : 0 < c.toNat) (within : c.toNat ≤ (read p 0).toNat) : classCheck p c = true := by
  have bounds := header valid
  have one : (1 : UInt64) ≤ c := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ c.toNat; omega)
  have index : (c - 1).toNat = c.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ one]; rfl
  have less : c - 1 < read p 0 := UInt64.lt_iff_toNat_lt.mpr (by rw [index]; omega)
  have scan : c - 1 < read p 0 + read p 1 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [index, table_count bounds]
    omega
  have checked := (checks valid).2.2.1 (c - 1) scan
  have id : c - 1 + 1 = c := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, index]
    simp only [UInt64.reduceToNat]
    have cBound := UInt64.toNat_lt_size c
    rw [Nat.mod_eq_of_lt (by change c.toNat < 18446744073709551616 at cBound; omega)]
    omega
  simpa only [tableCheck, less, ite_true, id] using checked

theorem method_checked {p : Array UInt64} {m : UInt64} (valid : programValid p = true)
    (positive : 0 < m.toNat) (within : m.toNat ≤ (read p 1).toNat) : methodCheck p m = true := by
  have bounds := header valid
  have one : (1 : UInt64) ≤ m := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ m.toNat; omega)
  have previous : (m - 1).toNat = m.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ one]; rfl
  have index : (read p 0 + (m - 1)).toNat = (read p 0).toNat + (m.toNat - 1) := by
    rw [UInt64.toNat_add, previous, Nat.mod_eq_of_lt (by have n := bounds.classesBound; have count := bounds.methodsBound; omega)]
  have notClass : ¬ read p 0 + (m - 1) < read p 0 := by rw [UInt64.lt_iff_toNat_lt, index]; omega
  have scan : read p 0 + (m - 1) < read p 0 + read p 1 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [index, table_count bounds]
    omega
  have checked := (checks valid).2.2.1 (read p 0 + (m - 1)) scan
  have subtract : read p 0 ≤ read p 0 + (m - 1) := UInt64.le_iff_toNat_le.mpr (by rw [index]; omega)
  have id : read p 0 + (m - 1) - read p 0 + 1 = m := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ subtract, index]
    simp only [UInt64.reduceToNat]
    have count := bounds.methodsBound
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simpa only [tableCheck, notClass, ite_false, id] using checked

structure Class (p : Array UInt64) (c : UInt64) : Prop where
  parent : (classAt p c 0).toNat < c.toNat
  metaPositive : 0 < (classAt p c 1).toNat
  metaBound : (classAt p c 1).toNat ≤ (read p 0).toNat
  fieldsBound : (classAt p c 2).toNat ≤ 1048576
  reserved : classAt p c 3 = 0
  inherited : classAt p c 0 ≠ 0 → (classAt p (classAt p c 0) 2).toNat ≤ (classAt p c 2).toNat

structure Method (p : Array UInt64) (m : UInt64) : Prop where
  ownerPositive : 0 < (methodAt p m 0).toNat
  ownerBound : (methodAt p m 0).toNat ≤ (read p 0).toNat
  arityPositive : 0 < (methodAt p m 2).toNat
  arityBound : (methodAt p m 2).toNat ≤ 1048576
  localsBound : (methodAt p m 3).toNat ≤ 1048576
  pcBound : (methodAt p m 4).toNat < (read p 2).toNat
  primitiveBound : (methodAt p m 5).toNat ≤ 8

theorem class_bounds {p : Array UInt64} {c : UInt64} (valid : programValid p = true)
    (positive : 0 < c.toNat) (within : c.toNat ≤ (read p 0).toNat) : Class p c := by
  have checked := class_checked valid positive within
  have all : classAt p c 0 < c ∧ classAt p c 1 > 0 ∧ classAt p c 1 ≤ read p 0 ∧
      classAt p c 2 ≤ 1048576 ∧ classAt p c 3 = 0 ∧
      (if classAt p c 0 == 0 then true else if classAt p c 0 < c then
        decide (classAt p (classAt p c 0) 2 ≤ classAt p c 2) else false) = true := by
    simpa only [classCheck, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using checked
  rcases all with ⟨parent, metaPositive, metaBound, fields, reserved, inherited⟩
  refine ⟨UInt64.lt_iff_toNat_lt.mp parent, UInt64.lt_iff_toNat_lt.mp metaPositive,
    UInt64.le_iff_toNat_le.mp metaBound, UInt64.le_iff_toNat_le.mp fields, reserved, ?_⟩
  intro nonzero
  simp only [show (classAt p c 0 == 0) = false from beq_eq_false_iff_ne.mpr nonzero,
    Bool.false_eq_true, ite_false, parent, ite_true, decide_eq_true_eq] at inherited
  exact UInt64.le_iff_toNat_le.mp inherited

theorem method_bounds {p : Array UInt64} {m : UInt64} (valid : programValid p = true)
    (positive : 0 < m.toNat) (within : m.toNat ≤ (read p 1).toNat) : Method p m := by
  have checked := method_checked valid positive within
  have all : 0 < (methodAt p m 0).toNat ∧ (methodAt p m 0).toNat ≤ (read p 0).toNat ∧
      0 < (methodAt p m 2).toNat ∧ (methodAt p m 2).toNat ≤ 1048576 ∧
      (methodAt p m 3).toNat ≤ 1048576 ∧ (methodAt p m 4).toNat < (read p 2).toNat ∧
      (methodAt p m 5).toNat ≤ 8 := by
    simpa only [methodCheck, Bool.and_assoc, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.reduceToNat] using checked
  rcases all with ⟨ownerPositive, ownerBound, arityPositive, arityBound, localsBound, pc, primitive⟩
  exact ⟨ownerPositive, ownerBound, arityPositive, arityBound, localsBound, pc, primitive⟩

theorem entry_arity {p : Array UInt64} (valid : programValid p = true) : methodAt p (read p 3) 2 = 1 := by
  have checked := (checks valid).2.2.2
  have entry : methodAt p (read p 3) 2 = 1 ∧ methodAt p (read p 3) 1 ≠ 0 := by
    simpa only [entryCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using checked
  exact entry.1

end Project.Smalltalk.ProgramBounds
