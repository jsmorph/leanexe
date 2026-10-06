import Project.Smalltalk.ProgramBounds
import Project.Smalltalk.BindingLoop

namespace Project.Smalltalk.BootBudget
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def need (p : Array UInt64) : UInt64 :=
  classAt p (methodAt p (read p 3) 0) 2 + methodAt p (read p 3) 2 + methodAt p (read p 3) 3 + 2

def count (p : Array UInt64) : Nat :=
  (classAt p (methodAt p (read p 3) 0) 2).toNat + (methodAt p (read p 3) 2).toNat +
    (methodAt p (read p 3) 3).toNat + 2

theorem entry_method {p : Array UInt64} (valid : programValid p = true) : ProgramBounds.Method p (read p 3) :=
  ProgramBounds.method_bounds valid (ProgramBounds.header valid).entryPositive (ProgramBounds.header valid).entryBound

theorem entry_class {p : Array UInt64} (valid : programValid p = true) :
    ProgramBounds.Class p (methodAt p (read p 3) 0) :=
  ProgramBounds.class_bounds valid (entry_method valid).ownerPositive (entry_method valid).ownerBound

theorem need_toNat {p : Array UInt64} (valid : programValid p = true) : (need p).toNat = count p := by
  have fields := (entry_class valid).fieldsBound
  have arity := (entry_method valid).arityBound
  have locals := (entry_method valid).localsBound
  simp only [need, count, UInt64.toNat_add, UInt64.reduceToNat]
  omega

theorem locals_values (s : Array UInt64) (args receiver : UInt64) (start count : Nat)
    (positive : 0 < start) (bound : start + count ≤ 2097152) :
    BindingLoop.slotValues s args 1 receiver start count = List.replicate count 1 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    have small : start < UInt64.size := by change start < 18446744073709551616; omega
    have nonzero : start.toUInt64 ≠ (0 : UInt64) := by
      intro zero
      have natural := congrArg UInt64.toNat zero
      rw [UInt64.toNat_ofNat_of_lt' small] at natural
      change start = 0 at natural
      omega
    have outside : ¬ start.toUInt64 < (1 : UInt64) := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' small]
      change ¬ start < 1
      omega
    simp only [BindingLoop.slotValues, ArgumentBinding.slotValue,
      show (start.toUInt64 == (0 : UInt64)) = false from beq_eq_false_iff_ne.mpr nonzero,
      Bool.false_eq_true, ite_false, outside, List.replicate_succ]
    rw [ih (start + 1) (by omega) (by omega)]

theorem entry_values (s : Array UInt64) (receiver : UInt64) (locals : Nat) (bound : locals ≤ 1048576) :
    BindingLoop.slotValues s 0 1 receiver 0 (1 + locals) = receiver :: List.replicate locals 1 := by
  rw [Nat.add_comm 1 locals, BindingLoop.slotValues]
  change ArgumentBinding.slotValue s 0 1 receiver 0 :: BindingLoop.slotValues s 0 1 receiver 1 locals = _
  simp only [ArgumentBinding.slotValue, BEq.rfl, ite_true]
  rw [locals_values s 0 receiver 1 locals (by decide) (by omega)]

end Project.Smalltalk.BootBudget
