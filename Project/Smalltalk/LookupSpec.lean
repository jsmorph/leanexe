import Project.Smalltalk.LookupStep

namespace Project.Smalltalk.LookupSpec
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime

def candidate (p : Array UInt64) (owner selector : UInt64) (method : Nat) : Bool :=
  owner != 0 && methodAt p method.toUInt64 0 == owner && methodAt p method.toUInt64 1 == selector

/-- Check methods in increasing ID order and return the first match, or zero. -/
def own (p : Array UInt64) (owner selector : UInt64) (start : Nat) : Nat → UInt64
  | 0 => 0
  | count + 1 =>
    if candidate p owner selector (start + 1) then (start + 1).toUInt64
    else own p owner selector (start + 1) count

/-- Check each class before its parent, with an explicit class-visit limit. -/
def search (p : Array UInt64) (owner selector : UInt64) : Nat → UInt64
  | 0 => 0
  | fuel + 1 =>
    if owner == 0 then 0 else
    let method := own p owner selector 0 (read p 1).toNat
    if method != 0 then method else search p (classAt p owner 0) selector fuel

theorem own_zero (p : Array UInt64) (selector : UInt64) (start count : Nat) : own p 0 selector start count = 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [own, candidate, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, ih]

theorem search_zero (p : Array UInt64) (selector : UInt64) (fuel : Nat) : search p 0 selector fuel = 0 := by
  cases fuel <;> simp only [search, BEq.rfl, ite_true]

end Project.Smalltalk.LookupSpec
