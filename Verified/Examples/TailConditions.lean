import Verified.Reflect.Command

namespace Verified.Examples.TailConditions

def boolCount (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else boolCount (n - 1) (acc + n)
termination_by n.toNat
decreasing_by
  simp_all only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat]
  omega

def neCount (n acc : UInt64) : UInt64 :=
  if n ≠ 0 then neCount (n - 1) (acc + n) else acc
termination_by n.toNat
decreasing_by
  simp_all only [ne_eq, ← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat]
  omega

def diteCount (n acc : UInt64) : UInt64 :=
  if _h : n = 0 then acc else diteCount (n - 1) (acc + n)
termination_by n.toNat
decreasing_by
  simp_all only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat]
  omega

def tupleCount (n : UInt64) (state : UInt64 × Float) : UInt64 × Float :=
  match state with
  | (word, value) =>
    if n = 0 then (word, value) else tupleCount (n - 1) (word + n, value + n.toFloat)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def pairRead (n : UInt64) (state : Array UInt64 × UInt64) : UInt64 :=
  match state with
  | (xs, acc) =>
    if n = 0 then acc else pairRead (n - 1) (xs, acc + xs[(n - 1).toNat]!)
termination_by n.toNat
decreasing_by
  simp_all only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat]
  omega

structure ReadState where
  xs : Array UInt64
  acc : UInt64

instance : LeanExe.Pipeline.Flat ReadState (Array UInt64 × UInt64) :=
  ⟨fun s => (s.xs, s.acc)⟩

def recordRead (n : UInt64) (state : ReadState) : UInt64 :=
  match state with
  | ⟨xs, acc⟩ =>
    if n = 0 then acc else recordRead (n - 1) ⟨xs, acc + xs[(n - 1).toNat]!⟩
termination_by n.toNat
decreasing_by
  simp_all only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat]
  omega

verified_compile compiled := [boolCount, neCount, diteCount, tupleCount, pairRead, recordRead]

#print axioms compiled.bytes

end Verified.Examples.TailConditions
