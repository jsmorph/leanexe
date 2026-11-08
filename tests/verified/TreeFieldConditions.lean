import Verified.Reflect.Command

/-! A record of a recursive type whose word, structure leaf, array, buffer, or child field holds an
`if` on `a + 2^63 < b + 2^63`, each compiled under 20000 heartbeats, and in a match alternative.
The kernel checks the equation of each family of the record's values at every index.  With the
values in place of variables, it compared each value with the family at its index and unfolded the
`if` first, evaluating the condition's `Decidable` instance in a number of steps linear in 2^63,
and every command below ran out of heartbeats.  Every theorem that the commands add uses only the
axioms `propext`, `Classical.choice`, and `Quot.sound`. -/

namespace Verified.Tests.TreeFieldConditions

open LeanExe LeanExe.Pipeline

structure P where
  u : UInt64
  v : UInt64

instance : Flat P (UInt64 × UInt64) := ⟨fun p => (p.u, p.v)⟩

inductive T where
  | leaf
  | node (left : T) (w : UInt64) (p : P) (right : T) (xs : Array UInt64) (bs : LeanExe.Bytes)

def T.encode : T → Node
  | .leaf => .null
  | .node l w p r xs bs => .record [.child l.encode, .word w, .word p.u, .word p.v,
      .child r.encode, .array xs, .bytes bs, .word (UInt64.ofNat bs.data.size)]

instance : Encode T := ⟨T.encode⟩

verified_recursive_type T

def wordIf (a b : UInt64) (l r : T) (p : P) (xs : Array UInt64) (bs : LeanExe.Bytes) : T :=
  .node l (if a + 0x8000000000000000 < b + 0x8000000000000000 then a else b) p r xs bs

def leafIf (a b : UInt64) (l r : T) (xs : Array UInt64) (bs : LeanExe.Bytes) : T :=
  .node l a ⟨if a + 0x8000000000000000 < b + 0x8000000000000000 then a else b, b⟩ r xs bs

def arrayIf (a b : UInt64) (l r : T) (p : P) (xs ys : Array UInt64) (bs : LeanExe.Bytes) : T :=
  .node l a p r (if a + 0x8000000000000000 < b + 0x8000000000000000 then xs else ys) bs

def bytesIf (a b : UInt64) (l r : T) (p : P) (xs : Array UInt64) (bs cs : LeanExe.Bytes) : T :=
  .node l a p r xs (if a + 0x8000000000000000 < b + 0x8000000000000000 then bs else cs)

def childIf (a b : UInt64) (l r : T) (p : P) (xs : Array UInt64) (bs : LeanExe.Bytes) : T :=
  .node (if a + 0x8000000000000000 < b + 0x8000000000000000 then l else r) a p .leaf xs bs

def matchIf (b : UInt64) (t : T) : T :=
  match t with
  | .leaf => .leaf
  | .node l w p r xs bs =>
    .node l (if w + 0x8000000000000000 < b + 0x8000000000000000 then w else b)
      ⟨if p.u + 0x8000000000000000 < b + 0x8000000000000000 then p.u else b, p.v⟩ r xs bs

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile word := [wordIf]

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile leaf := [leafIf]

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile array := [arrayIf]

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile buffer := [bytesIf]

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile child := [childIf]

set_option Elab.async false in
set_option maxHeartbeats 20000 in
verified_compile alternative := [matchIf]

open Lean Elab Command in
elab "check_tree_field_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for space in [`word, `leaf, `array, `buffer, `child, `alternative] do
    let pre := `Verified.Tests.TreeFieldConditions ++ space
    let theorems := (← getEnv).constants.fold (init := #[]) fun acc name info =>
      if pre.isPrefixOf name && info matches .thmInfo _ then acc.push name else acc
    unless (← getEnv).contains (pre ++ `bytes) do
      throwError "{pre} has no theorem bytes"
    for theoremName in theorems do
      for axiomName in ← collectAxioms theoremName do
        unless permitted.contains axiomName do
          throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo "tree field condition check passed"

check_tree_field_axioms

end Verified.Tests.TreeFieldConditions
