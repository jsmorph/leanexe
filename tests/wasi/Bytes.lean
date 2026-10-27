import LeanExe.Dialect.Bytes

open LeanExe

example : Bytes.get (bytes![0, 255, 128]) 0 = 0 := rfl
example : Bytes.get (bytes![0, 255, 128]) 1 = 255 := rfl
example : Bytes.get (bytes![0, 255, 128]) 2 = 128 := rfl
example : Bytes.get (bytes![0, 255, 128]) 3 = 0 := rfl
example : Bytes.size (bytes![]) = 0 := rfl
example : Bytes.get (Bytes.build 3 (fun i => 256 + i)) 2 = 2 := rfl

/-- error: byte literal exceeds 255 -/
#guard_msgs in
example : Bytes := bytes![256]

open Lean Elab Command in
elab "check_bytes_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``Bytes.get_build, ``Bytes.get_toNat_lt]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Bytes axiom check passed for {declarations.size} theorems"

check_bytes_axioms
