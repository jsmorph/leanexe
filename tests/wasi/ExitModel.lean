import LeanExe.Wasi.Prefix
import Verified.Wasi.Observed

open LeanExe.Wasi

namespace ExitModel

def host : Host (Option UInt64) where
  exited world := world
  read _ _ _ _ := False
  write _ _ _ _ _ := False
  exit _ code final := code < 126 ∧ final = some code
  exitTrap world code message final :=
    126 ≤ code ∧ message = "rejected exit" ∧ final = world
  read_bound h := h.elim
  write_bound h := h.elim
  read_exited h := h.elim
  write_exited h := h.elim
  exit_recorded h := h.2
  exitTrap_exited h := h.2.2

example : Exec host (exit (α := Unit) 125) none [.exit 125] (.exited 125) (some 125) :=
  .exit ⟨by decide, rfl⟩

example : Exec host (exit (α := Unit) 126) none [.exitTrap 126 "rejected exit"]
    (.trapped "rejected exit") none :=
  .exitTrap ⟨by decide, rfl, rfl⟩

example : Exec host (exit (α := Unit) 4294967303) none [.exit 7] (.exited 7) (some 7) :=
  .exit ⟨by decide, rfl⟩

example : Exec host (exit (α := Unit) 4294967422) none [.exitTrap 126 "rejected exit"]
    (.trapped "rejected exit") none :=
  .exitTrap ⟨by decide, rfl, rfl⟩

example (next : Unit → Action UInt64) :
    Exec host (Action.bind (exit 256) next) none [.exitTrap 256 "rejected exit"]
      (.trapped "rejected exit") none :=
  .exitTrap ⟨by decide, rfl, rfl⟩

example {action : Action α} {trace message final}
    (h : Exec host action none trace (.trapped message) final) : final = none :=
  h.exited_marker

end ExitModel
