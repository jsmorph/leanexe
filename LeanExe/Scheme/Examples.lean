import LeanExe.Scheme.VM

/-! Hand-assembled programs for the VM; these do not introduce a Scheme compiler. -/

namespace LeanExe.Scheme.VM.Examples

/-- `(subtract 10 3)`: arguments must retain source order. -/
def arguments : Code := #[
  .close 5 [1, 2], .push (.word 10), .push (.word 3), .call 2, .ret,
  .load 1, .load 2, .binary .sub, .ret
]

/-- An operand below a call must survive the call and return. -/
def pendingOperand : Code := #[
  .push (.word 100), .close 5 [], .call 0, .binary .add, .ret,
  .push (.word 23), .ret
]

/-- The caller's environment is restored after a parameter shadows its binding. -/
def shadowing : Code := #[
  .close 6 [1], .push (.word 3), .call 1, .drop, .load 1, .ret,
  .load 1, .ret
]

/-- A closure sees subsequent mutation through the location it captured. -/
def sharedMutation : Code := #[
  .close 8 [], .store 2, .drop, .push (.word 9), .store 1, .drop, .load 2, .tailcall 0,
  .load 1, .ret
]

/-- Self-reference is an ordinary captured location; each recursive call is a tail call. -/
def countdown (n : UInt64) : Code := #[
  .load 2, .push (.word n), .tailcall 1,
  .load 1, .push (.word 0), .binary .equal, .branch 9, .push (.word 0), .ret,
  .load 2, .load 1, .push (.word 1), .binary .sub, .tailcall 1
]

def countdownInitial : State :=
  initial [(2, 0)] #[.closure 3 [1] [(2, 0)]]

/-!
The callback saves its continuation and returns 10. The caller then increments a
shared counter and invokes the saved continuation twice, with 1 and 2. Each resume
must recover the pending operand 100, but keep the latest counter. The result is 102.
Names 1, 2, 4 refer to the counter, saved continuation, and latest result; name 3 is
the callback parameter. The callback has already returned before either invocation.
-/
def multiShot : Code := #[
  .push (.word 100), .push .callcc, .close 21 [3], .call 1,
  .binary .add, .store 4, .drop,
  .load 1, .push (.word 2), .binary .less, .branch 19,
  .load 1, .push (.word 1), .binary .add, .store 1, .drop,
  .load 2, .load 1, .tailcall 1,
  .load 4, .ret,
  .load 3, .store 2, .drop, .push (.word 10), .ret
]

def multiShotInitial : State :=
  initial [(1, 0), (2, 1), (4, 2)] #[.word 0, .unit, .unit]

/-- Even `call/cc` used as its own callback goes through explicit application states. -/
def nestedCallcc : Code := #[.push .callcc, .push .callcc, .tailcall 1]

end LeanExe.Scheme.VM.Examples
