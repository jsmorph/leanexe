import Verified.ExprSpec

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem _root_.Wasm.TrapOK.allocPart {d d' : Bool} {P P' : Prop}
    [Decidable P] [Decidable P'] {Q : Assertion Unit}
    (h : TrapOK (d || !decide P) Q) (hd : d' = true → d = true)
    (hP : d = false → P → P') : TrapOK (d' || !decide P') Q := by
  have h' : TrapOK (d || (true && !decide P)) Q := by simpa only [Bool.true_and] using h
  exact h'.part (a' := true) hd (fun _ => rfl) hP

end Verified
