import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit
open Wasm

syntax (name := wpFixedFrame) "wp_fixed_frame" (Lean.Parser.Tactic.simpArgs)? : tactic

macro_rules
  | `(tactic| wp_fixed_frame $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic| wp_run [List.set, List.getElem?_cons, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.succ_ne_zero, reduceIte, $extra,*])

end Project.ProofKit
