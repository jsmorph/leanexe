import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit
open Wasm

syntax (name := wpFixedFrame) "wp_fixed_frame" (Lean.Parser.Tactic.simpArgs)? : tactic

macro_rules
  | `(tactic| wp_fixed_frame $[[$args,*]]?) => do
    let extra := args.map (·.getElems) |>.getD #[]
    `(tactic| wp_run [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.succ_ne_zero, reduceIte, $extra,*])

macro "wp_fixed_frame_step" : tactic => `(tactic|
  (first
    | rw [wp_localGet_cons]
    | rw [wp_localSet_cons]
    | rw [wp_constI64_cons]
   simp only [Locals.get, Locals.set?, List.length, List.getElem?_cons_zero,
     List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceSub,
     Nat.reduceLT, Nat.succ_ne_zero, reduceIte]))

end Project.ProofKit
