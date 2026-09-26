import Project.Compiler.TypedConditionals

namespace Project.Compiler.ArithmeticValidation

open Wasm.Binary
open Wasm.Binary.Validator
open Project.Compiler.ArithmeticEncoding

/-- Finishing an empty frame restores its outer stack, including after a branch. -/
theorem finish_empty (context : Context) (path : List Nat) (rest : List ValType)
    (poly : Bool) :
    finishFrame context path rest.length { values := rest, polymorphic := false }
      { values := rest, polymorphic := poly } [] =
        .ok { values := rest, polymorphic := false } := by
  simp [finishFrame, popMany, popExpectedList, StackState.pushMany]
  rfl

theorem block_empty (context : Context) (path : List Nat) (base : Nat)
    (rest : List ValType) (body : List Instr) (poly : Bool)
    (valid : validateInstrs { context with labels := [] :: context.labels }
      path rest.length { values := rest, polymorphic := false } 0 body =
        .ok { values := rest, polymorphic := poly }) :
    validateInstr context path base { values := rest, polymorphic := false }
      (.block .empty body) = .ok { values := rest, polymorphic := false } := by
  simp only [validateInstr, blockResults, valid, bind, Except.bind, finish_empty]

theorem loop_empty (context : Context) (path : List Nat) (base : Nat)
    (rest : List ValType) (body : List Instr) (poly : Bool)
    (valid : validateInstrs { context with labels := [] :: context.labels }
      path rest.length { values := rest, polymorphic := false } 0 body =
        .ok { values := rest, polymorphic := poly }) :
    validateInstr context path base { values := rest, polymorphic := false }
      (.loop .empty body) = .ok { values := rest, polymorphic := false } := by
  simp only [validateInstr, blockResults, valid, bind, Except.bind, finish_empty]

theorem branch_empty (context : Context) (path : List Nat) (rest : List ValType)
    (depth : UInt32) (label : context.labels[depth.toNat]? = some []) :
    validateInstr context path rest.length { values := rest, polymorphic := false }
      (.br depth) = .ok { values := rest, polymorphic := true } := by
  simp [validateInstr, label, popMany, popExpectedList, markUnreachable, bottom]
  rfl

theorem branch_if_empty (context : Context) (path : List Nat) (base : Nat)
    (rest : List ValType) (room : base ≤ rest.length)
    (depth : UInt32) (label : context.labels[depth.toNat]? = some []) :
    validateInstr context path base { values := .i32 :: rest, polymorphic := false }
      (.brIf depth) = .ok { values := rest, polymorphic := false } := by
  simp only [validateInstr, pop_typed context path base .i32 rest room,
    bind, Except.bind, label, popMany, List.reverse_nil, popExpectedList,
    pure, Except.pure, StackState.pushMany, List.nil_append]

/-- The production while layout is well typed for any typed condition and body.
The exit branch targets its surrounding block; the back edge targets its loop.
Neither label accepts a result, and the loop leaves the outer stack unchanged. -/
theorem Sequence.while {count : Nat} {condition body : List LeanExe.Wasm.Instr}
    (c : Sequence count [] [.i32] condition) (b : Sequence count [] [] body) :
    Sequence count [] [] [.block [.loop
      (condition ++ [.eqzI32, .brIf 1] ++ body ++ [.br 0])]] := by
  obtain ⟨rc, ec, vc⟩ := c
  obtain ⟨rb, eb, vb⟩ := b
  let rawBody := rc ++ [.i32Eqz, .brIf 1] ++ rb ++ [.br 0]
  have encoded : ProgramEncoding
      (condition ++ [.eqzI32, .brIf 1] ++ body ++ [.br 0]) rawBody :=
    ((ec.append (.cons (.atom .eqz32) (.cons (.atom (.brIf 1 (by decide))) .nil))).append eb).append
      (.cons (.atom (.br 0 (by decide))) .nil)
  refine ⟨[.block .empty [.loop .empty rawBody]],
    .cons (.block0 (.cons (.loop0 encoded) .nil)) .nil, ?_⟩
  intro context locals path base index rest room
  apply validate_cons (block_empty context (path ++ [index]) base rest _ false ?_) rfl
  apply validate_cons (loop_empty _ _ rest.length rest _ true ?_) rfl
  dsimp only [rawBody]
  apply validate_append
  · apply validate_append
    · apply validate_append
      · exact vc { context with labels := [] :: [] :: context.labels } locals _ rest.length 0 rest le_rfl
      · apply validate_cons (instr := .i32Eqz) (unary_typed _ _ rest.length .i32 .i32 rest le_rfl)
        apply validate_cons (branch_if_empty _ _ rest.length rest le_rfl 1 rfl) rfl
    · exact vb { context with labels := [] :: [] :: context.labels } locals _ rest.length _ rest le_rfl
  · apply validate_cons (branch_empty _ _ rest 0 rfl) rfl

end Project.Compiler.ArithmeticValidation
