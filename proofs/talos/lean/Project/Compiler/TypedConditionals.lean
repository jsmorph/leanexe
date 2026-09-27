import Project.Compiler.TypedSequences

namespace Project.Compiler.ArithmeticValidation

open Wasm.Binary
open Wasm.Binary.Validator
open Project.Compiler.ArithmeticEncoding

theorem finish_i64 (context : Context) (path : List Nat) (rest : List ValType) :
    finishFrame context path rest.length { values := rest, polymorphic := false }
      { values := .i64 :: rest, polymorphic := false } [.i64] =
        .ok { values := .i64 :: rest, polymorphic := false } := by
  have popped : popMany context path rest.length [.i64]
      { values := .i64 :: rest, polymorphic := false } =
        .ok { values := rest, polymorphic := false } := by
    unfold popMany
    change (popExpected context path rest.length .i64
      { values := .i64 :: rest, polymorphic := false } >>= _) = _
    rw [pop_typed context path rest.length .i64 rest le_rfl]
    rfl
  unfold finishFrame
  rw [popped]
  simp [bind, Except.bind, StackState.pushMany]
  rfl

theorem if_i64 (context : Context) (path : List Nat) (base : Nat) (rest : List ValType)
    (room : base ≤ rest.length) (left right : List Instr)
    (leftValid : validateInstrs { context with labels := [.i64] :: context.labels }
      (path ++ [0]) rest.length { values := rest, polymorphic := false } 0 left =
        .ok { values := .i64 :: rest, polymorphic := false })
    (rightValid : validateInstrs { context with labels := [.i64] :: context.labels }
      (path ++ [1]) rest.length { values := rest, polymorphic := false } 0 right =
        .ok { values := .i64 :: rest, polymorphic := false }) :
    validateInstr context path base { values := .i32 :: rest, polymorphic := false }
      (.iff (.value .i64) left (some right)) =
        .ok { values := .i64 :: rest, polymorphic := false } := by
  unfold validateInstr
  rw [pop_typed context path base .i32 rest room]
  simp only [bind, Except.bind, blockResults, leftValid, rightValid, finish_i64]
  simp
  rfl

theorem Sequence.if64 {count : Nat} {left right : List LeanExe.Wasm.Instr}
    (a : Sequence count [] [.i64] left) (b : Sequence count [] [.i64] right) :
    Sequence count [.i32] [.i64] [.iff true left (some right)] := by
  obtain ⟨ra, ea, va⟩ := a
  obtain ⟨rb, eb, vb⟩ := b
  refine ⟨[.iff (.value .i64) ra (some rb)], .cons (.if64 ea eb) .nil, ?_⟩
  intro context locals path base index rest room
  apply validate_cons (if_i64 context (path ++ [index]) base rest room ra rb ?_ ?_) rfl
  · exact va { context with labels := [.i64] :: context.labels } locals
      ((path ++ [index]) ++ [0]) rest.length 0 rest le_rfl
  · exact vb { context with labels := [.i64] :: context.labels } locals
      ((path ++ [index]) ++ [1]) rest.length 0 rest le_rfl

end Project.Compiler.ArithmeticValidation
