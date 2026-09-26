import Project.Compiler.ArithmeticEmission
import Project.Artifact.Binary.Validate

namespace Project.Compiler.ArithmeticValidation

open Wasm.Binary
open Wasm.Binary.Validator

@[simp] theorem signed64_range (value : UInt64) :
    inSignedRange 64 value.toBitVec.toInt = true := by
  simp only [inSignedRange, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨BitVec.le_toInt value.toBitVec, BitVec.toInt_lt⟩

@[simp] theorem validate_const64 (context : Context) (path : List Nat) (base : Nat)
    (state : StackState) (value : UInt64) :
    validateInstr context path base state (.i64Const value.toBitVec.toInt) =
      .ok (state.push .i64) := by
  simp only [validateInstr, signed64_range, ite_true]
  rfl

@[simp] theorem negative_one_range : inSignedRange 32 (-1) = true := by decide

theorem pop_typed (context : Context) (path : List Nat) (base : Nat)
    (type : ValType) (rest : List ValType) (room : base ≤ rest.length) :
    popExpected context path base type { values := type :: rest, polymorphic := false } =
      .ok { values := rest, polymorphic := false } := by
  have different : rest.length + 1 ≠ base := by omega
  simp [popExpected, different]
  rfl

theorem unary_typed (context : Context) (path : List Nat) (base : Nat)
    (input output : ValType) (rest : List ValType) (room : base ≤ rest.length) :
    unary context path base input output { values := input :: rest, polymorphic := false } =
      .ok { values := output :: rest, polymorphic := false } := by
  unfold unary
  rw [pop_typed context path base input rest room]
  rfl

theorem binary_typed (context : Context) (path : List Nat) (base : Nat)
    (input output : ValType) (rest : List ValType) (room : base ≤ rest.length) :
    binary context path base input output { values := input :: input :: rest, polymorphic := false } =
      .ok { values := output :: rest, polymorphic := false } := by
  unfold binary
  rw [pop_typed context path base input (input :: rest) (by simp; omega)]
  change (popExpected context path base input { values := input :: rest, polymorphic := false } >>= _) = _
  rw [pop_typed context path base input rest room]
  rfl

theorem validate_cons {context : Context} {path : List Nat} {base index : Nat}
    {start middle finish : StackState} {instr : Instr} {rest : List Instr}
    (head : validateInstr context (path ++ [index]) base start instr = .ok middle)
    (tail : validateInstrs context path base middle (index + 1) rest = .ok finish) :
    validateInstrs context path base start index (instr :: rest) = .ok finish := by
  simp only [validateInstrs, head]
  exact tail

theorem validate_append {context : Context} {path : List Nat} {base : Nat}
    {left right : List Instr} {index : Nat} {start middle finish : StackState}
    (first : validateInstrs context path base start index left = .ok middle)
    (second : validateInstrs context path base middle (index + left.length) right = .ok finish) :
    validateInstrs context path base start index (left ++ right) = .ok finish := by
  induction left generalizing index start with
  | nil =>
    have same : start = middle := Except.ok.inj first
    subst start
    exact second
  | cons instr rest ih =>
    cases step : validateInstr context (path ++ [index]) base start instr with
    | error err =>
      rw [validateInstrs, step] at first
      change (Except.error err : Except ValidationError StackState) = .ok middle at first
      cases first
    | ok next =>
      apply validate_cons step
      apply ih
      · simpa only [validateInstrs, step, bind, Except.bind] using first
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

end Project.Compiler.ArithmeticValidation
