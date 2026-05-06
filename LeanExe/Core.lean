import LeanExe.Examples.AsciiDigits

namespace LeanExe.Core

inductive ScalarTy where
  | bool
  | u8
  | u32
  | u64
  deriving BEq, Repr

inductive Ty where
  | unit
  | scalar (ty : ScalarTy)
  | byteArray
  | product (left right : Ty)
  | sum (left right : Ty)
  deriving BEq, Repr

inductive BytePredicate where
  | asciiDigit
  deriving BEq, Repr

inductive Program where
  | allBytes (pred : BytePredicate)
  deriving BEq, Repr

def evalPred : BytePredicate → UInt8 → Bool
  | .asciiDigit, b => LeanExe.Examples.AsciiDigits.isAsciiDigit b

def Program.eval : Program → ByteArray → Bool
  | .allBytes pred, input => input.toList.all (evalPred pred)

def asciiDigits : Program :=
  .allBytes .asciiDigit

theorem asciiDigits_correct (input : ByteArray) :
    asciiDigits.eval input = LeanExe.Examples.AsciiDigits.validate input := rfl

structure CheckedValidator where
  program : Program
  sound :
    ∀ input,
      program.eval input = true →
      LeanExe.Examples.AsciiDigits.WellFormed input

def checkedAsciiDigits : CheckedValidator where
  program := asciiDigits
  sound := by
    intro input h
    exact LeanExe.Examples.AsciiDigits.validate_sound input h

def eraseProofs (validator : CheckedValidator) : Program :=
  validator.program

theorem eraseProofs_eval (validator : CheckedValidator) (input : ByteArray) :
    (eraseProofs validator).eval input = validator.program.eval input := rfl

structure LoweredValidator where
  min : Nat
  max : Nat
  deriving BEq, Repr

def LoweredValidator.evalByte (validator : LoweredValidator) (b : UInt8) : Bool :=
  decide (validator.min <= b.toNat ∧ b.toNat <= validator.max)

def LoweredValidator.eval (validator : LoweredValidator) (input : ByteArray) : Bool :=
  input.toList.all validator.evalByte

def lower : Program → LoweredValidator
  | .allBytes .asciiDigit => { min := 48, max := 57 }

theorem lower_correct (program : Program) (input : ByteArray) :
    (lower program).eval input = program.eval input := by
  cases program with
  | allBytes pred =>
      cases pred
      change
        input.toList.all (fun b => decide (48 <= b.toNat ∧ b.toNat <= 57)) =
          input.toList.all (fun b => LeanExe.Examples.AsciiDigits.isAsciiDigit b)
      rfl

end LeanExe.Core
