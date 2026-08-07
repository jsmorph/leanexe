import Interpreter

namespace Project.ProofKit.Annotation

open Wasm

inductive Field where
  | block
  | loop
  | thenBranch
  | elseBranch
  deriving Repr, BEq, DecidableEq

structure Step where
  instructionIndex : Nat
  field : Field
  deriving Repr, BEq, DecidableEq

def descend (program : Program) (step : Step) : Option Program := do
  let instruction ← program[step.instructionIndex]?
  match step.field, instruction with
  | .block, .block _ _ body => some body
  | .loop, .loop _ _ body => some body
  | .thenBranch, .iff _ _ thenBody _ => some thenBody
  | .elseBranch, .iff _ _ _ elseBody => some elseBody
  | _, _ => none

def resolve : Program → List Step → Option Program
  | program, [] => some program
  | program, step :: rest => do
      let child ← descend program step
      resolve child rest

def region (program : Program) (path : List Step)
    (startIndex endIndex : Nat) : Option Program :=
  (resolve program path).map fun instructions =>
    (instructions.drop startIndex).take (endIndex - startIndex)

end Project.ProofKit.Annotation
