import LeanExe.WGSL.Source

/-! Syntax for the emitted statement subset. Local references are de Bruijn
slots resolved by the parser. Bindings and loops remain statements: parsing
does not substitute their values or run a symbolic evaluator. -/
namespace LeanExe.WGSL.Statement
open Source

inductive Prim where
  | literal (word : UInt32)
  | copy (slot : Nat)
  | loadA (index : Source.Index)
  | loadB (index : Source.Index)
  | add (left right : Nat)
  | mul (left right : Nat)
  deriving Repr, BEq, DecidableEq

/-- `finish` is the value assigned to the enclosing accumulator or output.
`loop` preserves the initializer reference, body scope and subsequent code.
The surface parser checks the exact zero/test/increment/assignment syntax. -/
inductive Code where
  | finish (slot : Nat)
  | bind (value : Prim) (next : Code)
  | loop (count initial : Nat) (body next : Code)
  deriving Repr, BEq, DecidableEq

def Prim.term : Prim → Source.Term
  | .literal w => .lit w
  | .copy n => .local n
  | .loadA i => .readA i
  | .loadB i => .readB i
  | .add a b => .add (.local a) (.local b)
  | .mul a b => .mul (.local a) (.local b)

def Code.term : Code → Source.Term
  | .finish n => .local n
  | .bind value next => .letE value.term next.term
  | .loop count initial body next =>
      .letE (.fold count (.local initial) body.term) next.term

def Prim.lean : Prim → String
  | .literal w => s!"(.literal {w.toNat})"
  | .copy n => s!"(.copy {n})"
  | .loadA i => s!"(.loadA {i.lean})"
  | .loadB i => s!"(.loadB {i.lean})"
  | .add a b => s!"(.add {a} {b})"
  | .mul a b => s!"(.mul {a} {b})"

def Code.lean : Code → String
  | .finish n => s!"(.finish {n})"
  | .bind value next => s!"(.bind {value.lean} {next.lean})"
  | .loop count initial body next => s!"(.loop {count} {initial} {body.lean} {next.lean})"

end LeanExe.WGSL.Statement
