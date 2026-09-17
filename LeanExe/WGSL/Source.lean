import LeanExe.WGSL.Generate

/-! Source operations and the expression tree used by the body compiler.
`UInt32` values are binary32 words; the arithmetic argument supplies their
interpretation. No source definition is selected by a GEMM equality witness. -/
namespace LeanExe.WGSL.Source

abbrev Kernel := ScalarArithmetic → WordBuffer → WordBuffer → Nat → Nat → UInt32

/-- Ascending, sequential fold, with an explicit initial word. -/
def fold (count : Nat) (initial : UInt32) (step : Nat → UInt32 → UInt32) : UInt32 :=
  Nat.rec initial (fun k acc => step k acc) count

inductive Index where
  | lit (value : Nat)
  | row
  | col
  | local (slot : Nat)
  | add (left right : Index)
  | mul (left right : Index)
  deriving Repr, BEq, DecidableEq

def Index.eval (row col : Nat) (locals : List Nat) : Index → Nat
  | .lit n => n
  | .row => row
  | .col => col
  | .local i => locals[i]?.getD 0
  | .add a b => a.eval row col locals + b.eval row col locals
  | .mul a b => a.eval row col locals * b.eval row col locals

inductive Term where
  | lit (word : UInt32)
  | local (slot : Nat)
  | readA (index : Index)
  | readB (index : Index)
  | add (left right : Term)
  | mul (left right : Term)
  | letE (value body : Term)
  | fold (count : Nat) (initial body : Term)
  deriving Repr, BEq, DecidableEq

def Term.eval (arithmetic : ScalarArithmetic) (a b : WordBuffer)
    (row col : Nat) (indices : List Nat) (words : List UInt32) : Term → UInt32
  | .lit word => word
  | .local i => words[i]?.getD 0
  | .readA i => a (i.eval row col indices)
  | .readB i => b (i.eval row col indices)
  | .add x y => arithmetic.add (x.eval arithmetic a b row col indices words)
      (y.eval arithmetic a b row col indices words)
  | .mul x y => arithmetic.mul (x.eval arithmetic a b row col indices words)
      (y.eval arithmetic a b row col indices words)
  | .letE value body => body.eval arithmetic a b row col indices
      (value.eval arithmetic a b row col indices words :: words)
  | .fold count initial body => Source.fold count
      (initial.eval arithmetic a b row col indices words)
      (fun k acc => body.eval arithmetic a b row col (k :: indices) (acc :: words))

def Term.kernel (term : Term) : Kernel := fun arithmetic a b row col =>
  term.eval arithmetic a b row col [] []

structure Shape where
  rows : Nat
  cols : Nat
  elementsA : Nat
  elementsB : Nat
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

/-- Inclusive upper bound. The grammar is monotone in all index variables. -/
def Index.bound (shape : Shape) (locals : List Nat) : Index → Except String Nat
  | .lit n => if n ≤ 4294967295 then pure n else .error "index literal exceeds u32"
  | .row => pure (shape.rows - 1)
  | .col => pure (shape.cols - 1)
  | .local i => match locals[i]? with
      | some n => pure n
      | none => .error "unbound index local"
  | .add a b => do
      let n := (← a.bound shape locals) + (← b.bound shape locals)
      if n > 4294967295 then throw "index addition may overflow u32"
      pure n
  | .mul a b => do
      let n := (← a.bound shape locals) * (← b.bound shape locals)
      if n > 4294967295 then throw "index multiplication may overflow u32"
      pure n

def Term.validate (shape : Shape) (indices : List Nat) (wordCount : Nat) :
    Term → Except String Unit
  | .lit _ => pure ()
  | .local i => if i < wordCount then pure () else .error "unbound word local"
  | .readA i => do
      if (← i.bound shape indices) ≥ shape.elementsA then throw "A index may be out of bounds"
  | .readB i => do
      if (← i.bound shape indices) ≥ shape.elementsB then throw "B index may be out of bounds"
  | .add a b | .mul a b => do
      a.validate shape indices wordCount
      b.validate shape indices wordCount
  | .letE value body => do
      value.validate shape indices wordCount
      body.validate shape indices (wordCount + 1)
  | .fold count initial body => do
      if count > 65535 then throw "fold count exceeds 65535"
      initial.validate shape indices wordCount
      body.validate shape ((count - 1) :: indices) (wordCount + 1)

def validate (shape : Shape) (term : Term) : Except String Unit := do
  if shape.rows == 0 || shape.cols == 0 then throw "output dimensions must be positive"
  if shape.rows > 524280 || shape.cols > 524280 then throw "dispatch dimension exceeds 65535 workgroups"
  if shape.elementsA == 0 || shape.elementsB == 0 ||
      shape.elementsA > 33554432 || shape.elementsB > 33554432 ||
      shape.rows * shape.cols > 33554432 then throw "buffers must have 1..33554432 elements"
  term.validate shape [] 0

def Index.lean : Index → String
  | .lit n => s!"(.lit {n})"
  | .row => ".row"
  | .col => ".col"
  | .local n => s!"(.local {n})"
  | .add a b => s!"(.add {a.lean} {b.lean})"
  | .mul a b => s!"(.mul {a.lean} {b.lean})"

def Term.lean : Term → String
  | .lit n => s!"(.lit {n.toNat})"
  | .local n => s!"(.local {n})"
  | .readA i => s!"(.readA {i.lean})"
  | .readB i => s!"(.readB {i.lean})"
  | .add a b => s!"(.add {a.lean} {b.lean})"
  | .mul a b => s!"(.mul {a.lean} {b.lean})"
  | .letE a b => s!"(.letE {a.lean} {b.lean})"
  | .fold n initial body => s!"(.fold {n} {initial.lean} {body.lean})"

end LeanExe.WGSL.Source
