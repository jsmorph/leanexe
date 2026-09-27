import Project.SpectralKL.WordEstimator

/-! The integer reduction kernel is one program value. Its interpreter and WGSL
printer consume that value. The source parser is defined in WordShaderSource. -/
namespace Project.SpectralKL.WordShader
open WordMoments

inductive Var where
  | row | entry | width | lo | hi | old | term
deriving DecidableEq, Repr

inductive Op where
  | add | sub | mul | div | mod
deriving DecidableEq, Repr

inductive Expr where
  | lit (v : UInt32)
  | var (v : Var)
  | load (index : Expr)
  | bin (op : Op) (a b : Expr)
  | carry (a b : Expr)
deriving DecidableEq, Repr

structure Env where
  input : Nat → UInt32
  row : UInt32
  entry : UInt32
  width : UInt32
  lo : UInt32
  hi : UInt32
  old : UInt32
  term : UInt32

def Env.get (e : Env) : Var → UInt32
  | .row => e.row | .entry => e.entry | .width => e.width
  | .lo => e.lo | .hi => e.hi | .old => e.old | .term => e.term

def Op.eval : Op → UInt32 → UInt32 → UInt32
  | .add,a,b => a+b | .sub,a,b => a-b | .mul,a,b => a*b
  | .div,a,b => a/b | .mod,a,b => a%b

def Expr.eval (e : Env) : Expr → UInt32
  | .lit v => v
  | .var v => e.get v
  | .load i => e.input (i.eval e).toNat
  | .bin op a b => op.eval (a.eval e) (b.eval e)
  | .carry a b => if a.eval e < b.eval e then 1 else 0

structure Program where
  meanTerm : Expr
  productTerm : Expr
  nextLo : Expr
  nextHi : Expr
deriving DecidableEq, Repr

def address (column : Expr) : Expr := .bin .add (.bin .mul (.var .row) (.var .width)) column

def kernel : Program := {
  meanTerm := .load (address (.var .entry))
  productTerm := .bin .mul
    (.load (address (.bin .div (.bin .sub (.var .entry) (.var .width)) (.var .width))))
    (.load (address (.bin .mod (.bin .sub (.var .entry) (.var .width)) (.var .width))))
  nextLo := .bin .add (.var .lo) (.var .term)
  nextHi := .bin .add (.var .hi) (.carry (.var .lo) (.var .old))
}

def termAt (p : Program) (input : Nat → UInt32) (width entry row : UInt32) : UInt32 :=
  let env : Env := ⟨input,row,entry,width,0,0,0,0⟩
  if entry < width then p.meanTerm.eval env else p.productTerm.eval env

def step (p : Program) (input : Nat → UInt32) (width entry row : UInt32) (s : Sum64) : Sum64 :=
  let initial : Env := ⟨input,row,entry,width,s.lo,s.hi,0,0⟩
  let term := if entry < width then p.meanTerm.eval initial else p.productTerm.eval initial
  let env : Env := ⟨input,row,entry,width,s.lo,s.hi,s.lo,term⟩
  let lo := p.nextLo.eval env
  let hi := p.nextHi.eval {env with lo := lo}
  ⟨lo,hi⟩

theorem kernel_step (input : Nat → UInt32) (width entry row : UInt32) (s : Sum64) :
    step kernel input width entry row s = addWord s (termAt kernel input width entry row) := by
  rfl

/-- Denotation of the canonical increasing u32 loop. All row values are below
the u32 count, so its increment never wraps before the loop terminates. -/
def run (p : Program) (input : Nat → UInt32) (width entry count : UInt32) : Sum64 :=
  (List.range count.toNat).foldl (fun s r => step p input width entry (UInt32.ofNat r) s) ⟨0,0⟩

theorem run_eq_reduce (input : Nat → UInt32) (width entry count : UInt32) :
    run kernel input width entry count =
      reduce ((List.range count.toNat).map fun r => termAt kernel input width entry (UInt32.ofNat r)) := by
  simp only [run,reduce,List.foldl_map,kernel_step]

theorem run_value (input : Nat → UInt32) (width entry count : UInt32) (h : count.toNat ≤ 1048576) :
    (run kernel input width entry count).value =
      ((List.range count.toNat).map fun r => (termAt kernel input width entry (UInt32.ofNat r)).toNat).sum := by
  rw [run_eq_reduce,reduce_exact _ (by simpa using h)]
  simp only [List.map_map,Function.comp_def]

def Var.source : Var → String
  | .row => "row" | .entry => "entry" | .width => "params.width"
  | .lo => "lo" | .hi => "hi" | .old => "old" | .term => "term"

def Op.source : Op → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"

def Expr.tokens : Expr → List String
  | .lit v => [toString v.toNat++"u"]
  | .var v => [v.source]
  | .load i => ["samples","["]++i.tokens++["]"]
  | .bin op a b => ["("]++a.tokens++[op.source]++b.tokens++[")"]
  | .carry a b => ["select","(","0u",",","1u",",","("]++a.tokens++["<"]++b.tokens++[")",")"]

def preamble : List String := [
  "struct","Params","{","rows",":","u32",",","width",":","u32",",","entries",":","u32",",","padding",":","u32","}",
  "@group(0)","@binding(0)","var<uniform>","params",":","Params",";",
  "@group(0)","@binding(1)","var<storage,read>","samples",":","array<u32>",";",
  "@group(0)","@binding(2)","var<storage,read_write>","moments",":","array<vec2<u32>>",";",
  "@compute","@workgroup_size(64)","fn","main","(","@builtin(global_invocation_id)","gid",":","vec3<u32>",")","{",
  "let","entry","=","gid.x",";","if","(","entry",">=","params.entries",")","{","return",";","}",
  "var","lo","=","0u",";","var","hi","=","0u",";",
  "for","(","var","row","=","0u",";","row","<","params.rows",";","row","=","(","row","+","1u",")",")","{",
  "var","term","=","0u",";","if","(","entry","<","params.width",")","{","term","="]

def middle1 : List String := [";","}","else","{","term","="]
def middle2 : List String := [";","}","let","old","=","lo",";","lo","="]
def middle3 : List String := [";","hi","="]
def suffix : List String := [";","}","moments","[","entry","]","=","vec2<u32>","(","lo",",","hi",")",";","}"]

def Program.tokens (p : Program) : List String :=
  preamble++p.meanTerm.tokens++middle1++p.productTerm.tokens++middle2++
    p.nextLo.tokens++middle3++p.nextHi.tokens++suffix

def renderTokens (tokens : List String) : List Char :=
  tokens.flatMap fun t => t.toList++[' ']

def Program.source (p : Program) : String := String.ofList (renderTokens p.tokens)

#print axioms run_value
end Project.SpectralKL.WordShader
