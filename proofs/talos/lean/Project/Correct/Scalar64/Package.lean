import Lean
import Project.Correct.Scalar64.Encode
import Project.Correct.Scalar64.Certificate

/-! Untrusted serialization for portable proof-carrying packages. Only data is
emitted. The verifier reconstructs closed equalities and audits their axioms. -/
namespace Project.Correct.Scalar64.Package
open Lean
open Project.ProofKit.ScalarTransition

private def node (tag : String) (fields : List Json := []) : Json :=
  Json.arr ((Json.str tag :: fields).toArray)
private def number (n : Nat) : Json := toJson n
private def opName : U64Op → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .divU => "divU" | .remU => "remU"
  | .bitAnd => "bitAnd" | .bitOr => "bitOr" | .bitXor => "bitXor"
  | .shiftLeft => "shiftLeft" | .shiftRight => "shiftRight"

def expression : {type : ScalarType} → Expr type → Json
  | _, .get i => node "get" [number i]
  | _, .const v => node "const" [number v.toNat]
  | _, .bconst v => node "bconst" [toJson v]
  | _, .bin op a b => node "bin" [toJson (opName op), expression a, expression b]
  | _, .eq a b => node "eq" [expression a, expression b]
  | _, .ne a b => node "ne" [expression a, expression b]
  | _, .ltU a b => node "ltU" [expression a, expression b]
  | _, .leU a b => node "leU" [expression a, expression b]
  | _, .not a => node "not" [expression a]
  | _, .and a b => node "and" [expression a, expression b]
  | _, .or a b => node "or" [expression a, expression b]
  | _, .ite c a b => node "ite" [expression c, expression a, expression b]

def command : Command → Json
  | .skip => node "skip"
  | .assign i e => node "assign" [number i, expression e]
  | .seq a b => node "seq" [command a, command b]
  | .branch c a b => node "branch" [expression c, command a, command b]
  | .loop c b => node "loop" [expression c, command b]
  | .call dst fn args => node "call" [number dst, number fn, toJson (args.map expression)]

def function (f : Function) : Json :=
  Json.mkObj [("arity", number f.arity), ("locals", number f.localCount),
    ("scratch", number f.scratch), ("body", command f.body), ("result", expression f.result)]

private def wordOp : LeanExe.TypeSafety.WordBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .min => "min" | .max => "max" | .bitAnd => "bitAnd" | .bitOr => "bitOr"
  | .bitXor => "bitXor" | .shiftLeft => "shiftLeft" | .shiftRight => "shiftRight"
private def cmpOp : LeanExe.TypeSafety.NatCmpOp → String
  | .eq => "eq" | .lt => "lt" | .le => "le"

mutual
  def core : LeanExe.TypeSafety.Expr → Except String Json
    | .var i => pure (node "var" [number i])
    | .bool v => pure (node "bool" [toJson v])
    | .word .w64 v => pure (node "word" [number v])
    | .letE a b => return node "letE" [← core a, ← core b]
    | .ifE c a b => return node "ifE" [← core c, ← core a, ← core b]
    | .wordBin .w64 op a b => return node "wordBin" [toJson (wordOp op), ← core a, ← core b]
    | .wordCmp .w64 op a b => return node "wordCmp" [toJson (cmpOp op), ← core a, ← core b]
    | .call fn args => return node "call" [number fn, toJson (← cores args)]
    | _ => .error "scalar64: unsupported source core form"
  def cores : List LeanExe.TypeSafety.Expr → Except String (List Json)
    | [] => pure []
    | e :: es => return (← core e) :: (← cores es)
end

/-- Entry for an untrusted generator. A Certificate must already have been checked
against the original source declaration; unknown or unsupported sources fail closed. -/
def emit (certificate : Certificate Input args source) (directory : System.FilePath) : IO Unit := do
  let .ok bytes := encode certificate.functions certificate.exportName certificate.entry
    | throw (IO.userError "scalar64: IR admission or byte encoding failed")
  let .ok sourceCore := cores certificate.core
    | throw (IO.userError "scalar64: source form outside profile")
  let data := Json.mkObj [
    ("functions", toJson (certificate.functions.map function)),
    ("core", toJson sourceCore),
    ("signatures", toJson (certificate.signatures.map (fun s => s.params.length))),
    ("core_entry", number certificate.coreEntry),
    ("entry", number certificate.entry), ("export", toJson certificate.exportName),
    ("arity", number certificate.function.arity)]
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "program.wasm") bytes
  IO.FS.writeFile (directory / "translation.json") (data.pretty ++ "\n")

end Project.Correct.Scalar64.Package
