import Project.TinyGpt2.Model
import Project.WGSL.Precision
import Lean

open Project.TinyGpt2 Project.WGSL

def rowList (x : Row) : List UInt64 := [x.x0, x.x1, x.x2, x.x3]
def contextList (x : Context) : List UInt64 :=
  rowList x.r0 ++ rowList x.r1 ++ rowList x.r2 ++ rowList x.r3
def wideList (x : WideRow) : List UInt64 := rowList x.low ++ rowList x.high
def probabilityList (x : Project.Softmax.Result) : List UInt64 := [x.p0,x.p1,x.p2,x.p3]
def fields (pairs : List (String × List UInt64)) : Lean.Json :=
  Lean.Json.mkObj (pairs.map fun (name, words) => (name, Lean.toJson (words.map (fun x => toString x.toNat))))

def trace (w : Array UInt64) (t0 t1 t2 t3 : UInt64) : Lean.Json := Id.run do
  let embedded : Context := ⟨embedding w t0 0, embedding w t1 1, embedding w t2 2, embedding w t3 3⟩
  let normalized : Context := ⟨norm w 2464 embedded.r0, norm w 2464 embedded.r1,
    norm w 2464 embedded.r2, norm w 2464 embedded.r3⟩
  let q := project4 w 1040 normalized.r3
  let k := projectContext w 1056 normalized
  let v := projectContext w 1072 normalized
  let scores0 := [k.r0,k.r1,k.r2,k.r3].map fun r => attentionScore q.x0 q.x1 r.x0 r.x1
  let scores1 := [k.r0,k.r1,k.r2,k.r3].map fun r => attentionScore q.x2 q.x3 r.x2 r.x3
  let p0 := headProbabilities 4 q.x0 q.x1 ⟨k.r0.x0,k.r1.x0,k.r2.x0,k.r3.x0⟩ ⟨k.r0.x1,k.r1.x1,k.r2.x1,k.r3.x1⟩
  let p1 := headProbabilities 4 q.x2 q.x3 ⟨k.r0.x2,k.r1.x2,k.r2.x2,k.r3.x2⟩ ⟨k.r0.x3,k.r1.x3,k.r2.x3,k.r3.x3⟩
  let attended := attentionRow 4 q k v
  let projected := project4 w 1088 attended
  let attention := addRows projected (loadRow w 1104)
  let r1 := addRows embedded.r3 attention
  let n2 := norm w 2472 r1
  let expanded := expandRow w n2
  let activated : WideRow := ⟨activate expanded.low,activate expanded.high⟩
  let projectedContract : Row := ⟨dotColumn8 w 1148 4 0 activated,dotColumn8 w 1148 4 1 activated,
    dotColumn8 w 1148 4 2 activated,dotColumn8 w 1148 4 3 activated⟩
  let contracted := contractRow w activated
  let r2 := addRows r1 contracted
  let h := norm w 2480 r2
  let head := (List.range 256).map fun j => logit w h j.toUInt64
  let mixed := (List.range 256).map fun j => Id.run do
    let mut acc : UInt32 := 0
    for i in [:4] do
      acc := Wasm.IEEE32.add acc (Wasm.IEEE32.mul (Precision.demote (rowList h)[i]!)
        (Precision.demote w[1184+256*i+j]!))
    return Wasm.IEEE64.add (Precision.promote acc) w[2208+j]!
  return fields [("embedding",contextList embedded),("norm1",contextList normalized),
    ("query",rowList q),("keys",contextList k),("values",contextList v),
    ("scores",scores0++scores1),("probability",probabilityList p0++probabilityList p1),
    ("attended",rowList attended),("attentionProjection",rowList projected),("attention",rowList attention),
    ("residual1",rowList r1),("norm2",rowList n2),("expanded",wideList expanded),
    ("activated",wideList activated),("contractProjection",rowList projectedContract),
    ("contracted",rowList contracted),("residual2",rowList r2),("hidden",rowList h),("head64",head),("mixed",mixed)]

def main (args : List String) : IO Unit := do
  unless args.length = 5 do throw (IO.userError "expected weights JSON and four byte tokens")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile args[0]!))
  let texts ← IO.ofExcept (Lean.fromJson? json : Except String (Array String))
  let words ← texts.mapM fun text => do
    let some n := text.toNat? | throw (IO.userError "invalid parameter word")
    unless n < 2^64 do throw (IO.userError "parameter exceeds 64 bits")
    pure n.toUInt64
  unless words.size = 2488 do throw (IO.userError "expected 2488 parameter words")
  let tokens ← args.tail!.mapM fun text => do
    let some n := text.toNat? | throw (IO.userError "invalid token")
    unless n < 256 do throw (IO.userError "token exceeds 255")
    pure n.toUInt64
  IO.println (trace words tokens[0]! tokens[1]! tokens[2]! tokens[3]!).compress
