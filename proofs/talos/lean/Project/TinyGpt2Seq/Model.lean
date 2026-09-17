import Project.TinyGpt2.Model
import Project.TinyGpt2Seq.Layout
import Project.SequenceSoftmax.Model

namespace Project.TinyGpt2Seq
open Project.TinyGpt2

def normalizedInputs (w tokens : Array UInt64) : Array Row := Id.run do
  let mut rows := #[]
  for i in [:tokens.size] do
    rows := rows.push (norm w Layout.norm1 (embedding w tokens[i]! i.toUInt64))
  return rows

def projectRows (w : Array UInt64) (offset : Nat) (rows : Array Row) : Array Row :=
  rows.map fun x => project4 w offset x

def scores (q0 q1 : UInt64) (second : Bool) (keys : Array Row) : Array UInt64 :=
  keys.map fun k =>
    if second then attentionScore q0 q1 k.x2 k.x3
    else attentionScore q0 q1 k.x0 k.x1

def weightedValues (p0 p1 : Array UInt64) (values : Array Row) : Row := Id.run do
  let mut x : Row := ⟨0, 0, 0, 0⟩
  for i in [:values.size] do
    let v := values[i]!
    x := ⟨Wasm.IEEE64.add x.x0 (Wasm.IEEE64.mul p0[i]! v.x0),
      Wasm.IEEE64.add x.x1 (Wasm.IEEE64.mul p0[i]! v.x1),
      Wasm.IEEE64.add x.x2 (Wasm.IEEE64.mul p1[i]! v.x2),
      Wasm.IEEE64.add x.x3 (Wasm.IEEE64.mul p1[i]! v.x3)⟩
  return x

def attentionRow (w : Array UInt64) (rows : Array Row) : Row :=
  let q := project4 w Layout.query rows[rows.size-1]!
  let k := projectRows w Layout.key rows
  let v := projectRows w Layout.value rows
  let p0 := SequenceSoftmax.compute (scores q.x0 q.x1 false k)
  let p1 := SequenceSoftmax.compute (scores q.x2 q.x3 true k)
  weightedValues p0 p1 v

def expandRow (w : Array UInt64) (x : Row) : WideRow :=
  let low := Row.mk (dotColumn4 w Layout.expand 8 0 x) (dotColumn4 w Layout.expand 8 1 x)
    (dotColumn4 w Layout.expand 8 2 x) (dotColumn4 w Layout.expand 8 3 x)
  let high := Row.mk (dotColumn4 w Layout.expand 8 4 x) (dotColumn4 w Layout.expand 8 5 x)
    (dotColumn4 w Layout.expand 8 6 x) (dotColumn4 w Layout.expand 8 7 x)
  ⟨addRows low (loadRow w Layout.expandBias), addRows high (loadRow w (Layout.expandBias+4))⟩

def contractRow (w : Array UInt64) (x : WideRow) : Row :=
  addRows ⟨dotColumn8 w Layout.contract 4 0 x, dotColumn8 w Layout.contract 4 1 x,
    dotColumn8 w Layout.contract 4 2 x, dotColumn8 w Layout.contract 4 3 x⟩
    (loadRow w Layout.contractBias)

def hidden (w tokens : Array UInt64) : Row :=
  let position := tokens.size-1
  let rows := normalizedInputs w tokens
  let attended := attentionRow w rows
  let attention := addRows (project4 w Layout.attention attended) (loadRow w Layout.attentionBias)
  let r1 := addRows (embedding w tokens[position]! position.toUInt64) attention
  let expanded := expandRow w (norm w Layout.norm2 r1)
  let activated := WideRow.mk (activate expanded.low) (activate expanded.high)
  let r2 := addRows r1 (contractRow w activated)
  norm w Layout.normFinal r2

def logit (w : Array UInt64) (x : Row) (token : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dotColumn4 w Layout.head 256 token.toNat x) w[Layout.headBias+token.toNat]!

end Project.TinyGpt2Seq
