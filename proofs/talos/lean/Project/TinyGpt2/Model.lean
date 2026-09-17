import Project.TinyGpt2.Layout
import Project.Affine.Model
import Project.LayerNorm.Model
import Project.SoftmaxWide.Model
import Project.GeluWide.Model

namespace Project.TinyGpt2

structure Row where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  deriving DecidableEq, Inhabited

structure WideRow where
  low : Row
  high : Row
  deriving DecidableEq, Inhabited

structure Context where
  r0 : Row
  r1 : Row
  r2 : Row
  r3 : Row
  deriving DecidableEq, Inhabited

def loadRow (w : Array UInt64) (offset : Nat) : Row :=
  ⟨w[offset]!, w[offset+1]!, w[offset+2]!, w[offset+3]!⟩

def addRows (x y : Row) : Row :=
  ⟨Wasm.IEEE64.add x.x0 y.x0, Wasm.IEEE64.add x.x1 y.x1,
    Wasm.IEEE64.add x.x2 y.x2, Wasm.IEEE64.add x.x3 y.x3⟩

def embedding (w : Array UInt64) (token position : UInt64) : Row :=
  addRows (loadRow w (Layout.token+4*token.toNat))
    (loadRow w (Layout.position+4*position.toNat))

def norm (w : Array UInt64) (offset : Nat) (x : Row) : Row :=
  let g := loadRow w offset
  let b := loadRow w (offset+4)
  let y := LayerNorm.compute x.x0 x.x1 x.x2 x.x3 g.x0 g.x1 g.x2 g.x3 b.x0 b.x1 b.x2 b.x3
  ⟨y.y0, y.y1, y.y2, y.y3⟩

def dotColumn4 (w : Array UInt64) (offset width column : Nat) (x : Row) : UInt64 :=
  Affine.dot4 x.x0 x.x1 x.x2 x.x3 w[offset+column]! w[offset+width+column]!
    w[offset+2*width+column]! w[offset+3*width+column]!

def dotColumn8 (w : Array UInt64) (offset width column : Nat) (x : WideRow) : UInt64 :=
  Affine.dot8 x.low.x0 x.low.x1 x.low.x2 x.low.x3 x.high.x0 x.high.x1 x.high.x2 x.high.x3
    w[offset+column]! w[offset+width+column]! w[offset+2*width+column]!
    w[offset+3*width+column]! w[offset+4*width+column]! w[offset+5*width+column]!
    w[offset+6*width+column]! w[offset+7*width+column]!

def project4 (w : Array UInt64) (offset : Nat) (x : Row) : Row :=
  ⟨dotColumn4 w offset 4 0 x, dotColumn4 w offset 4 1 x,
    dotColumn4 w offset 4 2 x, dotColumn4 w offset 4 3 x⟩

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

def activate (x : Row) : Row :=
  ⟨GeluWide.evaluateAll x.x0, GeluWide.evaluateAll x.x1, GeluWide.evaluateAll x.x2, GeluWide.evaluateAll x.x3⟩

def projectContext (w : Array UInt64) (offset : Nat) (x : Context) : Context :=
  ⟨project4 w offset x.r0, project4 w offset x.r1, project4 w offset x.r2, project4 w offset x.r3⟩

def contextRow (x : Context) (position : UInt64) : Row :=
  if position == 0 then x.r0 else if position == 1 then x.r1
  else if position == 2 then x.r2 else x.r3

def attentionScore (q0 q1 k0 k1 : UInt64) : UInt64 :=
  Wasm.IEEE64.div (Affine.dot2 q0 q1 k0 k1) 0x3FF6A09E667F3BCD

def headProbabilities (n q0 q1 : UInt64) (k0 k1 : Row) : Softmax.Result :=
  SoftmaxWide.compute n (attentionScore q0 q1 k0.x0 k1.x0) (attentionScore q0 q1 k0.x1 k1.x1)
    (attentionScore q0 q1 k0.x2 k1.x2) (attentionScore q0 q1 k0.x3 k1.x3)

def weightedValue (p : Softmax.Result) (v0 v1 v2 v3 : UInt64) : UInt64 :=
  Affine.dot4 p.p0 p.p1 p.p2 p.p3 v0 v1 v2 v3

def attentionRow (n : UInt64) (q : Row) (k v : Context) : Row :=
  let p0 := headProbabilities n q.x0 q.x1
    ⟨k.r0.x0, k.r1.x0, k.r2.x0, k.r3.x0⟩ ⟨k.r0.x1, k.r1.x1, k.r2.x1, k.r3.x1⟩
  let p1 := headProbabilities n q.x2 q.x3
    ⟨k.r0.x2, k.r1.x2, k.r2.x2, k.r3.x2⟩ ⟨k.r0.x3, k.r1.x3, k.r2.x3, k.r3.x3⟩
  ⟨weightedValue p0 v.r0.x0 v.r1.x0 v.r2.x0 v.r3.x0,
    weightedValue p0 v.r0.x1 v.r1.x1 v.r2.x1 v.r3.x1,
    weightedValue p1 v.r0.x2 v.r1.x2 v.r2.x2 v.r3.x2,
    weightedValue p1 v.r0.x3 v.r1.x3 v.r2.x3 v.r3.x3⟩

def hidden (w : Array UInt64) (t0 t1 t2 t3 position : UInt64) : Row :=
  let embedded := Context.mk (embedding w t0 0) (embedding w t1 1)
    (embedding w t2 2) (embedding w t3 3)
  let normalized := Context.mk (norm w Layout.norm1 embedded.r0) (norm w Layout.norm1 embedded.r1)
    (norm w Layout.norm1 embedded.r2) (norm w Layout.norm1 embedded.r3)
  let q := project4 w Layout.query (contextRow normalized position)
  let k := projectContext w Layout.key normalized
  let v := projectContext w Layout.value normalized
  let attended := attentionRow (position+1) q k v
  let attention := addRows (project4 w Layout.attention attended) (loadRow w Layout.attentionBias)
  let r1 := addRows (contextRow embedded position) attention
  let expanded := expandRow w (norm w Layout.norm2 r1)
  let activated := WideRow.mk (activate expanded.low) (activate expanded.high)
  let r2 := addRows r1 (contractRow w activated)
  norm w Layout.normFinal r2

def logit (w : Array UInt64) (x : Row) (token : UInt64) : UInt64 :=
  Wasm.IEEE64.add (dotColumn4 w Layout.head 256 token.toNat x) w[Layout.headBias+token.toNat]!

end Project.TinyGpt2
