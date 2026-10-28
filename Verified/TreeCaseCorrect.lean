import Verified.TreeCaseNode

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline

theorem spec_treeCase {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : shape.hasNull = true → Expr S Γ t)
    (nodes : (r : Fin shape.records) → Expr S (shape.context r Γ) t)
    (emptySpec : ∀ hn env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (empty hn) env slots paid live)
    (nodeSpec : ∀ r env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (nodes r) env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty nodes) env slots paid
        live := by
  intro env slots paid live
  cases hv : env.get x with
  | nil hn =>
    exact spec_treeCase_empty hm x empty nodes hn (emptySpec hn) env slots paid live hv
  | node r words arrays buffers children =>
    exact spec_treeCase_node hm x empty nodes r (nodeSpec r) env slots paid live words children
      hv

end Verified
