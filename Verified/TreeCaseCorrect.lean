import Verified.TreeCaseNode

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline

theorem spec_treeCase {S : List Sig} {Γ : List Ty} {t : Ty} {shape : TreeShape}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (x : Var Γ (.tree shape)) (empty : Expr S Γ t) (node : Expr S (shape.context Γ) t)
    (emptySpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv empty env slots paid live)
    (nodeSpec : ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv node env slots paid live) :
    ∀ env slots paid live,
      CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.treeCase x empty node) env slots paid live := by
  intro env slots paid live
  cases hv : env.get x with
  | nil => exact spec_treeCase_empty hm x empty node emptySpec env slots paid live hv
  | node words children =>
    exact spec_treeCase_node hm x empty node nodeSpec env slots paid live words children hv

end Verified
