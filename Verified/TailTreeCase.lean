import Verified.TailTreeNode

namespace Verified

open Wasm

theorem tail_treeCase_spec {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : shape.hasNull = true → TailBody S params result Γ)
    (nodes : (r : Fin shape.records) → TailBody S params result (shape.context r Γ))
    (emptySpec : ∀ hn, TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (empty hn))
    (nodeSpec : ∀ r, TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (nodes r)) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty nodes) := by
  intro env
  cases hv : env.get x with
  | nil hn => exact tail_treeCase_empty hm targetModes x empty nodes hn (emptySpec hn) env hv
  | node r words arrays buffers children =>
    exact tail_treeCase_node hm targetModes x empty nodes r (nodeSpec r) env words arrays buffers
      children hv

#print axioms tail_treeCase_spec

end Verified
