import Verified.TailTreeNode

namespace Verified

open Wasm

theorem tail_treeCase_spec {S : List Sig} {Γ params : List Ty} {result : Ty}
    {shape : TreeShape} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {pool : Bytes.LiteralPool} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (targetModes : List Mode) (x : Var Γ (.tree shape))
    (empty : TailBody S params result Γ) (node : TailBody S params result (shape.context Γ))
    (emptySpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes empty)
    (nodeSpec : TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes node) :
    TailCodeSpec (pool := pool) m funs flags bounds fits host pv targetModes (.treeCase x empty node) := by
  intro env
  cases hv : env.get x with
  | nil => exact tail_treeCase_empty hm targetModes x empty node emptySpec env hv
  | node words children =>
    exact tail_treeCase_node hm targetModes x empty node nodeSpec env words children hv

#print axioms tail_treeCase_spec

end Verified
