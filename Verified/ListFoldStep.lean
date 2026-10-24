import Verified.ListFoldSource
import Verified.TailTreeCase
import Verified.TailLet
import Verified.TailNext

namespace Verified.ListFold

open Wasm

theorem step_spec {S : List Sig} {e : Elem} {captures : List Ty}
    {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
    {host : HostEnv Unit} {pv : List Value} (hm : Runtime m)
    (body : Expr S (context e captures) (.elem e))
    (bodySpec : ∀ env slots paid live,
      CodeSpec m funs flags bounds fits host pv body env slots paid live) :
    TailCodeSpec m funs flags bounds fits host pv [] (tailBody body) := by
  apply tail_treeCase_spec hm []
  · intro _
    exact tail_ret_spec hm [] _ (spec_var hm _)
  · intro r
    obtain rfl := listShape_cell r
    change TailCodeSpec _ _ _ _ _ _ _ [] (TailBody.letE body _)
    apply tail_let_spec hm [] body _ bodySpec
    apply tail_next_spec hm []
    intro i
    obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
    rw [hx]
    exact spec_var hm x

#print axioms step_spec

end Verified.ListFold
