import Verified.TailBranch
import Verified.TailLetPair

namespace Verified

open Wasm

theorem TailBody.code_spec {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (hm : Runtime m) {pv : List Value}
    {d0 : UInt64} (hCalls : CallsAt m funs flags bounds fits d0) {Γ params : List Ty}
    {result : Ty} (targetModes : List Mode) (body : TailBody S params result Γ) :
    (body.depthCalls = true → pv.head? = some (.i64 d0)) →
    TailCodeSpec m funs flags bounds fits host pv targetModes body := by
  induction body with
  | ret value =>
    intro hDepth
    exact tail_ret_spec hm targetModes value
      (Expr.code_spec m funs flags bounds fits host hm hCalls value hDepth)
  | next args =>
    intro hDepth
    exact tail_next_spec hm targetModes args fun i =>
      Expr.code_spec m funs flags bounds fits host hm hCalls (args i) fun hd =>
        hDepth (le_argsAny _ i hd)
  | ite cond yes no yesSpec noSpec =>
    intro hDepth
    exact tail_ite_spec hm targetModes cond yes no
      (Expr.code_spec m funs flags bounds fits host hm hCalls cond fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (yesSpec fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
      (noSpec fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letE value body bodySpec =>
    intro hDepth
    exact tail_let_spec hm targetModes value body
      (Expr.code_spec m funs flags bounds fits host hm hCalls value fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letPair value body bodySpec =>
    intro hDepth
    exact tail_letPair_spec hm targetModes value body
      (Expr.code_spec m funs flags bounds fits host hm hCalls value fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec fun hd => hDepth (by simp [TailBody.depthCalls, hd]))

#print axioms TailBody.code_spec

end Verified
