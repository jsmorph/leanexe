import Verified.TailBranch
import Verified.TailLetPair
import Verified.TailTreeCase
import Verified.ExprCorrect

namespace Verified

open Wasm

theorem TailBody.code_spec {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (hm : Runtime m) {pv : List Value}
    {d0 : UInt64} {pool : Bytes.LiteralPool}
    (hCalls : CallsAt m funs flags bounds fits d0 pool) {Γ params : List Ty}
    {result : Ty} (targetModes : List Mode) (body : TailBody S params result Γ) :
    body.Covered pool →
    (body.depthCalls = true → pv.head? = some (.i64 d0)) →
    TailCodeSpec m funs flags bounds fits host pv targetModes body pool := by
  induction body with
  | ret value =>
    intro hCovered hDepth
    exact tail_ret_spec hm targetModes value
      (Expr.code_spec m funs flags bounds fits host hm hCalls value hCovered hDepth)
  | next args =>
    intro hCovered hDepth
    have hArgs : ∀ i, (args i).Covered pool :=
      (literals_args_subset.mp hCovered)
    exact tail_next_spec hm targetModes args fun i =>
      Expr.code_spec m funs flags bounds fits host hm hCalls (args i) (hArgs i) fun hd =>
        hDepth (le_argsAny _ i hd)
  | ite cond yes no yesSpec noSpec =>
    intro hCovered hDepth
    have hParts : (cond.Covered pool ∧ yes.Covered pool) ∧ no.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals, Expr.Covered, List.append_subset,
        and_assoc] using hCovered
    exact tail_ite_spec hm targetModes cond yes no
      (Expr.code_spec m funs flags bounds fits host hm hCalls cond hParts.1.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (yesSpec hParts.1.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
      (noSpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letE value body bodySpec =>
    intro hCovered hDepth
    have hParts : value.Covered pool ∧ body.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals, Expr.Covered, List.append_subset] using hCovered
    exact tail_let_spec hm targetModes value body
      (Expr.code_spec m funs flags bounds fits host hm hCalls value hParts.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | letPair value body bodySpec =>
    intro hCovered hDepth
    have hParts : value.Covered pool ∧ body.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals, Expr.Covered, List.append_subset] using hCovered
    exact tail_letPair_spec hm targetModes value body
      (Expr.code_spec m funs flags bounds fits host hm hCalls value hParts.1 fun hd =>
        hDepth (by simp [TailBody.depthCalls, hd]))
      (bodySpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
  | treeCase x empty node emptySpec nodeSpec =>
    intro hCovered hDepth
    have hParts : empty.Covered pool ∧ node.Covered pool := by
      simpa only [TailBody.Covered, TailBody.literals, List.append_subset] using hCovered
    exact tail_treeCase_spec hm targetModes x empty node
      (emptySpec hParts.1 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))
      (nodeSpec hParts.2 fun hd => hDepth (by simp [TailBody.depthCalls, hd]))

#print axioms TailBody.code_spec

end Verified
