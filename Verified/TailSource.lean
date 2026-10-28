import Verified.Compile
import Verified.FunRename
import Verified.TailRun

namespace Verified

def TailBody.toExpr (g : Sig) (hp : g.params = params) (hr : g.result = result) :
    {Γ : List Ty} → TailBody S params result Γ → Expr (g :: S) Γ result
  | _, .ret value => value.renameFuns (fun f => .there f)
  | _, .next args => by
    subst hp hr
    exact .call .here (fun i => (args i).renameFuns (fun f => .there f))
  | _, .ite cond yes no =>
    .ite (cond.renameFuns (fun f => .there f)) (yes.toExpr g hp hr) (no.toExpr g hp hr)
  | _, .letE value body => .letE (value.renameFuns (fun f => .there f)) (body.toExpr g hp hr)
  | _, .letPair value body => .letPair (value.renameFuns (fun f => .there f)) (body.toExpr g hp hr)
  | _, .treeCase x empty nodes =>
    .treeCase x (fun h => (empty h).toExpr g hp hr) (fun r => (nodes r).toExpr g hp hr)

theorem TailBody.toExpr_denote (body : TailBody S params result Γ) (g : Sig)
    (hp : g.params = params) (hr : g.result = result)
    (M : Env params → result.denote) (funs : Funs S) (env : Env Γ) :
    (body.toExpr g hp hr).denote
        (.cons (fun state => hr.symm ▸ M (hp ▸ state)) funs) env =
      (body.denote funs env).elim M id := by
  subst hp hr
  induction body with
  | ret value => simp [TailBody.toExpr, TailBody.denote, Expr.denote_weakenFuns]
  | next args =>
    simp only [TailBody.toExpr, Expr.denote, Funs.get, TailBody.denote, Sum.elim_inl]
    congr 2
    funext i
    exact Expr.denote_weakenFuns (args i) M funs env
  | ite cond yes no hy hn =>
    simp only [TailBody.toExpr, Expr.denote, Expr.denote_weakenFuns, TailBody.denote]
    split <;> simp_all
  | letE value body ih => simp [TailBody.toExpr, Expr.denote, Expr.denote_weakenFuns,
      TailBody.denote, ih]
  | letPair value body ih => simp [TailBody.toExpr, Expr.denote, Expr.denote_weakenFuns,
      TailBody.denote, ih]
  | treeCase x empty nodes he hn =>
    simp only [TailBody.toExpr, Expr.denote, TailBody.denote]
    cases env.get x with
    | nil h => exact he h env
    | node r words arrays buffers children =>
      exact hn r (Env.treeFields _ r words arrays buffers children env)

theorem TailBody.usesFast_eq (body : TailBody S params result Γ) (i : Nat) :
    body.usesFast i = body.uses i := by
  unfold TailBody.usesFast
  have hExpr : ∀ {Γ t} (e : Expr S Γ t) i, e.useMask.testBit i = e.uses i :=
    fun e i => e.usesFast_eq i
  induction body generalizing i with
  | treeCase x empty nodes emptyIh nodesIh =>
    simp only [TailBody.useMask, TailBody.uses, Nat.testBit_or, argsMask_testBit,
      Nat.testBit_shiftRight, testBit_one_shiftLeft, nodesIh, Nat.add_comm]
    split <;> simp_all
  | _ =>
    simp_all [TailBody.useMask, TailBody.uses, argsMask_testBit, Nat.testBit_or,
      Nat.testBit_shiftRight, hExpr, Nat.add_comm,
      testBit_one_shiftLeft, -Nat.testBit_shiftLeft]

theorem TailFunc.exists_run (func : TailFunc S) (funs : Funs S) (h : func.Decreases funs)
    (state : Env func.params) :
    ∃ value n, Tail.Run (func.body.denote funs) state value n :=
  Tail.Run.exists_of_wellFounded (measure (func.rank funs)).wf h state

theorem TailFunc.agrees (func : TailFunc S) (funs : Funs S) (h : func.Decreases funs)
    (meaning : Env func.params → func.result.denote)
    (fixed : ∀ state, meaning state = (func.body.denote funs state).elim meaning id)
    (state : Env func.params) :
    ∃ n, Tail.Run (func.body.denote funs) state (meaning state) n := by
  obtain ⟨value, n, run⟩ := func.exists_run funs h state
  have eq := run.eq_of_fixed fixed
  refine ⟨n, ?_⟩
  rw [eq]
  exact run

#print axioms TailBody.usesFast_eq
#print axioms TailBody.toExpr_denote
#print axioms TailFunc.exists_run
#print axioms TailFunc.agrees

end Verified
