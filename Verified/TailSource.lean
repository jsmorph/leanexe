import Verified.Compile
import Verified.FunRename
import Verified.TailRun

namespace Verified

inductive TailBody (S : List Sig) (params : List Ty) (result : Ty) : List Ty → Type where
  | ret (value : Expr S Γ result) : TailBody S params result Γ
  | next (args : (i : Fin params.length) → Expr S Γ (params.get i)) :
      TailBody S params result Γ
  | ite (cond : Expr S Γ .bool) (yes no : TailBody S params result Γ) :
      TailBody S params result Γ
  | letE (value : Expr S Γ t) (body : TailBody S params result (t :: Γ)) :
      TailBody S params result Γ
  | letPair (value : Expr S Γ (.pair s t)) (body : TailBody S params result (t :: s :: Γ)) :
      TailBody S params result Γ

def TailBody.denote (funs : Funs S) : {Γ : List Ty} → TailBody S params result Γ →
    Env Γ → Sum (Env params) result.denote
  | _, .ret value, env => .inr (value.denote funs env)
  | _, .next args, env => .inl (Env.ofFn fun i => (args i).denote funs env)
  | _, .ite cond yes no, env =>
    if cond.denote funs env then yes.denote funs env else no.denote funs env
  | _, .letE value body, env => body.denote funs (.cons (value.denote funs env) env)
  | _, .letPair value body, env =>
    let pair := value.denote funs env
    body.denote funs (.cons pair.2 (.cons pair.1 env))

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

def TailBody.uses : {Γ : List Ty} → TailBody S params result Γ → Nat → Bool
  | _, .ret value, i => value.uses i
  | _, .next args, i => argsAny fun j => (args j).uses i
  | _, .ite cond yes no, i => cond.uses i || yes.uses i || no.uses i
  | _, .letE value body, i => value.uses i || body.uses (i + 1)
  | _, .letPair value body, i => value.uses i || body.uses (i + 2)

def TailBody.useMask : {Γ : List Ty} → TailBody S params result Γ → Nat
  | _, .ret value => value.useMask
  | _, .next args => argsMask fun j => (args j).useMask
  | _, .ite cond yes no => cond.useMask ||| yes.useMask ||| no.useMask
  | _, .letE value body => value.useMask ||| body.useMask >>> 1
  | _, .letPair value body => value.useMask ||| body.useMask >>> 2

def TailBody.usesFast (body : TailBody S params result Γ) (i : Nat) : Bool :=
  body.useMask.testBit i

theorem TailBody.usesFast_eq (body : TailBody S params result Γ) (i : Nat) :
    body.usesFast i = body.uses i := by
  unfold TailBody.usesFast
  have hExpr : ∀ {Γ t} (e : Expr S Γ t) i, e.useMask.testBit i = e.uses i :=
    fun e i => e.usesFast_eq i
  induction body generalizing i <;>
    simp_all [TailBody.useMask, TailBody.uses, argsMask_testBit, Nat.testBit_or,
      Nat.testBit_shiftRight, hExpr, Nat.add_comm]

def TailBody.depthCalls : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.depthCalls
  | _, .next args => argsAny fun i => (args i).depthCalls
  | _, .ite cond yes no => cond.depthCalls || yes.depthCalls || no.depthCalls
  | _, .letE value body | _, .letPair value body => value.depthCalls || body.depthCalls

def TailBody.aborts : {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.aborts
  | _, .next args => argsAny fun i => (args i).aborts
  | _, .ite cond yes no => cond.aborts || yes.aborts || no.aborts
  | _, .letE value body | _, .letPair value body => value.aborts || body.aborts

def TailBody.placeArgs (targetModes : List Mode) (modes : List Mode) :
    {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.placeArgs
  | _, .next args =>
    !(argsAny fun i => !(args i).placeArgs) &&
      !(argsAny fun i =>
        !(params.get i).scalar &&
          if paramMode params targetModes i == .owned then (args i).varIndex?.isNone
          else !(args i).isPlace || (args i).mode modes != .borrowed)
  | _, .ite cond yes no =>
    cond.placeArgs && yes.placeArgs targetModes modes && no.placeArgs targetModes modes
  | _, .letE value body =>
    value.placeArgs && body.placeArgs targetModes (value.mode modes :: modes)
  | _, .letPair value body =>
    value.placeArgs && body.placeArgs targetModes (value.mode modes :: value.mode modes :: modes)

structure TailFunc (S : List Sig) where
  name : String
  params : List Ty
  result : Ty
  modes : List Mode
  body : TailBody S params result params
  placeArgs : body.placeArgs modes (paramModes params modes) = true
  rank : Funs S → Env params → Nat

def TailFunc.Decreases (func : TailFunc S) (funs : Funs S) : Prop :=
  ∀ state next, func.body.denote funs state = .inl next → func.rank funs next < func.rank funs state

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
