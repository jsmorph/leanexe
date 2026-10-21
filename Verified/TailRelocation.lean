import Verified.FunRelocation

namespace Verified

def TailBody.renameFuns {S T : List Sig} (ρ : FunRenaming S T) :
    {Γ : List Ty} → TailBody S params result Γ → TailBody T params result Γ
  | _, .ret value => .ret (value.renameFuns ρ)
  | _, .next args => .next (fun i => (args i).renameFuns ρ)
  | _, .ite cond yes no => .ite (cond.renameFuns ρ) (yes.renameFuns ρ) (no.renameFuns ρ)
  | _, .letE value body => .letE (value.renameFuns ρ) (body.renameFuns ρ)
  | _, .letPair value body => .letPair (value.renameFuns ρ) (body.renameFuns ρ)
  | _, .treeCase x empty node => .treeCase x (empty.renameFuns ρ) (node.renameFuns ρ)

theorem TailBody.aborts_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (body : TailBody S params result Γ) : (body.renameFuns ρ).aborts = body.aborts := by
  induction body <;> simp_all [TailBody.renameFuns, TailBody.aborts, Expr.aborts_renameFuns]

theorem TailBody.depthCalls_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (body : TailBody S params result Γ) : (body.renameFuns ρ).depthCalls = body.depthCalls := by
  induction body <;> simp_all [TailBody.renameFuns, TailBody.depthCalls, Expr.depthCalls_renameFuns]

theorem TailBody.placeArgs_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (body : TailBody S params result Γ) (targetModes modes : List Mode) :
    (body.renameFuns ρ).placeArgs targetModes modes = body.placeArgs targetModes modes := by
  induction body generalizing modes <;>
    simp_all [TailBody.renameFuns, TailBody.placeArgs, Expr.placeArgs_renameFuns,
      Expr.varIndex_renameFuns, Expr.isPlace_renameFuns, Expr.mode_renameFuns]

theorem TailBody.denote_renameFuns {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (target : Funs T)
    (h : ∀ {g : Sig} (v : FVar S g) env, target.get (ρ v) env = funs.get v env)
    (body : TailBody S params result Γ) (env : Env Γ) :
    (body.renameFuns ρ).denote target env = body.denote funs env := by
  induction body <;> simp_all [TailBody.renameFuns, TailBody.denote,
    Expr.denote_renameFuns ρ funs target h]

def TailFunc.renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : TailFunc S) : TailFunc T where
  name := f.name
  params := f.params
  result := f.result
  modes := f.modes
  body := f.body.renameFuns ρ
  placeArgs := (f.body.placeArgs_renameFuns ρ f.modes (paramModes f.params f.modes)).trans f.placeArgs
  rank := fun target => f.rank (target.reindex ρ)

theorem TailFunc.sig_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : TailFunc S) :
    (f.renameFuns ρ).sig = f.sig := by
  simp only [TailFunc.sig, TailFunc.aborts, TailFunc.depth, TailFunc.renameFuns,
    TailBody.aborts_renameFuns, TailBody.depthCalls_renameFuns]

theorem TailFunc.decreases_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : TailFunc S)
    (funs : Funs S) (target : Funs T)
    (h : ∀ {g : Sig} (v : FVar S g) env, target.get (ρ v) env = funs.get v env)
    (decreases : f.Decreases funs) : (f.renameFuns ρ).Decreases target := by
  intro state next hNext
  change Env f.params at state next
  change (f.body.renameFuns ρ).denote target state = .inl next at hNext
  rw [TailBody.denote_renameFuns ρ funs target h] at hNext
  have hRanks := Funs.reindex_eq ρ funs target h
  change f.rank (target.reindex ρ) next < f.rank (target.reindex ρ) state
  simpa only [hRanks] using decreases state next hNext

end Verified
