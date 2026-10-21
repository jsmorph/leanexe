import Verified.FunRenameBound

namespace Verified

theorem Expr.aborts_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).aborts = e.aborts := by
  induction e <;> simp_all [Expr.renameFuns, Expr.aborts]

theorem Expr.depthCalls_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).depthCalls = e.depthCalls := by
  induction e <;> simp_all [Expr.renameFuns, Expr.depthCalls]

theorem Expr.placeArgs_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (e : Expr S Γ t) :
    (e.renameFuns ρ).placeArgs = e.placeArgs := by
  induction e <;> simp_all [Expr.renameFuns, Expr.placeArgs, Expr.isPlace_renameFuns,
    Expr.varIndex_renameFuns]

def FVar.appendLeft {S : List Sig} {g : Sig} (T : List Sig) : FVar S g → FVar (S ++ T) g
  | .here => .here
  | .there f => .there (f.appendLeft T)

def FVar.appendRight {T : List Sig} {g : Sig} :
    (S : List Sig) → FVar T g → FVar (S ++ T) g
  | [], f => f
  | _ :: S, f => .there (f.appendRight S)

def Funs.append {S T : List Sig} : Funs S → Funs T → Funs (S ++ T)
  | .nil, target => target
  | .cons f rest, target => .cons f (rest.append target)

theorem Funs.get_appendLeft {S T : List Sig} (funs : Funs S) (target : Funs T)
    {g : Sig} (f : FVar S g) (env : Env g.params) :
    (funs.append target).get (f.appendLeft T) env = funs.get f env := by
  induction f with
  | here => cases funs; rfl
  | there f ih => cases funs with | cons _ rest => exact ih rest env

theorem Funs.get_appendRight {S T : List Sig} (funs : Funs S) (target : Funs T)
    {g : Sig} (f : FVar T g) (env : Env g.params) :
    (funs.append target).get (f.appendRight S) env = target.get f env := by
  induction funs with
  | nil => rfl
  | cons _ rest ih => exact ih

def Func.renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : Func S) : Func T where
  name := f.name
  params := f.params
  result := f.result
  body := f.body.renameFuns ρ
  placeArgs := (f.body.placeArgs_renameFuns ρ).trans f.placeArgs
  modes := f.modes

theorem Func.sig_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : Func S) :
    (f.renameFuns ρ).sig = f.sig := by
  simp only [Func.sig, Func.aborts, Func.depth, Func.renameFuns,
    Expr.aborts_renameFuns, Expr.depthCalls_renameFuns]

theorem Func.denote_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : Func S)
    (funs : Funs S) (target : Funs T)
    (h : ∀ {g : Sig} (v : FVar S g) env, target.get (ρ v) env = funs.get v env)
    (env : Env f.params) : (f.renameFuns ρ).denote target env = f.denote funs env :=
  f.body.denote_renameFuns ρ funs target h env

def FunRenaming.lift {S T : List Sig} (ρ : FunRenaming S T) (h : Sig) :
    FunRenaming (h :: S) (h :: T)
  | _, .here => .here
  | _, .there f => .there (ρ f)

def Funs.reindex {S T : List Sig} (ρ : FunRenaming S T) (target : Funs T) : Funs S :=
  match S with
  | [] => .nil
  | _ :: _ => .cons (target.get (ρ .here)) (target.reindex (fun f => ρ (.there f)))

theorem Funs.get_reindex {S T : List Sig} (ρ : FunRenaming S T) (target : Funs T)
    {g : Sig} (f : FVar S g) (env : Env g.params) :
    (target.reindex ρ).get f env = target.get (ρ f) env := by
  induction f with
  | here => rfl
  | there f ih => exact ih (fun v => ρ (.there v)) env

theorem Funs.reindex_eq {S T : List Sig} (ρ : FunRenaming S T)
    (funs : Funs S) (target : Funs T)
    (h : ∀ {g : Sig} (v : FVar S g) env, target.get (ρ v) env = funs.get v env) :
    target.reindex ρ = funs := by
  induction funs with
  | nil => rfl
  | cons f rest ih =>
    change Funs.cons (target.get (ρ .here))
      (target.reindex (fun v => ρ (.there v))) = .cons f rest
    congr 1
    · funext env
      exact h .here env
    · exact ih (fun v => ρ (.there v)) (fun v env => h (.there v) env)

def RecFunc.renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : RecFunc S) : RecFunc T where
  name := f.name
  params := f.params
  result := f.result
  modes := f.modes
  body := f.body.renameFuns (ρ.lift f.sig)
  placeArgs := (f.body.placeArgs_renameFuns (ρ.lift f.sig)).trans f.placeArgs

theorem RecFunc.sig_renameFuns {S T : List Sig} (ρ : FunRenaming S T) (f : RecFunc S) :
    (f.renameFuns ρ).sig = f.sig := rfl

end Verified
