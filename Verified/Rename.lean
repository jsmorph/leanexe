import Verified.Source

namespace Verified

abbrev Renaming (Γ Δ : List Ty) := ∀ {t}, Var Γ t → Var Δ t

def Renaming.lift {s : Ty} (ρ : Renaming Γ Δ) : Renaming (s :: Γ) (s :: Δ)
  | _, .here => .here
  | _, .there x => .there (ρ x)

def Renaming.liftRepeat (t : Ty) : (n : Nat) → Renaming Γ Δ →
    Renaming (List.replicate n t ++ Γ) (List.replicate n t ++ Δ)
  | 0, ρ => ρ
  | n + 1, ρ => Renaming.lift (Renaming.liftRepeat t n ρ)

def Renaming.treeFields (shape : TreeShape) (ρ : Renaming Γ Δ) :
    Renaming (shape.context Γ) (shape.context Δ) :=
  Renaming.lift (Renaming.liftRepeat .word shape.words
    (Renaming.liftRepeat (.tree shape) shape.children ρ))

def Env.remap : {Γ Δ : List Ty} → Renaming Γ Δ → Env Δ → Env Γ
  | [], _, _, _ => .nil
  | _ :: _, _, ρ, env => .cons (env.get (ρ .here)) (env.remap fun x => ρ (.there x))

theorem Env.ext_get {env env' : Env Γ} (h : ∀ {t} (x : Var Γ t), env.get x = env'.get x) :
    env = env' := by
  induction env with
  | nil => cases env'; rfl
  | cons v env ih =>
    cases env' with
    | cons v' env' =>
      have hv : v = v' := h .here
      have he : env = env' := ih fun x => h (.there x)
      cases hv
      cases he
      rfl

@[simp] theorem Env.get_remap (ρ : Renaming Γ Δ) (env : Env Δ) (x : Var Γ t) :
    (env.remap ρ).get x = env.get (ρ x) := by
  induction x with
  | here => rfl
  | there x ih => exact ih _

@[simp] theorem Env.remap_lift {s : Ty} (ρ : Renaming Γ Δ) (env : Env Δ) (v : s.denote) :
    (Env.cons v env).remap ρ.lift = .cons v (env.remap ρ) := by
  apply Env.ext_get
  intro t x
  cases x <;> simp [Env.get, Renaming.lift]

@[simp] theorem Env.remap_there {s : Ty} (env : Env Γ) (v : s.denote) :
    (Env.cons v env).remap (fun x => .there x) = env := by
  apply Env.ext_get
  intro t x
  simp [Env.get]

@[simp] theorem Env.remap_prependRepeat (t : Ty) (n : Nat) (values : Fin n → t.denote)
    (env : Env Δ) (ρ : Renaming Γ Δ) :
    (env.prependRepeat t n values).remap (ρ.liftRepeat t n) =
      (env.remap ρ).prependRepeat t n values := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Env.prependRepeat, Renaming.liftRepeat, Env.remap_lift, ih]

@[simp] theorem Env.remap_treeFields (shape : TreeShape) (words : Fin shape.words → UInt64)
    (children : Fin shape.children → Tree shape) (env : Env Δ) (ρ : Renaming Γ Δ) :
    (env.treeFields shape words children).remap (ρ.treeFields shape) =
      (env.remap ρ).treeFields shape words children := by
  let rc : Renaming (List.replicate shape.children (.tree shape) ++ Γ)
      (List.replicate shape.children (.tree shape) ++ Δ) :=
    Renaming.liftRepeat (.tree shape) shape.children ρ
  let rwds : Renaming (List.replicate shape.words .word ++
      (List.replicate shape.children (.tree shape) ++ Γ))
      (List.replicate shape.words .word ++
      (List.replicate shape.children (.tree shape) ++ Δ)) :=
    Renaming.liftRepeat .word shape.words rc
  exact (Env.remap_lift (s := .treeHeader shape) rwds
    (Env.prependRepeat .word shape.words words
      (env.prependRepeat (.tree shape) shape.children children))
    (TreeHeader.unit (shape := shape))).trans
    (congrArg (Env.cons (t := .treeHeader shape) TreeHeader.unit)
      ((Env.remap_prependRepeat .word shape.words words
        (env.prependRepeat (.tree shape) shape.children children) rc).trans
        (congrArg (Env.prependRepeat .word shape.words words)
          (Env.remap_prependRepeat (.tree shape) shape.children children env ρ))))

def Expr.rename : {Γ Δ : List Ty} → {t : Ty} → Renaming Γ Δ → Expr S Γ t → Expr S Δ t
  | _, _, _, _, .word n => .word n
  | _, _, _, _, .bool b => .bool b
  | _, _, _, ρ, .var x => .var (ρ x)
  | _, _, _, _, .treeNil shape => .treeNil shape
  | _, _, _, ρ, .treeNode reuse words children =>
    .treeNode (reuse.map fun x => ρ x) (fun i => (words i).rename ρ)
      (fun i => (children i).rename ρ)
  | _, _, _, ρ, .treeCase (shape := shape) x empty node =>
    .treeCase (ρ x) (empty.rename ρ) (node.rename (ρ.treeFields shape))
  | _, _, _, ρ, .bin op a b => .bin op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .cmp op a b => .cmp op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .not a => .not (a.rename ρ)
  | _, _, _, ρ, .and a b => .and (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .or a b => .or (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .ite c a b => .ite (c.rename ρ) (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .letE a b => .letE (a.rename ρ) (b.rename ρ.lift)
  | _, _, _, ρ, .call f args => .call f (fun i => (args i).rename ρ)
  | _, _, _, ρ, .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .letPair a b => .letPair (a.rename ρ) (b.rename (Renaming.lift (Renaming.lift ρ)))
  | _, _, _, ρ, .loop n a c b =>
    .loop (n.rename ρ) (a.rename ρ) (c.rename ρ.lift)
      (b.rename (Renaming.lift (Renaming.lift ρ)))
  | _, _, _, ρ, .fold x a b =>
    .fold (ρ x) (a.rename ρ) (b.rename (Renaming.lift (Renaming.lift (Renaming.lift ρ))))
  | _, _, _, ρ, .listFold args body => .listFold (fun i => (args i).rename ρ) body
  | _, _, _, ρ, .size x => .size (ρ x)
  | _, _, _, ρ, .leSize x i => .leSize (ρ x) (ρ i)
  | _, _, _, ρ, .get x i => .get (ρ x) (i.rename ρ)
  | _, _, _, ρ, .build n e => .build (n.rename ρ) (e.rename ρ.lift)
  | _, _, _, ρ, .set x i v => .set (ρ x) (i.rename ρ) (v.rename ρ)
  | _, _, _, ρ, .push x v => .push (ρ x) (v.rename ρ)
  | _, _, _, ρ, .append x y => .append (ρ x) (ρ y)
  | _, _, _, ρ, .insertAt x i v => .insertAt (ρ x) (i.rename ρ) (v.rename ρ)
  | _, _, _, ρ, .eraseAt x i => .eraseAt (ρ x) (i.rename ρ)
  | _, _, _, _, .float n => .float n
  | _, _, _, _, .float32 n => .float32 n
  | _, _, _, ρ, .fbin op a b => .fbin op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .funary op a => .funary op (a.rename ρ)
  | _, _, _, ρ, .fcmp op a b => .fcmp op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .toFloat op a => .toFloat op (a.rename ρ)
  | _, _, _, ρ, .toWord op a => .toWord op (a.rename ρ)
  | _, _, _, ρ, .fbin32 op a b => .fbin32 op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .funary32 op a => .funary32 op (a.rename ρ)
  | _, _, _, ρ, .fcmp32 op a b => .fcmp32 op (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .toFloat32 op a => .toFloat32 op (a.rename ρ)
  | _, _, _, ρ, .toWord32 op a => .toWord32 op (a.rename ρ)
  | _, _, _, ρ, .mk a b => .mk (a.rename ρ) (b.rename ρ)
  | _, _, _, ρ, .proj x p => .proj (ρ x) p

theorem Expr.denote_rename (e : Expr S Γ t) (ρ : Renaming Γ Δ) (funs : Funs S)
    (env : Env Δ) : (e.rename ρ).denote funs env = e.denote funs (env.remap ρ) := by
  induction e generalizing Δ with
  | call f args ih =>
    simp only [Expr.rename, Expr.denote]
    congr 2
    funext i
    exact ih i ρ env
  | listFold args body ihArgs _ =>
    simp only [Expr.rename, Expr.denote]
    congr 2
    funext i
    exact ihArgs i ρ env
  | treeNil => rfl
  | treeNode reuse words children ihWords ihChildren =>
    simp only [Expr.rename, Expr.denote]
    congr 1
    · funext i
      exact ihWords i ρ env
    · funext i
      exact ihChildren i ρ env
  | treeCase x empty node ihEmpty ihNode =>
    simp only [Expr.rename, Expr.denote, Env.get_remap]
    cases hv : env.get (ρ x) with
    | nil => exact ihEmpty ρ env
    | node words children =>
      change (node.rename (ρ.treeFields _)).denote funs (env.treeFields _ words children) =
        node.denote funs ((env.remap ρ).treeFields _ words children)
      exact (ihNode (ρ.treeFields _) (env.treeFields _ words children)).trans
        (congrArg (node.denote funs) (Env.remap_treeFields _ words children env ρ))
  | _ => simp_all only [Expr.rename, Expr.denote, Env.get_remap, Env.remap_lift]

#print axioms Expr.denote_rename

end Verified
