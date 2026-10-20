import Verified.ListFoldResource

namespace Verified.ListFold

def nativeCost {α : Type} (step : α → UInt64 → α)
    (charge : UInt64 → List UInt64 → α → Nat) : List UInt64 → α → Nat
  | [], _ => 0
  | head :: tail, acc => charge head tail acc + nativeCost step charge tail (step acc head)

def nativeFits {α : Type} (step : α → UInt64 → α)
    (valid : UInt64 → List UInt64 → α → Bool) : List UInt64 → α → Bool
  | [], _ => true
  | head :: tail, acc => valid head tail acc && nativeFits step valid tail (step acc head)

theorem cost_ofList {α β : Type} (flatten : α → β)
    (step : Tree listShape → UInt64 → Tree listShape → β → β)
    (native : α → UInt64 → α)
    (charge : Tree listShape → UInt64 → Tree listShape → β → Nat)
    (cost : UInt64 → List UInt64 → α → Nat)
    (hstep : ∀ head tail acc, step (Tree.ofList (head :: tail)) head (Tree.ofList tail)
      (flatten acc) = flatten (native acc head))
    (hcost : ∀ head tail acc, charge (Tree.ofList (head :: tail)) head (Tree.ofList tail)
      (flatten acc) = cost head tail acc) (xs : List UInt64) (init : α) :
    (Tree.ofList xs).foldCostWith step charge (flatten init) = nativeCost native cost xs init := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih =>
    change charge (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten init) +
      (Tree.ofList tail).foldCostWith step charge
        (step (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten init)) = _
    rw [hcost, hstep]
    exact congrArg (cost head tail init + ·) (ih (native init head))

theorem fits_ofList {α β : Type} (flatten : α → β)
    (step : Tree listShape → UInt64 → Tree listShape → β → β)
    (native : α → UInt64 → α)
    (valid : Tree listShape → UInt64 → Tree listShape → β → Bool)
    (check : UInt64 → List UInt64 → α → Bool)
    (hstep : ∀ head tail acc, step (Tree.ofList (head :: tail)) head (Tree.ofList tail)
      (flatten acc) = flatten (native acc head))
    (hcheck : ∀ head tail acc, valid (Tree.ofList (head :: tail)) head (Tree.ofList tail)
      (flatten acc) = check head tail acc) (xs : List UInt64) (init : α) :
    (Tree.ofList xs).foldFitsWith step valid (flatten init) = nativeFits native check xs init := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih =>
    change (valid (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten init) &&
      (Tree.ofList tail).foldFitsWith step valid
        (step (Tree.ofList (head :: tail)) head (Tree.ofList tail) (flatten init))) = _
    rw [hcheck, hstep]
    exact congrArg (fun value => check head tail init && value) (ih (native init head))

@[simp] theorem nativeCost_zero {α : Type} (step : α → UInt64 → α)
    (xs : List UInt64) (init : α) : nativeCost step (fun _ _ _ => 0) xs init = 0 := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih => simp only [nativeCost, ih, Nat.zero_add]

@[simp] theorem nativeFits_true {α : Type} (step : α → UInt64 → α)
    (xs : List UInt64) (init : α) : nativeFits step (fun _ _ _ => true) xs init = true := by
  induction xs generalizing init with
  | nil => rfl
  | cons head tail ih => simp only [nativeFits, ih, Bool.true_and]

end ListFold

namespace Reflect

theorem listFold_eq {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty} {α : Type}
    (funs : Funs S) (env : Env Γ) (flatten : α → e.denote)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (xs : List UInt64) (init : α) (step : α → UInt64 → α) (captured : Env captures)
    (hargs : Env.ofFn (fun i => (args i).denote funs env) =
      .cons (Tree.ofList xs) (.cons (flatten init) captured))
    (hstep : ∀ head tail acc, body.denote funs
      (Env.treeFields listShape (fun _ => head) (fun _ => Tree.ofList tail)
        (.cons (Tree.ofList (head :: tail)) (.cons (flatten acc) captured))) = flatten (step acc head)) :
    (Expr.listFold args body).denote funs env = flatten (xs.foldl step init) := by
  rw [Expr.denote, hargs]
  exact Tree.foldlWith_ofList flatten _ step hstep xs init

theorem listFold_bound {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty} {α : Type}
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) (env : Env Γ) (flatten : α → e.denote)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (xs : List UInt64) (init : α) (step : α → UInt64 → α) (captured : Env captures)
    (I : Nat) (B : UInt64 → List UInt64 → α → Nat)
    (hargs : Env.ofFn (fun i => (args i).denote funs env) =
      .cons (Tree.ofList xs) (.cons (flatten init) captured))
    (hstep : ∀ head tail acc, body.denote funs
      (Env.treeFields listShape (fun _ => head) (fun _ => Tree.ofList tail)
        (.cons (Tree.ofList (head :: tail)) (.cons (flatten acc) captured))) = flatten (step acc head))
    (hI : (argsSum fun i => if ((ListFold.params e captures).get i).scalar then
      (args i).allocs funs flags bounds modes paid
        (fun k => live k || argsAny fun j => (args j).uses k) env else 0) = I)
    (hB : ∀ head tail acc, body.allocs funs flags bounds
      (listShape.modes .borrowed (paramModes (ListFold.params e captures) []))
      (List.replicate listShape.bindCount false ++ List.replicate (ListFold.params e captures).length false)
      (ListFold.bodyLive e captures)
      (Env.treeFields listShape (fun _ => head) (fun _ => Tree.ofList tail)
        (.cons (Tree.ofList (head :: tail)) (.cons (flatten acc) captured))) = B head tail acc) :
    (Expr.listFold args body).allocs funs flags bounds modes paid live env =
      I + ListFold.nativeCost step B xs init := by
  rw [Expr.allocs, hI, hargs]
  exact congrArg (I + ·) (ListFold.cost_ofList flatten _ step _ B hstep hB xs init)

theorem listFold_fits {S : List Sig} {Γ : List Ty} {e : Elem} {captures : List Ty} {α : Type}
    (funs : Funs S) (fits : Fits S) (env : Env Γ) (flatten : α → e.denote)
    (args : (i : Fin (ListFold.params e captures).length) →
      Expr S Γ ((ListFold.params e captures).get i))
    (body : Expr S (ListFold.context e captures) (.elem e))
    (xs : List UInt64) (init : α) (step : α → UInt64 → α) (captured : Env captures)
    (I : Bool) (B : UInt64 → List UInt64 → α → Bool)
    (hargs : Env.ofFn (fun i => (args i).denote funs env) =
      .cons (Tree.ofList xs) (.cons (flatten init) captured))
    (hstep : ∀ head tail acc, body.denote funs
      (Env.treeFields listShape (fun _ => head) (fun _ => Tree.ofList tail)
        (.cons (Tree.ofList (head :: tail)) (.cons (flatten acc) captured))) = flatten (step acc head))
    (hI : (argsAll fun i => (args i).fits funs fits env) = I)
    (hB : ∀ head tail acc, body.fits funs fits
      (Env.treeFields listShape (fun _ => head) (fun _ => Tree.ofList tail)
        (.cons (Tree.ofList (head :: tail)) (.cons (flatten acc) captured))) = B head tail acc) :
    (Expr.listFold args body).fits funs fits env = (I && ListFold.nativeFits step B xs init) := by
  rw [Expr.fits, hI, hargs]
  exact congrArg (fun value => I && value) (ListFold.fits_ofList flatten _ step _ B hstep hB xs init)

#print axioms listFold_eq
#print axioms listFold_bound
#print axioms listFold_fits

end Reflect
end Verified
