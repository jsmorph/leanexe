import Verified.Reflect.BoundLemmas
import Verified.Reflect.FitsLemmas
import Verified.TreeAgree

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {funs : Funs S} {flags : Flags S}
  {bounds : Bounds S} {fits : Fits S} {modes : List Mode} {paid : List Bool}
  {live : Nat → Bool} {env : Env Γ}

theorem argsSum_one (f : Fin 1 → Nat) : argsSum f = f 0 := Nat.add_zero _

theorem argsAny_one (f : Fin 1 → Bool) : argsAny f = f 0 := Bool.or_false _

theorem argsAll_one (f : Fin 1 → Bool) : argsAll f = f 0 := Bool.and_true _

theorem treeNil_bound (shape : TreeShape) (h : shape.hasNull = true) :
    (Expr.treeNil shape h : Expr S Γ (.tree shape)).allocs funs flags bounds modes paid live env =
      0 :=
  rfl

theorem listCons_eq {reuse : Option (Var Γ (.treeHeader listShape listCell))}
    {head : Expr S Γ .word} {tail : Expr S Γ (.tree listShape)}
    {x : UInt64} {xs : List UInt64}
    (hh : head.denote funs env = x) (ht : tail.denote funs env = Tree.ofList xs) :
    (Expr.treeNode listCell reuse (fun _ => head) (fun _ => tail)).denote funs env =
      Tree.ofList (x :: xs) := by
  subst hh
  simp only [Expr.denote, Tree.ofList, ht]
  rfl

theorem listCons_bound {reuse : Option (Var Γ (.treeHeader listShape listCell))}
    {head : Expr S Γ .word} {tail : Expr S Γ (.tree listShape)} {H T K P : Nat}
    (hh : head.allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) || tail.uses k) env = H)
    (ht : tail.allocs funs flags bounds modes paid
      (fun k => live k || optionVarUses reuse k) env = T)
    (hk : coerceCost (.tree listShape) (tail.mode modes) .owned (tail.denote funs env) = K)
    (hp : (match reuse with
      | some x => if modeAt modes x.index = .owned ∧ live x.index = false then 0 else 64
      | none => 64) = P) :
    (Expr.treeNode listCell reuse (fun _ => head) (fun _ => tail)).allocs
      funs flags bounds modes paid live env = H + (T + K) + P := by
  simp only [Expr.allocs]
  erw [argsSum_one, argsSum_one]
  change head.allocs funs flags bounds modes paid
      (fun k => ((live k || optionVarUses reuse k) ||
        argsAny (n := 1) (fun j => decide (0 < j.val) && head.uses k)) ||
        argsAny (n := 1) (fun _ => tail.uses k)) env +
    (tail.allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        argsAny (n := 1) (fun j => decide (0 < j.val) && tail.uses k)) env +
      coerceCost (.tree listShape) (tail.mode modes) .owned (tail.denote funs env)) +
    _ = _
  simp only [argsAny_one, Fin.val_zero, Nat.lt_irrefl, decide_false,
    Bool.false_and, Bool.or_false]
  rw [hh, ht, hk]
  apply congrArg (fun p => H + (T + K) + p)
  have hWidth : 8 * listShape.width listCell = 16 := by decide
  cases reuse <;> simpa only [hWidth, allocCost] using hp

theorem listCons_fits {reuse : Option (Var Γ (.treeHeader listShape listCell))}
    {head : Expr S Γ .word} {tail : Expr S Γ (.tree listShape)} {H T : Bool}
    (hh : head.fits funs fits env = H) (ht : tail.fits funs fits env = T) :
    (Expr.treeNode listCell reuse (fun _ => head) (fun _ => tail)).fits funs fits env =
      (H && T) := by
  simp only [Expr.fits]
  erw [argsAll_one, argsAll_one, hh, ht]

theorem listCase_eq {t : Ty} (x : Var Γ (.tree listShape))
    (empty : Expr S Γ t) (node : Expr S (listShape.context listCell Γ) t)
    {α : Type} (flatten : α → t.denote) (xs : List UInt64) (a : α) (b : UInt64 → List UInt64 → α)
    (hx : env.get x = Tree.ofList xs)
    (he : empty.denote funs env = flatten a)
    (hn : ∀ y ys, node.denote funs (Env.treeFields listShape listCell (fun _ => y)
      (fun _ => Tree.ofList ys) env) = flatten (b y ys)) :
    (Expr.treeCase x (fun _ => empty) (listBranch node)).denote funs env =
      flatten (xs.casesOn a b) := by
  cases xs with
  | nil => simpa only [Expr.denote, hx, Tree.ofList] using he
  | cons y ys => simpa only [Expr.denote, hx, Tree.ofList, listCell, listBranch] using hn y ys

theorem varCost_eq {t : Ty} (x : Var Γ t) {C : Nat}
    (h : (Expr.var x).allocs funs flags bounds modes paid live env = C) :
    x.cost modes live (env.get x) = C := h

/-- The mode of a match on a list, from the modes of its node and empty branches. -/
theorem listCase_mode {t : Ty} (empty : Expr S Γ t) (node : Expr S (listShape.context listCell Γ) t)
    (modes : List Mode) (rootMode : Mode) :
    recordsJoin (fun r => (listBranch (β := fun r => Expr S (listShape.context r Γ) t) node r).mode
          (listShape.modes r rootMode modes))
        (if _h : listShape.hasNull = true then empty.mode modes else .borrowed) =
      (node.mode (listShape.modes listCell rootMode modes)).join (empty.mode modes) :=
  rfl

theorem listCase_bound {t : Ty} (x : Var Γ (.tree listShape))
    (empty : Expr S Γ t) (node : Expr S (listShape.context listCell Γ) t)
    {xs : List UInt64} {C E : Nat} {N : UInt64 → List UInt64 → Nat}
    (hx : env.get x = Tree.ofList xs)
    (hc : x.cost modes (fun i => live i || node.uses (i + listShape.bindCount listCell))
      (env.get x) = C)
    (he : empty.allocs funs flags bounds modes paid live env +
      coerceCost t (empty.mode modes)
        ((node.mode (listShape.modes listCell (modeAt modes x.index) modes)).join
          (empty.mode modes))
        (empty.denote funs env) = E)
    (hn : ∀ y ys,
      node.allocs funs flags bounds (listShape.modes listCell (modeAt modes x.index) modes)
        (List.replicate (listShape.bindCount listCell) false ++ paid)
        (shift (listShape.bindCount listCell) live)
        (Env.treeFields listShape listCell (fun _ => y) (fun _ => Tree.ofList ys) env) +
      coerceCost t (node.mode (listShape.modes listCell (modeAt modes x.index) modes))
        ((node.mode (listShape.modes listCell (modeAt modes x.index) modes)).join
          (empty.mode modes))
        (node.denote funs (Env.treeFields listShape listCell (fun _ => y)
          (fun _ => Tree.ofList ys) env)) = N y ys) :
    (Expr.treeCase x (fun _ => empty) (listBranch node)).allocs funs flags bounds modes paid
      live env = xs.casesOn E (fun y ys => C + N y ys) := by
  cases xs with
  | nil =>
    simp only [Expr.allocs, hx, Tree.ofList, listCase_mode]
    exact he
  | cons y ys =>
    have hc' := hc
    rw [hx] at hc'
    simp only [Tree.ofList] at hc'
    simp only [Expr.allocs, hx, Tree.ofList, listCase_mode, listBranch_cell]
    rw [hc', Nat.add_assoc, hn]

theorem listCase_fits {t : Ty} (x : Var Γ (.tree listShape))
    (empty : Expr S Γ t) (node : Expr S (listShape.context listCell Γ) t)
    {xs : List UInt64} {E : Bool} {N : UInt64 → List UInt64 → Bool}
    (hx : env.get x = Tree.ofList xs)
    (he : empty.fits funs fits env = E)
    (hn : ∀ y ys, node.fits funs fits
      (Env.treeFields listShape listCell (fun _ => y) (fun _ => Tree.ofList ys) env) = N y ys) :
    (Expr.treeCase x (fun _ => empty) (listBranch node)).fits funs fits env = xs.casesOn E N := by
  cases xs with
  | nil => simpa only [Expr.fits, hx, Tree.ofList] using he
  | cons y ys => simpa only [Expr.fits, hx, Tree.ofList, listCell, listBranch] using hn y ys

end Verified.Reflect
