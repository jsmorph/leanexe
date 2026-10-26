import Verified.Reflect.TailLemmas
import Verified.TreeAgree

namespace Verified.Reflect

theorem tail_listCase_fixed {α β : Type} (meaning : α → β)
    (xs : List UInt64) (empty : β) (node : UInt64 → List UInt64 → β)
    (emptyStep : Sum α β) (nodeStep : UInt64 → List UInt64 → Sum α β)
    (he : empty = emptyStep.elim meaning id)
    (hn : ∀ x tail, node x tail = (nodeStep x tail).elim meaning id) :
    xs.casesOn (motive := fun _ => β) empty node =
      (xs.casesOn (motive := fun _ => Sum α β) emptyStep nodeStep).elim meaning id := by
  cases xs with
  | nil => exact he
  | cons x tail => exact hn x tail

theorem tail_listCase_eq {S : List Sig} {Γ params : List Ty} {result : Ty}
    {funs : Funs S} {env : Env Γ} {α β : Type}
    (φ : α → Env params) (ψ : β → result.denote)
    (x : Var Γ (.tree listShape))
    (empty : TailBody S params result Γ)
    (node : TailBody S params result (listShape.context listCell Γ))
    (xs : List UInt64) (emptyStep : Sum α β)
    (nodeStep : UInt64 → List UInt64 → Sum α β)
    (hx : env.get x = Tree.ofList xs)
    (he : empty.denote funs env = Sum.map φ ψ emptyStep)
    (hn : ∀ y ys, node.denote funs (Env.treeFields listShape listCell (fun _ => y)
      (fun _ => Tree.ofList ys) env) = Sum.map φ ψ (nodeStep y ys)) :
    (TailBody.treeCase x (fun _ => empty) (listBranch node)).denote funs env =
      Sum.map φ ψ (xs.casesOn emptyStep nodeStep) := by
  cases xs with
  | nil => simpa only [TailBody.denote, hx, Tree.ofList] using he
  | cons y ys =>
    simpa only [TailBody.denote, hx, Tree.ofList, listCell, listBranch] using hn y ys

end Verified.Reflect
