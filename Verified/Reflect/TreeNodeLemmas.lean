import Verified.Reflect.TreeLemmas

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {shape : TreeShape} {funs : Funs S}
  {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {modes : List Mode}
  {paid : List Bool} {live : Nat → Bool} {env : Env Γ}

theorem treeNode_eq (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape))
    (wordValues : Fin shape.words → UInt64) (childValues : Fin shape.children → Tree shape)
    (hw : ∀ i, (words i).denote funs env = wordValues i)
    (hc : ∀ i, (children i).denote funs env = childValues i) :
    (Expr.treeNode reuse words children).denote funs env = .node wordValues childValues := by
  simp only [Expr.denote]
  exact congrArg₂ Tree.node (funext hw) (funext hc)

theorem treeNode_bound (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape))
    (W : Fin shape.words → Nat) (C K : Fin shape.children → Nat) (P : Nat)
    (hw : ∀ i, (words i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
        (argsAny fun j => (children j).uses k)) env = W i)
    (hc : ∀ i, (children i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (children j).uses k)) env = C i)
    (hk : ∀ i, coerceCost (.tree shape) ((children i).mode modes) .owned
      ((children i).denote funs env) = K i)
    (hp : (match reuse with
      | some x => if modeAt modes x.index = .owned ∧ live x.index = false then 0
          else allocCost (8 * shape.fields.length)
      | none => allocCost (8 * shape.fields.length)) = P) :
    (Expr.treeNode reuse words children).allocs funs flags bounds modes paid live env =
      argsSum W + (argsSum C + argsSum K) + P := by
  simp only [Expr.allocs, hw, hc, hk, argsSum_add]
  cases reuse <;> exact congrArg (fun p => argsSum W + (argsSum C + argsSum K) + p) hp

theorem treeNode_fits (reuse : Option (Var Γ (.treeHeader shape)))
    (words : Fin shape.words → Expr S Γ .word)
    (children : Fin shape.children → Expr S Γ (.tree shape))
    (W : Fin shape.words → Bool) (C : Fin shape.children → Bool)
    (hw : ∀ i, (words i).fits funs fits env = W i)
    (hc : ∀ i, (children i).fits funs fits env = C i) :
    (Expr.treeNode reuse words children).fits funs fits env = (argsAll W && argsAll C) := by
  simp only [Expr.fits, hw, hc]

end Verified.Reflect
