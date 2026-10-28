import Verified.Reflect.TreeLemmas

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records} {funs : Funs S}
  {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {modes : List Mode}
  {paid : List Bool} {live : Nat → Bool} {env : Env Γ}

theorem treeNode_eq (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (wordValues : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrayValues : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (bufferValues : Fin (shape.buffers r) → LeanExe.Bytes)
    (childValues : Fin (shape.children r) → Tree shape)
    (hw : ∀ i, (words i).denote funs env = wordValues i)
    (ha : ∀ i, (arrays i).denote funs env = arrayValues i)
    (hb : ∀ i, (buffers i).denote funs env = bufferValues i)
    (hc : ∀ i, (children i).denote funs env = childValues i) :
    (Expr.treeNode r reuse words arrays buffers children).denote funs env =
      .node r wordValues (normalFamily arrayValues) (normalFamily bufferValues) childValues := by
  simp only [Expr.denote]
  have hArrays : (fun i => (arrays i).denote funs env) = arrayValues := funext ha
  have hBuffers : (fun i => (buffers i).denote funs env) = bufferValues := funext hb
  rw [show (fun i => (words i).denote funs env) = wordValues from funext hw,
    show (fun i => (children i).denote funs env) = childValues from funext hc]
  exact congrArg₂ (fun a b => Tree.node r wordValues a b childValues)
    (congrArg normalFamily hArrays) (congrArg normalFamily hBuffers)

theorem treeNode_bound (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (W : Fin (shape.words r) → Nat) (C K : Fin (shape.children r) → Nat)
    (A AK : Fin (shape.arrays r) → Nat) (B BK : Fin (shape.buffers r) → Nat) (P : Nat)
    (hw : ∀ i, (words i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
        (argsAny fun j => (children j).uses k) || (argsAny fun j => (arrays j).uses k) ||
        (argsAny fun j => (buffers j).uses k)) env = W i)
    (hc : ∀ i, (children i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (children j).uses k) ||
        (argsAny fun j => (arrays j).uses k) || (argsAny fun j => (buffers j).uses k)) env = C i)
    (hk : ∀ i, coerceCost (.tree shape) ((children i).mode modes) .owned
      ((children i).denote funs env) = K i)
    (ha : ∀ i, (arrays i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (arrays j).uses k) ||
        (argsAny fun j => (buffers j).uses k)) env = A i)
    (hak : ∀ i, coerceCost (shape.arrayTy r i) ((arrays i).mode modes) .owned
      ((arrays i).denote funs env) = AK i)
    (hb : ∀ i, (buffers i).allocs funs flags bounds modes paid
      (fun k => (live k || optionVarUses reuse k) ||
        (argsAny fun j => decide (i.val < j.val) && (buffers j).uses k)) env = B i)
    (hbk : ∀ i, coerceCost .bytes ((buffers i).mode modes) .owned
      ((buffers i).denote funs env) = BK i)
    (hp : (match reuse with
      | some x => if modeAt modes x.index = .owned ∧ live x.index = false then 0
          else allocCost (8 * shape.width r)
      | none => allocCost (8 * shape.width r)) = P) :
    (Expr.treeNode r reuse words arrays buffers children).allocs funs flags bounds modes paid live
        env =
      argsSum W + (argsSum C + argsSum K) + (argsSum A + argsSum AK) + (argsSum B + argsSum BK) +
        P := by
  simp only [Expr.allocs, hw, hc, hk, ha, hak, hb, hbk, argsSum_add]
  cases reuse <;> exact congrArg (fun p => argsSum W + (argsSum C + argsSum K) +
    (argsSum A + argsSum AK) + (argsSum B + argsSum BK) + p) hp

theorem treeNode_fits (reuse : Option (Var Γ (.treeHeader shape r)))
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (W : Fin (shape.words r) → Bool) (C : Fin (shape.children r) → Bool)
    (A : Fin (shape.arrays r) → Bool) (B : Fin (shape.buffers r) → Bool)
    (hw : ∀ i, (words i).fits funs fits env = W i)
    (hc : ∀ i, (children i).fits funs fits env = C i)
    (ha : ∀ i, (arrays i).fits funs fits env = A i)
    (hb : ∀ i, (buffers i).fits funs fits env = B i) :
    (Expr.treeNode r reuse words arrays buffers children).fits funs fits env =
      (argsAll W && argsAll C && argsAll A && argsAll B) := by
  simp only [Expr.fits, hw, hc, ha, hb]

end Verified.Reflect
