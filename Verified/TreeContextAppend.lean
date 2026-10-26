import Verified.ContextHEq
import Verified.TreeContextLayout

namespace Verified

theorem TreeShape.context_append (shape : TreeShape) (r : Fin shape.records) (Γ : List Ty) :
    shape.context r [] ++ Γ = shape.context r Γ := by
  simp [TreeShape.context, List.append_assoc]

theorem Env.treeFields_append {Γ : List Ty} (shape : TreeShape) (r : Fin shape.records)
    (words : Fin (shape.words r) → UInt64) (children : Fin (shape.children r) → Tree shape)
    (env : Env Γ) :
    HEq ((Env.treeFields shape r words children .nil).append env)
      (Env.treeFields shape r words children env) := by
  have hChildren := Env.repeat_append Env.nil env (.tree shape) (shape.children r) children
  have hWords := Env.repeat_append
    (Env.prependRepeat (.tree shape) (shape.children r) children Env.nil) env
    .word (shape.words r) words
  have hTail := Env.repeat_heq (by simp) hChildren .word (shape.words r) words
  exact Env.cons_heq (t := .treeHeader shape r) (by simp [List.append_assoc])
    (hWords.trans hTail) .unit

end Verified
