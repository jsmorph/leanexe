import Verified.ContextHEq
import Verified.TreeContextLayout

namespace Verified

theorem TreeShape.context_append (shape : TreeShape) (Γ : List Ty) :
    shape.context [] ++ Γ = shape.context Γ := by
  simp [TreeShape.context, List.append_assoc]

theorem Env.treeFields_append {Γ : List Ty} (shape : TreeShape)
    (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape)
    (env : Env Γ) :
    HEq ((Env.treeFields shape words children .nil).append env)
      (Env.treeFields shape words children env) := by
  have hChildren := Env.repeat_append Env.nil env (.tree shape) shape.children children
  have hWords := Env.repeat_append
    (Env.prependRepeat (.tree shape) shape.children children Env.nil) env
    .word shape.words words
  have hTail := Env.repeat_heq (by simp) hChildren .word shape.words words
  exact Env.cons_heq (t := .treeHeader shape) (by simp [List.append_assoc])
    (hWords.trans hTail) .unit

end Verified
