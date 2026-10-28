import Verified.ContextHEq
import Verified.TreeContextLayout

namespace Verified

theorem TreeShape.context_append (shape : TreeShape) (r : Fin shape.records) (Γ : List Ty) :
    shape.context r [] ++ Γ = shape.context r Γ := by
  simp [TreeShape.context, List.append_assoc]

theorem Env.treeFields_append {Γ : List Ty} (shape : TreeShape) (r : Fin shape.records)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape) (env : Env Γ) :
    HEq ((Env.treeFields shape r words arrays buffers children .nil).append env)
      (Env.treeFields shape r words arrays buffers children env) := by
  have hBuffers := Env.repeat_append Env.nil env .bytes (shape.buffers r) buffers
  have hArrays := Env.fn_append (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil) env
    (shape.arrays r) (shape.arrayTy r) arrays
  have hArraysTail := Env.fn_heq (by simp) hBuffers (shape.arrays r) (shape.arrayTy r) arrays
  have hChildren := Env.repeat_append
    (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil)) env
    (.tree shape) (shape.children r) children
  have hChildrenTail := Env.repeat_heq (by simp) (hArrays.trans hArraysTail) (.tree shape)
    (shape.children r) children
  have hWords := Env.fn_append
    (Env.prependRepeat (.tree shape) (shape.children r) children
      (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil))) env
    (shape.words r) (shape.wordTy r) words
  have hTail := Env.fn_heq (by simp) (hChildren.trans hChildrenTail) (shape.words r)
    (shape.wordTy r) words
  exact Env.cons_heq (t := .treeHeader shape r) (by simp [List.append_assoc])
    (hWords.trans hTail) .unit

end Verified
