import Verified.TreeContextLayout
import Verified.TreeMatchMemory

namespace Verified

open Wasm LeanExe.Pipeline

theorem Env.Rep.repeatFields {heap : Heap} {store : Store Unit} {Γ : List Ty}
    {tail : Env Γ} {modes : List Mode} {rest : List Value}
    (hTail : Env.Rep (paramMode Γ modes) heap store rest tail) (t : Ty) (mode : Mode) :
    ∀ n (values : Fin n → t.denote) (words : Fin n → UInt64),
      (∀ i, t.Rep (t.paramMode mode) heap store [.i64 (words i)] (values i)) →
      Env.Rep (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        heap store ((List.ofFn fun i => Value.i64 (words i)) ++ rest)
        (Env.prependRepeat t n values tail)
  | 0, _, _, _ => hTail
  | n + 1, values, words, hValues => by
    refine ⟨[.i64 (words 0)], (List.ofFn fun i => Value.i64 (words i.succ)) ++ rest,
      by simp only [List.ofFn_succ, List.cons_append, List.nil_append], ?_, ?_⟩
    · simpa only [paramMode, List.replicate_succ, List.cons_append, paramModes,
        List.headD_cons, List.getD_cons_zero] using hValues 0
    · have hRest := Env.Rep.repeatFields hTail t mode n
        (fun i => values i.succ) (fun i => words i.succ) (fun i => hValues i.succ)
      unfold Verified.paramMode at hRest
      simpa only [paramMode, List.replicate_succ, List.cons_append, paramModes,
        List.headD_cons, List.tail_cons, List.getD_cons_succ] using hRest

theorem treeFields_rep {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {mode : Mode} {p : UInt64} {words : Fin (shape.words r) → UInt64}
    {children : Fin (shape.children r) → Tree shape}
    {pointers : Fin (shape.children r) → UInt64}
    (hHeader : mode.header shape r heap store p)
    (hChildren : ∀ i, mode.node heap store (pointers i) (children i).toNode) :
    Env.Rep (paramMode (shape.context r []) (shape.modes r mode [])) heap store
      (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape r words children .nil) := by
  have hTrees := Env.Rep.repeatFields (heap := heap) (store := store) (Γ := [])
    (modes := []) (tail := .nil) (rest := []) rfl (.tree shape) mode (shape.children r)
    children pointers (fun i => ⟨pointers i, rfl, hChildren i⟩)
  have hWords := Env.Rep.repeatFields hTrees .word .borrowed (shape.words r) words words
    (fun _ => rfl)
  unfold Verified.paramMode at hWords
  rw [show (List.ofFn fun i => Value.i64 (pointers i)) ++ [] =
    (List.ofFn fun i => Value.i64 (pointers i)) from List.append_nil _] at hWords
  refine ⟨[.i64 p], _, rfl, ?_, ?_⟩
  · exact ⟨p, rfl, hHeader⟩
  · convert hWords using 1
    · funext i
      simp only [TreeShape.context, TreeShape.modes, paramMode, paramModes,
        List.headD_cons, List.tail_cons, List.getD_cons_succ]
    · rfl

end Verified
