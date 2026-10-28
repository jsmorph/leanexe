import Verified.TreeContextLayout
import Verified.TreeMatchMemory
import Verified.WordCode

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

/-- The values `vals` of the types `ts`, one value each, represent `values` before the rest of a
context. -/
theorem Env.Rep.fnFields {heap : Heap} {store : Store Unit} {Γ : List Ty}
    {tail : Env Γ} {modes : List Mode} {rest : List Value}
    (hTail : Env.Rep (paramMode Γ modes) heap store rest tail) (mode : Mode) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (vals : Fin n → Value),
      (∀ i, (ts i).Rep ((ts i).paramMode mode) heap store [vals i] (values i)) →
      Env.Rep (paramMode (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes))
        heap store (List.ofFn vals ++ rest) (Env.prependFn n ts values tail)
  | 0, _, _, _, _ => hTail
  | n + 1, ts, values, vals, hValues => by
    refine ⟨[vals 0], List.ofFn (fun i => vals i.succ) ++ rest,
      by simp only [List.ofFn_succ, List.cons_append, List.nil_append], ?_, ?_⟩
    · simpa only [paramMode, tysOfFn, List.replicate_succ, List.cons_append, paramModes,
        List.headD_cons, List.getD_cons_zero] using hValues 0
    · have hRest := Env.Rep.fnFields hTail mode n (fun i => ts i.succ)
        (fun i => values i.succ) (fun i => vals i.succ) (fun i => hValues i.succ)
      unfold Verified.paramMode at hRest
      simpa only [paramMode, tysOfFn, List.replicate_succ, List.cons_append, paramModes,
        List.headD_cons, List.tail_cons, List.getD_cons_succ] using hRest

/-- An empty repetition represents nothing beyond its tail. -/
theorem Env.Rep.repeatZero {heap : Heap} {store : Store Unit} {Γ : List Ty}
    {tail : Env Γ} {modes : List Mode} {rest : List Value}
    (hTail : Env.Rep (paramMode Γ modes) heap store rest tail) (t : Ty) (mode : Mode) :
    ∀ n, n = 0 → ∀ values : Fin n → t.denote,
      Env.Rep (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        heap store rest (Env.prependRepeat t n values tail)
  | 0, _, _ => hTail

/-- The words of a branch's variables: the record's address, its word fields, the addresses of its
children, and the addresses of its arrays. -/
def TreeShape.branchValues (shape : TreeShape) (r : Fin shape.records) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (pointers : Fin (shape.children r) → UInt64) (arrayPtrs : Fin (shape.arrays r) → UInt64) :
    List Value :=
  .i64 p :: (shape.wordValues r words ++ ((List.ofFn fun i => Value.i64 (pointers i)) ++
    (List.ofFn fun i => Value.i64 (arrayPtrs i))))

theorem treeFields_rep {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {pointers : Fin (shape.children r) → UInt64} {arrayPtrs : Fin (shape.arrays r) → UInt64}
    (hHeader : mode.header shape r heap store p)
    (hChildren : ∀ i, mode.node heap store (pointers i) (children i).toNode)
    (hArrays : ∀ i, mode.array heap store (arrayPtrs i) ((shape.arrayElem r i).words (arrays i))) :
    Env.Rep (paramMode (shape.context r []) (shape.modes r mode [])) heap store
      (shape.branchValues r p words pointers arrayPtrs)
      (Env.treeFields shape r words arrays buffers children .nil) := by
  have hBuffers := Env.Rep.repeatZero (heap := heap) (store := store) (Γ := []) (modes := [])
    (tail := .nil) (rest := []) rfl .bytes mode (shape.buffers r) (shape.buffers_eq_zero r)
    buffers
  have hArrayRep := Env.Rep.fnFields hBuffers mode (shape.arrays r) (shape.arrayTy r) arrays
    (fun i => Value.i64 (arrayPtrs i)) (fun i => ⟨arrayPtrs i, rfl, hArrays i⟩)
  have hTrees := Env.Rep.repeatFields hArrayRep (.tree shape) mode (shape.children r)
    children pointers (fun i => ⟨pointers i, rfl, hChildren i⟩)
  have hWords := Env.Rep.fnFields hTrees .borrowed (shape.words r) (shape.wordTy r) words
    (fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i))
    (fun i => shape.wordValues_rep r words i)
  unfold Verified.paramMode at hWords
  rw [show (List.ofFn fun i => Value.i64 (arrayPtrs i)) ++ [] =
    (List.ofFn fun i => Value.i64 (arrayPtrs i)) from List.append_nil _] at hWords
  refine ⟨[.i64 p], _, rfl, ?_, ?_⟩
  · exact ⟨p, rfl, hHeader⟩
  · convert hWords using 1
    · funext i
      simp only [TreeShape.context, TreeShape.modes, paramMode, paramModes,
        List.headD_cons, List.tail_cons, List.getD_cons_succ]
    · rfl

end Verified
