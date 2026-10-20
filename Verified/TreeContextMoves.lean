import Verified.TreeContextRep
import Verified.TreeMatchBlocks

namespace Verified

open Wasm LeanExe.Pipeline

theorem Env.moves_repeatFields {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (t : Ty) (mode : Mode) (hWidth : t.width = 1) :
    ∀ n (values : Fin n → t.denote) (words : Fin n → UInt64),
      Env.moves store (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        ((List.ofFn fun i => Value.i64 (words i)) ++ rest) (Env.prependRepeat t n values tail) =
      (List.ofFn fun i => match t.paramMode mode with
        | .owned => t.pointers store [.i64 (words i)] (values i)
        | .borrowed => []).flatten ++ Env.moves store (paramMode Γ modes) rest tail
  | 0, _, _ => rfl
  | n + 1, values, words => by
    rw [List.ofFn_succ]
    change Env.moves store _ ([.i64 (words 0)] ++
      ((List.ofFn fun i => Value.i64 (words i.succ)) ++ rest)) (.cons _ _) = _
    rw [Env.moves_cons (by simpa using hWidth.symm)]
    unfold Verified.paramMode
    simp only [List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
    have h := Env.moves_repeatFields (tail := tail) (modes := modes) store rest t mode hWidth n
      (fun i => values i.succ) (fun i => words i.succ)
    unfold Verified.paramMode at h
    rw [h]
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    rfl

theorem Env.reads_repeatFields {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (t : Ty) (mode : Mode) (hWidth : t.width = 1) :
    ∀ n (values : Fin n → t.denote) (words : Fin n → UInt64),
      Env.reads store (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        ((List.ofFn fun i => Value.i64 (words i)) ++ rest) (Env.prependRepeat t n values tail) =
      (List.ofFn fun i => match t.paramMode mode with
        | .owned => []
        | .borrowed => t.reads store [.i64 (words i)] (values i)).flatten ++
        Env.reads store (paramMode Γ modes) rest tail
  | 0, _, _ => rfl
  | n + 1, values, words => by
    rw [List.ofFn_succ]
    change Env.reads store _ ([.i64 (words 0)] ++
      ((List.ofFn fun i => Value.i64 (words i.succ)) ++ rest)) (.cons _ _) = _
    rw [Env.reads_cons (by simpa using hWidth.symm)]
    unfold Verified.paramMode
    simp only [List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
    have h := Env.reads_repeatFields (tail := tail) (modes := modes) store rest t mode hWidth n
      (fun i => values i.succ) (fun i => words i.succ)
    unfold Verified.paramMode at h
    rw [h]
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    rfl

theorem treeFields_moves (store : Store Unit) (shape : TreeShape) (mode : Mode) (p : UInt64)
    (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape)
    (pointers : Fin shape.children → UInt64) :
    Env.moves store (paramMode (shape.context []) (shape.modes mode []))
      (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape words children .nil) = match mode with
      | .borrowed => []
      | .owned => p :: (List.ofFn fun i =>
          (children i).toNode.pointers store (pointers i)).flatten := by
  have hChildren := Env.moves_repeatFields (tail := Env.nil) (modes := []) store []
    (.tree shape) mode rfl shape.children children pointers
  have hWords := Env.moves_repeatFields
    (tail := Env.prependRepeat (.tree shape) shape.children children Env.nil)
    (modes := List.replicate shape.children mode ++ []) store
    (List.ofFn fun i => Value.i64 (pointers i)) .word .borrowed rfl shape.words words words
  rw [show (List.ofFn fun i => Value.i64 (pointers i)) ++ [] =
    (List.ofFn fun i => Value.i64 (pointers i)) from List.append_nil _] at hChildren
  unfold Verified.paramMode at hWords hChildren ⊢
  change Env.moves store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape) .unit _) = _
  rw [Env.moves_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren]
  cases mode <;> simp [Ty.paramMode, Ty.pointers, Env.moves, List.ofFn_const]

theorem treeFields_reads (store : Store Unit) (shape : TreeShape) (mode : Mode) (p : UInt64)
    (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape)
    (pointers : Fin shape.children → UInt64) :
    Env.reads store (paramMode (shape.context []) (shape.modes mode []))
      (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape words children .nil) = match mode with
      | .owned => []
      | .borrowed => (List.ofFn fun i =>
          (children i).toNode.slotRegions store (pointers i)).flatten := by
  have hChildren := Env.reads_repeatFields (tail := Env.nil) (modes := []) store []
    (.tree shape) mode rfl shape.children children pointers
  have hWords := Env.reads_repeatFields
    (tail := Env.prependRepeat (.tree shape) shape.children children Env.nil)
    (modes := List.replicate shape.children mode ++ []) store
    (List.ofFn fun i => Value.i64 (pointers i)) .word .borrowed rfl shape.words words words
  rw [show (List.ofFn fun i => Value.i64 (pointers i)) ++ [] =
    (List.ofFn fun i => Value.i64 (pointers i)) from List.append_nil _] at hChildren
  unfold Verified.paramMode at hWords hChildren ⊢
  change Env.reads store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape) .unit _) = _
  rw [Env.reads_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren]
  cases mode <;> simp [Ty.paramMode, Ty.reads, Env.reads, List.ofFn_const]

theorem treeFields_reads_owned (store : Store Unit) (shape : TreeShape) (p : UInt64)
    (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape)
    (pointers : Fin shape.children → UInt64) :
    Env.reads store (paramMode (shape.context []) (shape.modes .owned []))
      (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape words children .nil) = [] :=
  treeFields_reads store shape .owned p words children pointers

end Verified
