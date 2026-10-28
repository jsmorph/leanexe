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

/-- Borrowed values of one word each move nothing. -/
theorem Env.moves_fnFields {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (mode : Mode) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (vals : Fin n → Value),
      (∀ i, (ts i).width = 1) → (∀ i, (ts i).paramMode mode = .borrowed) →
      Env.moves store (paramMode (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes))
        (List.ofFn vals ++ rest) (Env.prependFn n ts values tail) =
      Env.moves store (paramMode Γ modes) rest tail
  | 0, _, _, _, _, _ => rfl
  | n + 1, ts, values, vals, hWidth, hb => by
    rw [List.ofFn_succ]
    change Env.moves store _ ([vals 0] ++ (List.ofFn (fun i => vals i.succ) ++ rest))
      (.cons _ _) = _
    rw [Env.moves_cons (by simpa using (hWidth 0).symm)]
    unfold Verified.paramMode
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ, hb 0, List.nil_append]
    have h := Env.moves_fnFields (tail := tail) (modes := modes) store rest mode n
      (fun i => ts i.succ) (fun i => values i.succ) (fun i => vals i.succ)
      (fun i => hWidth i.succ) (fun i => hb i.succ)
    unfold Verified.paramMode at h
    exact h

/-- Borrowed values of one word each that protect no region read nothing. -/
theorem Env.reads_fnFields {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (mode : Mode) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (vals : Fin n → Value),
      (∀ i, (ts i).width = 1) → (∀ i, (ts i).paramMode mode = .borrowed) →
      (∀ i ws, (ts i).reads store ws (values i) = []) →
      Env.reads store (paramMode (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes))
        (List.ofFn vals ++ rest) (Env.prependFn n ts values tail) =
      Env.reads store (paramMode Γ modes) rest tail
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, ts, values, vals, hWidth, hb, hReads => by
    rw [List.ofFn_succ]
    change Env.reads store _ ([vals 0] ++ (List.ofFn (fun i => vals i.succ) ++ rest))
      (.cons _ _) = _
    rw [Env.reads_cons (by simpa using (hWidth 0).symm)]
    unfold Verified.paramMode
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ, hb 0, hReads 0,
      List.nil_append]
    have h := Env.reads_fnFields (tail := tail) (modes := modes) store rest mode n
      (fun i => ts i.succ) (fun i => values i.succ) (fun i => vals i.succ)
      (fun i => hWidth i.succ) (fun i => hb i.succ) (fun i => hReads i.succ)
    unfold Verified.paramMode at h
    exact h

theorem treeFields_moves (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (mode : Mode) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) :
    Env.moves store (paramMode (shape.context r []) (shape.modes r mode []))
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape r words children .nil) = match mode with
      | .borrowed => []
      | .owned => p :: (List.ofFn fun i =>
          (children i).toNode.pointers store (pointers i)).flatten := by
  have hChildren := Env.moves_repeatFields (tail := Env.nil) (modes := []) store []
    (.tree shape) mode rfl (shape.children r) children pointers
  have hWords := Env.moves_fnFields
    (tail := Env.prependRepeat (.tree shape) (shape.children r) children Env.nil)
    (modes := List.replicate (shape.children r) mode ++ []) store
    (List.ofFn fun i => Value.i64 (pointers i)) .borrowed (shape.words r) (shape.wordTy r) words
    (fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i))
    (shape.wordTy_width r) (fun i => shape.wordTy_paramMode r i _)
  rw [show (List.ofFn fun i => Value.i64 (pointers i)) ++ [] =
    (List.ofFn fun i => Value.i64 (pointers i)) from List.append_nil _] at hChildren
  unfold Verified.paramMode at hWords hChildren ⊢
  change Env.moves store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape r) .unit _) = _
  rw [Env.moves_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren]
  cases mode <;> simp [Ty.paramMode, Ty.pointers, Env.moves, List.ofFn_const]

theorem treeFields_reads (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (mode : Mode) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) :
    Env.reads store (paramMode (shape.context r []) (shape.modes r mode []))
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape r words children .nil) = match mode with
      | .owned => []
      | .borrowed => (List.ofFn fun i =>
          (children i).toNode.slotRegions store (pointers i)).flatten := by
  have hChildren := Env.reads_repeatFields (tail := Env.nil) (modes := []) store []
    (.tree shape) mode rfl (shape.children r) children pointers
  have hWords := Env.reads_fnFields
    (tail := Env.prependRepeat (.tree shape) (shape.children r) children Env.nil)
    (modes := List.replicate (shape.children r) mode ++ []) store
    (List.ofFn fun i => Value.i64 (pointers i)) .borrowed (shape.words r) (shape.wordTy r) words
    (fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i))
    (shape.wordTy_width r) (fun i => shape.wordTy_paramMode r i _) (fun _ _ => rfl)
  rw [show (List.ofFn fun i => Value.i64 (pointers i)) ++ [] =
    (List.ofFn fun i => Value.i64 (pointers i)) from List.append_nil _] at hChildren
  unfold Verified.paramMode at hWords hChildren ⊢
  change Env.reads store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape r) .unit _) = _
  rw [Env.reads_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren]
  cases mode <;> simp [Ty.paramMode, Ty.reads, Env.reads, List.ofFn_const]

theorem treeFields_reads_owned (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) :
    Env.reads store (paramMode (shape.context r []) (shape.modes r .owned []))
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))
      (Env.treeFields shape r words children .nil) = [] :=
  treeFields_reads store shape r .owned p words children pointers

end Verified
