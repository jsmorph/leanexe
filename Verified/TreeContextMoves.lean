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

/-- Values of one word each, in any mode, move the pointers of those that the mode owns. -/
theorem Env.moves_fnFieldsMode {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (mode : Mode) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (words : Fin n → UInt64),
      (∀ i, (ts i).width = 1) →
      Env.moves store (paramMode (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes))
        ((List.ofFn fun i => Value.i64 (words i)) ++ rest) (Env.prependFn n ts values tail) =
      (List.ofFn fun i => match (ts i).paramMode mode with
        | .owned => (ts i).pointers store [.i64 (words i)] (values i)
        | .borrowed => []).flatten ++ Env.moves store (paramMode Γ modes) rest tail
  | 0, _, _, _, _ => rfl
  | n + 1, ts, values, words, hWidth => by
    rw [List.ofFn_succ]
    change Env.moves store _ ([.i64 (words 0)] ++
      ((List.ofFn fun i => Value.i64 (words i.succ)) ++ rest)) (.cons _ _) = _
    rw [Env.moves_cons (by simpa using (hWidth 0).symm)]
    unfold Verified.paramMode
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
    have h := Env.moves_fnFieldsMode (tail := tail) (modes := modes) store rest mode n
      (fun i => ts i.succ) (fun i => values i.succ) (fun i => words i.succ)
      (fun i => hWidth i.succ)
    unfold Verified.paramMode at h
    rw [h]
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    rfl

/-- Values of one word each, in any mode, protect the regions of those that the mode borrows. -/
theorem Env.reads_fnFieldsMode {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (mode : Mode) :
    ∀ n (ts : Fin n → Ty) (values : (i : Fin n) → (ts i).denote) (words : Fin n → UInt64),
      (∀ i, (ts i).width = 1) →
      Env.reads store (paramMode (tysOfFn n ts ++ Γ) (List.replicate n mode ++ modes))
        ((List.ofFn fun i => Value.i64 (words i)) ++ rest) (Env.prependFn n ts values tail) =
      (List.ofFn fun i => match (ts i).paramMode mode with
        | .owned => []
        | .borrowed => (ts i).reads store [.i64 (words i)] (values i)).flatten ++
        Env.reads store (paramMode Γ modes) rest tail
  | 0, _, _, _, _ => rfl
  | n + 1, ts, values, words, hWidth => by
    rw [List.ofFn_succ]
    change Env.reads store _ ([.i64 (words 0)] ++
      ((List.ofFn fun i => Value.i64 (words i.succ)) ++ rest)) (.cons _ _) = _
    rw [Env.reads_cons (by simpa using (hWidth 0).symm)]
    unfold Verified.paramMode
    simp only [tysOfFn, List.replicate_succ, List.cons_append, paramModes, List.headD_cons,
      List.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
    have h := Env.reads_fnFieldsMode (tail := tail) (modes := modes) store rest mode n
      (fun i => ts i.succ) (fun i => values i.succ) (fun i => words i.succ)
      (fun i => hWidth i.succ)
    unfold Verified.paramMode at h
    rw [h]
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc]
    rfl

theorem Env.moves_repeatZero {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (t : Ty) (mode : Mode) :
    ∀ n, n = 0 → ∀ values : Fin n → t.denote,
      Env.moves store (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        rest (Env.prependRepeat t n values tail) = Env.moves store (paramMode Γ modes) rest tail
  | 0, _, _ => rfl

theorem Env.reads_repeatZero {Γ : List Ty} {tail : Env Γ} {modes : List Mode}
    (store : Store Unit) (rest : List Value) (t : Ty) (mode : Mode) :
    ∀ n, n = 0 → ∀ values : Fin n → t.denote,
      Env.reads store (paramMode (List.replicate n t ++ Γ) (List.replicate n mode ++ modes))
        rest (Env.prependRepeat t n values tail) = Env.reads store (paramMode Γ modes) rest tail
  | 0, _, _ => rfl

theorem treeFields_moves (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (mode : Mode) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) (arrayPtrs : Fin (shape.arrays r) → UInt64) :
    Env.moves store (paramMode (shape.context r []) (shape.modes r mode []))
      (shape.branchValues r p words pointers arrayPtrs)
      (Env.treeFields shape r words arrays buffers children .nil) = match mode with
      | .borrowed => []
      | .owned => p :: ((List.ofFn fun i =>
          (children i).toNode.pointers store (pointers i)).flatten ++
          (List.ofFn fun i => [arrayPtrs i]).flatten) := by
  have hBuffers := Env.moves_repeatZero (tail := Env.nil) (modes := []) store [] .bytes mode
    (shape.buffers r) (shape.buffers_eq_zero r) buffers
  have hArrays := Env.moves_fnFieldsMode
    (tail := Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil)
    (modes := List.replicate (shape.buffers r) mode ++ []) store [] mode (shape.arrays r)
    (shape.arrayTy r) arrays arrayPtrs (shape.arrayTy_width r)
  have hChildren := Env.moves_repeatFields
    (tail := Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil))
    (modes := List.replicate (shape.arrays r) mode ++ (List.replicate (shape.buffers r) mode ++ []))
    store (List.ofFn fun i => Value.i64 (arrayPtrs i)) (.tree shape) mode rfl (shape.children r)
    children pointers
  have hWords := Env.moves_fnFields
    (tail := Env.prependRepeat (.tree shape) (shape.children r) children
      (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil)))
    (modes := List.replicate (shape.children r) mode ++
      (List.replicate (shape.arrays r) mode ++ (List.replicate (shape.buffers r) mode ++ [])))
    store ((List.ofFn fun i => Value.i64 (pointers i)) ++
      (List.ofFn fun i => Value.i64 (arrayPtrs i))) .borrowed (shape.words r)
    (shape.wordTy r) words
    (fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i))
    (shape.wordTy_width r) (fun i => shape.wordTy_paramMode r i _)
  rw [show (List.ofFn fun i => Value.i64 (arrayPtrs i)) ++ [] =
    (List.ofFn fun i => Value.i64 (arrayPtrs i)) from List.append_nil _] at hArrays
  unfold Verified.paramMode at hWords hChildren hArrays hBuffers ⊢
  change Env.moves store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape r) .unit _) = _
  rw [Env.moves_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren, hArrays, hBuffers]
  cases mode <;> simp [Ty.paramMode, Ty.pointers, Env.moves, List.ofFn_const, TreeShape.arrayTy]

theorem treeFields_reads (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (mode : Mode) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) (arrayPtrs : Fin (shape.arrays r) → UInt64) :
    Env.reads store (paramMode (shape.context r []) (shape.modes r mode []))
      (shape.branchValues r p words pointers arrayPtrs)
      (Env.treeFields shape r words arrays buffers children .nil) = match mode with
      | .owned => []
      | .borrowed => (List.ofFn fun i =>
          (children i).toNode.slotRegions store (pointers i)).flatten ++
          (List.ofFn fun i => [((arrayPtrs i).toNat,
            8 * (((shape.arrayElem r i).words (arrays i)).size + 1))]).flatten := by
  have hBuffers := Env.reads_repeatZero (tail := Env.nil) (modes := []) store [] .bytes mode
    (shape.buffers r) (shape.buffers_eq_zero r) buffers
  have hArrays := Env.reads_fnFieldsMode
    (tail := Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil)
    (modes := List.replicate (shape.buffers r) mode ++ []) store [] mode (shape.arrays r)
    (shape.arrayTy r) arrays arrayPtrs (shape.arrayTy_width r)
  have hChildren := Env.reads_repeatFields
    (tail := Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil))
    (modes := List.replicate (shape.arrays r) mode ++ (List.replicate (shape.buffers r) mode ++ []))
    store (List.ofFn fun i => Value.i64 (arrayPtrs i)) (.tree shape) mode rfl (shape.children r)
    children pointers
  have hWords := Env.reads_fnFields
    (tail := Env.prependRepeat (.tree shape) (shape.children r) children
      (Env.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Env.prependRepeat .bytes (shape.buffers r) buffers Env.nil)))
    (modes := List.replicate (shape.children r) mode ++
      (List.replicate (shape.arrays r) mode ++ (List.replicate (shape.buffers r) mode ++ [])))
    store ((List.ofFn fun i => Value.i64 (pointers i)) ++
      (List.ofFn fun i => Value.i64 (arrayPtrs i))) .borrowed (shape.words r)
    (shape.wordTy r) words
    (fun i => typedValue (shape.elem r i).slotType (shape.slotWords r words i))
    (shape.wordTy_width r) (fun i => shape.wordTy_paramMode r i _) (fun _ _ => rfl)
  rw [show (List.ofFn fun i => Value.i64 (arrayPtrs i)) ++ [] =
    (List.ofFn fun i => Value.i64 (arrayPtrs i)) from List.append_nil _] at hArrays
  unfold Verified.paramMode at hWords hChildren hArrays hBuffers ⊢
  change Env.reads store _ ([.i64 p] ++ _)
    (Env.cons (t := .treeHeader shape r) .unit _) = _
  rw [Env.reads_cons rfl]
  simp only [TreeShape.context, TreeShape.modes, paramModes, List.headD_cons, List.tail_cons,
    List.getD_cons_zero, List.getD_cons_succ, Ty.paramMode]
  erw [hWords, hChildren, hArrays, hBuffers]
  cases mode <;> simp [Ty.paramMode, Ty.reads, Env.reads, List.ofFn_const, TreeShape.arrayTy]

theorem treeFields_reads_owned (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote)
    (buffers : Fin (shape.buffers r) → LeanExe.Bytes)
    (children : Fin (shape.children r) → Tree shape)
    (pointers : Fin (shape.children r) → UInt64) (arrayPtrs : Fin (shape.arrays r) → UInt64) :
    Env.reads store (paramMode (shape.context r []) (shape.modes r .owned []))
      (shape.branchValues r p words pointers arrayPtrs)
      (Env.treeFields shape r words arrays buffers children .nil) = [] :=
  treeFields_reads store shape r .owned p words arrays buffers children pointers arrayPtrs

end Verified
