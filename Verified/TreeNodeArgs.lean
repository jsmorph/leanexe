import Verified.FieldsArgs
import Verified.WordCode

namespace Verified

/-- The arguments of a construction in the order of evaluation: its words, children, arrays, and
buffers. -/
def treeArgs {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) :
    Args S Γ (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) .bytes ++ [])))) :=
  Args.prependFn (shape.words r) (shape.wordTy r) words
    (Args.prependRepeat (.tree shape) (shape.children r) children
      (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Args.prependRepeat .bytes (shape.buffers r) buffers .nil)))

theorem treeArgs_denote {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (funs : Funs S) (env : Env Γ) (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) :
    (treeArgs words children arrays buffers).denote funs env =
      Env.prependFn (shape.words r) (shape.wordTy r) (fun i => (words i).denote funs env)
        (Env.prependRepeat (.tree shape) (shape.children r)
          (fun i => (children i).denote funs env)
          (Env.prependFn (shape.arrays r) (shape.arrayTy r) (fun i => (arrays i).denote funs env)
            (Env.prependRepeat .bytes (shape.buffers r) (fun i => (buffers i).denote funs env)
              .nil))) := by
  simp only [treeArgs, Args.denote_prependFn, Args.denote_prependRepeat, Args.denote]

theorem treeArgs_forall {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Prop)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes)
    (hWords : ∀ i, P i.val (words i))
    (hChildren : ∀ i, P (shape.words r + i.val) (children i))
    (hArrays : ∀ i, P (shape.words r + shape.children r + i.val) (arrays i))
    (hBuffers : ∀ i, P (shape.words r + shape.children r + shape.arrays r + i.val) (buffers i)) :
    ∀ i, P i.val ((treeArgs words children arrays buffers).get i) := by
  apply Args.forall_get_prependFn P _ _ _ _ hWords
  apply Args.forall_get_prependRepeat (fun j value => P (shape.words r + j) value) _ _ _ _
    hChildren
  apply Args.forall_get_prependFn (fun j value => P (shape.words r + (shape.children r + j)) value)
    _ _ _ _ (fun i => by simpa only [Nat.add_assoc] using hArrays i)
  apply Args.forall_get_prependRepeat
    (fun j value => P (shape.words r + (shape.children r + (shape.arrays r + j))) value) _ _ _ _
    (fun i => by simpa only [Nat.add_assoc] using hBuffers i)
  intro i
  exact Fin.elim0 i

@[simp] theorem TreeShape.arrayTy_types (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.arrays r)) : (shape.arrayTy r i).types = [.i64] :=
  rfl

theorem treeArgs_any {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Bool)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) :
    (argsAny fun i => P i.val ((treeArgs words children arrays buffers).get i)) =
      ((argsAny fun i => P i.val (words i)) ||
        (argsAny fun i => P (shape.words r + i.val) (children i)) ||
        (argsAny fun i => P (shape.words r + shape.children r + i.val) (arrays i)) ||
        (argsAny fun i =>
          P (shape.words r + shape.children r + shape.arrays r + i.val) (buffers i))) := by
  have h1 := Args.any_prependFn P (shape.words r) (shape.wordTy r) words
    (Args.prependRepeat (.tree shape) (shape.children r) children
      (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Args.prependRepeat .bytes (shape.buffers r) buffers .nil)))
  have h2 := Args.any_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + j) value) (.tree shape)
    (shape.children r) children
    (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Args.prependRepeat .bytes (shape.buffers r) buffers .nil))
  have h3 := Args.any_prependFn
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + (shape.children r + j)) value)
    (shape.arrays r) (shape.arrayTy r) arrays
    (Args.prependRepeat .bytes (shape.buffers r) buffers .nil)
  have h4 := Args.any_prependRepeat
    (fun {t} j (value : Expr S Γ t) =>
      P (shape.words r + (shape.children r + (shape.arrays r + j))) value)
    .bytes (shape.buffers r) buffers .nil
  dsimp only [treeArgs]
  rw [h1, h2, h3, h4]
  simp only [argsAny, Bool.or_false, Bool.or_assoc, Nat.add_assoc]

theorem treeArgs_sum {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (P : {t : Ty} → Nat → Expr S Γ t → Nat)
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) :
    (argsSum fun i => P i.val ((treeArgs words children arrays buffers).get i)) =
      (argsSum fun i => P i.val (words i)) +
        (argsSum fun i => P (shape.words r + i.val) (children i)) +
        (argsSum fun i => P (shape.words r + shape.children r + i.val) (arrays i)) +
        (argsSum fun i =>
          P (shape.words r + shape.children r + shape.arrays r + i.val) (buffers i)) := by
  have h1 := Args.sum_prependFn P (shape.words r) (shape.wordTy r) words
    (Args.prependRepeat (.tree shape) (shape.children r) children
      (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
        (Args.prependRepeat .bytes (shape.buffers r) buffers .nil)))
  have h2 := Args.sum_prependRepeat
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + j) value) (.tree shape)
    (shape.children r) children
    (Args.prependFn (shape.arrays r) (shape.arrayTy r) arrays
      (Args.prependRepeat .bytes (shape.buffers r) buffers .nil))
  have h3 := Args.sum_prependFn
    (fun {t} j (value : Expr S Γ t) => P (shape.words r + (shape.children r + j)) value)
    (shape.arrays r) (shape.arrayTy r) arrays
    (Args.prependRepeat .bytes (shape.buffers r) buffers .nil)
  have h4 := Args.sum_prependRepeat
    (fun {t} j (value : Expr S Γ t) =>
      P (shape.words r + (shape.children r + (shape.arrays r + j))) value)
    .bytes (shape.buffers r) buffers .nil
  dsimp only [treeArgs]
  rw [h1, h2, h3, h4]
  simp only [argsSum, Nat.add_zero, Nat.add_assoc]

theorem treeArgs_live {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) (kept : Nat → Bool)
    (offset k : Nat) :
    fieldLive (treeArgs words children arrays buffers).get kept offset k =
      (kept k || (argsAny fun i => decide (offset ≤ i.val) && (words i).uses k) ||
        (argsAny fun i => decide (offset ≤ shape.words r + i.val) && (children i).uses k) ||
        (argsAny fun i =>
          decide (offset ≤ shape.words r + shape.children r + i.val) && (arrays i).uses k) ||
        (argsAny fun i =>
          decide (offset ≤ shape.words r + shape.children r + shape.arrays r + i.val) &&
            (buffers i).uses k)) := by
  rw [fieldLive, treeArgs_any (fun {t} j (value : Expr S Γ t) =>
    decide (offset ≤ j) && value.uses k) words children arrays buffers]
  simp only [Bool.or_assoc]

theorem treeArgs_wordLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) (kept : Nat → Bool)
    (i : Fin (shape.words r)) (k : Nat) :
    fieldLive (treeArgs words children arrays buffers).get kept (i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (words j).uses k) ||
        (argsAny fun j => (children j).uses k) || (argsAny fun j => (arrays j).uses k) ||
        (argsAny fun j => (buffers j).uses k)) := by
  rw [treeArgs_live]
  have hi := i.isLt
  have hChildren : (fun j : Fin (shape.children r) =>
      decide (i.val + 1 ≤ shape.words r + j.val) && (children j).uses k) =
      fun j => (children j).uses k := by
    funext j
    simp only [show i.val + 1 ≤ shape.words r + j.val by omega, decide_true, Bool.true_and]
  have hArrays : (fun j : Fin (shape.arrays r) =>
      decide (i.val + 1 ≤ shape.words r + shape.children r + j.val) && (arrays j).uses k) =
      fun j => (arrays j).uses k := by
    funext j
    simp only [show i.val + 1 ≤ shape.words r + shape.children r + j.val by omega, decide_true,
      Bool.true_and]
  have hBuffers : (fun j : Fin (shape.buffers r) =>
      decide (i.val + 1 ≤ shape.words r + shape.children r + shape.arrays r + j.val) &&
        (buffers j).uses k) =
      fun j => (buffers j).uses k := by
    funext j
    simp only [show i.val + 1 ≤ shape.words r + shape.children r + shape.arrays r + j.val by
      omega, decide_true, Bool.true_and]
  rw [hChildren, hArrays, hBuffers]
  simp only [Nat.add_one_le_iff]

theorem treeArgs_childLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) (kept : Nat → Bool)
    (i : Fin (shape.children r)) (k : Nat) :
    fieldLive (treeArgs words children arrays buffers).get kept (shape.words r + i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (children j).uses k) ||
        (argsAny fun j => (arrays j).uses k) || (argsAny fun j => (buffers j).uses k)) := by
  rw [treeArgs_live]
  have hi := i.isLt
  have hWords : (fun j : Fin (shape.words r) =>
      decide (shape.words r + i.val + 1 ≤ j.val) && (words j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + i.val + 1 ≤ j.val by omega, decide_false, Bool.false_and]
  have hChildren : (fun j : Fin (shape.children r) =>
      decide (shape.words r + i.val + 1 ≤ shape.words r + j.val) && (children j).uses k) =
      fun j => decide (i.val < j.val) && (children j).uses k := by
    funext j
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  have hArrays : (fun j : Fin (shape.arrays r) =>
      decide (shape.words r + i.val + 1 ≤ shape.words r + shape.children r + j.val) &&
        (arrays j).uses k) =
      fun j => (arrays j).uses k := by
    funext j
    simp only [show shape.words r + i.val + 1 ≤ shape.words r + shape.children r + j.val by omega,
      decide_true, Bool.true_and]
  have hBuffers : (fun j : Fin (shape.buffers r) =>
      decide (shape.words r + i.val + 1 ≤
        shape.words r + shape.children r + shape.arrays r + j.val) && (buffers j).uses k) =
      fun j => (buffers j).uses k := by
    funext j
    simp only [show shape.words r + i.val + 1 ≤
      shape.words r + shape.children r + shape.arrays r + j.val by omega, decide_true,
      Bool.true_and]
  rw [hWords, hChildren, hArrays, hBuffers, argsAny_false, Bool.or_false]

theorem treeArgs_arrayLive {S : List Sig} {Γ : List Ty} {shape : TreeShape} {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) (kept : Nat → Bool)
    (i : Fin (shape.arrays r)) (k : Nat) :
    fieldLive (treeArgs words children arrays buffers).get kept
        (shape.words r + shape.children r + i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (arrays j).uses k) ||
        (argsAny fun j => (buffers j).uses k)) := by
  rw [treeArgs_live]
  have hi := i.isLt
  have hWords : (fun j : Fin (shape.words r) =>
      decide (shape.words r + shape.children r + i.val + 1 ≤ j.val) && (words j).uses k) =
      fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + shape.children r + i.val + 1 ≤ j.val by omega, decide_false,
      Bool.false_and]
  have hChildren : (fun j : Fin (shape.children r) =>
      decide (shape.words r + shape.children r + i.val + 1 ≤ shape.words r + j.val) &&
        (children j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + shape.children r + i.val + 1 ≤ shape.words r + j.val by
      omega, decide_false, Bool.false_and]
  have hArrays : (fun j : Fin (shape.arrays r) =>
      decide (shape.words r + shape.children r + i.val + 1 ≤
        shape.words r + shape.children r + j.val) && (arrays j).uses k) =
      fun j => decide (i.val < j.val) && (arrays j).uses k := by
    funext j
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  have hBuffers : (fun j : Fin (shape.buffers r) =>
      decide (shape.words r + shape.children r + i.val + 1 ≤
        shape.words r + shape.children r + shape.arrays r + j.val) && (buffers j).uses k) =
      fun j => (buffers j).uses k := by
    funext j
    simp only [show shape.words r + shape.children r + i.val + 1 ≤
      shape.words r + shape.children r + shape.arrays r + j.val by omega, decide_true,
      Bool.true_and]
  rw [hWords, hChildren, hArrays, hBuffers, argsAny_false, argsAny_false, Bool.or_false,
    Bool.or_false]

theorem treeArgs_bufferLive {S : List Sig} {Γ : List Ty} {shape : TreeShape}
    {r : Fin shape.records}
    (words : (i : Fin (shape.words r)) → Expr S Γ (shape.wordTy r i))
    (children : Fin (shape.children r) → Expr S Γ (.tree shape))
    (arrays : (i : Fin (shape.arrays r)) → Expr S Γ (shape.arrayTy r i))
    (buffers : Fin (shape.buffers r) → Expr S Γ .bytes) (kept : Nat → Bool)
    (i : Fin (shape.buffers r)) (k : Nat) :
    fieldLive (treeArgs words children arrays buffers).get kept
        (shape.words r + shape.children r + shape.arrays r + i.val + 1) k =
      (kept k || (argsAny fun j => decide (i.val < j.val) && (buffers j).uses k)) := by
  rw [treeArgs_live]
  have hi := i.isLt
  have hWords : (fun j : Fin (shape.words r) =>
      decide (shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤ j.val) &&
        (words j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤ j.val by
      omega, decide_false, Bool.false_and]
  have hChildren : (fun j : Fin (shape.children r) =>
      decide (shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤
        shape.words r + j.val) && (children j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤
      shape.words r + j.val by omega, decide_false, Bool.false_and]
  have hArrays : (fun j : Fin (shape.arrays r) =>
      decide (shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤
        shape.words r + shape.children r + j.val) && (arrays j).uses k) = fun _ => false := by
    funext j
    have hj := j.isLt
    simp only [show ¬shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤
      shape.words r + shape.children r + j.val by omega, decide_false, Bool.false_and]
  have hBuffers : (fun j : Fin (shape.buffers r) =>
      decide (shape.words r + shape.children r + shape.arrays r + i.val + 1 ≤
        shape.words r + shape.children r + shape.arrays r + j.val) && (buffers j).uses k) =
      fun j => decide (i.val < j.val) && (buffers j).uses k := by
    funext j
    congr 1
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  rw [hWords, hChildren, hArrays, hBuffers, argsAny_false, argsAny_false, argsAny_false,
    Bool.or_false, Bool.or_false, Bool.or_false]

theorem tysOfFn_flatMap_types : (n : Nat) → (ts : Fin n → Ty) → (tys : Fin n → Wasm.ValueType) →
    (∀ i, (ts i).types = [tys i]) → (tysOfFn n ts).flatMap Ty.types = List.ofFn tys
  | 0, _, _, _ => rfl
  | n + 1, ts, tys, h => by
    rw [tysOfFn, List.flatMap_cons, h 0, List.ofFn_succ,
      tysOfFn_flatMap_types n (fun i => ts i.succ) (fun i => tys i.succ) (fun i => h i.succ)]
    rfl

/-- The WebAssembly types of a record's fields in a construction's locals: each word field's slot
type, then i64 for each child. -/
theorem flatMap_types_replicate_tree (shape : TreeShape) :
    (n : Nat) → (List.replicate n (Ty.tree shape)).flatMap Ty.types = List.replicate n .i64
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, flatMap_types_replicate_tree shape n]
    rfl

theorem flatMap_types_replicate_bytes :
    (n : Nat) → (List.replicate n Ty.bytes).flatMap Ty.types = List.replicate (2 * n) .i64
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, flatMap_types_replicate_bytes n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]
    rfl

/-- The WebAssembly types of a construction's arguments in its locals: each word field's slot type,
then i64 for each child and each array, and two for each buffer. -/
theorem tysOfFn_widthSum : (n : Nat) → (ts : Fin n → Ty) → (∀ i, (ts i).width = 1) →
    ((tysOfFn n ts).map Ty.width).sum = n
  | 0, _, _ => rfl
  | n + 1, ts, h => by
    simp only [tysOfFn, List.map_cons, List.sum_cons, h 0,
      tysOfFn_widthSum n (fun i => ts i.succ) (fun i => h i.succ)]
    omega

theorem replicate_widthSum (t : Ty) : (n : Nat) →
    ((List.replicate n t).map Ty.width).sum = n * t.width
  | 0 => by simp
  | n + 1 => by
    simp only [List.replicate_succ, List.map_cons, List.sum_cons, replicate_widthSum t n,
      Nat.add_mul, Nat.one_mul]
    omega

/-- The locals that a record's arguments take: one for each word, child, and array, and two for
each buffer. -/
theorem treeArgs_widths (shape : TreeShape) (r : Fin shape.records) :
    ((tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (Ty.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) Ty.bytes ++ [])))).map Ty.width).sum =
      shape.words r + shape.children r + shape.arrays r + 2 * shape.buffers r := by
  have hTree : (Ty.tree shape).width = 1 := rfl
  have hBytes : Ty.bytes.width = 2 := rfl
  simp only [List.map_append, List.sum_append, List.append_nil,
    tysOfFn_widthSum (shape.words r) (shape.wordTy r) (fun i => shape.elem_width r i),
    tysOfFn_widthSum (shape.arrays r) (shape.arrayTy r) (fun _ => rfl),
    replicate_widthSum, hTree, hBytes]
  omega

theorem treeArgs_types (shape : TreeShape) (r : Fin shape.records) :
    (tysOfFn (shape.words r) (shape.wordTy r) ++
      (List.replicate (shape.children r) (Ty.tree shape) ++
        (tysOfFn (shape.arrays r) (shape.arrayTy r) ++
          (List.replicate (shape.buffers r) Ty.bytes ++ [])))).flatMap Ty.types =
      shape.wordTypes r ++ (List.replicate (shape.children r) .i64 ++
        (List.replicate (shape.arrays r) .i64 ++ List.replicate (2 * shape.buffers r) .i64)) := by
  rw [List.append_nil, List.flatMap_append, List.flatMap_append, List.flatMap_append,
    tysOfFn_flatMap_types (shape.words r) (shape.wordTy r) (fun i => (shape.elem r i).slotType)
      (fun i => Elem.types_one (shape.elem r i) (shape.elem_width r i)),
    tysOfFn_flatMap_types (shape.arrays r) (shape.arrayTy r) (fun _ => .i64) (fun _ => rfl),
    flatMap_types_replicate_tree, flatMap_types_replicate_bytes, List.ofFn_const]
  rfl

end Verified
