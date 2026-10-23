import Verified.State
import Verified.Rename
import Verified.Bound

namespace Verified

open LeanExe.ProofKit LeanExe.Pipeline Wasm

private theorem array_fold_prefix [Inhabited α] (xs : Array α) (step : β → α → β)
    (init : β) (n : Nat) (hn : n ≤ xs.size) :
    Nat.fold n (fun i _ acc => step acc xs[i]!) init =
      ArrayFold.foldPrefix xs step init n := by
  induction n with
  | zero => simp [ArrayFold.foldPrefix]
  | succ n ih =>
    rw [Nat.fold_succ, ih (by omega), ArrayFold.foldPrefix_succ xs step init n (by omega)]
    rw [getElem!_pos xs n (by omega)]

theorem array_fold_eq_loop [Inhabited α] (xs : Array α) (step : β → α → β)
    (init : β) (hSize : xs.size < UInt64.size) :
    xs.foldl step init = LeanExe.loop xs.size.toUInt64 init
      (fun i acc => step acc xs[i.toNat]!) := by
  unfold LeanExe.loop
  rw [UInt64.toNat_ofNat_of_lt' hSize]
  have hIndices :
      (fun (i : Nat) (_ : i < xs.size) (acc : β) => step acc xs[(UInt64.ofNat i).toNat]!) =
        (fun (i : Nat) (_ : i < xs.size) (acc : β) => step acc xs[i]!) := by
    funext i hi acc
    rw [UInt64.toNat_ofNat_of_lt' (hi.trans hSize)]
  rw [hIndices, array_fold_prefix xs step init xs.size (Nat.le_refl _),
    ArrayFold.foldPrefix_size]

theorem Ty.Rep.array_size_lt {mode : Mode} {heap : Heap} {store : Store Unit}
    {e : Elem} {ws : List Value} {xs : Array e.denote}
    (h : Ty.Rep mode heap store (.array e) ws xs) : xs.size < UInt64.size := by
  obtain ⟨ptr, -, hArray⟩ := h
  have hWords := hArray.borrow.values.size_lt
  rw [Elem.words_size] at hWords
  exact (Nat.le_mul_of_pos_right xs.size e.width_pos).trans_lt hWords

theorem Ty.Rep.array_fold_eq_loop {mode : Mode} {heap : Heap} {store : Store Unit}
    {e : Elem} {ws : List Value} {xs : Array e.denote}
    (h : Ty.Rep mode heap store (.array e) ws xs) (step : β → e.denote → β) (init : β) :
    xs.foldl step init = LeanExe.loop xs.size.toUInt64 init
      (fun i acc => step acc xs[i.toNat]!) :=
  Verified.array_fold_eq_loop xs step init h.array_size_lt

/-- The loop implementation of a fold body whose variables 0 and 1 are the element and
accumulator. -/
def Expr.foldLoop (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: Γ) t) : Expr S Γ t :=
  .loop (.size x) init (.bool true)
    (.letE (.get (.there (.there x)) (.var (.there .here)))
      (body.rename (Renaming.lift (Renaming.lift (fun x => .there x)))))

theorem Expr.denote_foldLoop (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: Γ) t) (funs : Funs S) (env : Env Γ)
    (hSize : (env.get x).size < UInt64.size) :
    (Expr.foldLoop x init body).denote funs env =
      (env.get x).foldl (fun acc value => body.denote funs (.cons value (.cons acc env)))
        (init.denote funs env) := by
  rw [array_fold_eq_loop (env.get x) _ _ hSize]
  simp [Expr.foldLoop, Expr.denote, Expr.denote_rename, Env.get]

theorem loop_counted (n : UInt64) (init : α) (step : UInt64 → UInt64 → α → α) :
    LeanExe.loop n ((0 : UInt64), init)
        (fun i state => (state.1 + 1, step i state.1 state.2)) =
      (n, LeanExe.loop n init (fun i state => step i i state)) := by
  have h (k : Nat) :
      Nat.fold k (fun j _ (state : UInt64 × α) =>
        (state.1 + 1, step (UInt64.ofNat j) state.1 state.2)) (0, init) =
      (UInt64.ofNat k,
        Nat.fold k (fun j _ state => step (UInt64.ofNat j) (UInt64.ofNat j) state) init) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Nat.fold_succ, ih, UInt64.ofNat_add]; rfl
  simpa [LeanExe.loop] using h n.toNat

theorem Expr.foldExpand_denote (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (funs : Funs S) (env : Env Γ)
    (hSize : (env.get x).size < UInt64.size) :
    (Expr.foldExpand x init body).denote funs env = (Expr.fold x init body).denote funs env := by
  simp only [Expr.foldExpand, Expr.foldStep, Expr.denote, Env.get]
  rw [array_fold_eq_loop (env.get x) _ _ hSize]
  exact (congrArg Prod.snd (loop_counted (env.get x).size.toUInt64 (init.denote funs env)
    (fun j i state => body.denote funs
      (.cons ((env.get x)[j.toNat]!) (.cons state (.cons i env)))))).symm

theorem Expr.foldExpand_aborts (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    (Expr.foldExpand x init body).aborts = (Expr.fold x init body).aborts := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.aborts]

theorem Expr.foldExpand_depthCalls (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    (Expr.foldExpand x init body).depthCalls = (Expr.fold x init body).depthCalls := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.depthCalls]

theorem Expr.foldExpand_uses (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (i : Nat) :
    (Expr.foldExpand x init body).uses i = (Expr.fold x init body).uses i := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.uses, Var.index, Nat.add_assoc,
    Bool.or_left_comm, Bool.or_comm]

theorem Expr.foldExpand_placeArgs (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    (Expr.foldExpand x init body).placeArgs = (Expr.fold x init body).placeArgs := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.placeArgs]

theorem Expr.foldExpand_mode (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (modes : List Mode) :
    (Expr.foldExpand x init body).mode modes = (Expr.fold x init body).mode modes := rfl

theorem Expr.foldExpand_width (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) :
    (Expr.foldExpand x init body).width = (Expr.fold x init body).width := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.width, Ty.width, Ty.copyScratch, Ty.scalar]

theorem Expr.foldExpand_paid (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (flags : Flags S) (modes : List Mode)
    (paid : List Bool) (live : Nat → Bool) :
    (Expr.foldExpand x init body).paid flags modes paid live =
      (Expr.fold x init body).paid flags modes paid live := rfl

theorem Expr.foldExpand_allocs (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (modes : List Mode) (paid : List Bool) (live : Nat → Bool) (env : Env Γ) :
    (Expr.foldExpand x init body).allocs funs flags bounds modes paid live env =
      (Expr.fold x init body).allocs funs flags bounds modes paid live env := by
  simp [Expr.foldExpand, Expr.foldStep, Expr.allocs, loopAlloc, Expr.mode, Expr.paid,
    Expr.denote, Var.cost, modeAt, Env.get, Var.index]

theorem Expr.foldExpand_fits (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (funs : Funs S) (fits : Fits S) (env : Env Γ) :
    (Expr.foldExpand x init body).fits funs fits env = (Expr.fold x init body).fits funs fits env := rfl

theorem Expr.foldStep_code {pool : Bytes.LiteralPool} (x : Var Γ (.array e))
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) :
    (Expr.foldStep x body).code (pool := pool) h slots base live =
      getCode (Γ := t :: .word :: Γ) slots (base + e.width)
          (fun i => live i || body.usesFast (i + 1)) (.there (.there x))
          (fun live => Var.code (Γ := t :: .word :: Γ) (t := .word)
            h slots (base + e.width) live (.there .here)) ++
        storeCode h base e.types ++
        body.code (pool := pool) h (⟨base, .borrowed⟩ :: slots) (base + e.width) (shift 1 live) := by
  simp [Expr.foldStep, Expr.code, Expr.mode, Ty.types, Ty.width, List.append_assoc]

theorem Expr.foldExpand_code {pool : Bytes.LiteralPool}
    (x : Var Γ (.array e)) (init : Expr S Γ t)
    (body : Expr S (.elem e :: t :: .word :: Γ) t) (h : Nat) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) :
    (Expr.foldExpand x init body).code (pool := pool) h slots base live =
      (Expr.fold x init body).code (pool := pool) h slots base live := by
  simp only [Expr.foldExpand, Expr.code, Expr.foldStep_code, boolWord, Bool.cond_true]

#print axioms array_fold_eq_loop
#print axioms Ty.Rep.array_size_lt
#print axioms Ty.Rep.array_fold_eq_loop
#print axioms Expr.denote_foldLoop
#print axioms Expr.foldExpand_denote
#print axioms Expr.foldExpand_code

end Verified
