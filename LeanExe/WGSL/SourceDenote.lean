import LeanExe.WGSL.Source
import LeanExe.Pipeline.Implements
import LeanExe.Dialect.Loop

/-!
The denotation of the source language from the values of the locals it reads and the arrays at
its pointer locals, without memory: `Expr.denote`, and `Stmt.denote`, in which a loop tests its
condition at most `loopBound` times.  `Stmt.denote_frame` keeps the locals outside a statement's
writes, and `Stmt.denote_loop` gives the denotation of `Stmt.loop` as `LeanExe.loop`.
-/

namespace LeanExe.WGSL.Source

open Wasm LeanExe.Pipeline

def Expr.denote (locals : Nat → Option Value) (arrays : Nat → Option (Array UInt64)) :
    {type : ScalarType} → Expr type → Option type.denote
  | .u64, .get j => match locals j with
    | some (.i64 v) => some v
    | _ => none
  | .u64, .const v => some v
  | .bool, .bconst b => some b
  | .u64, .bin op left right => do
      pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .eq left right => do
      pure ((← left.denote locals arrays) == (← right.denote locals arrays))
  | .bool, .ne left right => do
      pure ((← left.denote locals arrays) != (← right.denote locals arrays))
  | .bool, .ltU left right => do
      pure (decide ((← left.denote locals arrays) < (← right.denote locals arrays)))
  | .bool, .leU left right => do
      pure (decide ((← left.denote locals arrays) ≤ (← right.denote locals arrays)))
  | .bool, .not operand => (operand.denote locals arrays).map (!·)
  | .bool, .and left right => do
      if (← left.denote locals arrays) then right.denote locals arrays else pure false
  | .bool, .or left right => do
      if (← left.denote locals arrays) then pure true else right.denote locals arrays
  | .u64, .ite c t e => do
      if (← c.denote locals arrays) then t.denote locals arrays else e.denote locals arrays
  | .f32, .getF32 j => match locals j with
    | some (.f32 v) => some v
    | _ => none
  | .f32, .constF32 bits => some bits
  | .f32, .binF32 op left right => do
      pure (op.apply (← left.denote locals arrays) (← right.denote locals arrays))
  | .f32, .unF32 op operand => (operand.denote locals arrays).map op.apply
  | .f32, .ofBits32 operand => (operand.denote locals arrays).map (·.toUInt32)
  | .u64, .toBits32 operand => (operand.denote locals arrays).map (·.toUInt64)
  | .f32, .iteF32 c t e => do
      if (← c.denote locals arrays) then t.denote locals arrays else e.denote locals arrays
  | .bool, .eqF32 left right => do
      pure (IEEE32.eq (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .ltF32 left right => do
      pure (IEEE32.lt (← left.denote locals arrays) (← right.denote locals arrays))
  | .bool, .leF32 left right => do
      pure (IEEE32.le (← left.denote locals arrays) (← right.denote locals arrays))
  | .u64, .read array position => do
      let xs ← arrays array
      let k ← position.denote locals arrays
      pure xs[k.toNat]!
  | _, _ => none

theorem denote_two {locals : Nat → Option Value} {arrays : Nat → Option (Array UInt64)}
    {t1 t2 t : ScalarType} {left : Expr t1} {right : Expr t2} {f : t1.denote → t2.denote → t.denote}
    {v : t.denote}
    (h : (do pure (f (← left.denote locals arrays) (← right.denote locals arrays))) = some v) :
    ∃ lv rv, left.denote locals arrays = some lv ∧ right.denote locals arrays = some rv ∧
      f lv rv = v := by
  cases hl : left.denote locals arrays <;> cases hr : right.denote locals arrays <;>
    simp_all

def Expr.denoteLocals : {type : ScalarType} → Expr type → Nat
  | _, .get j | _, .getF32 j => j + 1
  | _, .bin _ left right | _, .eq left right | _, .ne left right
  | _, .ltU left right | _, .leU left right | _, .and left right | _, .or left right
  | _, .binF32 _ left right | _, .eqF32 left right | _, .ltF32 left right
  | _, .leF32 left right => max left.denoteLocals right.denoteLocals
  | _, .not operand | _, .unF32 _ operand | _, .ofBits32 operand | _, .toBits32 operand =>
    operand.denoteLocals
  | _, .ite condition yes no | _, .iteF32 condition yes no =>
    max condition.denoteLocals (max yes.denoteLocals no.denoteLocals)
  | _, .read _ position => position.denoteLocals
  | _, _ => 0

theorem Expr.denote_congr {type : ScalarType} (e : Expr type)
    (locals next : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (same : ∀ j, j < e.denoteLocals → next j = locals j) :
    e.denote next arrays = e.denote locals arrays := by
  induction e generalizing locals next <;>
    simp_all [Expr.denoteLocals, Expr.denote, or_imp, forall_and]

/-- At most `fuel` tests of `cond`: while it holds, `body`. -/
def loopIter (cond : α → Option Bool) (body : α → Option α) : Nat → α → Option α
  | 0, _ => none
  | fuel + 1, x => do if (← cond x) then loopIter cond body fuel (← body x) else pure x

/-- The bound on the tests of a loop's condition. -/
def loopBound : Nat := 2 ^ 64

/-- The locals a statement assigns. -/
def Stmt.writes : Stmt → List Nat
  | .assign j _ => [j]
  | .seq a b => a.writes ++ b.writes
  | .ite _ a b => a.writes ++ b.writes
  | .while _ b => b.writes
  | .load _ j _ => [j]
  | .call _ _ results => results
  | .skip | .store _ _ | .abort => []

def Stmt.denote (arrays : Nat → Option (Array UInt64)) :
    Stmt → (Nat → Option Value) → Option (Nat → Option Value)
  | .skip, locals => some locals
  | .assign (type := type) j e, locals =>
      if arrays j = none then
        (e.denote locals arrays).map fun v i => if i = j then some (type.value v) else locals i
      else none
  | .seq a b, locals => (Stmt.denote arrays a locals).bind (Stmt.denote arrays b)
  | .ite c a b, locals => do
      if (← c.denote locals arrays) then a.denote arrays locals else b.denote arrays locals
  | .while c body, locals =>
      loopIter (fun l => c.denote l arrays) (Stmt.denote arrays body) loopBound locals
  | _, _ => none

theorem loopIter_succ (cond : α → Option Bool) (body : α → Option α) (fuel : Nat) (x : α) :
    loopIter cond body (fuel + 1) x =
      (cond x).bind fun b => if b then (body x).bind (loopIter cond body fuel) else some x := by
  simp only [loopIter, Option.bind_eq_bind, Option.pure_def]

/-- A property that each iteration keeps holds of the result. -/
theorem loopIter_inv {cond : α → Option Bool} {body : α → Option α} (P : α → Prop)
    (hStep : ∀ x y, P x → cond x = some true → body x = some y → P y) :
    ∀ fuel x r, P x → loopIter cond body fuel x = some r → P r := by
  intro fuel
  induction fuel with
  | zero => intro x r _ h; cases h
  | succ fuel ih =>
      intro x r hx h
      rw [loopIter_succ] at h
      cases hc : cond x with
      | none => simp [hc] at h
      | some b =>
        cases b
        · simp only [hc, Option.bind_some, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at h
          exact h ▸ hx
        · simp only [hc, Option.bind_some, ↓reduceIte] at h
          cases hb : body x with
          | none => simp [hb] at h
          | some y =>
            simp only [hb, Option.bind_some] at h
            exact ih y r (hStep x y hx hc hb) h

/-- Locals outside a statement's writes keep their values. -/
theorem Stmt.denote_frame (arrays : Nat → Option (Array UInt64)) :
    ∀ (s : Stmt) (L L' : Nat → Option Value), s.denote arrays L = some L' →
      ∀ j, j ∉ s.writes → L' j = L j := by
  intro s
  induction s with
  | skip =>
      intro L L' h j _
      cases h; rfl
  | assign i e =>
      intro L L' h j hj
      simp only [Stmt.denote] at h
      split at h
      · obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
        have : j ≠ i := by simpa [Stmt.writes] using hj
        simp [this]
      · cases h
  | seq a b iha ihb =>
      intro L L' h j hj
      simp only [Stmt.denote, Option.bind_eq_some_iff] at h
      obtain ⟨L1, h1, h2⟩ := h
      simp only [Stmt.writes, List.mem_append, not_or] at hj
      rw [ihb L1 L' h2 j hj.2, iha L L1 h1 j hj.1]
  | ite c a b iha ihb =>
      intro L L' h j hj
      simp only [Stmt.denote, Option.bind_eq_bind] at h
      simp only [Stmt.writes, List.mem_append, not_or] at hj
      cases hc : c.denote L arrays with
      | none => simp [hc] at h
      | some v =>
          cases v <;> simp only [hc, Option.bind_some, Bool.false_eq_true, ↓reduceIte] at h
          · exact ihb L L' h j hj.2
          · exact iha L L' h j hj.1
  | «while» c body ih =>
      intro L L' h j hj
      simp only [Stmt.writes] at hj
      simp only [Stmt.denote] at h
      exact loopIter_inv (fun l => l j = L j)
        (fun x y hx _ hy => (ih x y hy j hj).trans hx) _ L L' rfl h
  | _ =>
      intro L L' h
      simp [Stmt.denote] at h

/-- The state after the first `k` iterations of `LeanExe.loop`. -/
def loopPrefix (f : UInt64 → α → α) (init : α) (k : Nat) : α :=
  Nat.fold k (fun i _ state => f (UInt64.ofNat i) state) init

theorem loopPrefix_succ (f : UInt64 → α → α) (init : α) (k : Nat) :
    loopPrefix f init (k + 1) = f (UInt64.ofNat k) (loopPrefix f init k) := by
  simp [loopPrefix, Nat.fold_succ]

/-- Local `limit` receives `count`, and for each index from 0 below it, held in
local `index`, `body` runs. -/
def Stmt.loop (limit index : Nat) (count : Expr .u64) (body : Stmt) : Stmt :=
  .seq (.assign limit count) <|
  .seq (.assign index (.const 0)) <|
  .while (.ltU (.get index) (.get limit)) <|
    .seq body (.assign index (.bin .add (.get index) (.const 1)))

/-- The locals `vars` hold `values`. -/
def LocalsHold (L : Nat → Option Value) (vars : List Nat) (values : List Value) : Prop :=
  List.Forall₂ (fun j v => L j = some v) vars values

theorem LocalsHold.congr {L L' : Nat → Option Value} {vars : List Nat} {values : List Value}
    (h : LocalsHold L vars values) (hSame : ∀ j ∈ vars, L' j = L j) : LocalsHold L' vars values := by
  unfold LocalsHold at *
  induction h with
  | nil => exact .nil
  | @cons j v js vs hj _ ih =>
      exact .cons ((hSame j (by simp)).trans hj) (ih fun j' hj' => hSame j' (by simp [hj']))

/-- The denotation of the compiler's loop template: `LeanExe.loop n init f` in the locals `vars`,
provided each run of `body` at index `k` turns locals holding `s` into locals holding `f k s`. -/
theorem Stmt.denote_loop [Scalar α] {arrays : Nat → Option (Array UInt64)} {limit index : Nat}
    {count : Expr .u64} {body : Stmt} {vars : List Nat} {L : Nat → Option Value} {n : UInt64}
    {init : α} (f : UInt64 → α → α)
    (hDistinct : limit ≠ index) (hArrays : arrays limit = none ∧ arrays index = none)
    (hOutside : limit ∉ body.writes ∧ index ∉ body.writes)
    (hVars : ∀ j ∈ vars, j ≠ limit ∧ j ≠ index)
    (hCount : count.denote L arrays = some n)
    (hInit : LocalsHold L vars (Scalar.values init))
    (hBody : ∀ (k : Nat) (s : α) (Lc : Nat → Option Value), k < n.toNat →
      (∀ j, j ∉ limit :: index :: body.writes → Lc j = L j) →
      Lc index = some (.i64 (UInt64.ofNat k)) → Lc limit = some (.i64 n) →
      LocalsHold Lc vars (Scalar.values s) →
      ∃ L2, body.denote arrays Lc = some L2 ∧
        LocalsHold L2 vars (Scalar.values (f (UInt64.ofNat k) s))) :
    ∃ L', (Stmt.loop limit index count body).denote arrays L = some L' ∧
      LocalsHold L' vars (Scalar.values (LeanExe.loop n init f)) := by
  have hn := n.toNat_lt
  let cond := fun l => (Expr.ltU (.get index) (.get limit)).denote l arrays
  let step := Stmt.denote arrays (.seq body (.assign index (.bin .add (.get index) (.const 1))))
  have key : ∀ d k Lc fuel, n.toNat - k = d → k ≤ n.toNat → d + 1 ≤ fuel →
      (∀ j, j ∉ limit :: index :: body.writes → Lc j = L j) →
      Lc index = some (.i64 (UInt64.ofNat k)) → Lc limit = some (.i64 n) →
      LocalsHold Lc vars (Scalar.values (loopPrefix f init k)) →
      ∃ L', loopIter cond step fuel Lc = some L' ∧
        LocalsHold L' vars (Scalar.values (loopPrefix f init n.toNat)) := by
    intro d
    induction d with
    | zero =>
        intro k Lc fuel hd hk hfuel _ hIndex hLimit hHold
        obtain rfl : k = n.toNat := by omega
        obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        have hc : cond Lc = some false := by
          simp [cond, Expr.denote, hIndex, hLimit]
        refine ⟨Lc, ?_, hHold⟩
        rw [loopIter_succ, hc]
        rfl
    | succ d ih =>
        intro k Lc fuel hd hk hfuel hFrame hIndex hLimit hHold
        obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        have hkn : k < n.toNat := by omega
        have hk64 : (UInt64.ofNat k).toNat = k := by simp; omega
        have hc : cond Lc = some true := by
          simp only [cond, Expr.denote, hIndex, hLimit, Option.bind_eq_bind, Option.pure_def,
            Option.bind_some, Option.some.injEq, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hk64]
          exact hkn
        obtain ⟨L2, hL2, hHold2⟩ := hBody k _ Lc hkn hFrame hIndex hLimit hHold
        have hKeep2 := Stmt.denote_frame arrays body Lc L2 hL2
        let L3 : Nat → Option Value := fun i =>
          if i = index then some (.i64 (UInt64.ofNat k + 1)) else L2 i
        have hstep : step Lc = some L3 := by
          simp only [step, Stmt.denote, hL2, Option.bind_some, hArrays.2, ↓reduceIte,
            Expr.denote, hKeep2 index hOutside.2, hIndex, Option.bind_eq_bind, Option.pure_def,
            Option.map_some, Option.some.injEq]
          funext i
          simp [L3, ScalarType.value, U64Op.apply]
        obtain ⟨L', hIter, hHold'⟩ := ih (k + 1) L3 fuel (by omega) (by omega) (by omega)
          (fun j hj => by
            simp only [List.mem_cons, not_or] at hj
            simp only [L3, hj.2.1, ↓reduceIte]
            rw [hKeep2 j hj.2.2]
            exact hFrame j (by simp [hj.1, hj.2.1, hj.2.2]))
          (by
            simp only [L3, ↓reduceIte, Option.some.injEq, Value.i64.injEq]
            apply UInt64.toNat_inj.mp
            simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
            omega)
          (by simp only [L3, hDistinct, ↓reduceIte]; rw [hKeep2 limit hOutside.1]; exact hLimit)
          (by
            rw [loopPrefix_succ]
            exact hHold2.congr fun j hj => by simp [L3, (hVars j hj).2])
        refine ⟨L', ?_, hHold'⟩
        rw [loopIter_succ, hc]
        simp only [Option.bind_some, ↓reduceIte, hstep]
        exact hIter
  let L2 : Nat → Option Value := fun i =>
    if i = index then some (.i64 0) else if i = limit then some (.i64 n) else L i
  have hEq : (Stmt.loop limit index count body).denote arrays L = loopIter cond step loopBound L2 := by
    let L1 : Nat → Option Value := fun i => if i = limit then some (.i64 n) else L i
    have h1 : (Stmt.assign limit count).denote arrays L = some L1 := by
      simp only [Stmt.denote, hArrays.1, ↓reduceIte, hCount, Option.map_some]
      rfl
    have h2 : (Stmt.assign index (.const 0)).denote arrays L1 = some L2 := by
      simp only [Stmt.denote, hArrays.2, ↓reduceIte]
      rfl
    show ((Stmt.assign limit count).denote arrays L).bind (fun L1 =>
      ((Stmt.assign index (.const 0)).denote arrays L1).bind (fun L2 =>
        loopIter cond step loopBound L2)) = _
    rw [h1, Option.bind_some, h2, Option.bind_some]
  obtain ⟨L', hIter, hHold⟩ := key n.toNat 0 L2 loopBound (by omega) (by omega)
    (by simp only [loopBound]; omega)
    (fun j hj => by
      simp only [List.mem_cons, not_or] at hj
      simp [L2, hj.1, hj.2.1])
    (by simp [L2])
    (by simp [L2, hDistinct])
    (hInit.congr fun j hj => by simp [L2, (hVars j hj).1, (hVars j hj).2])
  exact ⟨L', hEq ▸ hIter, hHold⟩

/-- An element of an `Array Float32`, read as a word, holds the element's bits in its low half,
and a missing element reads as 0, the bits of the default. -/
theorem getElem!_map_toBits32 (xs : Array Float32) (k : Nat) :
    (xs.map fun x : Float32 => x.toBits.toUInt64)[k]!.toUInt32 = (xs[k]!).toBits := by
  by_cases h : k < xs.size
  · rw [getElem!_pos (xs.map _) k (by simpa using h), getElem!_pos xs k h]
    simp
  · rw [getElem!_neg (xs.map _) k (by simpa using h), getElem!_neg xs k h]
    decide +kernel

end LeanExe.WGSL.Source
