import LeanExe.IR.Fold
import LeanExe.Pipeline.Implements
import LeanExe.Dialect.Loop

/-!
The rule lemma for the compiler's loop template.  The compiler translates
`LeanExe.loop n init f` to assignments of `init`'s components to state locals and
`Stmt.loop`, which runs the translation of `f i` for each index `i` below `n`.
-/

namespace LeanExe.IR

open Wasm LeanExe.ProofKit LeanExe.Pipeline

variable {m : Module} {a : Bool}

/-- Locals `vars` hold `values`. -/
def State.Holds (state : State) (vars : List Nat) (values : List Value) : Prop :=
  List.Forall₂ (fun j value => state.get j = some value) vars values

/-- Locals below `scratch` and outside `writes` keep their values. -/
theorem State.Holds.frame {before after : State} {scratch : Nat} {writes vars : List Nat}
    {values : List Value} (hFrame : State.Frame scratch writes before after)
    (hVars : ∀ j ∈ vars, j < scratch ∧ j ∉ writes) (hHolds : before.Holds vars values) :
    after.Holds vars values := by
  unfold State.Holds at *
  induction hHolds with
  | nil => exact .nil
  | @cons j value js vs hGet _ ih =>
      have hj := hVars j (by simp)
      exact .cons ((hFrame.get j hj.1 hj.2).trans hGet)
        (ih fun j' hj' => hVars j' (List.mem_cons_of_mem _ hj'))

theorem State.Holds.set? {state next : State} {index : Nat} {value : Value}
    {vars : List Nat} {values : List Value} (hSet : state.set? index value = some next)
    (hVars : index ∉ vars) (hHolds : state.Holds vars values) : next.Holds vars values := by
  unfold State.Holds at *
  induction hHolds with
  | nil => exact .nil
  | @cons j value js vs hGet _ ih =>
      have hNe : j ≠ index := fun h => hVars (h ▸ List.mem_cons_self)
      exact .cons ((State.get_set?_ne hNe hSet).trans hGet)
        (ih fun h => hVars (List.mem_cons_of_mem _ h))

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

theorem ofNat_lt_iff {k : Nat} {n : UInt64} (hk : k ≤ n.toNat) :
    UInt64.ofNat k < n ↔ k < n.toNat := by
  have hn := n.toNat_lt
  have hSize : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]

/-- The counting loop with an invariant `Inv k store vals` over the store and the values
`vals` of the locals `vars`, which may change the store: if each run of `body` at index
`k < n` takes the invariant at `k` to the invariant at `k + 1`, writing only `writes` below
scratch, then the loop takes the invariant at 0 to the invariant at `n`.  It changes only
`limit`, `index`, `writes`, and scratch locals. -/
theorem Stmt.loop_inv {scratch limit index : Nat} {count : Expr .u64} {body : Stmt}
    {vars writes : List Nat} {initial : Store Unit} {before : State} {n : UInt64}
    {vals0 : List Value} (Inv : Nat → Store Unit → List Value → Prop)
    (hDistinct : limit ≠ index) (hLimit : limit < scratch) (hIndex : index < scratch)
    (hOutside : limit ∉ writes ∧ index ∉ writes)
    (hVars : ∀ j ∈ vars, j ∈ writes ∧ j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hInit : before.Holds vars vals0) (hInv0 : Inv 0 initial vals0)
    (hBody : ∀ (k : Nat) (store : Store Unit) (vals : List Value) (state : State), k < n.toNat →
      Inv k store vals → State.Frame scratch (limit :: index :: writes) before state →
      state.Holds vars vals →
      state.get index = some (.i64 (UInt64.ofNat k)) → state.get limit = some (.i64 n) →
      TripleA a m body scratch (fun s st => s = store ∧ st = state)
        (fun s st => State.Frame scratch writes state st ∧
          ∃ vals', st.Holds vars vals' ∧ Inv (k + 1) s vals')) :
    TripleA a m (.loop limit index count body) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => State.Frame scratch (limit :: index :: writes) before state ∧
        ∃ vals, state.Holds vars vals ∧ Inv n.toNat store vals) := by
  obtain ⟨hLimitOut, hIndexOut⟩ := hOutside
  have hVarsOut : ∀ j ∈ vars, j < scratch ∧ j ∉ [limit, index] := fun j hj => by
    have := hVars j hj
    refine ⟨this.2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hLimitOut (h ▸ this.1), fun h => hIndexOut (h ▸ this.1)⟩
  have hIndexVars : index ∉ vars := fun h => hIndexOut (hVars index h).1
  have hn := n.toNat_lt
  let LoopInv : Store Unit → State → Prop := fun store state =>
    State.Frame scratch (limit :: index :: writes) before state ∧
      ∃ k, k ≤ n.toNat ∧ state.get index = some (.i64 (UInt64.ofNat k)) ∧
        state.get limit = some (.i64 n) ∧ ∃ vals, state.Holds vars vals ∧ Inv k store vals
  let measure : Store Unit → State → Nat := fun _ state =>
    match state.get index with
    | some (.i64 k) => n.toNat - k.toNat
    | _ => 0
  obtain ⟨c1, hCountEval⟩ := hCount
  have hFrameC := Expr.eval_frame (limit :: index :: writes) count initial.mem scratch before c1
    _ hCountEval
  obtain ⟨s1, hSet1⟩ := State.exists_set? (state := c1) (index := limit) (.i64 n)
    (by have := hFrameC.params; have := hFrameC.locals; omega)
  have hFrame1 := hFrameC.set? hSet1 (Or.inl (by simp))
  obtain ⟨s2, hSet2⟩ := State.exists_set? (state := s1) (index := index) (.i64 0)
    (by have := hFrame1.params; have := hFrame1.locals; omega)
  have hFrame2 := hFrame1.set? hSet2 (Or.inl (by simp))
  have hKeep2 : State.Frame scratch [limit, index] before s2 :=
    ((Expr.eval_frame [limit, index] count initial.mem scratch before c1 _ hCountEval).set?
      hSet1 (Or.inl (by simp))).set? hSet2 (Or.inl (by simp))
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = s1) ?_ <|
    Stmt.seq_spec (M := fun store state => store = initial ∧ state = s2) ?_ <|
    (Stmt.while_spec LoopInv measure ?_ fun bound => ?_).mono ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨n, c1, s1, hCountEval, hSet1, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, s1, s2, rfl, hSet2, rfl, rfl⟩
  · rintro store state ⟨-, k, -, hIndexGet, hLimitGet, -⟩
    exact ⟨decide (UInt64.ofNat k < n), state, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply TripleA.of_forall
    rintro store state ⟨current, ⟨hFrame, k, hk, hIndexGet, hLimitGet, vals, hHolds, hInvK⟩, rfl,
      hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hk] at hLess
    refine Stmt.seq_spec (hBody k store vals current hLess hInvK hFrame hHolds hIndexGet
      hLimitGet) ?_
    apply TripleA.of_forall
    rintro s1' t1 ⟨hFrameBody, vals', hHoldsT1, hInvT1⟩
    have hIndexT1 : t1.get index = some (.i64 (UInt64.ofNat k)) :=
      (hFrameBody.get index hIndex hIndexOut).trans hIndexGet
    have hLimitT1 : t1.get limit = some (.i64 n) :=
      (hFrameBody.get limit hLimit hLimitOut).trans hLimitGet
    obtain ⟨t2, hSetT2⟩ := State.exists_set? (state := t1) (index := index)
      (.i64 (UInt64.ofNat k + 1))
      (by have := hFrameBody.params; have := hFrameBody.locals; have := hFrame.params;
          have := hFrame.locals; omega)
    have hFrameT1 : State.Frame scratch (limit :: index :: writes) before t1 :=
      hFrame.trans ⟨hFrameBody.params, hFrameBody.locals, fun j hj hOut =>
        hFrameBody.get j hj (fun h => hOut (by simp [h]))⟩
    refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store' state' ⟨hStore, hState⟩
    subst store' state'
    refine ⟨UInt64.ofNat k + 1, t1, t2, by simp [Expr.eval, hIndexT1, U64Op.apply], hSetT2,
      ⟨hFrameT1.set? hSetT2 (Or.inl (by simp)), k + 1, hLess, ?_, ?_, vals',
        hHoldsT1.set? hSetT2 hIndexVars, hInvT1⟩, ?_⟩
    · rw [State.get_set?_same hSetT2]
      congr 2
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
      omega
    · rw [State.get_set?_ne hDistinct hSetT2, hLimitT1]
    · simp only [measure, State.get_set?_same hSetT2, hIndexGet, UInt64.toNat_add,
        UInt64.toNat_ofNat', UInt64.reduceToNat]
      rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨hFrame2, 0, Nat.zero_le _, State.get_set?_same hSet2, ?_, vals0,
      hInit.frame hKeep2 hVarsOut, hInv0⟩
    rw [State.get_set?_ne hDistinct hSet2, State.get_set?_same hSet1]
  · rintro store state ⟨current, ⟨hFrame, k, hk, hIndexGet, hLimitGet, hHolds⟩, hCondition⟩
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hk] at hNotLess
    obtain rfl : k = n.toNat := by omega
    exact ⟨hFrame, hHolds⟩

/-- The loop leaves `LeanExe.loop n init f` in the state locals `vars`, provided
each run of `body` at index `k` turns a state holding `s` into one holding
`f k s`, writing only `writes` below scratch.  It keeps the store and changes only
`limit`, `index`, `writes`, and scratch locals. -/
theorem Stmt.loop_spec [Scalar α] {scratch limit index : Nat} {count : Expr .u64} {body : Stmt}
    {vars writes : List Nat} {initial : Store Unit} {before : State} {n : UInt64} {init : α}
    (f : UInt64 → α → α)
    (hDistinct : limit ≠ index) (hLimit : limit < scratch) (hIndex : index < scratch)
    (hOutside : limit ∉ writes ∧ index ∉ writes)
    (hVars : ∀ j ∈ vars, j ∈ writes ∧ j < scratch)
    (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hCount : ∃ next, count.eval initial.mem scratch before = some (n, next))
    (hInit : before.Holds vars (Scalar.values init))
    (hBody : ∀ (k : Nat) (s : α) (state : State), k < n.toNat →
      State.Frame scratch (limit :: index :: writes) before state →
      state.Holds vars (Scalar.values s) →
      state.get index = some (.i64 (UInt64.ofNat k)) → state.get limit = some (.i64 n) →
      TripleA a m body scratch (fun store st => store = initial ∧ st = state)
        (fun store st => store = initial ∧ State.Frame scratch writes state st ∧
          st.Holds vars (Scalar.values (f (UInt64.ofNat k) s)))) :
    TripleA a m (.loop limit index count body) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧
        State.Frame scratch (limit :: index :: writes) before state ∧
        state.Holds vars (Scalar.values (LeanExe.loop n init f))) := by
  refine (Stmt.loop_inv (vals0 := Scalar.values init)
    (fun k store vals => store = initial ∧ vals = Scalar.values (loopPrefix f init k))
    hDistinct hLimit hIndex hOutside hVars hRoom hCount hInit ⟨rfl, rfl⟩
    fun k store vals state hk ⟨hStore, hVals⟩ hFrame hHolds hIndexGet hLimitGet => ?_).mono
      (fun _ _ h => h) ?_
  · subst hStore hVals
    refine (hBody k _ state hk hFrame hHolds hIndexGet hLimitGet).mono (fun _ _ h => h) ?_
    rintro s st ⟨hs, hFrameBody, hHolds'⟩
    exact ⟨hFrameBody, _, hHolds', hs, by rw [loopPrefix_succ]⟩
  · rintro s st ⟨hFrame, vals, hHolds, hs, rfl⟩
    exact ⟨hs, hFrame, hHolds⟩

end LeanExe.IR
