import Project.IR.Fold
import Project.Pipeline.Implements
import LeanExe.Loop

/-!
The rule lemma for the compiler's loop template.  The compiler translates
`LeanExe.loop n init f` to assignments of `init`'s components to state locals and
`Stmt.loop`, which runs the translation of `f i` for each index `i` below `n`.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline

variable {m : Module}

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
      Triple m body scratch (fun store st => store = initial ∧ st = state)
        (fun store st => store = initial ∧ State.Frame scratch writes state st ∧
          st.Holds vars (Scalar.values (f (UInt64.ofNat k) s)))) :
    Triple m (.loop limit index count body) scratch
      (fun store state => store = initial ∧ state = before)
      (fun store state => store = initial ∧
        State.Frame scratch (limit :: index :: writes) before state ∧
        state.Holds vars (Scalar.values (LeanExe.loop n init f))) := by
  obtain ⟨hLimitOut, hIndexOut⟩ := hOutside
  have hVarsOut : ∀ j ∈ vars, j < scratch ∧ j ∉ [limit, index] := fun j hj => by
    have := hVars j hj
    refine ⟨this.2, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hLimitOut (h ▸ this.1), fun h => hIndexOut (h ▸ this.1)⟩
  have hIndexVars : index ∉ vars := fun h => hIndexOut (hVars index h).1
  have hWrites : ∀ j ∈ [limit, index], j ∈ limit :: index :: writes := by simp
  have hn := n.toNat_lt
  let Inv : Store Unit → State → Prop := fun store state =>
    store = initial ∧ State.Frame scratch (limit :: index :: writes) before state ∧
      ∃ k, k ≤ n.toNat ∧ state.get index = some (.i64 (UInt64.ofNat k)) ∧
        state.get limit = some (.i64 n) ∧
        state.Holds vars (Scalar.values (loopPrefix f init k))
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
    (Stmt.while_spec Inv measure ?_ fun bound => ?_).mono ?_ ?_
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨n, c1, s1, hCountEval, hSet1, rfl, rfl⟩
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, s1, s2, rfl, hSet2, rfl, rfl⟩
  · rintro store state ⟨-, -, k, -, hIndexGet, hLimitGet, -⟩
    exact ⟨decide (UInt64.ofNat k < n), state, by simp [Expr.eval, hIndexGet, hLimitGet]⟩
  · apply Triple.of_forall
    rintro store state ⟨current, ⟨hStore, hFrame, k, hk, hIndexGet, hLimitGet, hHolds⟩, rfl,
      hCondition⟩
    subst store
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at hCondition
    obtain ⟨hLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hk] at hLess
    refine Stmt.seq_spec (M := fun store st => store = initial ∧
        State.Frame scratch writes current st ∧
        st.Holds vars (Scalar.values (f (UInt64.ofNat k) (loopPrefix f init k))))
      (hBody k _ current hLess hFrame hHolds hIndexGet hLimitGet) ?_
    · apply Triple.of_forall
      rintro store t1 ⟨hStore, hFrameBody, hHoldsT1⟩
      subst store
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
      rintro store state ⟨hStore, hState⟩
      subst store state
      refine ⟨UInt64.ofNat k + 1, t1, t2, by simp [Expr.eval, hIndexT1, U64Op.apply], hSetT2,
        ⟨rfl, hFrameT1.set? hSetT2 (Or.inl (by simp)), k + 1, hLess, ?_, ?_, ?_⟩, ?_⟩
      · rw [State.get_set?_same hSetT2]
        congr 2
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      · rw [State.get_set?_ne hDistinct hSetT2, hLimitT1]
      · rw [loopPrefix_succ]
        exact hHoldsT1.set? hSetT2 hIndexVars
      · simp only [measure, State.get_set?_same hSetT2, hIndexGet, UInt64.toNat_add,
          UInt64.toNat_ofNat', UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · rintro store state ⟨rfl, rfl⟩
    refine ⟨rfl, hFrame2, 0, Nat.zero_le _, State.get_set?_same hSet2, ?_, ?_⟩
    · rw [State.get_set?_ne hDistinct hSet2, State.get_set?_same hSet1]
    · exact hInit.frame hKeep2 hVarsOut
  · rintro store state ⟨current, ⟨hStore, hFrame, k, hk, hIndexGet, hLimitGet, hHolds⟩,
      hCondition⟩
    subst store
    simp only [Expr.eval, hIndexGet, hLimitGet, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hCondition
    obtain ⟨hNotLess, rfl⟩ := hCondition
    rw [ofNat_lt_iff hk] at hNotLess
    obtain rfl : k = n.toNat := by omega
    exact ⟨rfl, hFrame, hHolds⟩

end Project.IR
