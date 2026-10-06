import LeanExe.IR.Denote
import LeanExe.IR.Loop

/-!
The memory-free denotation of statements built from assignments, sequences, and loops, over the
locals and arrays of `Expr.denote`.  A loop tests its condition at most `loopBound` times.
`Stmt.denote_spec` shows that the compiled code of a statement whose denotation succeeds ends in
a state that holds the denoted locals, and `Stmt.denote_loop` gives the denotation of the
compiler's loop template as `LeanExe.loop`.
-/

namespace LeanExe.IR

open Wasm LeanExe.ProofKit LeanExe.Pipeline

variable {m : Module}

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
  | «while» c body ih =>
      intro L L' h j hj
      simp only [Stmt.writes] at hj
      simp only [Stmt.denote] at h
      exact loopIter_inv (fun l => l j = L j)
        (fun x y hx _ hy => (ih x y hy j hj).trans hx) _ L L' rfl h
  | _ =>
      intro L L' h
      simp [Stmt.denote] at h

/-- The compiled code of a statement whose denotation succeeds keeps the store, writes only the
statement's locals below the scratch base, and ends in a state that holds the denoted locals. -/
theorem Stmt.denote_spec {arrays : Nat → Option (Array UInt64)} {store : Store Unit}
    {scratch : Nat} :
    ∀ (s : Stmt) (L L' : Nat → Option Value) (state : State),
      Agrees L arrays store scratch state → s.denote arrays L = some L' →
      (∀ j ∈ s.writes, j < scratch) →
      scratch + s.scratchWidth ≤ state.params.length + state.locals.length →
      Triple m s scratch (fun st s0 => st = store ∧ s0 = state)
        (fun st s1 => st = store ∧ State.Frame scratch s.writes state s1 ∧
          Agrees L' arrays store scratch s1) := by
  intro s
  induction s with
  | skip =>
      intro L L' state hAgree h _ _
      cases h
      exact Stmt.skip_spec.mono (fun _ _ h => h) fun _ _ ⟨h1, h2⟩ => by
        subst h1 h2; exact ⟨rfl, State.Frame.refl _ _ _, hAgree⟩
  | assign j e =>
      rename_i type
      intro L L' state hAgree h hW hRoom
      simp only [Stmt.denote] at h
      split at h
      · rename_i hNone
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Stmt.scratchWidth] at hRoom
        obtain ⟨next, hEval⟩ := Expr.eval_denote e scratch state v hAgree hRoom hv
        have hFrameE := Expr.eval_frame [j] e store.mem scratch state next v hEval
        have hj : j < scratch := hW j (by simp [Stmt.writes])
        obtain ⟨s1, hSet⟩ := State.exists_set? (state := next) (index := j) (type.value v)
          (by rw [hFrameE.params, hFrameE.locals]; omega)
        refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro st s0 ⟨rfl, rfl⟩
        refine ⟨v, next, s1, hEval, hSet, rfl, hFrameE.set? hSet (Or.inl (by simp)),
          fun i w hi => ?_, fun a xs ha => ?_⟩
        · by_cases hij : i = j
          · subst hij
            simp only [↓reduceIte, Option.some.injEq] at hi
            subst hi
            exact ⟨hj, State.get_set?_same hSet⟩
          · simp only [hij, ↓reduceIte] at hi
            obtain ⟨hlt, hget⟩ := hAgree.locals i w hi
            refine ⟨hlt, ?_⟩
            rw [State.get_set?_ne hij hSet,
              Expr.eval_preserves_below e _ scratch s0 next v i hEval hlt]
            exact hget
        · obtain ⟨hlt, ptr, hget, hAt⟩ := hAgree.arrays a xs ha
          have hne : a ≠ j := fun h => by subst h; rw [hNone] at ha; cases ha
          refine ⟨hlt, ptr, ?_, hAt⟩
          rw [State.get_set?_ne hne hSet,
            Expr.eval_preserves_below e _ scratch s0 next v a hEval hlt]
          exact hget
      · cases h
  | seq a b iha ihb =>
      intro L L' state hAgree h hW hRoom
      simp only [Stmt.denote, Option.bind_eq_some_iff] at h
      obtain ⟨L1, h1, h2⟩ := h
      simp only [Stmt.scratchWidth] at hRoom
      refine Stmt.seq_spec (iha L L1 state hAgree h1
        (fun j hj => hW j (by simp [Stmt.writes, hj])) (by omega)) ?_
      apply Triple.of_forall
      rintro st s1 ⟨rfl, hF1, hA1⟩
      refine (ihb L1 L' s1 hA1 h2 (fun j hj => hW j (by simp [Stmt.writes, hj]))
        (by rw [hF1.params, hF1.locals]; omega)).mono (fun _ _ h => h) ?_
      rintro st s2 ⟨rfl, hF2, hA2⟩
      exact ⟨rfl, (hF1.weaken fun j hj => List.mem_append_left _ hj).trans
        (hF2.weaken fun j hj => List.mem_append_right _ hj), hA2⟩
  | «while» c body ih =>
      intro L L' state hAgree h hW hRoom
      classical
      simp only [Stmt.denote] at h
      simp only [Stmt.scratchWidth] at hRoom
      simp only [Stmt.writes] at hW ⊢
      let iter := loopIter (fun l => c.denote l arrays) (Stmt.denote arrays body)
      let Good : State → Nat → Prop := fun s k =>
        ∃ Lc, Agrees Lc arrays store scratch s ∧ iter k Lc = some L'
      let Inv : Store Unit → State → Prop := fun st s =>
        st = store ∧ State.Frame scratch body.writes state s ∧ ∃ k, Good s k
      let measure : Store Unit → State → Nat := fun _ s =>
        if hs : ∃ k, Good s k then Nat.find hs else 0
      have hRoomOf : ∀ s, State.Frame scratch body.writes state s →
          scratch + max c.scratchWidth body.scratchWidth ≤ s.params.length + s.locals.length :=
        fun s hF => by rw [hF.params, hF.locals]; exact hRoom
      -- One test of the condition, from a state with a sufficient bound.
      have hTest : ∀ s k Lc, State.Frame scratch body.writes state s →
          Agrees Lc arrays store scratch s → iter k Lc = some L' →
          ∃ k' b next, k = k' + 1 ∧ c.denote Lc arrays = some b ∧
            c.eval store.mem scratch s = some (b, next) := by
        intro s k Lc hF hA hI
        cases k with
        | zero => cases hI
        | succ k' =>
          rw [show iter (k' + 1) Lc = _ from loopIter_succ _ _ k' Lc] at hI
          cases hc : c.denote Lc arrays with
          | none => simp [hc] at hI
          | some b =>
            obtain ⟨next, hE⟩ := Expr.eval_denote c scratch s b hA
              (by have := hRoomOf s hF; omega) hc
            exact ⟨k', b, next, rfl, rfl, hE⟩
      refine (Stmt.while_spec Inv measure ?_ ?_).mono
        (fun st s ⟨h1, h2⟩ => ⟨h1, h2 ▸ State.Frame.refl _ _ _, loopBound, L, h2 ▸ hAgree, h⟩) ?_
      · rintro st s ⟨rfl, hF, k, Lc, hA, hI⟩
        obtain ⟨_, b, next, -, -, hE⟩ := hTest s k Lc hF hA hI
        exact ⟨b, next, hE⟩
      · intro n
        apply Triple.of_forall
        rintro st s ⟨before, ⟨rfl, hF, hk⟩, hm, hc⟩
        have hGood := Nat.find_spec hk
        have hmeasure : measure st before = Nat.find hk := by simp only [measure, hk, ↓reduceDIte]
        obtain ⟨Lc, hA, hI⟩ := hGood
        obtain ⟨k', b, next, hk', hcd, hE⟩ := hTest before _ Lc hF hA hI
        rw [hE] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, hs⟩ := hc
        subst next
        rw [hk', show iter (k' + 1) Lc = _ from loopIter_succ _ _ k' Lc, hcd] at hI
        simp only [Option.bind_some, ↓reduceIte] at hI
        cases hbd : Stmt.denote arrays body Lc with
        | none => simp [hbd] at hI
        | some Lc1 =>
          simp only [hbd, Option.bind_some] at hI
          have hFc := Expr.eval_frame body.writes c _ scratch before s true hE
          have hAs := hA.frame (next := s) fun j hj =>
            Expr.eval_preserves_below c _ scratch before s true j hE hj
          have hFs := hF.trans hFc
          refine (ih Lc Lc1 s hAs hbd hW (by have := hRoomOf s hFs; omega)).mono
            (fun _ _ h => h) ?_
          rintro st2 s2 ⟨rfl, hF2, hA2⟩
          have hk2 : ∃ k, Good s2 k := ⟨k', Lc1, hA2, hI⟩
          refine ⟨⟨rfl, hFs.trans hF2, hk2⟩, ?_⟩
          simp only [measure, hk2, ↓reduceDIte]
          rw [← hm, hmeasure]
          have := Nat.find_min' hk2 (show Good s2 k' from ⟨Lc1, hA2, hI⟩)
          omega
      · rintro st s ⟨before, ⟨rfl, hF, k, Lc, hA, hI⟩, hc⟩
        obtain ⟨k', b, next, rfl, hcd, hE⟩ := hTest before k Lc hF hA hI
        rw [hE] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, hs⟩ := hc
        subst next
        rw [show iter (k' + 1) Lc = _ from loopIter_succ _ _ k' Lc, hcd] at hI
        simp only [Option.bind_some, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hI
        subst hI
        refine ⟨rfl, hF.trans (Expr.eval_frame body.writes c _ scratch before s false hE),
          hA.frame fun j hj => Expr.eval_preserves_below c _ scratch before s false j hE hj⟩
  | _ =>
      intro L L' state _ h
      simp [Stmt.denote] at h

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
            reduceCtorEq, or_self, Option.map_some, Option.some.injEq]
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

end LeanExe.IR
