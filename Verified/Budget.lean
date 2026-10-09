import Verified.Correct

/-! The compiler's correctness theorem with the allocation bound: the code of an expression traps
only through a call of a function whose code takes the call depth, or when `top` cannot rise by
the expression's bound, `Expr.allocs`, within the memory cap, and it raises `top` by at most that
bound. -/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The traps that the code of `e` may have from `heap` at `store`: any, when it calls a function
whose code takes the call depth, and otherwise those of allocation, when it may allocate and `top`
cannot rise by `bound` within the cap. -/
abbrev trapFlag {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (e : Expr S Γ t)
    (slots : List Slot) (heap : Heap) (store : Store Unit) (bound : Nat) : Bool :=
  e.depthCalls ||
    ((e.aborts || slots.any (·.mode == .owned)) && !decide (heap.Within store m bound))

/-- `CodeSpec` with the allocation bound: the code may trap only as `trapFlag` allows for the
bound `e.allocs`, and, when it takes no call depth, it raises `top` by at most that bound. -/
def CodeSpecB {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (bounds : Bounds S) (host : HostEnv Unit) (pv : List Value) (e : Expr S Γ t) (env : Env Γ)
    (slots : List Slot) (live : Nat → Bool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.half = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store (e.allocs funs bounds (slots.map Slot.mode) live env))
      Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (e.depthCalls = false →
        heap'.top.toNat ≤ heap.top.toNat + e.allocs funs bounds (slots.map Slot.mode) live env) →
      wp m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wp m (e.code h slots base live ++ rest) Q store s host

/-- The allowance of a part of an expression from that of the whole: the part calls a function
whose code takes the call depth only when the whole does, may allocate only when the whole may,
and, when the whole takes no call depth, has room for its bound when the whole has room for its
own. -/
theorem _root_.Wasm.TrapOK.part {Q : Assertion Unit} {d d' a a' : Bool} {P P' : Prop}
    [Decidable P] [Decidable P'] (h : TrapOK (d || (a && !decide P)) Q)
    (hd : d' = true → d = true) (ha : a' = true → a = true) (hP : d = false → P → P') :
    TrapOK (d' || (a' && !decide P')) Q := by
  cases hdv : d
  · have hd' : d' = false := by cases d' <;> simp_all
    refine h.of_imp fun h' => ?_
    simp only [hd', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h'
    simp only [hdv, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨ha h'.1, fun hp => h'.2 (hP hdv hp)⟩
  · exact TrapOK.any (by simpa [hdv] using h)

/-- Closes a fact that a part's call-depth or allocation flag implies the whole's. -/
macro "flag_tac" : tactic =>
  `(tactic| (intro h; simp only [Expr.depthCalls, Expr.aborts, Bool.or_eq_true] at h ⊢; tauto))

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {bounds : Bounds S} {host : HostEnv Unit}
  {pv : List Value}

/-- `seq_spec` with the allocation bound: the two parts trap only as the whole's allowance
`d || (a && …)` allows for the sum of their bounds, and, when the whole takes no call depth,
`top` rises by at most that sum. -/
theorem seq_specB {Γ : List Ty} {t u : Ty} {l : Expr S Γ t} {r : Expr S Γ u}
    (lSpec : ∀ env slots live, CodeSpecB m funs bounds host pv l env slots live)
    (rSpec : ∀ env slots live, CodeSpecB m funs bounds host pv r env slots live)
    (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (h base : Nat) (heap : Heap)
    (store : Store Unit) (s : Locals) (hh : s.half = h) (hpv : s.params = pv)
    (hVars : Holds env slots (fun i => live i || (l.uses i || r.uses i)) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hBase : s.params.length ≤ base)
    (hRoomL : base + l.width ≤ h) (hRoomR : base + r.width ≤ h)
    (hPlaceL : l.placeArgs = true) (hPlaceR : r.placeArgs = true) (rest : Program)
    (Q : Assertion Unit) {d a : Bool}
    (hTrap : TrapOK (d || (a && !decide (heap.Within store m
      (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
        r.allocs funs bounds (slots.map Slot.mode) live env)))) Q)
    (hdl : l.depthCalls = true → d = true) (hdr : r.depthCalls = true → d = true)
    (hal : (l.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (har : (r.aborts || slots.any (·.mode == .owned)) = true → a = true)
    (hNext : ∀ heap2 store2 s2 ws1 ws2,
      Step heap store (Holds.KeepDying env slots (fun i => live i || (l.uses i || r.uses i)) live
          store s) heap2 store2
        ((l.mode (slots.map Slot.mode)).fresh store2 t ws1 (l.denote funs env) ++
          (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env)) →
      Frame base s s2 → Holds env slots live base heap2 store2 s2 →
      t.Rep (l.mode (slots.map Slot.mode)) heap2 store2 ws1 (l.denote funs env) →
      u.Rep (r.mode (slots.map Slot.mode)) heap2 store2 ws2 (r.denote funs env) →
      Holds.Apart env slots live store2 s2 t (l.mode (slots.map Slot.mode)) ws1
        (l.denote funs env) →
      Holds.Apart env slots live store2 s2 u (r.mode (slots.map Slot.mode)) ws2
        (r.denote funs env) →
      (∀ x ∈ t.regions (l.mode (slots.map Slot.mode)) store2 ws1 (l.denote funs env),
        ∀ y ∈ (r.mode (slots.map Slot.mode)).fresh store2 u ws2 (r.denote funs env),
          regionsDisjoint x y) →
      (d = false → heap2.top.toNat ≤ heap.top.toNat +
        (l.allocs funs bounds (slots.map Slot.mode) (fun i => live i || r.uses i) env +
          r.allocs funs bounds (slots.map Slot.mode) live env)) →
      wp m rest Q store2 { s2 with values := ws2.reverse ++ (ws1.reverse ++ s.values) } host) :
    wp m (l.code h slots base (fun i => live i || r.uses i) ++ (r.code h slots base live ++ rest))
      Q store s host := by
  have hIn : ∀ i, (live i || r.uses i || l.uses i) = true →
      (live i || (l.uses i || r.uses i)) = true := fun i h => live_seq _ _ _ h
  have hVarsL := hVars.live_mono hIn
  have hdl' : d = false → l.depthCalls = false := fun hd => by
    cases hl : l.depthCalls
    · rfl
    · rw [hdl hl] at hd; exact nomatch hd
  have hdr' : d = false → r.depthCalls = false := fun hd => by
    cases hr : r.depthCalls
    · rfl
    · rw [hdr hr] at hd; exact nomatch hd
  refine lSpec env slots _ h base heap store s hh hpv hVarsL hAt hCap hBase hRoomL hPlaceL _ _
      (hTrap.part hdl hal fun _ hw => hw.mono (Nat.le_add_right _ _))
    fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  refine rSpec env slots live h base heap1 store1 { s1 with values := ws1.reverse ++ s.values }
    (a1.frame.half.trans hh) (a1.frame.params.trans hpv) (a1.holds.agree Frame.ofValues)
    a1.step.at_
    (by rw [a1.step.cap m]; exact hCap)
    (by show s1.params.length ≤ base; rw [a1.frame.params]; exact hBase) hRoomR hPlaceR _ _
    (hTrap.part hdr har fun hd hw => hw.after (hTop1 (hdl' hd)) (a1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hTop2 => ?_
  obtain ⟨hStep, hFrame, hRep1, hApart1, hDisjoint⟩ :=
    After.seq hVarsL a1 a2 (fun i h => by simp [h]) fun i h => by simp [h]
  exact hNext heap2 store2 s2 ws1 ws2
    (hStep.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hIn i h1, h2⟩) fun _ hb => hb) hFrame
    a2.holds hRep1 a2.rep hApart1 a2.apart hDisjoint fun hd => by
      have := hTop1 (hdl' hd); have := hTop2 (hdr' hd); omega

/-- A constant word. -/
theorem specB_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.word (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)


/-- A constant `Bool`. -/
theorem specB_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.bool (S := S) (Γ := Γ) value) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote] using
    hNext0 store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)


/-- A float constant, from its bit pattern. -/
theorem specB_float {Γ : List Ty} (bits : UInt64) :
    ∀ env slots live,
      CodeSpecB m funs bounds host pv (Expr.float (S := S) (Γ := Γ) bits) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  have hNext0 := fun store' s' ws a =>
    hNext heap store' s' ws a (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote, F64Bits.toBits_ofBits] using
    hNext0 store s [.f64 (Float.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float rfl] at hb; exact nomatch hb)


/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem specB_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.bin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op
  case div | rem =>
    have hW2 : base + 2 ≤ h := by
      have := hRoom
      simp only [Expr.width, BinOp.scratch] at this
      omega
    have hp2 : s2.params = s.params := hF.params
    have hh2 : s2.half = h := hF.half.trans hh
    simp only [BinOp.code, List.cons_append, List.nil_append]
    refine wp_localSet_local (by rw [hp2]; omega)
      (Locals.lt_total (show base + 1 < ({ s2 with values := _ } : Locals).half by
        rw [Locals.half_values, hh2]; omega)) ?_
    refine wp_localSet_local (vs := s.values)
      (s := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
        (.i64 (right.denote funs env)))
      (by show s2.params.length ≤ base; rw [hp2]; omega)
      (Locals.lt_total (by simp only [Locals.half_setLocal, Locals.half_values]; omega)) ?_
    let s2a := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
      (.i64 (right.denote funs env))
    let s2b := setLocal { s2a with values := s.values } base (.i64 (left.denote funs env))
    show wp m _ Q store2 s2b host
    have hLowA : ({ s2 with values := .i64 (left.denote funs env) :: s.values } :
        Locals).params.length ≤ base + 1 := by
      show s2.params.length ≤ base + 1; rw [hp2]; omega
    have hLowB : ({ s2a with values := s.values } : Locals).params.length ≤ base := by
      show s2.params.length ≤ base; rw [hp2]; omega
    have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) := by
      rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]
      exact Locals.get_setLocal_same hLowA
        (Locals.lt_total (by simp only [Locals.half_values]; omega))
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) :=
      Locals.get_setLocal_same hLowB
        (Locals.lt_total (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hF2 : Frame base s2 s2b :=
      (Frame.setValues (s := s2) (vs := .i64 (left.denote funs env) :: s.values)
        (v := .i64 (right.denote funs env)) (by rw [hp2]; omega) (by omega) (by omega)).trans
        (Frame.setValues (s := s2a) (vs := s.values) (v := .i64 (left.denote funs env))
          (by show s2.params.length ≤ base; rw [hp2]; omega) le_rfl
          (by simp only [s2a, Locals.half_setLocal, Locals.half_values]; omega))
    have hFrame : Frame base s s2b := hF.trans hF2
    have hHolds : Holds env slots live base heap2 store2 s2b := hH.agree hF2
    have hs2b : s2b.values = s.values := rfl
    simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
    rw [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 store2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl)
  all_goals
    simpa [BinOp.code, Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using
      hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A comparison of words. -/
theorem specB_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.cmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op <;>
    simp only [CmpOp.instr, wp_eqI64_cons, wp_neI64_cons, wp_ltUI64_cons, wp_leUI64_cons,
      wp_extendUI32_cons]
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env < right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env ≤ right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv


/-- An operation on floats. -/
theorem specB_fbin {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fbin op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 [.f64 ((Expr.fbin op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr, Expr.denote, FBinOp.apply, f64Add, f64Sub, f64Mul, f64Div,
      F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div] using hv


/-- A comparison of floats. -/
theorem specB_fcmp {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.fcmp op left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr, wp_f64Lt_cons, wp_f64Le_cons, wp_f64Eq_cons, wp_extendUI32_cons]
  · cases hc : IEEE64.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_lt, f64Lt, boolWord] using hv
  · cases hc : IEEE64.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_le, f64Le, boolWord] using hv
  · cases hc : IEEE64.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.beq_eq, f64Eq, boolWord] using hv


/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem specB_funary {Γ : List Ty} (op : FUnOp) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.funary op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code]
  cases op with
  | neg =>
    simp only [FUnOp.code, List.cons_append, List.append_assoc, wp_f64Const_cons]
    refine eSpec env slots live h base heap store { s with values := .f64 0x8000000000000000 ::
      s.values } hh hpv (hVars.agree Frame.ofValues) hAt hCap hBase hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, FUnOp.apply, f64Sub, F64Bits.toBits_neg] using hv
  | sqrt | abs =>
    simp only [FUnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
        hTrap
      fun heap1 store1 s1 ws a1 hTop => ?_
    have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 store1 s1 [.f64 ((Expr.funary _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, FUnOp.apply, f64Sqrt, f64Abs, F64Bits.toBits_sqrt, F64Bits.toBits_abs]
      using hv


/-- A conversion of a word to a float. -/
theorem specB_toFloat {Γ : List Ty} (op : ToFloat) {e : Expr S Γ .word}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toFloat op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.f64 ((Expr.toFloat op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat.code, Expr.denote, ToFloat.apply, f64ConvertI64U, f64Add,
      F64Convert.toBits_toFloat, F64Bits.toBits_ofBits, add_negZero] using hv


/-- A conversion of a float to a word. -/
theorem specB_toWord {Γ : List Ty} (op : ToWord) {e : Expr S Γ .float}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.toWord op e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 store1 s1 [.i64 ((Expr.toWord op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord.instr, Expr.denote, ToWord.apply, i64TruncSatF64U, F64Convert.toUInt64_eq]
      using hv


/-- The negation of a `Bool`. -/
theorem specB_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots live, CodeSpecB m funs bounds host pv e env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.not e) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace _ _
      hTrap
    fun heap1 store1 s1 ws a1 hTop => ?_
  have hNext1 := fun store' s' ws a => hNext heap1 store' s' ws a hTop
  have hR := a1.rep
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  simpa [Expr.denote] using
    hNext1 store1 s1 _ (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)


/-- The conjunction of `Bool`s. -/
theorem specB_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.and left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- The disjunction of `Bool`s. -/
theorem specB_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots live, CodeSpecB m funs bounds host pv left env slots live)
    (rightSpec : ∀ env slots live, CodeSpecB m funs bounds host pv right env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.or left right) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB leftSpec rightSpec env slots live h base heap store s hh hpv hVars hAt hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wp_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext2 store2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)


/-- A tuple of two elements: the code of each, in order. -/
theorem specB_mk {Γ : List Ty} {a b : Elem} {first : Expr S Γ (.elem a)}
    {second : Expr S Γ (.elem b)}
    (firstSpec : ∀ env slots live, CodeSpecB m funs bounds host pv first env slots live)
    (secondSpec : ∀ env slots live, CodeSpecB m funs bounds host pv second env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.mk first second) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hR : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, List.append_assoc]
  refine seq_specB firstSpec secondSpec env slots live h base heap store s hh hpv hVars hAt hCap
      hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop => ?_
  have hNext2 := fun store' s' ws a => hNext heap2 store' s' ws a hTop
  have hR1' : ws1 = a.values (first.denote funs env) := hR1
  have hR2' : ws2 = b.values (second.denote funs env) := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 store2 s2
    (a.values (first.denote funs env) ++ b.values (second.denote funs env))
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simpa [List.reverse_append, List.append_assoc] using hv


/-- A variable: read in place when borrowed, moved where it dies, and copied where it stays
live. -/
theorem specB_var (hm : Runtime m) {Γ' : List Ty} {tTy : Ty} (x : Var Γ' tTy) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.var (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom _ rest Q hTrap hNext
  have hx : (fun i => live i || (Expr.var (S := S) x).uses i) x.index = true := by
    simp [Expr.uses]
  obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x hx
  have hl := hRep.length
  have hMode : (Expr.var (S := S) x).mode (slots.map Slot.mode) =
      (slots.getD x.index default).mode := Slot.modes_getD slots x.index
  have hLiveIn : ∀ i, live i = true → (live i || (Expr.var (S := S) x).uses i) = true :=
    fun i h => by simp [h]
  by_cases hCopy : (slots.getD x.index default).mode = .owned ∧ live x.index = true
  · -- A copy into new blocks.
    obtain ⟨hOwned, hLiveX⟩ := hCopy
    simp only [Expr.code, Var.code, hOwned, hLiveX, and_self, ↓reduceIte]
    have hc : (Expr.var (S := S) x).allocs funs bounds (slots.map Slot.mode) live env =
        tTy.copyCost (env.get x) := by
      simp only [Expr.allocs, Var.cost, modeAt, Slot.modes_getD, hOwned, hLiveX, and_self,
        ↓reduceIte]
    have hT : TrapOK (false || (true && !decide (heap.Within store m (tTy.copyCost (env.get x)))))
        Q := hTrap.part nofun (fun _ => by simp [Slot.any_owned hOwned])
      fun _ hw => by rwa [hc] at hw
    refine wp_copyCode hm tTy hAt hCap hT hh hRep hold hBelow hBase
      (by rw [hh]; simpa [Expr.width] using hRoom) fun heap' store' s' ws' hStep hRep' hF hTop => ?_
    have hHolds := (hVars.live_mono hLiveIn).step hStep (fun _ _ _ _ _ _ _ _ => trivial)
    refine hNext heap' store' s' ws' ⟨?_, hF, hHolds.frame hF le_rfl, ?_, ?_⟩
      (fun _ => by rw [hc]; exact hTop)
    · rw [hMode, hOwned]
      exact hStep.mono (fun _ _ => trivial) fun _ h => h
    · rw [hMode, hOwned]; exact hRep'
    · rw [hMode, hOwned]
      intro u y hy _ wy hwy hly b hb c hc
      have hwy' := ((hVars.live_mono hLiveIn).hold_agree hF hy hly).mp
        hwy
      obtain ⟨hSame, hFresh⟩ := (hVars.live_mono hLiveIn).regions_after hStep hy hwy' hly
        fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b hb)
  · simp only [Expr.code, Var.code, hCopy, ↓reduceIte]
    by_cases hOwned : (slots.getD x.index default).mode = .owned
    · -- A move: the variable dies here, and the value owns its blocks.
      have hDead : live x.index = false := by
        cases h : live x.index
        · rfl
        · exact absurd ⟨hOwned, h⟩ hCopy
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws ⟨?_, Frame.refl base s,
        hVars.live_mono hLiveIn, ?_, ?_⟩ fun _ => Nat.le_add_right _ _)
      · rw [hMode, hOwned]
        exact ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr,
          fun b hb => hk tTy x hx hDead hOwned ws hold hl b hb⟩⟩
      · rw [hMode]; exact hRep
      · rw [hMode, hOwned]
        intro u y hy _ wy hwy hly b hb c hc
        have hne : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 tTy u x y hx (hLiveIn _ hy) hne hOwned ws wy hold hl hwy hly b hb c hc
    · -- A view of a borrowed variable.
      have hBorrowed : (slots.getD x.index default).mode = .borrowed := by
        cases h : (slots.getD x.index default).mode
        · rfl
        · exact absurd h hOwned
      refine wp_loadCode ws hRep.typed hh hold (hNext heap store s ws (After.refl hAt hVars hLiveIn
        (by rw [hMode]; exact hRep) (by rw [hMode, hBorrowed]; rfl) ?_)
        fun _ => Nat.le_add_right _ _)
      rw [hMode]
      intro u y hy hm wy hwy hly b hb c hc
      rcases hm with hm | hm
      · exact absurd hm hOwned
      · have hne : y.index ≠ x.index := fun he => by
          rw [he] at hm; exact hOwned hm
        rw [hm] at hc
        exact regionsDisjoint_symm
          (hVars.2 u tTy y x (hLiveIn _ hy) hx hne hm wy ws hwy hly hold hl c hc b hb)


/-- The release of an array variable that a reader reads, when it is owned and dies there,
which leaves `top`. -/
theorem read_releaseT (hm : Runtime m) {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {live : Nat → Bool} {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    {vals : List Value} {rest : Program} {Q : Assertion Unit} {e : Elem} (x : Var Γ (.array e))
    (hVars : Holds env slots (fun k => live k || k == x.index) base heap store s)
    (hAt : heap.At store)
    (hNext : ∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → heap'.top = heap.top →
      wp m rest Q store' { s with values := vals } host) :
    wp m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode (.array e) (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host := by
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode (.array e) (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  refine wp_releaseVarsT hm _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (by split <;> simp) fun heap' store' e hTop => hNext heap' store' ?_ hTop
  have e' := e.mono (live' := live) fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  exact ⟨e'.step, ⟨e'.frame.params, e'.frame.length, e'.frame.below⟩,
    e'.holds.agree Frame.ofValues⟩

/-- The size of an array variable: the load of its length word, then the release of the variable
when it is owned and dies there. -/
theorem specB_size (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.size (S := S) x) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word hold
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, hPtr, wp_wrapI64_cons, wp_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode e.width_pos,
    words_div e.width_pos hnk]
  refine read_releaseT hm x hVars hAt fun heap' store' ev hTop => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl) fun _ => by rw [hTop]; omega

/-- A read of an array variable: the position in local `base`, a comparison of it with the
array's size as a flag in local `base + 1`, the position of the element's first word in local
`base`, the loads of its words under the flag, and the release of the variable when it is owned and
dies there. -/
theorem specB_get (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e))
    {i : Expr S Γ' .word}
    (iSpec : ∀ env slots live, CodeSpecB m funs bounds host pv i env slots live) :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.get x i) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt hCap hBase hRoom hPlace rest Q hTrap
    hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hi : i.width ≤ max i.width 2 := Nat.le_max_left ..
  have h2 : 2 ≤ max i.width 2 := Nat.le_max_right ..
  simp only [Expr.placeArgs] at hPlace
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  have hIn : ∀ k, ((live k || k == x.index) || i.uses k) = true →
      (live k || (Expr.get x i).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact live_assoc _ _ _ h
  refine iSpec env slots (fun k => live k || k == x.index) h base heap store s hh hpv
    (hVars.live_mono hIn) hAt hCap hBase (by omega) hPlace _ _
    hTrap fun heap1 store1 s1 ws1 a1 hTop1 => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.half = h := e1.frame.half.trans hh
  obtain ⟨hBelowX, wx, holdx, hRepx⟩ := e1.holds.1 _ x (by simp)
  obtain ⟨ptr, rfl, hBx⟩ := hRepx
  have hA := hBx.borrow.values
  have hLength := hA.lengthBound
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  have hk := e.width_pos
  have hn64 : (env.get x).size < UInt64.size := by
    have := Nat.le_mul_of_pos_right (env.get x).size hk
    rw [show UInt64.size = 18446744073709551616 from rfl]; omega
  simp only [Ty.width] at hBelowX
  have hPtr1 : s1.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word holdx
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  -- The position, in local `base`.
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHigh1 : base < s1.half := by rw [hh1]; omega
  refine wp_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  let s1a := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
  have hK : s1a.get base = some (.i64 (i.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hP : s1a.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLow1 (by omega)]
    exact hPtr1
  show wp m _ Q store1 s1a host
  simp only [wp_localGet_cons, Locals.get_values, hK, hP, wp_wrapI64_cons, wp_load64_cons,
    wrap_toUInt32, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wp_divCode hk,
    words_div hk hnk]
  simp only [wp_ltUI64_cons, wp_extendUI32_cons]
  -- The flag, in local `base + 1`.
  have hLess : i.denote funs env < UInt64.ofNat (env.get x).size ↔
      (i.denote funs env).toNat < (env.get x).size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn64]
  set b := decide ((i.denote funs env).toNat < (env.get x).size) with hb
  have hFlag : UInt64.ofNat (if i.denote funs env < UInt64.ofNat (env.get x).size then (1 : UInt32)
      else 0).toNat = boolWord b := by
    by_cases hc : (i.denote funs env).toNat < (env.get x).size
    · simp [hb, hc, hLess.mpr hc, boolWord]
    · simp [hb, hc, (not_congr hLess).mpr hc, boolWord]
  rw [hFlag]
  have hLowB : ({ s1a with values := s.values } : Locals).params.length ≤ base + 1 := by
    show s1.params.length ≤ base + 1; rw [hp1]; omega
  have hHighB : base + 1 < ({ s1a with values := s.values } : Locals).half := by
    simp only [s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowB (Locals.lt_total hHighB) ?_
  let s1b := setLocal { s1a with values := s.values } (base + 1) (.i64 (boolWord b))
  have hFb : s1b.get (base + 1) = some (.i64 (boolWord b)) :=
    Locals.get_setLocal_same hLowB (Locals.lt_total hHighB)
  have hKb : s1b.get base = some (.i64 (i.denote funs env)) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hK
  have hPb : s1b.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]; exact hP
  -- The position of the element's first word, in local `base`.
  show wp m _ Q store1 s1b host
  simp only [wp_localGet_cons, hKb]
  rw [wp_scaleCode]
  have hLowC : ({ s1b with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base; rw [hp1]; omega
  have hHighC : base < ({ s1b with values := s.values } : Locals).half := by
    simp only [s1b, s1a, Locals.half_setLocal, Locals.half_values, hh1]; omega
  refine wp_localSet_local hLowC (Locals.lt_total hHighC) ?_
  let s1c := setLocal { s1b with values := s.values } base
    (.i64 (i.denote funs env * wordCount e.width))
  have hWc : s1c.get base = some (.i64 (i.denote funs env * wordCount e.width)) :=
    Locals.get_setLocal_same hLowC (Locals.lt_total hHighC)
  have hFc : s1c.get (base + 1) = some (.i64 (boolWord b)) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hFb
  have hPc : s1c.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    rw [Locals.get_setLocal_ne hLowC (by omega), Locals.get_values]; exact hPb
  have f1 : Frame base s1 s1c :=
    ((Frame.setValues (s := s1) (vs := s.values) hLow1 le_rfl hHigh1).trans
      (Frame.setValues (s := s1a) (vs := s.values) hLowB (by omega)
        (by simpa [s1a, Locals.half_setLocal, Locals.half_values] using hHighB))).trans
      (Frame.setValues (s := s1b) (vs := s.values) hLowC le_rfl
        (by simpa [s1b, s1a, Locals.half_setLocal, Locals.half_values] using hHighC))
  have hFrame : Frame base s s1c := e1.frame.trans f1
  have hVars1 : Holds env slots (fun k => live k || k == x.index) base heap1 store1 s1c :=
    e1.holds.agree f1
  have hsc : s1c.values = s.values := rfl
  -- The words of the element, or zeros past the end.
  show wp m _ Q store1 s1c host
  refine wp_loadWordsCode (ws := e.words (env.get x)) b (fun _ => hA) 0 e.types s1c
    (e.toWords (env.get x)[(i.denote funs env).toNat]!) hPc hWc hFc
    (by rw [e.toWords_length, e.types_length]) (fun hbt => ?_) (fun hbf => ?_) ?_
  · have hc : (i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbt
    have hw : (i.denote funs env * wordCount e.width).toNat =
        (i.denote funs env).toNat * e.width := by
      have hs := words_scale (i := (i.denote funs env).toNat) hk
        (lt_of_le_of_lt (Nat.mul_le_mul_right e.width (Nat.le_of_lt hc)) hnk)
      rw [UInt64.ofNat_toNat] at hs
      rw [hs, UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]
          have := Nat.mul_le_mul_right e.width (Nat.le_of_lt hc); omega)]
    rw [hw, e.types_length, Elem.words_size]
    refine ⟨by
        have := Nat.mul_le_mul_right e.width (Nat.succ_le_of_lt hc)
        rw [Nat.succ_mul] at this; omega,
      fun j hj => ?_⟩
    rw [e.toWords_length] at hj
    rw [Nat.add_zero, Elem.words_getElem! e _ hc hj, getElem!_pos (env.get x) _ hc]
  · have hc : ¬(i.denote funs env).toNat < (env.get x).size := by simpa [hb] using hbf
    rw [getElem!_neg (env.get x) _ hc, e.toWords_default, e.types_length]
  · rw [e.values_typed, hsc]
    refine read_releaseT hm x hVars1 e1.step.at_ fun heap2 store2 e2 hTop2 => ?_
    have e12 := Evolves.trans (hVars.live_mono hIn) ⟨e1.step, hFrame, hVars1⟩ e2
      (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap2 store2 s1c (e.values (env.get x)[(i.denote funs env).toNat]!)
      ((After.ofScalar (t := .elem e) (mode := .borrowed) rfl e12.step rfl e12.frame e12.holds
        rfl).liveIn hIn) fun hd => by rw [hTop2]; exact hTop1 hd

/-- A component of a tuple variable: the loads of the words that hold it. -/
theorem specB_proj {Γ' : List Ty} {e e' : Elem} (x : Var Γ' (.elem e)) (p : Path e e') :
    ∀ env slots live, CodeSpecB m funs bounds host pv (Expr.proj (S := S) x p) env slots live := by
  intro env slots live h base heap store s hh hpv hVars hAt _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  have hRep' : ws = e.values (env.get x) := hRep
  subst hRep'
  simp only [Expr.code]
  exact wp_loadCode _ (by rw [e'.values_length, e'.types_length]) hh (p.holds hold)
    (hNext heap store s _ (After.refl hAt hVars (by intro i h; simp [Expr.uses, h]) rfl rfl
      (Holds.Apart.ofScalar rfl)) fun _ => Nat.le_add_right _ _)

end Cases

end Verified
