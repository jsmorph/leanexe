import LeanExe.Native.Proof.Control

/-!
The simulation of `block`, `loop`, and `iff`.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Facts about the C loop of a construct -/

section loops

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem exec_skip_inv {le le' : temp_env} {m m' : mem} {t : trace} {out : outcome}
    (h : exec_stmt A X ge empty_env le m .Sskip t le' m' out) :
    le' = le ∧ m' = m ∧ t = E0 ∧ out = .Out_normal := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

/-- The body followed by `break`, when the body completes normally or breaks. -/
theorem exec_seq_break {s0 : statement} {le le' : temp_env} {m m' : mem} {t : trace}
    {out : outcome} (h : exec_stmt A X ge empty_env le m s0 t le' m' out)
    (hout : out = .Out_normal ∨ out = .Out_break) :
    ∃ t', exec_stmt A X ge empty_env le m (seq s0 .Sbreak) t' le' m' .Out_break := by
  cases s0 with
  | Sskip =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := exec_skip_inv h
      exact ⟨E0, .exec_Sbreak _ _ _⟩
  | _ =>
      rcases hout with rfl | rfl
      · exact ⟨_, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h (.exec_Sbreak _ _ _)⟩
      · exact ⟨_, .exec_Sseq_2 _ _ _ _ _ _ _ _ _ h (by simp)⟩

/-- The body followed by `break`, when the body continues or returns. -/
theorem exec_seq_abrupt {s0 : statement} {le le' : temp_env} {m m' : mem} {t : trace}
    {out : outcome} (h : exec_stmt A X ge empty_env le m s0 t le' m' out)
    (hout : out ≠ .Out_normal) :
    exec_stmt A X ge empty_env le m (seq s0 .Sbreak) t le' m' out := by
  cases s0 with
  | Sskip => exact absurd (exec_skip_inv h).2.2.2 hout
  | _ => exact .exec_Sseq_2 _ _ _ _ _ _ _ _ _ h hout

theorem exec_wrap_prefix {s : statement} {le le' : temp_env} {m m' : mem} {t : trace}
    {out : outcome} (h : exec_stmt A X ge empty_env le m s t le' m' out) :
    exec_stmt A X ge empty_env le m (.Ssequence .Sskip s) (E0 ++ t) le' m' out :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sskip _ _ _) h

/-- The construct's loop ends normally when its body completes normally or breaks. -/
theorem exec_wrap_exit {s0 : statement} {le le' : temp_env} {m m' : mem} {t : trace}
    {out : outcome} (h : exec_stmt A X ge empty_env le m s0 t le' m' out)
    (hout : out = .Out_normal ∨ out = .Out_break) :
    ∃ t', exec_stmt A X ge empty_env le m (wrapLoop s0) t' le' m' .Out_normal := by
  obtain ⟨t', h'⟩ := exec_seq_break h hout
  exact ⟨_, .exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _ (exec_wrap_prefix h') .Out_break_or_return_B⟩

/-- The construct's loop returns when its body returns. -/
theorem exec_wrap_return {s0 : statement} {le le' : temp_env} {m m' : mem} {t : trace}
    {r : Option (val × type)} (h : exec_stmt A X ge empty_env le m s0 t le' m' (.Out_return r)) :
    exec_stmt A X ge empty_env le m (wrapLoop s0) (E0 ++ t) le' m' (.Out_return r) :=
  .exec_Sloop_stop1 _ _ _ _ _ _ _ _ _ _
    (exec_wrap_prefix (exec_seq_abrupt h (by simp))) (.Out_break_or_return_R r)

/-- The construct's loop runs again when its body continues. -/
theorem exec_wrap_continue {s0 : statement} {le le1 le2 : temp_env} {m m1 m2 : mem}
    {t1 t2 : trace} {out : outcome}
    (h1 : exec_stmt A X ge empty_env le m s0 t1 le1 m1 .Out_continue)
    (h2 : exec_stmt A X ge empty_env le1 m1 (wrapLoop s0) t2 le2 m2 out) :
    ∃ t, exec_stmt A X ge empty_env le m (wrapLoop s0) t le2 m2 out :=
  ⟨_, .exec_Sloop_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (exec_wrap_prefix (exec_seq_abrupt h1 (by simp))) .Out_normal_or_continue_C
    (.exec_Sskip _ _ _) h2⟩

end loops

/-! ## The outcome of a construct's loop -/

section

variable (A : Archi) (X : ExtSem) (E : Env) (c : FCtx)

/-- A branch `k + 1` levels out of a construct's body, which is `k` levels out of the
construct: `brk` is `k + 1` when the construct's loop ends. -/
structure PendingBreak (L : List Label) (k : Nat) {α : Type} (st : Store α) (sl : Locals)
    (le : temp_env) (m : mem) : Prop where
  target : ∃ l, L[k]? = some l ∧ l.final = false ∧
    (l.isLoop = false → ∀ t, l.result = some t →
      ∃ v, sl.values.head? = some v ∧ t.has v = true ∧ le[slotId l.base t]? = some (cval v))
  brk : le[brkId]? = some (.Vint (UInt32.ofNat (k + 1)))
  small : k + 1 < 2 ^ 31
  locals : LocalsRel le c.locals (sl.params ++ sl.locals)
  store : StoreRel E st m
  status : StatusRel E m 0

/-- What the construct's loop `W` does when Talos's result for the construct is `r`. -/
def ConstructOutcome (L : List Label) (σ' : List VT) {α : Type} (r : Continuation α)
    (W : statement) (le : temp_env) (m : mem) : Prop :=
  match r with
  | .Fallthrough st' sl' => curBase L ≤ σ'.length ∧ ∃ t le' m',
      exec_stmt A X E.ge empty_env le m W t le' m' .Out_normal ∧ Inv E c σ' st' sl' le' m' ∧
      Frame (curBase L) le le'
  | .Break k st' sl' => ∃ t le' m',
      exec_stmt A X E.ge empty_env le m W t le' m' .Out_normal ∧
      PendingBreak E c L k st' sl' le' m' ∧ ∀ l, L[k]? = some l → Frame l.base le le'
  | .Return st' vs => ∃ t le' m' out,
      exec_stmt A X E.ge empty_env le m W t le' m' out ∧ ReturnRel E c.results vs out m' ∧
      StoreRel E st' m' ∧ StatusRel E m' 0
  | .Trap st' msg => ∃ t le' m',
      exec_stmt A X E.ge empty_env le m W t le' m' (trapOut c.result) ∧
      StoreRel E st' m' ∧ StatusRel E m' (trapCode msg) ∧ trapCode msg ≠ 0
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

variable {A X E c}

theorem uint32_ofNat_eq_zero {k : Nat} (hk : k < 2 ^ 32) : UInt32.ofNat k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    simp only [UInt32.toNat_ofNat'] at this
    simp at this
    omega
  · rintro rfl; rfl

theorem eval_brk_ne {le : temp_env} {m : mem} {k : Nat}
    (h : le[brkId]? = some (.Vint (UInt32.ofNat k))) (hk : k < 2 ^ 32) :
    eval_expr A E.ge empty_env le m (.Ebinop .One (.Etempvar brkId tuint) (cint 0) tint)
      (.Vint (if k ≠ 0 then 1 else 0)) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h) (.eval_Econst_int _ _) ?_
  show sem_binary_operation A .One (.Vint (UInt32.ofNat k)) tuint (.Vint (UInt32.ofNat 0)) tuint m = _
  rw [sem_ne_ii]
  by_cases hk0 : k = 0
  · subst hk0; simp
  · have : UInt32.ofNat k ≠ 0 := fun e => hk0 ((uint32_ofNat_eq_zero hk).mp e)
    simp [this, hk0]

theorem eval_brk_eq {le : temp_env} {m : mem} {k : Nat}
    (h : le[brkId]? = some (.Vint (UInt32.ofNat k))) (hk : k < 2 ^ 32) :
    eval_expr A E.ge empty_env le m (.Ebinop .Oeq (.Etempvar brkId tuint) (cint 0) tint)
      (.Vint (if k = 0 then 1 else 0)) := by
  refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h) (.eval_Econst_int _ _) ?_
  show sem_binary_operation A .Oeq (.Vint (UInt32.ofNat k)) tuint (.Vint (UInt32.ofNat 0)) tuint m = _
  rw [sem_eq_ii]
  by_cases hk0 : k = 0
  · subst hk0; simp
  · have : UInt32.ofNat k ≠ 0 := fun e => hk0 ((uint32_ofNat_eq_zero hk).mp e)
    simp [this, hk0]

/-- The dispatch after a construct whose loop ended with `brk = 0` does nothing. -/
theorem exec_dispatch_zero {le : temp_env} {m : mem} (parent : Label)
    (h : le[brkId]? = some (.Vint 0)) :
    exec_stmt A X E.ge empty_env le m (dispatch parent) E0 le m .Out_normal := by
  have hc := eval_brk_ne (A := A) (E := E) (m := m) (k := 0) h (by decide)
  refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc ?_ (.exec_Sskip _ _ _)
  simp only [ne_eq, not_true_eq_false, ite_false]
  exact bool_int m 0

theorem ConstructOutcome.toOutcome {L : List Label} {σ' : List VT} {α : Type}
    {r : Continuation α} {W : statement} {le : temp_env} {m : mem} {parent : Label}
    (hp : L.head? = some parent) (h : ConstructOutcome A X E c L σ' r W le m) :
    Outcome A X E c L (some σ') r (.Ssequence W (dispatch parent)) le m := by
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨hb, t, le', m', hx, hinv, hf⟩ := h
      exact ⟨σ', rfl, hb, t ++ E0, le', m',
        .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx (exec_dispatch_zero parent hinv.brk), hinv, hf⟩
  | Break k st' sl' =>
      obtain ⟨t, le', m', hx, hpb, hf⟩ := h
      have hk1 : k + 1 < 2 ^ 32 := by have := hpb.small; omega
      have hc1 := eval_brk_ne (A := A) (E := E) (m := m') hpb.brk hk1
      have hsub : eval_expr A E.ge empty_env le' m'
          (.Ebinop .Osub (.Etempvar brkId tuint) (cint 1) tuint) (.Vint (UInt32.ofNat k)) := by
        refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hpb.brk) (.eval_Econst_int _ _) ?_
        show sem_binary_operation A .Osub (.Vint (UInt32.ofNat (k + 1))) tuint
          (.Vint (UInt32.ofNat 1)) tuint m' = _
        rw [sem_sub_ii, Int.sub_one_eq k (by omega)]
      let le2 := le'.insert brkId (.Vint (UInt32.ofNat k))
      have hb2 : le2[brkId]? = some (.Vint (UInt32.ofNat k)) := te_insert_same _ _ _
      have hc2 := eval_brk_eq (A := A) (E := E) (m := m') hb2 (by omega)
      have hframe : ∀ x t', le2[slotId x t']? = le'[slotId x t']? := fun x t' =>
        te_insert_ne _ (slotId_ne_brkId x t').symm
      obtain ⟨l, hl, hfin, hkept⟩ := hpb.target
      let out := if k = 0 then (if parent.isLoop then outcome.Out_continue else .Out_break)
        else .Out_break
      have hinner : exec_stmt A X E.ge empty_env le2 m'
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar brkId tuint) (cint 0) tint)
            (jump parent.isLoop) .Sbreak) E0 le2 m' out := by
        refine .exec_Sifthenelse _ _ _ _ _ _ _ (decide (k = 0)) _ _ _ _ hc2 ?_ ?_
        · by_cases hk0 : k = 0
          · subst hk0; simp; exact bool_int m' 1
          · simp [hk0]; exact bool_int m' 0
        · by_cases hk0 : k = 0
          · simp only [hk0, decide_true, ite_true, out]
            cases parent.isLoop
            · exact .exec_Sbreak _ _ _
            · exact .exec_Scontinue _ _ _
          · simp only [hk0, decide_false, ite_false, out]
            exact .exec_Sbreak _ _ _
      have hd : exec_stmt A X E.ge empty_env le' m' (dispatch parent) (E0 ++ E0) le2 m' out := by
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc1 ?_
          (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ hsub) hinner)
        simp only [ne_eq]
        have : UInt32.ofNat (k + 1) ≠ 0 := fun e => by
          have := (uint32_ofNat_eq_zero hk1).mp e; omega
        simp
        exact bool_int m' 1
      refine ⟨t ++ (E0 ++ E0), le2, m', out, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx hd, ?_,
        fun l' hl' => fun x hx' t' => by rw [hframe]; exact hf l' hl' x hx' t'⟩
      refine { target := ⟨l, hl, ?_, hfin, ?_⟩, outer := ?_, brk := hb2,
               small := by have := hpb.small; omega,
               locals := hpb.locals.insert_other _ (fun i => (localId_ne_brkId i).symm)
               store := hpb.store, status := hpb.status }
      · intro hk0
        subst hk0
        have : l = parent := by
          cases L with
          | nil => simp at hl
          | cons l0 L0 => simp at hl hp; rw [← hl, hp]
        subst this
        simp [out]
      · intro hloop t' hr
        obtain ⟨v, hv, ht, hs⟩ := hkept hloop t' hr
        exact ⟨v, hv, ht, by rw [hframe]; exact hs⟩
      · intro hk0; simp [out, hk0]
  | Return st' vs =>
      obtain ⟨t, le', m', out, hx, hrel, hg, hs⟩ := h
      exact ⟨t, le', m', out, .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hx (ReturnRel.ne_normal hrel), hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le', m', hx, hg, hs, hc⟩ := h
      exact ⟨t, le', m', .exec_Sseq_2 _ _ _ _ _ _ _ _ _ hx (trapOut_ne_normal _), hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

end

end LeanExe.Native
