import LeanExe.Native.Proof.Blocks
import LeanExe.Native.Proof.Results

/-!
The simulation of `br`, `br_if`, and `ret`.
-/

namespace LeanExe.Native

open Wasm LClight

/-- The jump of a branch `k` levels out to the target `l`. -/
def brGo (l : Label) (k : Nat) : statement :=
  if k = 0 then jump l.isLoop else .Ssequence (.Sset brkId (cint k)) .Sbreak

theorem brStmt_spec {L : List Label} {σ : List VT} {k : Nat} {s : statement}
    (h : brStmt L σ k = some s) :
    ∃ l, L[k]? = some l ∧ k < 2 ^ 31 ∧ l.final = false ∧
      ((∃ t σr, l.isLoop = false ∧ l.result = some t ∧ σ = t :: σr ∧
          s = .Ssequence (.Sset (slotId l.base t) (tmp σr.length t)) (brGo l k)) ∨
        ((l.isLoop = false → l.result = none) ∧ s = brGo l k)) := by
  simp [brStmt, Option.bind_eq_some_iff] at h
  obtain ⟨l, hl, ⟨hk, hfin⟩, h⟩ := h
  refine ⟨l, hl, hk, hfin, ?_⟩
  cases hloop : l.isLoop <;> cases hres : l.result <;> simp [hloop, hres] at h
  · exact .inr ⟨fun _ => rfl, by rw [← h]; simp only [brGo, hloop, seq]⟩
  · rename_i t
    cases σ with
    | nil => simp at h
    | cons t' σr =>
        simp at h
        obtain ⟨⟨rfl, -⟩, h⟩ := h
        exact .inl ⟨t', σr, rfl, rfl, rfl, by rw [← h]; simp only [brGo, hloop, seq]⟩
  · exact .inr ⟨fun h' => by simp at h', by rw [← h]; simp only [brGo, hloop, seq]⟩
  · exact .inr ⟨fun h' => by simp at h', by rw [← h]; simp only [brGo, hloop, seq]⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The jump of a branch from a state whose `brk` is 0. -/
theorem exec_brGo {le : temp_env} {m : mem} (l : Label) (k : Nat) :
    ∃ (le' : temp_env) (out : outcome), exec_stmt A X E.ge empty_env le m (brGo l k) E0 le' m out ∧
      (k = 0 → out = (if l.isLoop then outcome.Out_continue else outcome.Out_break) ∧ le' = le) ∧
      (k ≠ 0 → out = outcome.Out_break ∧ le' = le.insert brkId (.Vint (UInt32.ofNat k))) := by
  by_cases hk : k = 0
  · subst hk
    cases hl : l.isLoop
    · exact ⟨le, .Out_break, by simp [brGo, jump, hl]; exact .exec_Sbreak _ _ _,
        fun _ => by simp, fun h => absurd rfl h⟩
    · exact ⟨le, .Out_continue, by simp [brGo, jump, hl]; exact .exec_Scontinue _ _ _,
        fun _ => by simp, fun h => absurd rfl h⟩
  · refine ⟨le.insert brkId (.Vint (UInt32.ofNat k)), .Out_break, ?_, fun h => absurd h hk,
      fun _ => ⟨rfl, rfl⟩⟩
    simp only [brGo, hk, ite_false]
    exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _))
      (.exec_Sbreak _ _ _)

/-- A branch `k` levels out from a state related at `σ`. -/
theorem br_outcome {L : List Label} {σ : List VT} {k : Nat} {s : statement}
    (hs : brStmt L σ k = some s) {α : Type} {st : Store α} {sl : Locals} {le : temp_env}
    {m : mem} (hinv : Inv E c σ st sl le m) :
    ∃ t le' out, exec_stmt A X E.ge empty_env le m s t le' m out ∧
      BreakRel E c L k st sl le' m out ∧ ∀ l, L[k]? = some l → Frame l.base le le' := by
  obtain ⟨l, hl, hk, hfin, hcase⟩ := brStmt_spec hs
  have hbrk : ∀ (le1 : temp_env), le1[brkId]? = some (.Vint 0) →
      ∀ (le' : temp_env) (out : outcome),
      (k = 0 → out = (if l.isLoop then outcome.Out_continue else outcome.Out_break) ∧ le' = le1) →
      (k ≠ 0 → out = outcome.Out_break ∧ le' = le1.insert brkId (.Vint (UInt32.ofNat k))) →
      le'[brkId]? = some (.Vint (UInt32.ofNat k)) ∧ (∀ id, id ≠ brkId → le'[id]? = le1[id]?) := by
    intro le1 hb1 le' out h0 h1
    by_cases hk0 : k = 0
    · obtain ⟨-, rfl⟩ := h0 hk0
      subst hk0
      exact ⟨hb1, fun _ _ => rfl⟩
    · obtain ⟨-, rfl⟩ := h1 hk0
      exact ⟨te_insert_same _ _ _, fun id hid => te_insert_ne _ (Ne.symm hid)⟩
  rcases hcase with ⟨t, σr, hloop, hres, rfl, rfl⟩ | ⟨hnone, rfl⟩
  · obtain ⟨v, vr, hvs, ht, hslot, -⟩ := hinv.stack.cons_inv
    let le1 := le.insert (slotId l.base t) (cval v)
    have hb1 : le1[brkId]? = some (.Vint 0) := by
      rw [te_insert_ne _ (slotId_ne_brkId _ _)]; exact hinv.brk
    obtain ⟨le', out, hgo, h0, h1⟩ := exec_brGo (A := A) (X := X) (E := E) (le := le1) (m := m) l k
    obtain ⟨hb', hother⟩ := hbrk le1 hb1 le' out h0 h1
    refine ⟨E0 ++ E0, le', out,
      .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ hslot)) hgo,
      ?_, ?_⟩
    · refine { target := ⟨l, hl, ?_, hfin, ?_⟩, outer := ?_, brk := hb', small := hk,
               locals := ?_, store := hinv.store, status := hinv.status }
      · intro hk0; exact (h0 hk0).1
      · intro _ t' ht'
        rw [hres] at ht'; cases ht'
        refine ⟨v, by rw [hvs]; rfl, ht, ?_⟩
        rw [hother _ (slotId_ne_brkId _ _), te_insert_same]
      · intro hk0; exact (h1 hk0).1
      · refine ⟨hinv.locals.1, fun i hi => ?_⟩
        obtain ⟨w, hw, htw, hlw⟩ := hinv.locals.2 i hi
        refine ⟨w, hw, htw, ?_⟩
        rw [hother _ (localId_ne_brkId i), te_insert_ne _ (slotId_ne_localId _ _ i)]
        exact hlw
    · intro l' hl'
      rw [hl] at hl'; cases hl'
      intro x hx t'
      rw [hother _ (slotId_ne_brkId _ _), te_insert_ne _ (slotId_ne_of_height _ _ (by omega))]
  · obtain ⟨le', out, hgo, h0, h1⟩ := exec_brGo (A := A) (X := X) (E := E) (le := le) (m := m) l k
    obtain ⟨hb', hother⟩ := hbrk le hinv.brk le' out h0 h1
    refine ⟨E0, le', out, hgo, ?_, ?_⟩
    · refine { target := ⟨l, hl, ?_, hfin, ?_⟩, outer := ?_, brk := hb', small := hk,
               locals := ?_, store := hinv.store, status := hinv.status }
      · intro hk0; exact (h0 hk0).1
      · intro hloop t' ht'
        rw [hnone hloop] at ht'; cases ht'
      · intro hk0; exact (h1 hk0).1
      · refine ⟨hinv.locals.1, fun i hi => ?_⟩
        obtain ⟨w, hw, htw, hlw⟩ := hinv.locals.2 i hi
        exact ⟨w, hw, htw, by rw [hother _ (localId_ne_brkId i)]; exact hlw⟩
    · intro l' _ x _ t'
      rw [hother _ (slotId_ne_brkId _ _)]

theorem sim_br (F k : Nat) {CallOk : Nat → Prop} : InstrSimL A X E mod c CallOk F (.br k) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hinv
  cases hs0 : brStmt L σ k with
  | none => simp [trInstr, hs0] at htr
  | some s0 =>
  simp [trInstr, hs0] at htr
  obtain ⟨rfl, rfl, rfl⟩ := htr
  cases F with
  | zero => rw [execOne_zero]; trivial
  | succ f =>
      simp only [execOne.eq_def]
      obtain ⟨t, le', out, hx, hrel, hf⟩ := br_outcome hs0 hinv
      exact ⟨t, le', m, out, hx, hrel, hf⟩

theorem sim_br_if (F k : Nat) {CallOk : Nat → Prop} : InstrSimL A X E mod c CallOk F (.br_if k) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at htr
  obtain ⟨hb, rfl, s0, hs0, rfl, rfl, rfl⟩ := htr
  cases F with
  | zero => rw [execOne_zero]; trivial
  | succ f =>
      obtain ⟨x, vs, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
      have hinv' : Inv E c σr st { params := sl.params, locals := sl.locals, values := vs } le m :=
        { stack := hrest, locals := hinv.locals, store := hinv.store, status := hinv.status,
          brk := hinv.brk }
      have hc : eval_expr A E.ge empty_env le m (tmp σr.length .i32) (.Vint x) :=
        .eval_Etempvar _ _ _ hx
      by_cases hx0 : x = 0
      · subst hx0
        simp only [execOne.eq_def, hvs]
        refine ⟨σr, rfl, hb, E0, le, m, ?_, hinv', Frame.refl _ _⟩
        exact .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc
          (by show bool_val _ tuint m = _; simpa using bool_uint m 0) (.exec_Sskip _ _ _)
      · have heq : execOne (f + 1) mod st sl (.br_if k) env =
            .Break k st { params := sl.params, locals := sl.locals, values := vs } := by
          simp only [execOne.eq_def, hvs]
        rw [heq]
        obtain ⟨t, le', out, hx', hrel, hf⟩ := br_outcome hs0 hinv'
        exact ⟨t, le', m, out,
          .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc
            (by show bool_val _ tuint m = _; simpa [hx0] using bool_uint m x) hx',
          hrel, hf⟩

theorem sim_ret (hE : EnvOk E) (hres : ResOk E c.results) (F : Nat) {CallOk : Nat → Prop} :
    InstrSimL A X E mod c CallOk F .ret := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hinv
  cases F with
  | zero => rw [execOne_zero]; trivial
  | succ f =>
      simp only [execOne.eq_def]
      rcases hrs : c.results with _ | ⟨t, _ | ⟨t2, rs⟩⟩
      · simp [trInstr, hrs] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        refine ⟨E0, le, m, .Out_return none, .exec_Sreturn_none _ _ _, ?_, hinv.store,
          hinv.status⟩
        rw [hrs]; rfl
      · simp [trInstr, hrs] at htr
        obtain ⟨⟨hh, -⟩, rfl, rfl, rfl⟩ := htr
        cases σ with
        | nil => simp at hh
        | cons t' σr =>
            simp at hh; subst hh
            obtain ⟨v, vr, hvs, ht, hslot, -⟩ := hinv.stack.cons_inv
            refine ⟨E0, le, m, .Out_return (some (cval v, t'.ty)), ?_, ?_, hinv.store,
              hinv.status⟩
            · have := exec_stmt.exec_Sreturn_some (A := A) (X := X) (ge := E.ge) empty_env le m
                (tmp σr.length t') (cval v) (.eval_Etempvar _ _ _ hslot)
              simpa [tmp, typeof] using this
            · rw [hrs]
              exact ⟨v, by rw [hvs]; rfl, ht, rfl⟩
      · have hlen := (hres (by rw [hrs]; simp)).1
        have hint := (hres (by rw [hrs]; simp)).2
        rw [hrs] at hlen hint
        simp only [trInstr, hrs] at htr
        split at htr
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl, rfl⟩ := htr
          obtain ⟨htake, hb⟩ := hcond
          have hσ : σ = (t :: t2 :: rs).reverse ++ σ.drop (t :: t2 :: rs).length := by
            rw [← htake, List.take_append_drop]
          generalize hσr : σ.drop (t :: t2 :: rs).length = σr at hσ
          subst hσ
          obtain ⟨vtop, vr, hvs, hvlen, -, hargs⟩ := stack_args (t :: t2 :: rs) hinv.stack
          have hh : ((t :: t2 :: rs).reverse ++ σr).length - (t :: t2 :: rs).length = σr.length := by
            simp; omega
          rw [hh]
          obtain ⟨m', hx, hst', hs', hload, -⟩ := exec_resStores (A := A) (X := X) hE
            (t :: t2 :: rs) 0 σr.length vtop.reverse m (by simpa using hlen) hint hargs
            hinv.store hinv.status
          refine ⟨E0, le, m', .Out_return none, hx, ?_, hst', hs'⟩
          rw [hrs]
          refine ⟨rfl, by rw [hvs]; simp [hvlen], fun j hj => ?_⟩
          obtain ⟨v, hv, htv, hl⟩ := hload j hj
          refine ⟨v, ?_, htv, by simpa using hl⟩
          rw [hvs, List.take_left' hvlen]
          exact hv
        · cases htr

end

end LeanExe.Native
