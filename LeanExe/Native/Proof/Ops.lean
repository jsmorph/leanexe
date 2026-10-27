import LeanExe.Native.Proof.Straight

/-!
The simulation of the globals, the constants, the integer operations, and `unreachable`.
-/

namespace LeanExe.Native

open Wasm LClight

theorem pop2_i64 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.i64 :: .i64 :: σr) vs) :
    ∃ y x vr, vs = .i64 y :: .i64 x :: vr ∧ le[slotId (σr.length + 1) .i64]? = some (.Vlong y) ∧
      le[slotId σr.length .i64]? = some (.Vlong x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vs1, rfl, h1, hl1, h'⟩ := h.cons_inv
  obtain ⟨v2, vr, rfl, h2, hl2, hrest⟩ := h'.cons_inv
  obtain ⟨y, rfl⟩ := has_i64 h1
  obtain ⟨x, rfl⟩ := has_i64 h2
  exact ⟨y, x, vr, rfl, hl1, hl2, hrest⟩

theorem pop2_i32 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.i32 :: .i32 :: σr) vs) :
    ∃ y x vr, vs = .i32 y :: .i32 x :: vr ∧ le[slotId (σr.length + 1) .i32]? = some (.Vint y) ∧
      le[slotId σr.length .i32]? = some (.Vint x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vs1, rfl, h1, hl1, h'⟩ := h.cons_inv
  obtain ⟨v2, vr, rfl, h2, hl2, hrest⟩ := h'.cons_inv
  obtain ⟨y, rfl⟩ := has_i32 h1
  obtain ⟨x, rfl⟩ := has_i32 h2
  exact ⟨y, x, vr, rfl, hl1, hl2, hrest⟩

theorem pop1_i64 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.i64 :: σr) vs) :
    ∃ x vr, vs = .i64 x :: vr ∧ le[slotId σr.length .i64]? = some (.Vlong x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vr, rfl, h1, hl1, hrest⟩ := h.cons_inv
  obtain ⟨x, rfl⟩ := has_i64 h1
  exact ⟨x, vr, rfl, hl1, hrest⟩

theorem pop1_i32 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.i32 :: σr) vs) :
    ∃ x vr, vs = .i32 x :: vr ∧ le[slotId σr.length .i32]? = some (.Vint x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vr, rfl, h1, hl1, hrest⟩ := h.cons_inv
  obtain ⟨x, rfl⟩ := has_i32 h1
  exact ⟨x, vr, rfl, hl1, hrest⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem eval_ll {le : temp_env} {m : mem} {h h' : Nat} {x y : UInt64} {op : binary_operation}
    {ty : type} {v : val} (hx : le[slotId h .i64]? = some (.Vlong x))
    (hy : le[slotId h' .i64]? = some (.Vlong y))
    (hs : sem_binary_operation A op (.Vlong x) tulong (.Vlong y) tulong m = some v) :
    eval_expr A E.ge empty_env le m (.Ebinop op (tmp h .i64) (tmp h' .i64) ty) v :=
  .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (.eval_Etempvar _ _ _ hy) hs

/-- An `i64` binary operation that cannot trap. -/
theorem sim_ll (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt64 → UInt64 → UInt64)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .i64 :: .i64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.i64 :: σr) ∧
        s = .Sset (slotId σr.length .i64)
          (.Ebinop op (tmp σr.length .i64) (tmp (σr.length + 1) .i64) tulong))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .i64 y :: .i64 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st { params := sl.params, locals := sl.locals, values := .i64 (f x y) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, sem_binary_operation A op (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vlong (f x y))) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (eval_ll hx hy (hsem m x y)) rfl hb

theorem sim_addI64 (F : Nat) : InstrSim A X E mod c F .addI64 :=
  sim_ll F .addI64 .Oadd (· + ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_add_ll A)

theorem sim_subI64 (F : Nat) : InstrSim A X E mod c F .subI64 :=
  sim_ll F .subI64 .Osub (· - ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_sub_ll A)

theorem sim_mulI64 (F : Nat) : InstrSim A X E mod c F .mulI64 :=
  sim_ll F .mulI64 .Omul (· * ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_mul_ll A)

theorem sim_andI64 (F : Nat) : InstrSim A X E mod c F .andI64 :=
  sim_ll F .andI64 .Oand (· &&& ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_and_ll A)

theorem sim_orI64 (F : Nat) : InstrSim A X E mod c F .orI64 :=
  sim_ll F .orI64 .Oor (· ||| ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_or_ll A)

theorem sim_xorI64 (F : Nat) : InstrSim A X E mod c F .xorI64 :=
  sim_ll F .xorI64 .Oxor (· ^^^ ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
        simp [trInstr, i64Op, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_xor_ll A)

theorem trapCode_unreachable : trapCode "unreachable" = trapUnreachable := by decide
theorem trapCode_divZero : trapCode "integer divide by zero" = trapDivZero := by decide

/-- Running `s1`, which changes nothing, before `s2`. -/
theorem Outcome.prefix {L : List Label} {σ' : Option (List VT)} {α : Type} {r : Continuation α}
    {s1 s2 : statement} {le : temp_env} {m : mem}
    (h1 : exec_stmt A X E.ge empty_env le m s1 E0 le m .Out_normal)
    (h : Outcome A X E c L σ' r s2 le m) : Outcome A X E c L σ' r (.Ssequence s1 s2) le m := by
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ'', h', hb, t, le', m', hx, hinv, hf⟩ := h
      exact ⟨σ'', h', hb, E0 ++ t, le', m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hinv, hf⟩
  | Break k st' sl' =>
      obtain ⟨t, le', m', out, hx, hrel, hf⟩ := h
      exact ⟨E0 ++ t, le', m', out, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hrel, hf⟩
  | Return st' vs =>
      obtain ⟨t, le', m', out, hx, hrel, hg, hs⟩ := h
      exact ⟨E0 ++ t, le', m', out, .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hrel, hg, hs⟩
  | Trap st' msg =>
      obtain ⟨t, le', m', hx, hg, hs, hc⟩ := h
      exact ⟨E0 ++ t, le', m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 hx, hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h
  | Throwing _ _ _ _ => exact h

/-- A shift by the low six bits of the top `i64`. -/
theorem sim_shift (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt64 → UInt64 → UInt64)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .i64 :: .i64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.i64 :: σr) ∧
        s = .Sset (slotId σr.length .i64)
          (.Ebinop op (tmp σr.length .i64)
            (.Ebinop .Oand (tmp (σr.length + 1) .i64) (.Econst_long 63 tulong) tulong) tulong))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .i64 y :: .i64 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st { params := sl.params, locals := sl.locals, values := .i64 (f x (y % 64)) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, sem_binary_operation A op (.Vlong x) tulong (.Vlong (y &&& 63)) tulong m =
      some (.Vlong (f x (y % 64)))) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
          (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hy) (.eval_Econst_long _ _)
            (sem_and_ll A m y 63))
          (hsem m x y)) rfl hb

theorem sim_shlI64 (F : Nat) : InstrSim A X E mod c F .shlI64 :=
  sim_shift F .shlI64 .Oshl (· <<< ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_shl_ll A)

theorem sim_shrUI64 (F : Nat) : InstrSim A X E mod c F .shrUI64 :=
  sim_shift F .shrUI64 .Oshr (· >>> ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_shr_ll A)

/-- A division or remainder, which traps when the divisor is zero. -/
theorem sim_divrem (hE : EnvOk E) (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt64 → UInt64 → UInt64)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .i64 :: .i64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.i64 :: σr) ∧
        s = .Ssequence
          (.Sifthenelse (.Ebinop .Oeq (tmp (σr.length + 1) .i64) (.Econst_long 0 tulong) tint)
            (trapStmt trapDivZero c.result) .Sskip)
          (.Sset (slotId σr.length .i64)
            (.Ebinop op (tmp σr.length .i64) (tmp (σr.length + 1) .i64) tulong)))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .i64 y :: .i64 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        if y = 0 then .Trap st "integer divide by zero"
        else .Fallthrough st { params := sl.params, locals := sl.locals, values := .i64 (f x y) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, y ≠ 0 → sem_binary_operation A op (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vlong (f x y))) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      have hcond : eval_expr A E.ge empty_env le m
          (.Ebinop .Oeq (tmp (σr.length + 1) .i64) (.Econst_long 0 tulong) tint)
          (.Vint (if y = 0 then 1 else 0)) :=
        .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hy) (.eval_Econst_long _ _)
          (sem_eq_ll A m y 0)
      by_cases hy0 : y = 0
      · rw [ite_eq_left hy0]
        obtain ⟨m', hx', hg, hs⟩ := trap_exec (A := A) (X := X) (le := le) hE hinv.store
          hinv.status trapDivZero c.result
        refine ⟨E0, le, m', ?_, hg, by rw [trapCode_divZero]; exact hs,
          by rw [trapCode_divZero]; decide⟩
        refine .exec_Sseq_2 _ _ _ _ _ _ _ _ _ ?_ (by cases c.result <;> simp [trapOut])
        refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hcond ?_ hx'
        rw [hy0]; exact bool_int m 1
      · rw [ite_eq_right hy0]
        refine Outcome.prefix ?_ (push_step hrest hinv.locals hinv.store hinv.status hinv.brk
          (eval_ll hx hy (hsem m x y hy0)) rfl hb)
        refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hcond ?_ (.exec_Sskip _ _ _)
        rw [ite_eq_right hy0]; exact bool_int m 0

theorem sim_divUI64 (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .divUI64 :=
  sim_divrem hE F .divUI64 .Odiv (· / ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_div_ll A)

theorem sim_remUI64 (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .remUI64 :=
  sim_divrem hE F .remUI64 .Omod (· % ·)
    (fun L σ n s σ' n' h => by
      rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
      exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (sem_mod_ll A)

theorem sim_unreachable (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .unreachable := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def]
      obtain ⟨m', hx, hg, hs⟩ := trap_exec (A := A) (X := X) (le := le) hE hinv.store
        hinv.status trapUnreachable c.result
      exact ⟨E0, le, m', hx, hg, by rw [trapCode_unreachable]; exact hs,
        by rw [trapCode_unreachable]; decide⟩

theorem sim_eqI64 (F : Nat) : InstrSim A X E mod c F .eqI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, i64Cmp, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (eval_ll hx hy (sem_eq_ll A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_neI64 (F : Nat) : InstrSim A X E mod c F .neI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, i64Cmp, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (eval_ll hx hy (sem_ne_ll A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_ltUI64 (F : Nat) : InstrSim A X E mod c F .ltUI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, i64Cmp, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (eval_ll hx hy (sem_lt_ll A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_leUI64 (F : Nat) : InstrSim A X E mod c F .leUI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, i64Cmp, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (eval_ll hx hy (sem_le_ll A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_geUI64 (F : Nat) : InstrSim A X E mod c F .geUI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, i64Cmp, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (eval_ll hx hy (sem_ge_ll A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_eqzI64 (F : Nat) : InstrSim A X E mod c F .eqzI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
          (.eval_Econst_long _ _) (sem_eq_ll A m x 0)) (cast_int_uint m _)) rfl hb

theorem sim_eq (F : Nat) : InstrSim A X E mod c F .eq := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
          (.eval_Etempvar _ _ _ hy) (sem_eq_ii A m x y)) (cast_int_uint m _)) rfl hb

theorem sim_eqz (F : Nat) : InstrSim A X E mod c F .eqz := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
          (.eval_Econst_int _ _) (sem_eq_ii A m x _)) (cast_int_uint m _)) rfl hb

theorem sim_and (F : Nat) : InstrSim A X E mod c F .and := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have hsem := sem_and_ii A m x y
      rw [UInt32.and_comm] at hsem
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (.eval_Etempvar _ _ _ hy) hsem) rfl hb

theorem sim_wrapI64 (F : Nat) : InstrSim A X E mod c F .wrapI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) (cast_long_uint m x)) rfl hb

theorem sim_extendUI32 (F : Nat) : InstrSim A X E mod c F .extendUI32 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) (cast_uint_long m x)) rfl hb

theorem sim_const (F : Nat) (k : UInt32) : InstrSim A X E mod c F (.const k) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def]
      exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Econst_int _ _) rfl hbase

theorem sim_constI64 (F : Nat) (k : UInt64) : InstrSim A X E mod c F (.constI64 k) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def]
      exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Econst_long _ _) rfl hbase

theorem sim_globalGet (hE : EnvOk E) (hG : c.nglobals = E.globals.length) (F i : Nat) :
    InstrSim A X E mod c F (.globalGet i) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨hi, rfl, rfl, rfl⟩ := h
  rw [hG] at hi
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨v, hv, hl, -⟩ := hinv.store.1.2 i hi
      simp only [execOne.eq_def, hv]
      exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
        (eval_global_long (hE.globals i hi) hl) rfl hbase

theorem sim_globalSet (hE : EnvOk E) (hG : c.nglobals = E.globals.length) (F i : Nat) :
    InstrSim A X E mod c F (.globalSet i) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨hb, rfl⟩, ⟨hi, rfl⟩, rfl, rfl, rfl⟩ := h
  rw [hG] at hi
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      obtain ⟨w, hw, -, hva⟩ := hinv.store.1.2 i hi
      simp only [execOne.eq_def, hvs, hw]
      refine ⟨σr, rfl, hb, E0, le, _,
        exec_assign_long (hE.globals i hi) (.eval_Etempvar _ _ _ hx) rfl hva, ?_, Frame.refl _ _⟩
      exact { stack := hrest
              locals := hinv.locals
              store := ⟨GlobalsRel.store_global hE hinv.store.1 hi x, hinv.store.2.store_global hE hi _⟩
              status := hinv.status.store_global hE hi _
              brk := hinv.brk }

end

end LeanExe.Native
