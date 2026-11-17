import LeanExe.A64.Proof.LinuxCalls
import LeanExe.A64.Proof.MachineSim
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Wasi

/-!
The process of the Linux call layer's binding as a machine of the simulation.  `ProcRunWith T R P
code p q` is a run of `ProcReachWith` from `p` followed by a run of the program's model from a
process with FPCR at `fpcrValue`, which keeps FPCR and the trace: it contains every run of the
program's model, as `Machine.lift` requires, and its last step may leave the code.  When the code
lies below 2^55, two such runs compose, and a run that ends at a word of the code is one of
`ProcReachWith`.

`withMachine` holds a store by `StoreRel`, FPCR at `fpcrValue`, X17 at the area's address `area`,
and a relation `H` between the store's host state and the trace, and a trap ends at a stub of
`TrapAt` or at a state that `Ex` admits for the trap's message, with `H` between the trap's store
and the trace.  A model run keeps X17 when the code's instructions keep it, `Reach.x17`, which
holds for the code of `genWasiProgram`, whose generator checks `Instr.keepsX17` of each
instruction, so the area that the stubs pass to Linux is the one that the store relation names.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies)

/-! ## Instructions that keep X17 -/

theorem x17_setX {s : State} {d : Fin 32} {v : UInt64} (hd : (d.val != 17) = true) :
    (s.setX d v).x 17 = s.x 17 := by
  have hd' : d ≠ 17 := fun e => by subst e; exact absurd hd (by decide)
  exact State.x_setX_ne hd'

theorem x17_setXsp {s : State} {d : Fin 32} {v : UInt64} (hd : (d.val != 17) = true) :
    (s.setXsp d v).x 17 = s.x 17 := by
  by_cases h31 : d.val < 31
  · rw [State.setXsp_eq_setX h31]
    exact x17_setX hd
  · unfold State.setXsp
    rw [if_neg h31]
    rfl

/-- An instruction that `Instr.keepsX17` accepts keeps X17. -/
theorem exec_x17 {P : Platform} {i : Instr} {s t : State} (h : exec P i s = some t)
    (hk : i.keepsX17 = true) : t.x 17 = s.x 17 := by
  cases i
  case ldr r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact x17_setX hk
    · cases h
  case ldrb r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact x17_setX hk
    · cases h
  case ldrW r n imm =>
    obtain ⟨v, io, -, rfl⟩ := exec_ldrW_some h
    exact x17_setX hk
  case str r n imm =>
    simp only [exec] at h
    split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h
  case strb r n imm =>
    simp only [exec] at h
    split at h
    · cases h
    split at h
    · obtain rfl := Option.some.inj h
      rfl
    split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h
  case addImm d n imm =>
    obtain rfl := Option.some.inj h
    exact x17_setXsp hk
  case subImm d n imm =>
    obtain rfl := Option.some.inj h
    exact x17_setXsp hk
  case subsImm d n imm =>
    obtain rfl := Option.some.inj h
    exact x17_setX hk
  case subsReg d n m =>
    obtain rfl := Option.some.inj h
    exact x17_setX hk
  case bl imm =>
    obtain rfl := Option.some.inj h
    exact x17_setX (d := 30) (v := s.pc + 4) rfl
  all_goals
    simp only [exec, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first
        | exact x17_setX hk
        | rfl

/-- A run of the program's model keeps X17 when every instruction of the code keeps it. -/
theorem Reach.x17 {P : Platform} {code : UInt64 → Option UInt32}
    (hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true) {s t : State}
    (h : Reach P code s t) : t.x 17 = s.x 17 := by
  induction h with
  | refl => rfl
  | next hs _ ih =>
      obtain ⟨w, i, hc, hd, he⟩ := step_some hs
      rw [ih, exec_x17 he (hk _ _ _ hc hd)]

/-! ## Runs of the process with the call layer -/

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-- A run of the process from `p` to a process with FPCR at `fpcrValue`, followed by a run of the
program's model that keeps FPCR and the trace, or no step. -/
def ProcRunWith (T : List Call) (R : Replies) (P : Platform) (code : UInt64 → Option UInt32)
    (p q : Proc) : Prop :=
  p = q ∨ ∃ r, ProcReachWith T R P code p r ∧ r.fpcr = fpcrValue ∧ Reach P code r.core q.core ∧
    q.fpcr = r.fpcr ∧ q.trace = r.trace

/-- A step of the process starts at a word of the code. -/
theorem pstepWith_code {p q : Proc} (h : pstepWith T R P code p = some q) :
    ∃ w, code p.core.pc = some w := by
  unfold pstepWith at h
  split at h
  · exact ⟨_, by assumption⟩
  · unfold istep at h
    cases hc : code p.core.pc with
    | none => rw [hc] at h; cases h
    | some w => exact ⟨w, rfl⟩

theorem proc_eq' {r q : Proc} (hf : q.fpcr = r.fpcr) (ht : q.trace = r.trace) :
    { r with core := q.core } = q := by
  obtain ⟨c, f, t⟩ := q
  simp only at hf ht
  subst hf ht
  rfl

/-- A run of the program's model from a process with FPCR at `fpcrValue` to a process whose
program counter lies below 2^55 is a run of `ProcReachWith`, when the code lies below 2^55. -/
theorem procReachWith_of_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {r q : Proc}
    (hf : r.fpcr = fpcrValue) (h : Reach P code r.core q.core) (hq : q.core.pc.toNat < 2 ^ 55)
    (hf' : q.fpcr = r.fpcr) (ht : q.trace = r.trace) : ProcReachWith T R P code r q := by
  have := ProcReachWith.of_reach' (T := T) (R := R) hdom hf h hq
  rwa [proc_eq' hf' ht] at this

theorem ProcRunWith.trans (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p q z : Proc}
    (h1 : ProcRunWith T R P code p q) (h2 : ProcRunWith T R P code q z) :
    ProcRunWith T R P code p z := by
  rcases h1 with rfl | ⟨r1, hp1, hf1, hm1, hq1, ht1⟩
  · exact h2
  rcases h2 with rfl | ⟨r2, hp2, hf2, hm2, hz2, ht2⟩
  · exact .inr ⟨r1, hp1, hf1, hm1, hq1, ht1⟩
  cases hp2 with
  | refl =>
      exact .inr ⟨r1, hp1, hf1, hm1.trans hm2, by rw [hz2, hq1], by rw [ht2, ht1]⟩
  | next hs hr =>
      obtain ⟨w, hw⟩ := pstepWith_code hs
      have hq := procReachWith_of_run (T := T) (R := R) hdom hf1 hm1 (hdom _ _ hw) hq1 ht1
      exact .inr ⟨r2, hp1.trans (hq.trans (.next hs hr)), hf2, hm2, hz2, ht2⟩

/-- A run that ends at a word of the code is a run of `ProcReachWith`, when the code lies below
2^55. -/
theorem ProcRunWith.toWith (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p q : Proc}
    (h : ProcRunWith T R P code p q) {w : UInt32} (hw : code q.core.pc = some w) :
    ProcReachWith T R P code p q := by
  rcases h with rfl | ⟨r, hp, hf, hm, hq, ht⟩
  · exact .refl _
  exact hp.trans (procReachWith_of_run hdom hf hm (hdom _ _ hw) hq ht)

/-- A run of `ProcReachWith` to a process with FPCR at `fpcrValue`. -/
theorem ProcRunWith.ofWith {p q : Proc} (h : ProcReachWith T R P code p q)
    (hf : q.fpcr = fpcrValue) : ProcRunWith T R P code p q :=
  .inr ⟨q, h, hf, .refl _, rfl, rfl⟩

/-- A run of the program's model from a process with FPCR at `fpcrValue`. -/
theorem ProcRunWith.ofReach {p : Proc} (hf : p.fpcr = fpcrValue) {s : State}
    (h : Reach P code p.core s) : ProcRunWith T R P code p { p with core := s } :=
  .inr ⟨p, .refl _, hf, h, rfl, rfl⟩

/-! ## The machine -/

/-- The process as a machine for the calls `T` and the replies `R`: a state holds a store by
`StoreRel`, FPCR at `fpcrValue`, X17 at `area`, and the relation `H` between the store's host
state and the trace; a trap ends at a stub of `TrapAt` or at a state that `Ex` admits, with `H`
between the trap's store and the trace; the host environment is `env`. -/
def withMachine (T : List Call) (R : Replies) (P : Platform) (code : UInt64 → Option UInt32)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true) (area : UInt64)
    {α : Type} (H : α → List Event → Prop) (Ex : Shared → String → α → State → Prop)
    (env : HostEnv α) : Machine P code α where
  Q := Proc
  core p := p.core
  Rch := ProcRunWith T R P code
  SR cap gts st p :=
    StoreRel P cap gts st p.core ∧ p.fpcr = fpcrValue ∧ p.core.x 17 = area ∧ H st.host p.trace
  Trapped S st msg p :=
    (TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg p.core.pc ∨ Ex S msg st.host p.core) ∧
      p.fpcr = fpcrValue ∧ H st.host p.trace
  env := env
  refl _ := .inl rfl
  trans := ProcRunWith.trans hdom
  storeRel h := h.1
  lift {_ _ st p s} h hr :=
    ⟨{ p with core := s }, ProcRunWith.ofReach h.2.1 hr, rfl,
      fun st' h' hh => ⟨h', h.2.1, by
        show s.x 17 = area
        rw [Reach.x17 hk hr]
        exact h.2.2.1, by rw [hh]; exact h.2.2.2⟩,
      fun _ st' _ ht hh => ⟨.inl ht, h.2.1, by rw [hh]; exact h.2.2.2⟩⟩

end LeanExe.A64
