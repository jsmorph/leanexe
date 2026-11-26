module

public import LeanExe.A64.Proof.Linux
public import LeanExe.A64.Proof.MachineSim
public import LeanExe.A64.Proof.Function

@[expose] public section

/-!
A test of the interface of `Machine` on a process model whose steps impose conditions that the
program's model does not: the process of `LeanExe/A64/Linux.lean` steps a floating-point form only
while FPCR holds `fpcrValue` and every form only when the next program counter lies below 2^55.
`ProcRun K P code p q` is a run of the process from `p` followed by a run of the program's model
from a process with FPCR at `fpcrValue`, which keeps FPCR and the trace, so it contains every run
of the program's model from a process with FPCR at `fpcrValue`, as `Machine.lift` requires, and
its last step may leave the code.  When the code lies below 2^55, two such runs compose, and a run
that ends in the code is a run of the process.  `procMachine` is the machine whose store relation
adds FPCR at `fpcrValue` and a relation `H` between the store's host state and the trace to
`StoreRel`, and whose trap states add `H` between the trap's store and the trace to the stubs of
`TrapAt`, so that a trap's outcome carries the relation of its store to the trace.
`procMachine_calls` applies `Machine.calls_ok` to it.
-/

namespace LeanExe.A64.Test

open Wasm

variable {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32}

/-- A run of the process from `p` to a process with FPCR at `fpcrValue`, followed by a run of the
program's model that keeps FPCR and the trace, or no step. -/
def ProcRun (K : Kernel) (P : Platform) (code : UInt64 → Option UInt32) (p q : Proc) : Prop :=
  p = q ∨ ∃ r, ProcReach K P code p r ∧ r.fpcr = fpcrValue ∧ Reach P code r.core q.core ∧
    q.fpcr = r.fpcr ∧ q.trace = r.trace

/-- A step of the process starts at a word of the code. -/
theorem pstep_code {p q : Proc} (h : pstep K P code p = some q) : ∃ w, code p.core.pc = some w := by
  unfold pstep at h
  cases hc : code p.core.pc with
  | none => rw [hc] at h; cases h
  | some w => exact ⟨w, rfl⟩

/-- A process that `{ r with core := q.core }` equals. -/
theorem proc_eq {r q : Proc} (hf : q.fpcr = r.fpcr) (ht : q.trace = r.trace) :
    { r with core := q.core } = q := by
  obtain ⟨c, f, t⟩ := q
  simp only at hf ht
  subst hf ht
  rfl

/-- A run of the program's model from a process with FPCR at `fpcrValue` to a process whose
program counter lies below 2^55 is a run of the process, when the code lies below 2^55. -/
theorem procReach_of_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {r q : Proc}
    (hf : r.fpcr = fpcrValue) (h : Reach P code r.core q.core) (hq : q.core.pc.toNat < 2 ^ 55)
    (hf' : q.fpcr = r.fpcr) (ht : q.trace = r.trace) : ProcReach K P code r q := by
  have := ProcReach.of_reach' (K := K) hdom hf h hq
  rwa [proc_eq hf' ht] at this

theorem ProcRun.trans (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p q z : Proc}
    (h1 : ProcRun K P code p q) (h2 : ProcRun K P code q z) : ProcRun K P code p z := by
  rcases h1 with rfl | ⟨r1, hp1, hf1, hm1, hq1, ht1⟩
  · exact h2
  rcases h2 with rfl | ⟨r2, hp2, hf2, hm2, hz2, ht2⟩
  · exact .inr ⟨r1, hp1, hf1, hm1, hq1, ht1⟩
  cases hp2 with
  | refl =>
      exact .inr ⟨r1, hp1, hf1, hm1.trans hm2, by rw [hz2, hq1], by rw [ht2, ht1]⟩
  | next hs hr =>
      obtain ⟨w, hw⟩ := pstep_code hs
      have hq := procReach_of_run (K := K) hdom hf1 hm1 (hdom _ _ hw) hq1 ht1
      exact .inr ⟨r2, hp1.trans (hq.trans (.next hs hr)), hf2, hm2, hz2, ht2⟩

/-- A run that ends at a word of the code is a run of the process, when the code lies below
2^55. -/
theorem ProcRun.toProcReach (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {p q : Proc}
    (h : ProcRun K P code p q) {w : UInt32} (hw : code q.core.pc = some w) :
    ProcReach K P code p q := by
  rcases h with rfl | ⟨r, hp, hf, hm, hq, ht⟩
  · exact .refl _
  exact hp.trans (procReach_of_run hdom hf hm (hdom _ _ hw) hq ht)

/-- The process as a machine, with the host environment `env` and the relation `H` between the
store's host state and the trace. -/
def procMachine (K : Kernel) (P : Platform) (code : UInt64 → Option UInt32)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {α : Type} (H : α → List Event → Prop)
    (env : HostEnv α) : Machine P code α where
  Q := Proc
  core p := p.core
  Rch := ProcRun K P code
  SR cap gts st p := StoreRel P cap gts st p.core ∧ p.fpcr = fpcrValue ∧ H st.host p.trace
  Trapped S st msg p :=
    TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg p.core.pc ∧ H st.host p.trace
  env := env
  refl _ := .inl rfl
  trans := ProcRun.trans hdom
  storeRel h := h.1
  lift {_ _ st p s} h hr :=
    ⟨{ p with core := s }, .inr ⟨p, .refl _, h.2.1, hr, rfl, rfl⟩, rfl,
      fun st' h' hh => ⟨h', h.2.1, by rw [hh]; exact h.2.2⟩,
      fun _ st' _ ht hh => ⟨ht, by rw [hh]; exact h.2.2⟩⟩

/-- A trap's outcome over `procMachine`, unless the stack overflows, reaches a process whose trace
`H` relates to the host state of the trap's store. -/
theorem procMachine_trap (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {α : Type}
    (H : α → List Event → Prop) (env : HostEnv α) {E : Env} {ctl : List Ctl} {D : Nat}
    {fin : Option (List ValueType)} {endA : UInt64} {st : Store α} {msg : String} {p : Proc}
    (h : (procMachine K P code hdom H env).Outcome E ctl D fin endA (.Trap st msg) p) :
    ((p.core.sp - p.core.x 18).toNat < D ∧
      (procMachine K P code hdom H env).Overflows E.trapStack p) ∨
    ∃ q, ProcRun K P code p q ∧ H st.host q.trace := by
  rcases h with h | ⟨q, hr, -, -, hH⟩
  · exact .inl h
  · exact .inr ⟨q, hr, hH⟩

/-- `Machine.calls_ok` at the process: the functions of a table of stubs and generated functions
simulate under `env` at every fuel. -/
theorem procMachine_calls (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {α : Type}
    (H : α → List Event → Prop) (env : HostEnv α) {callee : Table} {S : Shared} {m : Module}
    (h64 : m.memIs64 = false) (hU : S.byteStores = true → P.normal P.uart = false)
    {need : Nat → Nat}
    (htab : ∀ k c, callee k = some c →
      (∃ imp hf, m.imports[k]? = some imp ∧ env.funcs[k]? = some hf ∧
        c.2 = (imp.params, imp.results) ∧
        (procMachine K P code hdom H env).StubSim S (need k) imp.params imp.results hf c.1) ∨
      ∃ f is, m.imports.length ≤ k ∧ m.funcs[k - m.imports.length]? = some f ∧
        c.2 = (f.params, f.results) ∧ genFunction callee S c.1 f = .ok is ∧ CodeAt code c.1 is)
    (hneed : ∀ k f, m.imports.length ≤ k → m.funcs[k - m.imports.length]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) (F : Nat) :
    (procMachine K P code hdom H env).CallsOk F m callee S need :=
  Machine.calls_ok _ h64 hU htab hneed F

end LeanExe.A64.Test
