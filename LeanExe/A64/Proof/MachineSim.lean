module

public import LeanExe.A64.Proof.Sim
public import LeanExe.ProofKit.Exec

@[expose] public section

/-!
The simulation over a machine.  A `Machine` runs the generated code: its states hold the
program's state, which `core` gives, its runs `Rch` contain the runs of the program's model, a
state holds Talos's store by the relation `SR`, `Trapped` states where a trap ends with its
message and store, and `env` is the host environment that Talos's run uses for the module's
imports.  `Machine.Outcome`,
`Machine.CallResult`, `Machine.CallOutcome`, `Machine.FunSim`, `Machine.CallsOk`, and
`Machine.InstrSim` are the forms of `Sim.lean`'s definitions over a machine.  `bare P code α` is
the program's model as a machine, with the store relation `StoreRel`, the trap stubs of
`TrapAt`, and the empty environment.  At it, `Overflows`, `Outcome`, `CallResult`, and
`CallOutcome` equal their general forms by `rfl`, `FunSim` and `CallsOk` are equivalent to their
general forms at every `α`, and `InstrSim` follows from its general form at every `α`: its
premise `CallsOk` assumes the functions' simulation for stores of every host state, while the
general form at `bare P code α` assumes it for stores of host state `α` alone.

`Leaf inst` states that Talos runs `inst` without its host environment or the module's functions
and imports and ends a fall-through, a branch, a return, or a trap with a store of the same host
state, and `Machine.InstrSim.of_leaf` carries the simulation of such a form from the program's
model to every machine.
-/

namespace LeanExe.A64

open Wasm

/-- A machine that runs the generated code, with Talos's stores of host state `α`: states `Q`,
the program's state `core q` of each, the runs `Rch` between states, the relation `SR cap gts st q`
by which `q` holds the store `st` of a memory of `cap` pages and globals of the types `gts`, the
states `Trapped S st msg q` at which a trap with the message `msg` and the store `st` ends for the
stubs of `S`, and the host environment `env` of the module's imports.  The runs compose, a state
that holds a store holds it in the area as `StoreRel` states, and a run of the program's model
from a state that holds a store is a run of the machine to a state that holds every store that
`StoreRel` relates to the run's end with the same host state and at which, when the run ends at
the stub of a trap's code, every trap with that code and a store of the same host state has
ended. -/
structure Machine (P : Platform) (code : UInt64 → Option UInt32) (α : Type) where
  Q : Type
  core : Q → State
  Rch : Q → Q → Prop
  SR : Nat → List ValueType → Store α → Q → Prop
  Trapped : Shared → Store α → String → Q → Prop
  env : HostEnv α
  refl (q : Q) : Rch q q
  trans {q₁ q₂ q₃ : Q} : Rch q₁ q₂ → Rch q₂ q₃ → Rch q₁ q₃
  storeRel {cap : Nat} {gts : List ValueType} {st : Store α} {q : Q} :
    SR cap gts st q → StoreRel P cap gts st (core q)
  lift {cap : Nat} {gts : List ValueType} {st : Store α} {q : Q} {s : State} :
    SR cap gts st q → Reach P code (core q) s →
    ∃ q', Rch q q' ∧ core q' = s ∧
      (∀ st' : Store α, StoreRel P cap gts st' s → st'.host = st.host → SR cap gts st' q') ∧
      ∀ (S : Shared) (st' : Store α) (msg : String),
        TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg s.pc → st'.host = st.host →
        Trapped S st' msg q'

/-- The program's model as a machine: its states and runs, the store relation `StoreRel`, the
trap stubs of `TrapAt`, and no imports. -/
def bare (P : Platform) (code : UInt64 → Option UInt32) (α : Type) : Machine P code α where
  Q := State
  core s := s
  Rch := Reach P code
  SR cap gts st s := StoreRel P cap gts st s
  Trapped S _ msg s := TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg s.pc
  env := {}
  refl s := .refl s
  trans h₁ h₂ := h₁.trans h₂
  storeRel h := h
  lift {_ _ _ _ s} _ h := ⟨s, h, rfl, fun _ h' _ => h', fun _ _ _ h' _ => h'⟩

namespace Machine

variable {P : Platform} {code : UInt64 → Option UInt32} {α : Type} (M : Machine P code α)

/-- `Overflows` over the machine `M`. -/
def Overflows (tS : UInt64) (q : M.Q) : Prop :=
  ∃ q', M.Rch q q' ∧ (M.core q').pc = tS ∧ (M.core q').io = (M.core q).io

/-- `Outcome` over the machine `M`: the runs are `M`'s, a state holds a store by `M.SR`, and a
trap ends at a state that `M.Trapped` admits. -/
def Outcome (E : Env) (ctl : List Ctl) (D : Nat) (fin : Option (List ValueType))
    (endA : UInt64) (r : Continuation α) (q : M.Q) : Prop :=
  (((M.core q).sp - (M.core q).x 18).toNat < D ∧ M.Overflows E.trapStack q) ∨
  match r with
  | .Fallthrough st' sl' => ∃ σ', fin = some σ' ∧ ∃ q', M.Rch q q' ∧ (M.core q').pc = endA ∧
      (M.core q').sp = (M.core q).sp ∧ (M.core q').io = (M.core q).io ∧
      (M.core q').x 18 = (M.core q).x 18 ∧
      MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q') ∧
      Inv P E.localTypes σ' sl' (M.core q') ∧ Frame (curBase ctl) (M.core q) (M.core q') ∧
      M.SR E.cap E.globalTypes st' q'
  | .Break k st' sl' => ∃ t, ctl[k]? = some t ∧ ∃ q', M.Rch q q' ∧
      (M.core q').pc = t.target ∧ (M.core q').sp = (M.core q).sp ∧
      (M.core q').io = (M.core q).io ∧ (M.core q').x 18 = (M.core q).x 18 ∧
      MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q') ∧
      LocalsRel (M.core q') (sl'.params ++ sl'.locals) ∧
      Typed E.localTypes (sl'.params ++ sl'.locals) ∧
      Kept t sl'.values (M.core q') ∧ Frame t.base (M.core q) (M.core q') ∧
      M.SR E.cap E.globalTypes st' q'
  | .Return st' vs => ∃ t, ctl.getLast? = some t ∧ ∃ q', M.Rch q q' ∧
      (M.core q').pc = t.target ∧ (M.core q').sp = (M.core q).sp ∧
      (M.core q').io = (M.core q).io ∧ (M.core q').x 18 = (M.core q).x 18 ∧
      MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q') ∧
      Kept t vs (M.core q') ∧ M.SR E.cap E.globalTypes st' q'
  | .Trap st' msg => ∃ q', M.Rch q q' ∧ (M.core q').io = (M.core q).io ∧
      M.Trapped E.toShared st' msg q'
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- `CallResult` over the machine `M`. -/
def CallResult (S : Shared) (ps rs : List ValueType) (vs : List Value) (res : Result α)
    (q : M.Q) : Prop :=
  match res with
  | .Success vs' st' => ∃ q', M.Rch q q' ∧ (M.core q').pc = (M.core q).x 30 ∧
      (M.core q').sp = (M.core q).sp ∧ (M.core q').x 18 = (M.core q).x 18 ∧
      (M.core q').io = (M.core q).io ∧ MemFrame (M.core q).sp 0 (M.core q) (M.core q') ∧
      vs'.length = rs.length + (vs.length - ps.length) ∧
      vs'.drop rs.length = vs.drop ps.length ∧
      StackRel (M.core q') (vs'.take rs.length) ∧ Typed rs.reverse (vs'.take rs.length) ∧
      M.SR S.cap S.globalTypes st' q'
  | .Trap st' msg => ∃ q', M.Rch q q' ∧ (M.core q').io = (M.core q).io ∧
      M.Trapped S st' msg q'
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- `CallOutcome` over the machine `M`. -/
def CallOutcome (S : Shared) (n : Nat) (ps rs : List ValueType) (vs : List Value)
    (res : Result α) (q : M.Q) : Prop :=
  (((M.core q).sp - (M.core q).x 18).toNat < n ∧ M.Overflows S.trapStack q) ∨
    M.CallResult S ps rs vs res q

/-- `FunSim` over the machine `M`, with Talos's run under `M.env`. -/
def FunSim (m : Module) (S : Shared) (need : Nat → Nat) (g k : Nat)
    (c : UInt64 × List ValueType × List ValueType) : Prop :=
  ∀ (st : Store α) (vs : List Value) (q : M.Q) (_ : c.2.1.length ≤ vs.length),
    Typed c.2.1.reverse (vs.take c.2.1.length) → (M.core q).pc = c.1 → StackOk P (M.core q) →
    M.SR S.cap S.globalTypes st q → StackRel (M.core q) (vs.take c.2.1.length) →
    M.CallOutcome S (need k) c.2.1 c.2.2 vs (Wasm.run g m k st vs M.env) q

/-- `CallsOk` over the machine `M`. -/
def CallsOk (F : Nat) (m : Module) (callee : Table) (S : Shared) (need : Nat → Nat) : Prop :=
  (S.byteStores = true → P.normal P.uart = false) ∧
    ∀ k c, callee k = some c → ∀ g < F, M.FunSim m S need g k c

theorem CallsOk.mono {M : Machine P code α} {F G : Nat} {m : Module} {callee : Table}
    {S : Shared} {need : Nat → Nat} (h : M.CallsOk F m callee S need) (hle : G ≤ F) :
    M.CallsOk G m callee S need :=
  ⟨h.1, fun k c hk g hg => h.2 k c hk g (by omega)⟩

/-- `InstrSim` over the machine `M`, with Talos's run under `M.env`. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (is : List Instr)
    (fin : Option (List ValueType)),
    genInstr E ctl σ a inst = .ok (is, fin) → CodeAt code a is → curBase ctl ≤ σ.length →
    CtlOk ctl →
    ∀ (m : Module) (st : Store α) (sl : Locals) (q : M.Q),
      Inv P E.localTypes σ sl (M.core q) → M.SR E.cap E.globalTypes st q →
      m.memIs64 = false → (M.core q).pc = a → ∀ (need : Nat → Nat) (D : Nat),
      M.CallsOk F m E.callee E.toShared need → (∀ j ∈ callsOf inst, need j ≤ D) →
      M.Outcome E ctl D fin (after a is.length) (execOne F m st sl inst M.env) q

end Machine

/-! ## The definitions of `Sim.lean` as the forms at the bare machine -/

section Bare

variable (P : Platform) (code : UInt64 → Option UInt32)

theorem Overflows.eq_bare {α : Type} (tS : UInt64) (ms : State) :
    Overflows P code tS ms = (bare P code α).Overflows tS ms := rfl

theorem Outcome.eq_bare (E : Env) (ctl : List Ctl) (D : Nat) (fin : Option (List ValueType))
    (endA : UInt64) {α : Type} (r : Continuation α) (ms : State) :
    Outcome P code E ctl D fin endA r ms = (bare P code α).Outcome E ctl D fin endA r ms := rfl

theorem CallResult.eq_bare (S : Shared) (ps rs : List ValueType) (vs : List Value) {α : Type}
    (res : Result α) (ms : State) :
    CallResult P code S ps rs vs res ms = (bare P code α).CallResult S ps rs vs res ms := rfl

theorem CallOutcome.eq_bare (S : Shared) (n : Nat) (ps rs : List ValueType) (vs : List Value)
    {α : Type} (res : Result α) (ms : State) :
    CallOutcome P code S n ps rs vs res ms = (bare P code α).CallOutcome S n ps rs vs res ms :=
  rfl

theorem FunSim.iff_bare (m : Module) (S : Shared) (need : Nat → Nat) (g k : Nat)
    (c : UInt64 × List ValueType × List ValueType) :
    FunSim P code m S need g k c ↔ ∀ α, (bare P code α).FunSim m S need g k c :=
  ⟨fun h _ => h, fun h {α} => h α⟩

theorem CallsOk.iff_bare (F : Nat) (m : Module) (callee : Table) (S : Shared)
    (need : Nat → Nat) :
    CallsOk P code F m callee S need ↔ ∀ α, (bare P code α).CallsOk F m callee S need :=
  ⟨fun h _ => ⟨h.1, fun k c hk g hg => (FunSim.iff_bare P code _ _ _ _ _ _).mp (h.2 k c hk g hg) _⟩,
    fun h => ⟨(h Unit).1, fun k c hk g hg =>
      (FunSim.iff_bare P code _ _ _ _ _ _).mpr fun α => (h α).2 k c hk g hg⟩⟩

/-- `InstrSim` follows from its form at the bare machine of every host state.  The converse does
not hold in general, since `InstrSim` assumes the functions' simulation for stores of every host
state while the form at `bare P code α` assumes it for stores of host state `α`. -/
theorem InstrSim.of_bare {F : Nat} {inst : Instruction}
    (h : ∀ α, (bare P code α).InstrSim F inst) : InstrSim P code F inst :=
  fun E ctl σ a is fin hg hc hb hctl α m st sl ms hinv hsr h64 hpc need D hcl hD =>
    h α E ctl σ a is fin hg hc hb hctl m st sl ms hinv hsr h64 hpc need D
      ((CallsOk.iff_bare P code _ _ _ _ _).mp hcl α) hD

end Bare

/-! ## Forms that run without the host -/

/-- The module `m` without its functions and imports. -/
def withoutFuncs (m : Module) : Module := { m with funcs := [], imports := [] }

/-- The store of a fall-through, a branch, a return, or a trap `r` has the host state `h`. -/
def HostKept {α : Type} (h : α) : Continuation α → Prop
  | .Fallthrough st _ => st.host = h
  | .Break _ st _ => st.host = h
  | .Return st _ => st.host = h
  | .Trap st _ => st.host = h
  | _ => True

/-- Talos runs `inst` in a module `m` under the host environment `env` as it runs it in
`withoutFuncs m` under the empty one, and that run ends, when it falls through, branches,
returns, or traps, with a store of the given store's host state. -/
def Leaf (inst : Instruction) : Prop :=
  ∀ {α : Type} (F : Nat) (m : Module) (st : Store α) (sl : Locals) (env : HostEnv α),
    execOne F m st sl inst env = execOne F (withoutFuncs m) st sl inst ∧
    HostKept st.host (execOne F (withoutFuncs m) st sl inst)

/-- Proves `Leaf inst` for a form whose case of `execOne` mentions neither the host environment
nor the module's functions and imports and builds every store from the given one by updates of
other fields. -/
macro "leaf_tac" : tactic => `(tactic| (
  intro α F m st sl env
  refine ⟨?_, ?_⟩
  · cases F <;> simp only [execOne.eq_def] <;> rfl
  · cases F with
    | zero => simp only [execOne.eq_def]; trivial
    | succ f =>
      simp only [execOne.eq_def]
      repeat' split
      all_goals first | trivial | rfl))

namespace Machine

variable {P : Platform} {code : UInt64 → Option UInt32} {α : Type} (M : Machine P code α)

/-- A run of the program's model that changes only the program counter is a run of the machine to
a state that holds the same store. -/
theorem lift_pc {cap : Nat} {gts : List ValueType} {st : Store α} {q : M.Q} {p : UInt64}
    (hsr : M.SR cap gts st q) (hr : Reach P code (M.core q) { M.core q with pc := p }) :
    ∃ q', M.Rch q q' ∧ M.core q' = { M.core q with pc := p } ∧ M.SR cap gts st q' := by
  obtain ⟨q', hq, hc, hst, -⟩ := M.lift hsr hr
  exact ⟨q', hq, hc, hst st ((M.storeRel hsr).regs rfl rfl rfl) rfl⟩

/-- An outcome of the program's model from the core of a state that holds the store `st` is an
outcome of the machine when the continuation keeps `st`'s host state. -/
theorem Outcome.of_bare {E : Env} {ctl : List Ctl} {D : Nat} {fin : Option (List ValueType)}
    {endA : UInt64} {r : Continuation α} {q : M.Q} {st : Store α}
    (h : A64.Outcome P code E ctl D fin endA r (M.core q))
    (hsr : M.SR E.cap E.globalTypes st q) (hk : HostKept st.host r) :
    M.Outcome E ctl D fin endA r q := by
  rcases h with ⟨hc, s', hr, hp, ho⟩ | h
  · obtain ⟨q', hq, hc', -⟩ := M.lift hsr hr
    subst hc'
    exact .inl ⟨hc, q', hq, hp, ho⟩
  refine .inr ?_
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf, s', hr, hp, hsp, hout, h18, hmf, hinv, hfr, hsr'⟩ := h
      obtain ⟨q', hq, hc', hst, -⟩ := M.lift hsr hr
      subst hc'
      exact ⟨σ', hf, q', hq, hp, hsp, hout, h18, hmf, hinv, hfr, hst st' hsr' hk⟩
  | Break k st' sl' =>
      obtain ⟨t, ht, s', hr, hp, hsp, hout, h18, hmf, hloc, hty, hkp, hfr, hsr'⟩ := h
      obtain ⟨q', hq, hc', hst, -⟩ := M.lift hsr hr
      subst hc'
      exact ⟨t, ht, q', hq, hp, hsp, hout, h18, hmf, hloc, hty, hkp, hfr, hst st' hsr' hk⟩
  | Return st' vs =>
      obtain ⟨t, ht, s', hr, hp, hsp, hout, h18, hmf, hkp, hsr'⟩ := h
      obtain ⟨q', hq, hc', hst, -⟩ := M.lift hsr hr
      subst hc'
      exact ⟨t, ht, q', hq, hp, hsp, hout, h18, hmf, hkp, hst st' hsr' hk⟩
  | Trap st' msg =>
      obtain ⟨s', hr, hout, hpc⟩ := h
      obtain ⟨q', hq, hc', -, htr⟩ := M.lift hsr hr
      subst hc'
      exact ⟨q', hq, hout, htr _ st' msg hpc hk⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact h.elim
  | Throwing _ _ _ _ => exact h.elim

/-- The simulation of a form that runs without the host, carried from the program's model to the
machine. -/
theorem InstrSim.of_leaf {F : Nat} {inst : Instruction} (h : A64.InstrSim P code F inst)
    (hl : Leaf inst) : M.InstrSim F inst := by
  intro E ctl σ a is fin hgen hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
  obtain ⟨he, hk⟩ := hl F m st sl M.env
  have hcl0 : A64.CallsOk P code F (withoutFuncs m) E.callee E.toShared need := by
    refine ⟨hcl.1, fun k c _ g _ => ?_⟩
    intro β st' vs ms _ _ _ _ _ _
    have hrun : Wasm.run g (withoutFuncs m) k st' vs = .Invalid "Function index out of bounds" := by
      simp only [Wasm.run, withoutFuncs, List.getElem?_nil]
    refine .inr ?_
    rw [hrun]
    trivial
  rw [he]
  exact Outcome.of_bare M (h E ctl σ a is fin hgen hcode hb hctl (withoutFuncs m) st sl (M.core q)
    hinv (M.storeRel hsr) h64 hpc need D hcl0 hD) hsr hk

end Machine

end LeanExe.A64
