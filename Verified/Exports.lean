module

public import Interpreter.Wasm.Semantics.Lemmas
public import Verified.Correct
public import Verified.AlignedEntries
public import LeanExe.Pipeline.ImplementsAligned

@[expose] public section

/-!
The theorems of a module hold for the module with other exports.  Talos's `execOne`, `exec`, and
`run` read no export of the module, and neither do the aligned runs of
[the aligned run definitions](../LeanExe/ProofKit/AlignedDefs.lean), so `Wasm.run_exports` states
that a run of `{ m with exports := e }` is the run of `m`, and
`LeanExe.ProofKit.alignedRun_exports` states the same of `AlignedRun`.  The proofs follow the
recursion of the definitions on the fuel, as Talos's `fuel_mono_aux` does, through
`execOne.eq_def` and Talos's `execOne_loop_succ` and `execOne_memOp_succ`.  The helpers that read
the module's types recursively, `Module.gcTypeEquiv` and `Module.gcTypeSubtype`, take their own
lemmas.  `Verified.selectExports names m` keeps the exports of `alloc` and `release` and those of
the names `names`, which the option `(exports := [f, g, …])` of `verified_compile` gives, and
`LeanExe.Pipeline.ImplementsA.selectExports` and its counterparts for `ImplementsAligned`,
`ImplementsTables`, `ImplementsTablesAligned`, and `ImplementsStatic` carry each theorem that
`verified_compile` states about the module of `compileWith` to that module.
-/

namespace Wasm

variable {α : Type}

/-- The loop of `Module.gcTypeEquiv` does not read the exports. -/
theorem gcTypeEquiv_go_exports (m : Module) (e : List Export) (fuel a b : Nat) :
    Module.gcTypeEquiv.go { m with exports := e } fuel a b = Module.gcTypeEquiv.go m fuel a b := by
  induction fuel generalizing a b with
  | zero =>
    conv => lhs; rw [Module.gcTypeEquiv.go]
    conv => rhs; rw [Module.gcTypeEquiv.go]
    rfl
  | succ f ih =>
    conv => lhs; rw [Module.gcTypeEquiv.go]
    conv => rhs; rw [Module.gcTypeEquiv.go]
    simp only [ih]
    rfl

/-- `Module.gcTypeEquiv` does not read the exports. -/
theorem gcTypeEquiv_exports (m : Module) (e : List Export) :
    ({ m with exports := e } : Module).gcTypeEquiv = m.gcTypeEquiv := by
  funext a b
  simp only [Module.gcTypeEquiv, gcTypeEquiv_go_exports]

/-- The loop of `Module.gcTypeSubtype` does not read the exports. -/
theorem gcTypeSubtype_go_exports (m : Module) (e : List Export) (b fuel x : Nat) :
    Module.gcTypeSubtype.go { m with exports := e } b fuel x =
      Module.gcTypeSubtype.go m b fuel x := by
  induction fuel generalizing x with
  | zero =>
    conv => lhs; rw [Module.gcTypeSubtype.go]
    conv => rhs; rw [Module.gcTypeSubtype.go]
    simp only [gcTypeEquiv_exports]
  | succ f ih =>
    conv => lhs; rw [Module.gcTypeSubtype.go]
    conv => rhs; rw [Module.gcTypeSubtype.go]
    simp only [gcTypeEquiv_exports, ih]

/-- `Module.gcTypeSubtype` does not read the exports. -/
theorem gcTypeSubtype_exports (m : Module) (e : List Export) :
    ({ m with exports := e } : Module).gcTypeSubtype = m.gcTypeSubtype := by
  funext a b
  simp only [Module.gcTypeSubtype, gcTypeSubtype_go_exports]

/-- `Module.indirectCallTypeOk` does not read the exports. -/
theorem indirectCallTypeOk_exports (m : Module) (e : List Export) :
    ({ m with exports := e } : Module).indirectCallTypeOk = m.indirectCallTypeOk := by
  funext fid t fn ty
  simp only [Module.indirectCallTypeOk, gcTypeSubtype_exports]
  rfl

/-- `AnyRef.matchesHeap` does not read the exports. -/
theorem matchesHeap_exports (m : Module) (e : List Export) :
    AnyRef.matchesHeap (α := α) { m with exports := e } = AnyRef.matchesHeap m := by
  funext st ht r
  cases r <;> simp only [AnyRef.matchesHeap, gcTypeSubtype_exports]

/-- `gcRefMatches` does not read the exports. -/
theorem gcRefMatches_exports (m : Module) (e : List Export) :
    gcRefMatches (α := α) { m with exports := e } = gcRefMatches m := by
  funext st n ht v
  cases v <;> simp only [gcRefMatches, matchesHeap_exports, gcTypeSubtype_exports] <;> rfl

/-- `execGcOp` does not read the exports. -/
theorem execGcOp_exports (m : Module) (e : List Export) :
    execGcOp (α := α) { m with exports := e } = execGcOp m := by
  funext st s g
  cases g <;> simp only [execGcOp, gcRefMatches_exports] <;> rfl

/-- `execOne`, `exec`, and `run` at fuel `n` do not read the exports: by induction on the fuel,
`runTail` at `n` from `run` at `n - 1`, `execOne` at `n` from the three at `n - 1`, `exec` at `n`
from `execOne` at `n` by induction on the program, and `run` at `n` from `exec` and `runTail` at
`n`. -/
theorem interp_exports (e : List Export) (n : Nat) :
    (∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction) (env : HostEnv α),
      execOne n { m with exports := e } st s inst env = execOne n m st s inst env) ∧
    (∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
      exec n { m with exports := e } st s p env = exec n m st s p env) ∧
    (∀ (m : Module) (id : Nat) (st : Store α) (ps : List Value) (env : HostEnv α),
      run n { m with exports := e } id st ps env = run n m id st ps env) := by
  have rest : ∀ n,
      (∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction) (env : HostEnv α),
        execOne n { m with exports := e } st s inst env = execOne n m st s inst env) →
      (∀ (m : Module) (id : Nat) (st : Store α) (vs : List Value) (env : HostEnv α),
        runTail n { m with exports := e } id st vs env = runTail n m id st vs env) →
      (∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
        exec n { m with exports := e } st s p env = exec n m st s p env) ∧
      (∀ (m : Module) (id : Nat) (st : Store α) (ps : List Value) (env : HostEnv α),
        run n { m with exports := e } id st ps env = run n m id st ps env) := by
    intro n hOne hTail
    have hExec : ∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
        exec n { m with exports := e } st s p env = exec n m st s p env := by
      intro m st s p env
      induction p generalizing st s with
      | nil => simp only [exec]
      | cons inst rest ih => simp only [exec, hOne, ih]
    exact ⟨hExec, fun m id st ps env => by simp only [run, hExec, hTail]⟩
  induction n with
  | zero =>
    have hOne : ∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
        (env : HostEnv α), execOne 0 { m with exports := e } st s inst env =
          execOne 0 m st s inst env := by
      intro m st s inst env
      simp only [execOne.eq_def]
    obtain ⟨hE, hR⟩ := rest 0 hOne fun m id st vs env => by simp only [runTail]
    exact ⟨hOne, hE, hR⟩
  | succ f ih =>
    obtain ⟨hO, hE, hR⟩ := ih
    have hOne : ∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
        (env : HostEnv α), execOne (f + 1) { m with exports := e } st s inst env =
          execOne (f + 1) m st s inst env := by
      intro m st s inst env
      cases inst with
      | loop ps rs body pt rt => simp only [execOne_loop_succ, hE, hO]
      | memOp k inner =>
        simp only [execOne_memOp_succ]
        cases st.extraMems[k - 1]? with
        | none => rfl
        | some memK =>
          cases m.extraMemories[k - 1]? with
          | none => rfl
          | some declK => simp only [hO { m with memory := some declK }]
      | callIndirect _ _ | returnCallIndirect _ _ | tableSize _ | tableGrow _ | memorySize
        | memoryGrow =>
        simp only [execOne.eq_def, hR, indirectCallTypeOk_exports]
        rfl
      | _ => simp only [execOne.eq_def, hE, hR, execGcOp_exports]
    obtain ⟨hE', hR'⟩ := rest (f + 1) hOne fun m id st vs env => by simp only [runTail, hR]
    exact ⟨hOne, hE', hR'⟩

/-- An instruction runs in `{ m with exports := e }` as it runs in `m`. -/
theorem execOne_exports (e : List Export) (fuel : Nat) (m : Module) (st : Store α) (s : Locals)
    (inst : Instruction) (env : HostEnv α) :
    execOne fuel { m with exports := e } st s inst env = execOne fuel m st s inst env :=
  (interp_exports e fuel).1 m st s inst env

/-- A program runs in `{ m with exports := e }` as it runs in `m`. -/
theorem exec_exports (e : List Export) (fuel : Nat) (m : Module) (st : Store α) (s : Locals)
    (p : Program) (env : HostEnv α) :
    exec fuel { m with exports := e } st s p env = exec fuel m st s p env :=
  (interp_exports e fuel).2.1 m st s p env

/-- A call runs in `{ m with exports := e }` as it runs in `m`. -/
theorem run_exports (e : List Export) (fuel : Nat) (m : Module) (id : Nat) (st : Store α)
    (ps : List Value) (env : HostEnv α) :
    run fuel { m with exports := e } id st ps env = run fuel m id st ps env :=
  (interp_exports e fuel).2.2 m id st ps env

/-- `Runs` of `m` gives `Runs` of `{ m with exports := e }`. -/
theorem Runs.exports {aborts : Bool} {env : HostEnv α} {m : Module} {id : Nat} {st : Store α}
    {args : List Value} {P : Store α → List Value → Prop} (e : List Export)
    (h : Runs aborts env m id st args P) :
    Runs aborts env { m with exports := e } id st args P := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun fuel hf => by rw [run_exports]; exact hN fuel hf⟩

end Wasm

namespace LeanExe.ProofKit

open Wasm

variable {α : Type}

/-- `AlignedOne`, `AlignedExec`, and `AlignedRun` at fuel `n` do not read the exports, by the
induction of `Wasm.interp_exports`. -/
theorem aligned_exports (e : List Export) (n : Nat) :
    (∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction) (env : HostEnv α),
      AlignedOne n { m with exports := e } st s inst env = AlignedOne n m st s inst env) ∧
    (∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
      AlignedExec n { m with exports := e } st s p env = AlignedExec n m st s p env) ∧
    (∀ (m : Module) (id : Nat) (st : Store α) (ps : List Value) (env : HostEnv α),
      AlignedRun n { m with exports := e } id st ps env = AlignedRun n m id st ps env) := by
  have rest : ∀ n,
      (∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction) (env : HostEnv α),
        AlignedOne n { m with exports := e } st s inst env = AlignedOne n m st s inst env) →
      (∀ (m : Module) (id : Nat) (st : Store α) (vs : List Value) (env : HostEnv α),
        AlignedRunTail n { m with exports := e } id st vs env = AlignedRunTail n m id st vs env) →
      (∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
        AlignedExec n { m with exports := e } st s p env = AlignedExec n m st s p env) ∧
      (∀ (m : Module) (id : Nat) (st : Store α) (ps : List Value) (env : HostEnv α),
        AlignedRun n { m with exports := e } id st ps env = AlignedRun n m id st ps env) := by
    intro n hOne hTail
    have hExec : ∀ (m : Module) (st : Store α) (s : Locals) (p : Program) (env : HostEnv α),
        AlignedExec n { m with exports := e } st s p env = AlignedExec n m st s p env := by
      intro m st s p env
      induction p generalizing st s with
      | nil => simp only [AlignedExec]
      | cons inst rest ih => simp only [AlignedExec, hOne, execOne_exports, ih]
    exact ⟨hExec, fun m id st ps env => by simp only [AlignedRun, hExec, exec_exports, hTail]⟩
  induction n with
  | zero =>
    have hOne : ∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
        (env : HostEnv α), AlignedOne 0 { m with exports := e } st s inst env =
          AlignedOne 0 m st s inst env := by
      intro m st s inst env
      simp only [AlignedOne]
    obtain ⟨hE, hR⟩ := rest 0 hOne fun m id st vs env => by simp only [AlignedRunTail]
    exact ⟨hOne, hE, hR⟩
  | succ f ih =>
    obtain ⟨hO, hE, hR⟩ := ih
    have hOne : ∀ (m : Module) (st : Store α) (s : Locals) (inst : Instruction)
        (env : HostEnv α), AlignedOne (f + 1) { m with exports := e } st s inst env =
          AlignedOne (f + 1) m st s inst env := by
      intro m st s inst env
      cases inst <;> simp only [AlignedOne, hE, hO, hR, exec_exports]
    obtain ⟨hE', hR'⟩ := rest (f + 1) hOne fun m id st vs env => by
      simp only [AlignedRunTail, hR]
    exact ⟨hOne, hE', hR'⟩

/-- The aligned run of a call in `{ m with exports := e }` is that in `m`. -/
theorem alignedRun_exports (e : List Export) (fuel : Nat) (m : Module) (id : Nat) (st : Store α)
    (ps : List Value) (env : HostEnv α) :
    AlignedRun fuel { m with exports := e } id st ps env = AlignedRun fuel m id st ps env :=
  (aligned_exports e fuel).2.2 m id st ps env

end LeanExe.ProofKit

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The module `m` with the exports of its functions 0 and 1, `alloc` and `release` in a module of
`compileWith`, and the exports named in `names`. -/
def selectExports (names : List String) (m : Module) : Module :=
  { m with exports := m.exports.take 2 ++ (m.exports.drop 2).filter fun x => names.contains x.name }

/-- `ImplementsA` of `m` holds of `selectExports names m`. -/
theorem _root_.LeanExe.Pipeline.ImplementsA.selectExports {α β : Type} {_ : Represent α}
    {_ : Represent β} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} (names : List String)
    (h : ImplementsA aborts m entry f Pre Post) :
    ImplementsA aborts (selectExports names m) entry f Pre Post :=
  fun env store heap params x hAt hPre hRep hSep hCap =>
    (h env store heap params x hAt hPre hRep hSep hCap).exports _

/-- `ImplementsAligned` of `m` holds of `selectExports names m`. -/
theorem _root_.LeanExe.Pipeline.ImplementsAligned.selectExports {α β : Type} {_ : Represent α}
    {_ : Represent β} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} (names : List String)
    (h : ImplementsAligned aborts m entry f Pre Post) :
    ImplementsAligned aborts (selectExports names m) entry f Pre Post := by
  intro env store heap params x hAt hPre hRep hSep hCap hIn
  obtain ⟨⟨N, hN⟩, hR⟩ := h env store heap params x hAt hPre hRep hSep hCap hIn
  exact ⟨⟨N, fun fuel hf => by
    show AlignedRun fuel { m with exports := _ } entry store params.reverse env
    rw [alignedRun_exports]; exact hN fuel hf⟩, hR.exports _⟩

/-- `ImplementsTables` of `m` holds of `selectExports names m`. -/
theorem ImplementsTables.selectExports {α β : Type} {_ : Represent α} {_ : Represent β}
    {aborts : Bool} {m : Module} {entry : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} (names : List String)
    (h : ImplementsTables aborts m entry f tables Pre Post) :
    ImplementsTables aborts (selectExports names m) entry f tables Pre Post :=
  fun env store heap params x hAt hPre hT hRep hSep hCap =>
    (h env store heap params x hAt hPre hT hRep hSep hCap).exports _

/-- `ImplementsTablesAligned` of `m` holds of `selectExports names m`. -/
theorem ImplementsTablesAligned.selectExports {α β : Type} {_ : Represent α} {_ : Represent β}
    {aborts : Bool} {m : Module} {entry : Nat} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} (names : List String)
    (h : ImplementsTablesAligned aborts m entry f tables Pre Post) :
    ImplementsTablesAligned aborts (selectExports names m) entry f tables Pre Post := by
  intro env store heap params x hAt hPre hT hRep hSep hCap hIn
  obtain ⟨⟨N, hN⟩, hR⟩ := h env store heap params x hAt hPre hT hRep hSep hCap hIn
  exact ⟨⟨N, fun fuel hf => by
    show AlignedRun fuel { m with exports := _ } entry store params.reverse env
    rw [alignedRun_exports]; exact hN fuel hf⟩, hR.exports _⟩

/-- `ImplementsStatic` of `m` holds of `selectExports names m`. -/
theorem ImplementsStatic.selectExports {α β : Type} {_ : Represent α} {_ : Represent β}
    {pool : Bytes.LiteralPool} {aborts : Bool} {m : Module} {entry : Nat} {f : α → β}
    {tables : List (UInt64 × Array UInt64)} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} (names : List String)
    (h : ImplementsStatic pool aborts m entry f tables Pre Post) :
    ImplementsStatic pool aborts (selectExports names m) entry f tables Pre Post :=
  fun env store heap params x hAt hPre hIn hT hRep hSep hCap =>
    (h env store heap params x hAt hPre hIn hT hRep hSep hCap).exports _

end Verified
