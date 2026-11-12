import Verified.Examples.WasiSys
import Verified.Wasi.HostTotalWith
import Verified.Wasi.SysRule
import LeanExe.Wasi.NoTrap

/-! A host whose flat calls always return errno 0 satisfies `Host.TotalFor` for every list of calls
and `Host.NoTraps`, and its reporter replies meet the premise of `reported_rule_observed`, so these
premises of the flat call theorems can be met.  The world records each call's last outputs by name,
and a call with a reporter reports the sizes that its reporter's last outputs give.  For the flat
call example, the host has an environment that satisfies `hostSpecWith` for the example's module
and call list, and it meets the reached-host premise of the example's `total`.  The heap and
resource premises of `total` are not discharged here.  The second review of the syscall increment
wrote the first version of this file. -/

open LeanExe LeanExe.Wasi Verified.Wasi

namespace SysWitness

def zeroBytes (n : Nat) : LeanExe.Bytes := ⟨⟨Array.replicate n 0⟩⟩

theorem zeroBytes_size (n : Nat) : (zeroBytes n).data.size = n := by
  simp [zeroBytes, ByteArray.size]

structure World where
  exited : Option UInt64
  last : String → List LeanExe.Bytes

def reportedOf (world : World) (call : Call) : List Nat :=
  match call.reporter with
  | some name => call.sizesOf (world.last name)
  | none => []

def outputsOf (world : World) (call : Call) (args : List Arg) : List LeanExe.Bytes :=
  (call.outputSizes (reportedOf world call) args).map zeroBytes

theorem outputsOf_sizes (world : World) (call : Call) (args : List Arg) :
    (outputsOf world call args).map (·.data.size) =
      call.outputSizes (reportedOf world call) args := by
  simp [outputsOf, List.map_map, Function.comp_def, zeroBytes_size]

def record (world : World) (call : Call) (outputs : List LeanExe.Bytes) : World :=
  { world with last := fun name => if name = call.name then outputs else world.last name }

def witness : Host World where
  exited world := world.exited
  read world _ reply after := reply = .returned 0 LeanExe.Bytes.empty ∧ after = world
  write world _ _ reply after := reply = .returned 0 0 ∧ after = world
  exit world code after := after = { world with exited := some code }
  exitTrap _ _ _ _ := False
  read_bound h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.zero_le _, show (0 : UInt64).toNat ≤ 76 by decide⟩
  write_bound h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.zero_le _, show (0 : UInt64).toNat ≤ 76 by decide⟩
  read_exited h := by
    obtain ⟨_, rfl⟩ := h
    rfl
  write_exited h := by
    obtain ⟨_, rfl⟩ := h
    rfl
  exit_recorded h := by
    subst h
    rfl
  exitTrap_exited h := h.elim
  sys world call args reply after :=
    reply = .returned 0 (outputsOf world call args) ∧
      after = record world call (outputsOf world call args)
  reported := reportedOf
  sys_bound h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨outputsOf_sizes _ _ _, show (0 : UInt64).toNat ≤ 76 by decide⟩
  sys_exited h := by
    obtain ⟨_, rfl⟩ := h
    rfl
  sys_reports h named := by
    obtain ⟨same, rfl⟩ := h
    injection same with _ outputs
    subst outputs
    simp [reportedOf, named, record]

theorem witness_total : witness.Total where
  read world _ := ⟨.returned 0 LeanExe.Bytes.empty, world, And.intro rfl rfl⟩
  write world _ _ := ⟨.returned 0 0, world, And.intro rfl rfl⟩
  exit world code := .inl ⟨{ world with exited := some code }, rfl⟩

theorem witness_totalFor (calls : List Call) : witness.TotalFor calls where
  toTotal := witness_total
  sys call _ world request _ _ :=
    ⟨.returned 0 (outputsOf world call request), record world call (outputsOf world call request),
      And.intro rfl rfl⟩

theorem witness_noTraps : witness.NoTraps where
  read h := by
    have same := And.left h
    cases same
  write h := by
    have same := And.left h
    cases same
  exitTrap h := h
  sys h := by
    have same := And.left h
    cases same

theorem witness_reporter_bound :
    ∀ world outputs after,
      witness.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        Resource.reportedSize outputs ≤ 3 := by
  intro world outputs after h
  have same := And.left h
  injection same with _ equal
  subst equal
  show Resource.reportedSize ((Call.argsGet.reporterCall.outputSizes [] []).map zeroBytes) ≤ 3
  decide

theorem witness_rule (values : List UInt64) :
    (∀ world trace outcome final, Exec (observedHost witness)
      (SysForm.reported.run Call.argsGet values) world trace outcome final →
        sysCost .reported Call.argsGet values trace ≤ Verified.Bytes.allocationCost 3) ∧
    (∀ world trace residual final, Prefix (observedHost witness)
      (SysForm.reported.run Call.argsGet values) world trace residual final →
        sysCost .reported Call.argsGet values trace ≤ Verified.Bytes.allocationCost 3) :=
  Resource.reported_rule_observed (host := witness) (call := Call.argsGet) (values := values)
    (limit := 3) (budget := Verified.Bytes.allocationCost 3) witness_reporter_bound (Nat.le_refl _)

/-- The reporter's sizes are the sizes of `args_get`'s regions in the world after the reporter. -/
example (world : World) (count size : LeanExe.Bytes) :
    witness.reported (record world Call.argsSizesGet [count, size]) Call.argsGet =
      Call.argsGet.sizesOf [count, size] := by
  simp [witness, reportedOf, record, Call.argsGet, Call.argsSizesGet]

theorem example_satisfiable :
    ∃ targetHost : Wasm.HostEnv (Observed World),
      targetHost.Satisfies Verified.Examples.WasiSys.command.module
        (hostSpecWith witness Verified.Examples.WasiSys.command.sysCalls) :=
  (witness_totalFor _).satisfiableWith _ rfl

theorem example_noTrapsAlong (world : World) :
    witness.NoTrapsAlong
      (Verified.Examples.WasiSys.main.bind fun status => (Action.exit status : Action UInt64))
      world :=
  witness_noTraps.along _ world

end SysWitness

open Lean Elab Command in
elab "check_wasi_sys_witness_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[``SysWitness.witness_totalFor, ``SysWitness.witness_noTraps,
    ``SysWitness.witness_rule, ``SysWitness.example_satisfiable, ``SysWitness.example_noTrapsAlong]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"WASI flat call witness check passed for {theorems.size} theorems"

check_wasi_sys_witness_axioms
