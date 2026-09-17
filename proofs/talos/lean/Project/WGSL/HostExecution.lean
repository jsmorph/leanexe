import Project.WGSL.HostBinary
import Project.WGSL.HostMemory
import Project.WGSL.Package
import Interpreter.Wasm.SmallStep

namespace Project.WGSL.HostExecution

open LeanExe.WGSL Wasm Wasm.SmallStep HostMemory Binary32 CodeLib.IEEE32

def input (config : GemmConfig) (memory : Mem) (a b : UInt32) : Dispatch.Input :=
  { buffers := {
      a := words (upload memory a.toNat (4 * config.elementsA))
      b := words (upload memory b.toNat (4 * config.elementsB))
      sizeA := config.elementsA, sizeB := config.elementsB, sizeC := config.elementsC }
    initialC := fun _ => 0x7fc00001 }

theorem input_valid (config : GemmConfig) (memory : Mem) (a b : UInt32) :
    (input config memory a b).buffers.Valid config := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- The native harness has explicit resource caps. Memory regions may overlap:
both inputs are snapshotted before any output bytes are written. -/
def Ready (config : GemmConfig) (memory : Mem) (a b c : UInt32) : Prop :=
  Fits memory a config.elementsA ∧ Fits memory b config.elementsB ∧ Fits memory c config.elementsC ∧
    config.elementsA ≤ 16384 ∧ config.elementsB ≤ 16384 ∧ config.elementsC ≤ 16384 ∧
    config.rows * config.cols * config.inner ≤ 262144

/-- Explicit foreign-runtime assumption: the import executes the checked WGSL
dispatch on byte-for-byte input snapshots, waits for completion, then copies
the result bytes back. This is a contract, not a proof of the native driver. -/
def contract {source metadata} (package : Package source metadata) : HostContract Unit :=
  fun st args result => ∀ a b c, args = [.i32 a, .i32 b, .i32 c] →
    Ready package.kernel.ast.config st.mem a b c →
    ∃ buffer : Nat → UInt8,
      (Dispatch.model semantics).Exec package.tag.profile package.kernel
        (input package.kernel.ast.config st.mem a b) (words buffer) ∧
      result = .Return [.i32 0] { st with
        mem := download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer }

def spec {source metadata} (package : Package source metadata) : HostSpec Unit :=
  { contracts := [contract package] }

def initial (env : HostEnv Unit) (st : Store Unit) (a b c : UInt32) : Config Unit :=
  { expr := .running {
      locals := { params := [.i32 a, .i32 b, .i32 c] }
      code := HostBinary.module.funcs[0]!.body
      resultArity := 1
      callerRemainder := [] }
    store := {
      runtime := { instances := #[{ module := HostBinary.module, host := env }], entry := ⟨0⟩ }
      wasm := st } }

private theorem import_exists : 0 < HostBinary.module.imports.length := by decide +kernel

theorem completes {source metadata} (package : Package source metadata)
    (env : HostEnv Unit) (conforms : env.Satisfies HostBinary.module (spec package))
    (st : Store Unit) (a b c : UInt32) (ready : Ready package.kernel.ast.config st.mem a b c) :
    ∃ buffer : Nat → UInt8,
      (Dispatch.model semantics).Exec package.tag.profile package.kernel
        (input package.kernel.ast.config st.mem a b) (words buffer) ∧
      TerminatesWith (initial env st a b c) (fun values store =>
        values = [.i32 0] ∧ store.wasm = { st with
          mem := download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer }) := by
  obtain ⟨hostFunction, hhost, hcontract⟩ := conforms.lookup_contract
    (i := 0) import_exists (c := contract package) rfl
  obtain ⟨buffer, run, invoke⟩ := hcontract st [.i32 a, .i32 b, .i32 c] a b c rfl ready
  refine ⟨buffer, run, ?_⟩
  let finish : MachineStore Unit := { (initial env st a b c).store with
    wasm := { st with mem := download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer } }
  refine ⟨[.instruction (.localGet 0), .instruction (.localGet 1), .instruction (.localGet 2),
    .host 0, .administrative .finish], [.i32 0], finish, ?_, rfl, rfl⟩
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.localGet (by rfl))
  apply Steps.cons (Step.callHostReturn import_exists rfl hhost invoke)
  exact Steps.cons .finish (Steps.refl _)

/-- Final Wasm memory contains the shader's matrix result. The statement uses
the actual small-step host call, exact bridge bytes, and checked WGSL package. -/
theorem exact {source metadata} (package : Package source metadata)
    (restrictedTag : package.tag = .separate)
    (env : HostEnv Unit) (conforms : env.Satisfies HostBinary.module (spec package))
    (st : Store Unit) (a b c : UInt32) (ready : Ready package.kernel.ast.config st.mem a b c) :
    HostBinary.Encodes ∧ TerminatesWith (initial env st a b c) (fun values store =>
      values = [.i32 0] ∧ store.wasm.mem.pages = st.mem.pages ∧
      (∀ address, address < c.toNat ∨ c.toNat + 4 * package.kernel.ast.config.elementsC ≤ address →
        store.wasm.mem.bytes address = st.mem.bytes address) ∧
      ∀ row col, row < package.kernel.ast.config.rows → col < package.kernel.ast.config.cols →
        store.wasm.mem.read32 (UInt32.ofNat (c.toNat + 4 * (row * package.kernel.ast.config.cols + col))) =
          gemmCell arithmetic package.kernel.ast.config
            (input package.kernel.ast.config st.mem a b).buffers.a
            (input package.kernel.ast.config st.mem a b).buffers.b row col) := by
  refine ⟨HostBinary.encoded, ?_⟩
  obtain ⟨buffer, run, terminates⟩ := completes package env conforms st a b c ready
  apply terminates.mono
  intro values store result
  rcases result with ⟨hv, hs⟩
  rw [hs]
  refine ⟨hv, rfl, ?_, ?_⟩
  · intro address outside
    exact download_outside _ _ _ _ outside
  · intro row col hr hc
    change (download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer).read32
      (UInt32.ofNat (c.toNat + 4 * (row * package.kernel.ast.config.cols + col))) = _
    rw [word_address (download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer)
      c ready.2.2.1 (Index.linear_lt hr hc)]
    rw [download_word st.mem c buffer (elements := package.kernel.ast.config.elementsC) (Index.linear_lt hr hc)]
    exact package.exact restrictedTag _ _ (input_valid ..) run hr hc

theorem numerical {source metadata} (package : Package source metadata)
    (env : HostEnv Unit) (conforms : env.Satisfies HostBinary.module (spec package))
    (st : Store Unit) (a b c : UInt32) (ready : Ready package.kernel.ast.config st.mem a b c) :
    HostBinary.Encodes ∧ TerminatesWith (initial env st a b c) (fun values store =>
      values = [.i32 0] ∧
      ∀ row col, row < package.kernel.ast.config.rows → col < package.kernel.ast.config.cols →
      ∀ budget : ℝ, DotDomain package.kernel.ast.config
        (input package.kernel.ast.config st.mem a b).buffers.a
        (input package.kernel.ast.config st.mem a b).buffers.b row col budget →
      let result := store.wasm.mem.read32
        (UInt32.ofNat (c.toNat + 4 * (row * package.kernel.ast.config.cols + col)))
      Finite result ∧ |value result - realDot package.kernel.ast.config
        (input package.kernel.ast.config st.mem a b).buffers.a
        (input package.kernel.ast.config st.mem a b).buffers.b row col package.kernel.ast.config.inner| ≤
          2 * package.kernel.ast.config.inner * arithmeticEpsilon) := by
  refine ⟨HostBinary.encoded, ?_⟩
  obtain ⟨buffer, run, terminates⟩ := completes package env conforms st a b c ready
  apply terminates.mono
  intro values store result
  rcases result with ⟨hv, hs⟩
  refine ⟨hv, ?_⟩
  intro row col hr hc budget domain
  rw [hs]
  change Finite ((download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer).read32 _) ∧ _
  rw [word_address (download st.mem c.toNat (4 * package.kernel.ast.config.elementsC) buffer)
    c ready.2.2.1 (Index.linear_lt hr hc)]
  rw [download_word st.mem c buffer (elements := package.kernel.ast.config.elementsC) (Index.linear_lt hr hc)]
  exact package.numerical _ _ (input_valid ..) run hr hc domain

#print axioms completes
#print axioms exact
#print axioms numerical

end Project.WGSL.HostExecution
