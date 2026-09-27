import Project.Core.Memory
import Project.Core.Correctness

namespace Project.Core.MemoryRuntime

open Wasm
open Project.ProofKit.ScalarTransition (State)

def code (count operation : Nat) : Wasm.Program := [.call (count + operation)]

def growFunction : Wasm.Function := { MemoryGrow.growFunction with typeIdx := some 1 }

def runtimeFunctions : List Wasm.Function :=
  [Memory.readFunction, Memory.writeFunction, Memory.sizeFunction, growFunction]

def memoryDeclaration : Wasm.MemDecl :=
  { pagesMin := 16, pagesMax := some 65536 }

def types (source : LeanExe.Core.Module) : List Wasm.FuncType :=
  (List.range (max (maxParams source) 2 + 1)).map functionSignature

/-- Compiled source functions and four concrete native-memory primitives. -/
def memoryModule (source : LeanExe.Core.Module) : Wasm.Module :=
  let base := Project.Core.compile source (code source.length) (memory := some memoryDeclaration)
  { base with
    funcs := base.funcs ++ runtimeFunctions
    types := types source
    gcTypes := (types source).map (fun type => { comp := .func type }) }

def represents (source : LeanExe.Core.Module) (bytes : ByteArray) (store : Store α) : Prop :=
  MemoryGrow.MemoryAt bytes store.mem ∧ store.memoryCap (memoryModule source) 0 = 65536

theorem source_lookup (source : LeanExe.Core.Module) (index : Nat) (function : LeanExe.Core.Function)
    (found : source[index]? = some function) :
    (memoryModule source).funcs[index]? = some (compileFunction 0 (code source.length) function) := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  change (source.map (compileFunction 0 (code source.length)) ++ runtimeFunctions)[index]? = _
  rw [List.getElem?_append_left (by simpa using bound), List.getElem?_map, found]
  rfl

theorem runtime_lookup (source : LeanExe.Core.Module) (operation : Nat) (function : Wasm.Function)
    (found : runtimeFunctions[operation]? = some function) :
    (memoryModule source).funcs[source.length + operation]? = some function := by
  simp [memoryModule, Project.Core.compile, List.getElem?_append_right, found]

theorem write_cap (source : LeanExe.Core.Module) (store : Store α) (address value : UInt64) :
    (Memory.writeStore store address value).memoryCap (memoryModule source) 0 =
      store.memoryCap (memoryModule source) 0 := by
  unfold Memory.writeStore
  split <;> rfl

theorem grow_cap (source : LeanExe.Core.Module) (store : Store α) (delta : UInt64) (cap : Nat) :
    (MemoryGrow.growStore store delta cap).memoryCap (memoryModule source) 0 =
      store.memoryCap (memoryModule source) 0 := by
  unfold MemoryGrow.growStore
  split <;> rfl

private theorem terminates_mono {module_ : Wasm.Module} {host : HostEnv α}
    {callee : Nat} {initial : Store α} {args : List Value}
    {P Q : Store α → List Value → Prop}
    (executed : TerminatesWith host module_ callee initial args P)
    (weaken : ∀ final values, P final values → Q final values) :
    TerminatesWith host module_ callee initial args Q := by
  obtain ⟨N, executed⟩ := executed
  refine ⟨N, ?_⟩
  intro fuel enough
  obtain ⟨values, final, ran, post⟩ := executed fuel enough
  exact ⟨values, final, ran, weaken final values post⟩

theorem read_correct (source : LeanExe.Core.Module) (host : HostEnv α) (store : Store α)
    (bytes : ByteArray) (address : UInt64) (represented : represents source bytes store) :
    TerminatesWith host (memoryModule source) (source.length + 0) store [.i64 address]
      (fun final values => represents source (LeanExe.Core.Memory.read address bytes).2 final ∧
        values = [.i64 (LeanExe.Core.Memory.read address bytes).1]) := by
  have executed := Memory.read_terminates host store bytes address
    (module_ := memoryModule source) (id := source.length + 0) rfl
    (by simpa [memoryModule, Project.Core.compile] using
      runtime_lookup source 0 Memory.readFunction rfl)
    represented.1.toBytesAt rfl
  apply terminates_mono executed
  rintro final values ⟨rfl, result⟩
  exact ⟨represented, result⟩

theorem write_correct (source : LeanExe.Core.Module) (host : HostEnv α) (store : Store α)
    (bytes : ByteArray) (address byte : UInt64) (represented : represents source bytes store) :
    TerminatesWith host (memoryModule source) (source.length + 1) store [.i64 byte, .i64 address]
      (fun final values => represents source (LeanExe.Core.Memory.write address byte bytes).2 final ∧
        values = [.i64 (LeanExe.Core.Memory.write address byte bytes).1]) := by
  have executed := Memory.write_terminates host store bytes address byte
    (module_ := memoryModule source) (id := source.length + 1) rfl
    (by simpa [memoryModule, Project.Core.compile] using
      runtime_lookup source 1 Memory.writeFunction rfl) represented.1 rfl
  apply terminates_mono executed
  rintro final values ⟨⟨rfl, memory⟩, result⟩
  exact ⟨⟨memory, (write_cap source store address byte).trans represented.2⟩, result⟩

theorem size_correct (source : LeanExe.Core.Module) (host : HostEnv α) (store : Store α)
    (bytes : ByteArray) (represented : represents source bytes store) :
    TerminatesWith host (memoryModule source) (source.length + 2) store []
      (fun final values => represents source (LeanExe.Core.Memory.size bytes).2 final ∧
        values = [.i64 (LeanExe.Core.Memory.size bytes).1]) := by
  have executed := Memory.size_terminates host store bytes
    (module_ := memoryModule source) (id := source.length + 2) rfl
    (by simpa [memoryModule, Project.Core.compile] using
      runtime_lookup source 2 Memory.sizeFunction rfl) represented.1.toBytesAt rfl
  apply terminates_mono executed
  rintro final values ⟨rfl, result⟩
  exact ⟨represented, result⟩

theorem grow_correct (source : LeanExe.Core.Module) (host : HostEnv α) (store : Store α)
    (bytes : ByteArray) (delta : UInt64) (represented : represents source bytes store) :
    TerminatesWith host (memoryModule source) (source.length + 3) store [.i64 delta]
      (fun final values => represents source (LeanExe.Core.Memory.grow delta bytes).2 final ∧
        values = [.i64 (LeanExe.Core.Memory.grow delta bytes).1]) := by
  apply invoke_of_wp (args := [delta]) (function := growFunction) rfl
    (by simpa [memoryModule, Project.Core.compile] using runtime_lookup source 3 growFunction rfl) rfl rfl
  apply MemoryGrow.grow_body_wp (memoryModule source) host store bytes delta represented.1
    (by rw [represented.2])
  refine ⟨MemoryGrow.growStore store delta (store.memoryCap (memoryModule source) 0),
    MemoryGrow.resultFrame delta
      (LeanExe.Core.Memory.nativeGrow bytes delta (store.memoryCap (memoryModule source) 0)).1,
    rfl, ⟨?_, ?_⟩, ?_⟩
  · simpa [LeanExe.Core.Memory.grow, represented.2] using
      MemoryGrow.nativeGrow_represents represented.1 delta
        (store.memoryCap (memoryModule source) 0) (by rw [represented.2])
  · exact (grow_cap source store delta _).trans represented.2
  · simp [MemoryGrow.resultFrame, LeanExe.Core.Memory.grow, represented.2]

theorem effect_correct (source : LeanExe.Core.Module) (host : HostEnv α)
    (operation : Nat) (args : List UInt64) (initial : ByteArray) (value : UInt64) (final : ByteArray)
    (performed : LeanExe.Core.Memory.effects operation args initial value final)
    (store : Store α) (frame : State) (represented : represents source initial store)
    (rest : Wasm.Program) (Q : Assertion α)
    (next : ∀ nextStore, represents source final nextStore →
      wp (memoryModule source) rest Q nextStore (frame.toLocals [.i64 value]) host) :
    wp (memoryModule source) (code source.length operation ++ rest) Q store
      (frame.toLocals (args.map Value.i64).reverse) host := by
  cases performed with
  | @read address initial value final computed =>
      have executed := read_correct source host store initial address represented
      rw [computed] at executed
      apply wp_call_tw (by simpa using executed)
      rintro nextStore values ⟨nextRep, rfl⟩
      exact next nextStore nextRep
  | @write address byte initial value final computed =>
      have executed := write_correct source host store initial address byte represented
      rw [computed] at executed
      apply wp_call_tw (by simpa using executed)
      rintro nextStore values ⟨nextRep, rfl⟩
      exact next nextStore nextRep
  | @size initial value final computed =>
      have executed := size_correct source host store initial represented
      rw [computed] at executed
      apply wp_call_tw (by simpa using executed)
      rintro nextStore values ⟨nextRep, rfl⟩
      exact next nextStore nextRep
  | @grow delta initial value final computed =>
      have executed := grow_correct source host store initial delta represented
      rw [computed] at executed
      apply wp_call_tw (by simpa using executed)
      rintro nextStore values ⟨nextRep, rfl⟩
      exact next nextStore nextRep

def context (source : LeanExe.Core.Module) (host : HostEnv α) : Context ByteArray α where
  source := source
  effects := LeanExe.Core.Memory.effects
  target := memoryModule source
  host := host
  effectCode := code source.length
  represents := represents source
  functions := source_lookup source
  effectCorrect := effect_correct source host

/-- Native byte-array effects, arbitrary core control and recursive calls all
execute in the compiler's concrete Talos module. -/
theorem correct (source : LeanExe.Core.Module) (host : HostEnv α)
    (executed : LeanExe.Core.Invokes source LeanExe.Core.Memory.effects
      callee initial args final value)
    (store : Store α) (represented : represents source initial store) :
    TerminatesWith host (memoryModule source) callee store (args.map Value.i64).reverse
      (fun next values => represents source final next ∧ values = [.i64 value]) := by
  simpa only [context, memoryModule, Project.Core.compile, List.length_nil, Nat.zero_add] using
    invocation_correct (context source host) executed store represented

end Project.Core.MemoryRuntime
