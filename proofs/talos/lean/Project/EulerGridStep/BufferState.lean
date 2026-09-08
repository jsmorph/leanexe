import Project.EulerGridStep.LiveBuffers

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Uniform live/free buffer contents and the runtime counters needed by successive operations. -/
structure BufferState (current : Store Unit) (count : Nat)
    (live : List LiveBuffer) (free : List UInt64) (allocs releases frees : UInt64) : Prop where
  liveAt : LiveBuffers current count live
  chain : FreeChain current count free
  freeHead : current.globals.globals[1]? = some (.i64 (free.headD 0))
  allocations : current.globals.globals[2]? = some (.i64 allocs)
  releases : current.globals.globals[4]? = some (.i64 releases)
  frees : current.globals.globals[5]? = some (.i64 frees)
  pages : current.mem.pages ≤ 65536

theorem BufferState.restrict_live {current : Store Unit} {count : Nat}
    {live : List LiveBuffer} {free : List UInt64} {allocs releases frees : UInt64}
    (hState : BufferState current count live free allocs releases frees)
    (keep : List LiveBuffer) (hKeep : ∀ buffer ∈ keep, buffer ∈ live) :
    BufferState current count keep free allocs releases frees :=
  { hState with liveAt := fun buffer hb => hState.liveAt buffer (hKeep buffer hb) }

/-- Complete field execution advances live/free lists and allocation count together. -/
theorem writeCellField_buffer_state {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (unused source root allocs releases frees : UInt64)
    (input : Array UInt64) (live : List LiveBuffer) (rest : List UInt64)
    (index field : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hi : 1 + 6 * index + field < input.size)
    (hState : BufferState initial input.size live (root :: rest) allocs releases frees)
    (hSource : ObjectsSeparate root input.size source input.size)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate root input.size buffer.root input.size)
    (hFree : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    TerminatesWith env m 27 initial
      [.i64 value, .i64 (UInt64.ofNat field), .i64 (UInt64.ofNat index), .i64 source, .i64 unused]
      (fun final values => values = [.i64 root, .i64 root] ∧
        FieldResult (.reuse root (fieldRequest input.size) (rest.headD 0) allocs)
          initial final source input (1 + 6 * index + field) value ∧
        BufferState final input.size
          (⟨root, input.set! (1 + 6 * index + field) value⟩ :: live) rest
          (allocs + 1) releases frees) := by
  apply (writeCellField_from_free_chain layout env initial unused source root allocs input rest
    index field value hInput hi hState.chain hState.freeHead hState.allocations
    hSource hFree hState.pages).mono
  rintro final values ⟨hValues, hResult, hChain, hGlobals⟩
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨hValues, hResult,
    ⟨hResult.add_live_buffer rfl live hState.liveAt hLive, hChain, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.releases
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.frees
  · rw [hResult.pages]
    exact hState.pages

/-- Complete release preserves the remaining live list and adds the freed buffer to its chain. -/
theorem release_owned_buffer_state {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (root allocs releases frees : UInt64)
    (input : Array UInt64) (live : List LiveBuffer) (rest : List UInt64)
    (hHeader : OwnedHeader initial root (fieldRequest input.size))
    (hArray : UInt64Array.At initial root input)
    (hState : BufferState initial input.size live rest allocs releases frees)
    (hLive : ∀ buffer ∈ live, ObjectsSeparate root input.size buffer.root input.size)
    (hFree : ∀ other ∈ rest, ObjectsSeparate root input.size other input.size) :
    TerminatesWith env m 40 initial [.i64 root]
      (fun final values => values = [] ∧
        ReleaseResult initial final root (fieldRequest input.size) (rest.headD 0) input ∧
        BufferState final input.size live (root :: rest) allocs (releases + 1) (frees + 1)) := by
  apply (release_owned_to_free_chain layout env initial root releases frees input rest hHeader hArray
    hState.chain hState.freeHead hState.releases hState.frees hFree).mono
  rintro final values ⟨hValues, hResult, hChain, hGlobals⟩
  have hGlobalLength := (List.getElem?_eq_some_iff.mp hState.frees).choose
  refine ⟨hValues, hResult,
    ⟨hResult.preserves_live_buffers input.size live hState.liveAt hLive, hChain, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simpa [List.getElem?_set] using hState.allocations
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hGlobals]
    simp (discharger := omega) [List.getElem?_set] <;> omega
  · rw [hResult.pages]
    exact hState.pages

#print axioms BufferState.restrict_live
#print axioms writeCellField_buffer_state
#print axioms release_owned_buffer_state
end Project.EulerGridStep.Execution
