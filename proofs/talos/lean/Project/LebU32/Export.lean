import Project.LebU32.Entry

namespace Project.LebU32.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def OutputAt (seed : Heap) (initial : Store Unit) (input : UInt64) (final : Store Unit)
    (values : List Value) : Prop :=
  ∃ bytes,
    bytes.data.toList = lebList 10 input ∧
    values = [.i64 (UInt64.ofNat (lebList 10 input).length), .i64 (bytePointer seed (lebList 10 input).length)] ∧
    FinishedStorage seed initial final (lebList 10 input).length bytes

theorem u32lebU64_correct (env : HostEnv Unit) (initial : Store Unit) (seed : Heap) (input : UInt64)
    (hInput : input.toNat < 4294967296) (hHeap : seed.At initial) (hNodes : seed.nodes = [])
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0) :
    TerminatesWith env «module» 1 initial [.i64 input] (OutputAt seed initial input) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_ (by decide)
  change wp «module» func1 _ initial
    { params := [.i64 input], locals := List.replicate 11 (.i64 0), values := [] } env
  unfold func1
  wp_run
  apply wp_call_tw (func0_encodes env initial seed input hInput hHeap hNodes hFit hMemory hPages hCap)
  rintro final values ⟨bytes, hBytes, rfl, hStorage⟩
  wp_run
  exact ⟨bytes, hBytes, by simp [func1Def], hStorage⟩

def initialHeap : Heap :=
  { top := 4096, nodes := [], allocations := 0, retains := 0, releases := 0, frees := 0 }

theorem u32leb_initial_correct (env : HostEnv Unit) (input : UInt64)
    (hInput : input.toNat < 4294967296) :
    TerminatesWith env «module» 1 («module».initialStore (α := Unit)) [.i64 input]
      (OutputAt initialHeap («module».initialStore (α := Unit)) input) := by
  apply u32lebU64_correct env _ initialHeap input hInput
  · exact ⟨rfl, .nil, by simp [initialHeap]⟩
  · rfl
  · decide
  · decide
  · decide
  · decide

#print axioms u32lebU64_correct
#print axioms u32leb_initial_correct
end Project.LebU32.Spec
