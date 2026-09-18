import Project.Gpt2LinearRows.EntryFrame
import Project.ProofKit.PackedAllocationMemory

namespace Project.Gpt2LinearRows

open Wasm Project.ProofKit PackedMemory

def bufferStore (initial : Store Unit) (base : UInt64) (count : Nat)
    (allocations : UInt64) (nodes : List Project.Runtime.FreeNode) : Store Unit :=
  FixedArrayAllocateNone.counted
    (PackedAllocation.allocated initial base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes)
    allocations

def outputRoot (base : UInt64) (count : Nat) (nodes : List Project.Runtime.FreeNode) : UInt64 :=
  PackedAllocation.root base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes

set_option maxRecDepth 32768 in
theorem body_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat)
    (base allocations : UInt64) (nodes : List Project.Runtime.FreeNode)
    (hweights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hinputSize : rows * inputWidth * 4 ≤ input.size)
    (hweightSize : (weightOffset + inputWidth * outputWidth) * 4 ≤ weights.size)
    (hbiasSize : (biasOffset + outputWidth) * 4 ≤ weights.size)
    (hwidth : inputWidth < UInt64.size) (houtWidth : outputWidth < UInt64.size)
    (hcount : 4 * (rows * outputWidth) ≤ 2^32)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (Project.Runtime.freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 allocations))
    (hList : Project.Runtime.FreeListAt initial.mem nodes)
    (hBump : Project.Runtime.takeFirstFitFrom 0
        (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes = none →
      base.toNat + 48 + PackedCapacity.capacityNat (4 * (rows * outputWidth)) ≤ 2^32 ∧
      FixedArrayBump.requiredPages base (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) ≤
        initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hweightsBelow : weightsPtr.toNat + weights.size ≤ base.toNat)
    (hinputBelow : inputPtr.toNat + input.size ≤ base.toNat)
    (hweightsSep : ∀ node ∈ nodes, weightsPtr.toNat + weights.size ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ weightsPtr.toNat)
    (hinputSep : ∀ node ∈ nodes, inputPtr.toNat + input.size ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ inputPtr.toNat)
    (Q : Assertion Unit)
    (hdone : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (4 * (rows * outputWidth))), .i64 (outputRoot base (rows * outputWidth) nodes)] →
      ByteArrayAt final.mem (outputRoot base (rows * outputWidth) nodes).toNat
        (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inputWidth outputWidth rows) →
      Memory.WritesRange (bufferStore initial base (rows * outputWidth) allocations nodes) final
        (outputRoot base (rows * outputWidth) nodes).toNat
        ((outputRoot base (rows * outputWidth) nodes).toNat + 4 * (rows * outputWidth)) →
      Q (.Fallthrough final result)) :
    wp «module» func1 Q initial
      (entryFrame (parameters weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows)) env := by
  have hcapacity := PackedCapacity.capacity_toNat (4 * (rows * outputWidth)) hcount
  have hspace := PackedCapacity.capacityNat_ge (4 * (rows * outputWidth))
  have hbump : Project.Runtime.takeFirstFitFrom 0
      (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes = none →
      base.toNat + 48 ≤ 4294967296 := by
    intro h
    have := (hBump h).1
    omega
  have hb := PackedAllocation.root_bounds initial base
    (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes hList
    (by intro h; rw [hcapacity]; exact (hBump h).1)
  rw [hcapacity] at hb
  have hfit : (outputRoot base (rows * outputWidth) nodes).toNat + 4 * (rows * outputWidth) ≤ 2^32 := by
    dsimp [outputRoot]
    omega
  have hmemory : (outputRoot base (rows * outputWidth) nodes).toNat + 4 * (rows * outputWidth) ≤
      (bufferStore initial base (rows * outputWidth) allocations nodes).mem.pages * 65536 := by
    dsimp only [bufferStore, FixedArrayAllocateNone.counted, outputRoot]
    omega
  have hweightBytes : ByteArrayAt (bufferStore initial base (rows * outputWidth) allocations nodes).mem
      weightsPtr.toNat weights :=
    PackedAllocation.byteArrayAt initial base _ nodes _ weights hweights hList hbump hweightsBelow hweightsSep
  have hinputBytes : ByteArrayAt (bufferStore initial base (rows * outputWidth) allocations nodes).mem
      inputPtr.toNat input :=
    PackedAllocation.byteArrayAt initial base _ nodes _ input hinput hList hbump hinputBelow hinputSep
  have hweightDisjoint := PackedAllocation.root_disjoint initial base
    (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes weightsPtr.toNat
    (weightsPtr.toNat + weights.size) hList hbump hweightsBelow hweightsSep
  have hinputDisjoint := PackedAllocation.root_disjoint initial base
    (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes inputPtr.toNat
    (inputPtr.toNat + input.size) hList hbump hinputBelow hinputSep
  rw [hcapacity] at hweightDisjoint hinputDisjoint
  have hsplit : func1 = func1.take 18 ++ (func1.drop 18).take 12 ++
      (func1.drop 30).take 15 ++ func1.drop 45 := rfl
  rw [hsplit]
  simp only [List.append_assoc]
  apply size_prefix env initial _ rows outputWidth rfl rfl rfl hcount
  apply capacity_prefix env initial _ rows outputWidth rfl
  rw [emitted_allocation]
  apply PackedAllocation.program_spec «module» env initial
    (parameters weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows)
    (saved (rows * outputWidth)) (List.replicate 8 (.i64 0)) 43 rfl
    base (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth))))
    (UInt64.ofNat outputWidth) 0 0 0 0 allocations nodes hGlobal0 hGlobal1 hGlobal2 hList
  · intro h
    simpa only [hcapacity, Nat.reducePow] using hBump h
  · exact hPages
  · rfl
  intro previous current capacity next
  have hsetup : func1.drop 45 = [.localGet 48, .localSet 42, .constI64 0, .localSet 10] ++
      (func1.drop 49).take 1 ++ func1.drop 50 := rfl
  rw [hsetup]
  simp only [List.append_assoc]
  simp [wp_simp, FixedArraySearch.frame, saved, parameters, -UInt64.ofNat_mul]
  apply generated_loop_spec env (bufferStore initial base (rows * outputWidth) allocations nodes)
    weightsPtr inputPtr (outputRoot base (rows * outputWidth) nodes) weights input
    weightOffset biasOffset inputWidth outputWidth rows _ hweightBytes hinputBytes
    hinputSize hweightSize hbiasSize hwidth houtWidth hfit hmemory
  · dsimp [outputRoot]
    omega
  · dsimp [outputRoot]
    omega
  · exact ⟨rfl, rfl, rfl, rfl, by change 10 < 57; decide⟩
  · simp [OutputState, parameters, -UInt64.ofNat_mul]
  intro final result hready hstate hbytes hwrites
  apply return_suffix env final result (outputRoot base (rows * outputWidth) nodes)
    (UInt64.ofNat (4 * (rows * outputWidth)))
    (by rw [hstate.1]; rfl) hstate.2.1 hready.1 hready.2.2.2.1 hstate.2.2
  intro result hvalues
  exact hdone final result hvalues hbytes hwrites

#print axioms body_spec

end Project.Gpt2LinearRows
