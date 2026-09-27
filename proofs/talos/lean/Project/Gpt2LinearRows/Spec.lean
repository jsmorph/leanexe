import Project.Gpt2LinearRows.Entry

namespace Project.Gpt2LinearRows.Spec

open Wasm Project.ProofKit PackedMemory

theorem linearRows_exact (env : HostEnv Unit) (initial : Store Unit)
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
    (hfreeBelow : ∀ node ∈ nodes, node.root.toNat + node.capacity.toNat ≤ base.toNat) :
    TerminatesWith env «module» 1 initial
      [.i64 (UInt64.ofNat rows), .i64 (UInt64.ofNat outputWidth), .i64 (UInt64.ofNat inputWidth),
        .i64 (UInt64.ofNat biasOffset), .i64 (UInt64.ofNat weightOffset),
        .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 (UInt64.ofNat weights.size), .i64 weightsPtr]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * (rows * outputWidth))), .i64 (outputRoot base (rows * outputWidth) nodes)] ∧
        ByteArrayAt final.mem (outputRoot base (rows * outputWidth) nodes).toNat
          (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inputWidth outputWidth rows) ∧
        ByteArrayAt final.mem inputPtr.toNat input ∧
        ByteArrayAt final.mem weightsPtr.toNat weights ∧
        Project.Runtime.FreeListAt final.mem
          (PackedAllocation.remaining (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes) ∧
        Memory.WritesRange (bufferStore initial base (rows * outputWidth) allocations nodes) final
          (outputRoot base (rows * outputWidth) nodes).toNat
          ((outputRoot base (rows * outputWidth) nodes).toNat + 4 * (rows * outputWidth))) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    (entryFrame (parameters weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows)) env
  apply body_spec env initial weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows
    base allocations nodes hweights hinput hinputSize hweightSize hbiasSize hwidth houtWidth hcount
    hGlobal0 hGlobal1 hGlobal2 hList hBump hPages hweightsBelow hinputBelow hweightsSep hinputSep
  intro final result hvalues hbytes hwrites
  have hcapacity := PackedCapacity.capacity_toNat (4 * (rows * outputWidth)) hcount
  have hspace := PackedCapacity.capacityNat_ge (4 * (rows * outputWidth))
  have hbump : Project.Runtime.takeFirstFitFrom 0
      (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))) nodes = none →
      base.toNat + 48 ≤ 4294967296 := by
    intro h
    have := (hBump h).1
    omega
  have hwritesCapacity := hwrites.mono (Nat.le_refl _)
    (show (outputRoot base (rows * outputWidth) nodes).toNat + 4 * (rows * outputWidth) ≤
      (outputRoot base (rows * outputWidth) nodes).toNat +
        (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))).toNat by rw [hcapacity]; omega)
  have hinputFinal := PackedAllocation.byteArrayAt_after_writes initial final base _ allocations
    nodes _ input hinput hList hbump hinputBelow hinputSep hwritesCapacity
  have hweightsFinal := PackedAllocation.byteArrayAt_after_writes initial final base _ allocations
    nodes _ weights hweights hList hbump hweightsBelow hweightsSep hwritesCapacity
  have hfreeFinal := PackedAllocation.freeListAt_after_writes initial final base _ allocations
    nodes hList hbump hfreeBelow hwritesCapacity
  have hpost := And.intro hbytes (And.intro hinputFinal
    (And.intro hweightsFinal (And.intro hfreeFinal hwrites)))
  simpa [func1Def, Function.numParams, hvalues, -UInt64.ofNat_mul] using hpost

#print axioms linearRows_exact

end Project.Gpt2LinearRows.Spec
