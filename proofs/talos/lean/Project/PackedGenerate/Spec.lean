import Project.PackedGenerate.Entry

namespace Project.PackedGenerate.Spec
open Wasm Project.ProofKit Project.PackedGenerate.Entry

theorem makeWords_exact (env : HostEnv Unit) (initial : Store Unit)
    (count : Nat) (offset : UInt32) (base allocations : UInt64)
    (nodes : List Project.Runtime.FreeNode)
    (hcount : 4 * count ≤ 2^32)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (Project.Runtime.freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 allocations))
    (hList : Project.Runtime.FreeListAt initial.mem nodes)
    (hNone : Project.Runtime.takeFirstFit (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes = none)
    (hFit32 : base.toNat + 48 + PackedCapacity.capacityNat (4 * count) ≤ 2^32)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) ≤
      initial.memoryCap «module» 0) :
    TerminatesWith env «module» 0 initial [.i64 offset.toUInt64, .i64 (UInt64.ofNat count)]
      (fun final values =>
        values = [.i64 (UInt64.ofNat (4 * count)), .i64 (base + 48)] ∧
        PackedMemory.ByteArrayAt final.mem (base + 48).toNat
          (LeanExe.Examples.Packed.makeWords count offset) ∧
        Memory.WritesRange (bufferStore initial base count allocations) final
          (base + 48).toNat ((base + 48).toNat + 4 * count)) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ initial (entryFrame count offset) env
    apply body_spec env initial count offset base allocations nodes hcount
      hGlobal0 hGlobal1 hGlobal2 hList hNone hFit32 hPages hCap
    intro final result hvalues hbytes hwrites
    simpa [func0Def, Function.numParams, hvalues] using And.intro hbytes hwrites

#print axioms makeWords_exact

end Project.PackedGenerate.Spec
