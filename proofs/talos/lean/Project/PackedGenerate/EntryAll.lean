import Project.PackedGenerate.Entry
import Project.ProofKit.PackedAllocation

namespace Project.PackedGenerate.EntryAll
open Wasm Project.ProofKit Project.PackedGenerate.Entry

theorem emitted_allocation : (func0.drop 23).take 15 = PackedAllocation.program 10 := rfl

def bufferStore (initial : Store Unit) (base : UInt64) (count : Nat)
    (allocations : UInt64) (nodes : List Project.Runtime.FreeNode) : Store Unit :=
  FixedArrayAllocateNone.counted
    (PackedAllocation.allocated initial base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes)
    allocations

def outputRoot (base : UInt64) (count : Nat) (nodes : List Project.Runtime.FreeNode) : UInt64 :=
  PackedAllocation.root base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes

theorem body_spec (env : HostEnv Unit) (initial : Store Unit)
    (count : Nat) (offset : UInt32) (base allocations : UInt64)
    (nodes : List Project.Runtime.FreeNode)
    (hcount : 4 * count ≤ 2^32)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (Project.Runtime.freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 allocations))
    (hList : Project.Runtime.FreeListAt initial.mem nodes)
    (hBump : Project.Runtime.takeFirstFitFrom 0
        (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes = none →
      base.toNat + 48 + PackedCapacity.capacityNat (4 * count) ≤ 2^32 ∧
      FixedArrayBump.requiredPages base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) ≤
        initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (Q : Assertion Unit)
    (hDone : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (4 * count)), .i64 (outputRoot base count nodes)] →
      PackedMemory.ByteArrayAt final.mem (outputRoot base count nodes).toNat
        (LeanExe.Examples.Packed.makeWords count offset) →
      Memory.WritesRange (bufferStore initial base count allocations nodes) final
        (outputRoot base count nodes).toNat ((outputRoot base count nodes).toNat + 4 * count) →
      Q (.Fallthrough final result)) :
    wp «module» func0 Q initial (entryFrame count offset) env := by
  have hcapacity := PackedCapacity.capacity_toNat (4 * count) hcount
  have hspace := PackedCapacity.capacityNat_ge (4 * count)
  have hb := PackedAllocation.root_bounds initial base
    (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes hList
    (by intro h; rw [hcapacity]; exact (hBump h).1)
  rw [hcapacity] at hb
  have hfit : (outputRoot base count nodes).toNat + 4 * count ≤ 2^32 := by
    dsimp [outputRoot]
    omega
  have hmemory : (outputRoot base count nodes).toNat + 4 * count ≤
      (bufferStore initial base count allocations nodes).mem.pages * 65536 := by
    dsimp only [bufferStore, FixedArrayAllocateNone.counted, outputRoot]
    omega
  have hsplit : func0 = func0.take 11 ++ (func0.drop 11).take 12 ++
      (func0.drop 23).take 15 ++ func0.drop 38 := rfl
  rw [hsplit]
  simp only [List.append_assoc]
  apply size_prefix env initial count offset hcount
  apply capacity_prefix env initial count offset
  rw [emitted_allocation]
  apply PackedAllocation.program_spec «module» env initial
    [.i64 (UInt64.ofNat count), .i64 offset.toUInt64] (saved count) [] 10 rfl
    base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) 0 0 0 0 0 allocations nodes
    hGlobal0 hGlobal1 hGlobal2 hList
  · intro h
    simpa only [hcapacity, Nat.reducePow] using hBump h
  · exact hPages
  · rfl
  intro previous current capacity next
  have hsetup : func0.drop 38 = [.localGet 15, .localSet 9, .constI64 0, .localSet 3] ++
      (func0.drop 42).take 1 ++ func0.drop 43 := rfl
  rw [hsetup]
  simp only [List.append_assoc]
  simp [wp_simp, FixedArraySearch.frame, saved, -UInt64.ofNat_mul]
  refine Loop.generated_loop_spec env (bufferStore initial base count allocations nodes) _
    (outputRoot base count nodes) count offset ?_ ?_ hfit hmemory (ReturnState count) ?_ ?_ Q _ ?_
  · exact ⟨rfl, rfl, rfl, rfl, by change 3 < 16; decide⟩
  · rfl
  · exact ⟨rfl, rfl, rfl⟩
  · intro next index hvalid h
    exact ⟨(FixedArrayCopy.counterFrame_get_ne _ _ _ _ _ (by decide)).trans h.1,
      (FixedArrayCopy.counterFrame_params_length ..).trans h.2.1,
      (FixedArrayCopy.counterFrame_locals_length ..).trans h.2.2⟩
  intro final result hready _ hreturn hbytes hwrites
  apply return_suffix env final result (outputRoot base count nodes) (UInt64.ofNat (4 * count))
    hreturn.2.1 hreturn.2.2 hready.1 hready.2.2.2.1 hreturn.1
  intro result hvalues
  exact hDone final result hvalues hbytes hwrites

#print axioms body_spec

end Project.PackedGenerate.EntryAll
