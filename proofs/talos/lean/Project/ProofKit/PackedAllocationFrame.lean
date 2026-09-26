import Project.ProofKit.PackedAllocation
import Project.ProofKit.I64Frame

namespace Project.ProofKit.PackedAllocation
open Wasm Project.Runtime

def allocatedFrame (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame frame.params (frame.locals.take (start - frame.params.length))
    (frame.locals.drop (start - frame.params.length + 6)) need previous current capacity next result

theorem allocatedFrame_typed (frame : Locals) (start : Nat)
    (need previous current capacity next result : UInt64) (hTyped : I64Values frame.locals) :
    I64Values (allocatedFrame frame start need previous current capacity next result).locals := by
  simp (config := { maxDischargeDepth := 64 }) only [allocatedFrame, FixedArraySearch.frame,
    List.cons_append, List.nil_append, I64Values.append, I64Values.cons,
    I64Values.take, I64Values.drop, hTyped]

theorem program_spec_frame_available (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (start : Nat) (base need count : UInt64) (nodes : List FreeNode)
    (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hLower : frame.params.length ≤ start)
    (hBound : start + 6 ≤ frame.params.length + frame.locals.length)
    (hNeed : frame.get start = some (.i64 need))
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages base need →
        FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0))
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64, wp module_ rest Q
      (FixedArrayAllocateNone.counted (allocated store base need nodes) count)
      (allocatedFrame frame start need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start ++ rest) Q store frame env := by
  obtain ⟨previous, current, capacity, next, result, hFrame⟩ := Frame.exists_allocator hValues hTyped
    (start - frame.params.length) need (by omega) (by
      rw [Nat.add_sub_of_le hLower]
      exact hNeed)
  have hStart : frame.params.length + (frame.locals.take (start - frame.params.length)).length = start := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
    omega
  have hProgram := program_spec_available module_ env store frame.params
    (frame.locals.take (start - frame.params.length)) (frame.locals.drop (start - frame.params.length + 6))
    start hStart base need previous current capacity next result count nodes
    hGlobal0 hGlobal1 hGlobal2 hList hBump hPages hMemory32 Q rest hNext
  rwa [← hFrame] at hProgram

theorem program_spec_frame (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (start : Nat) (base need count : UInt64) (nodes : List FreeNode)
    (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hLower : frame.params.length ≤ start)
    (hBound : start + 6 ≤ frame.params.length + frame.locals.length)
    (hNeed : frame.get start = some (.i64 need))
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64, wp module_ rest Q
      (FixedArrayAllocateNone.counted (allocated store base need nodes) count)
      (allocatedFrame frame start need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start ++ rest) Q store frame env := by
  exact program_spec_frame_available module_ env store frame start base need count nodes hValues hTyped
    hLower hBound hNeed hGlobal0 hGlobal1 hGlobal2 hList
    (fun h => ⟨(hBump h).1, fun _ => (hBump h).2⟩) hPages hMemory32 Q rest hNext

#print axioms program_spec_frame_available

#print axioms allocatedFrame_typed
#print axioms program_spec_frame

end Project.ProofKit.PackedAllocation
