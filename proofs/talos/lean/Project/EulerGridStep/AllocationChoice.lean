import Project.EulerGridStep.AllocationPost
import Project.EulerGridStep.FieldIndexing

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The two allocator paths needed by a uniform-size output arena. -/
inductive FieldAllocation where
  | fresh (heapTop allocs : UInt64)
  | reuse (root capacity next allocs : UInt64)

def fieldRequest (count : Nat) : UInt64 := UInt64.ofNat (8 * (count + 1))

def FieldAllocation.root : FieldAllocation → UInt64
  | .fresh heapTop _ => heapTop + 48
  | .reuse root _ _ _ => root

def FieldAllocation.capacity (choice : FieldAllocation) (count : Nat) : UInt64 :=
  match choice with
  | .fresh _ _ => fieldRequest count
  | .reuse _ capacity _ _ => capacity

def FieldAllocation.store (choice : FieldAllocation) (initial : Store Unit) (count : Nat) : Store Unit :=
  match choice with
  | .fresh heapTop allocs => FixedArrayAllocator.allocStore initial heapTop (fieldRequest count) 1 allocs
  | .reuse root capacity next allocs => reuseAllocatedStore initial root capacity next allocs

def FieldAllocation.frame (choice : FieldAllocation) (base : Locals) (count : Nat) : Locals :=
  match choice with
  | .fresh heapTop _ => fieldAllocFrame base heapTop (fieldRequest count)
  | .reuse root capacity next _ => reuseAllocFrame base root capacity next

def FieldAllocation.available (choice : FieldAllocation) (initial : Store Unit) : Prop :=
  match choice with
  | .fresh heapTop allocs =>
      heapTop.toNat + 48 ≤ 4294967296 ∧
      initial.globals.globals[0]? = some (.i64 heapTop) ∧
      initial.globals.globals[1]? = some (.i64 0) ∧
      initial.globals.globals[2]? = some (.i64 allocs)
  | .reuse root capacity next allocs =>
      initial.globals.globals[1]? = some (.i64 root) ∧
      initial.globals.globals[2]? = some (.i64 allocs) ∧
      initial.mem.read64 (root - 32).toUInt32 = capacity ∧
      initial.mem.read64 (root - 8).toUInt32 = next

/-- Physical capacity and separation required for allocating a cloned scalar array. -/
structure FieldAllocation.Valid (choice : FieldAllocation) (initial : Store Unit)
    (source : UInt64) (input : Array UInt64) : Prop where
  available : choice.available initial
  root48 : 48 ≤ choice.root.toNat
  root32 : choice.root.toNat < 4294967296
  enough : 8 * (input.size + 1) ≤ (choice.capacity input.size).toNat
  fit32 : choice.root.toNat + (choice.capacity input.size).toNat ≤ 4294967296
  fitMemory : choice.root.toNat + (choice.capacity input.size).toNat ≤ initial.mem.pages * 65536
  separate : source.toNat + 8 * (input.size + 1) ≤ choice.root.toNat - 48 ∨
    choice.root.toNat + 8 * (input.size + 1) ≤ source.toNat

theorem field_allocation_region (choice : FieldAllocation) (initial : Store Unit)
    (source : UInt64) (input : Array UInt64)
    (hInput : UInt64Array.At initial source input) (hValid : choice.Valid initial source input) :
    AllocatedRegion initial (choice.store initial input.size) source choice.root
      (choice.capacity input.size) input := by
  apply allocatedRegion_of_header_write initial _ source choice.root (choice.capacity input.size)
    input hInput hValid.root48 hValid.root32 hValid.enough hValid.fit32 hValid.fitMemory
    (by have := hValid.separate; omega)
  cases choice with
  | fresh heapTop allocs => exact fresh_alloc_memory initial heapTop _ allocs hValid.available.1
  | reuse root capacity next allocs => exact reused_alloc_memory initial root capacity next allocs

/-- Common exact execution contract for fresh allocation or a sufficient free-list head. -/
theorem field_allocation_spec (choice : FieldAllocation) (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (base : Locals) (source : UInt64) (input : Array UInt64)
    (hValid : choice.Valid initial source input)
    (hParams : base.params.length = 5) (hLocals : base.locals.length = 20)
    (hValues : base.values = []) (hRequest : base.locals[14]? = some (.i64 (fieldRequest input.size)))
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : m.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q (choice.store initial input.size) (choice.frame base input.size) env) :
    wp m (fieldAllocationRegion ++ rest) Q initial base env := by
  have hSize : 8 * (input.size + 1) < UInt64.size := by
    have := hValid.enough
    have := hValid.fit32
    change 8 * (input.size + 1) < 18446744073709551616
    omega
  have hRequestNat : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' hSize
  cases choice with
  | fresh heapTop allocs =>
      rcases hValid.available with ⟨hRoot, hHeap, hFree, hAllocs⟩
      have hFit := hValid.fitMemory
      change (heapTop + 48).toNat + (fieldRequest input.size).toNat ≤ _ at hFit
      rw [Allocation.root_toNat heapTop hRoot] at hFit
      exact field_allocation_bump_spec m env initial base heapTop (fieldRequest input.size) allocs
        hParams hLocals hValues hRequest (by rw [hRequestNat]; omega) hFit hPages hMemory32
        hHeap hFree hAllocs Q rest hNext
  | reuse root capacity next allocs =>
      rcases hValid.available with ⟨hFree, hAllocs, hCapacity, hNextRead⟩
      exact field_allocation_reuse_spec m env initial base root capacity (fieldRequest input.size) next allocs
        hParams hLocals hValues hRequest hFree hAllocs hValid.root48 hValid.root32
        (by have := hValid.fitMemory; change root.toNat + capacity.toNat ≤ _ at this; omega)
        hCapacity hNextRead
        (by change (fieldRequest input.size).toNat ≤ capacity.toNat
            rw [hRequestNat]; exact hValid.enough) Q rest hNext

#print axioms field_allocation_region
#print axioms field_allocation_spec
end Project.EulerGridStep.Execution
