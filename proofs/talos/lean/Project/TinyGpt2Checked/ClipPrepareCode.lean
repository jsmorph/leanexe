import Project.TinyGpt2Checked.ClipMap
import Project.F64Clip.AllocationMemory
import Project.ProofKit.FixedArrayReuse

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.F64Clip.Spec

def finishOwnedProgram (root saved : Nat) : Wasm.Program :=
  [.localGet root, .localSet saved, .localGet saved, .localSet 15, .localGet saved, .localSet 16]

def acceptProgram : Wasm.Program :=
  [.localGet 3, .localSet 17, .localGet 17, .wrapI64, .load64 0, .localSet 18] ++
  FixedArrayCapacity.localProgram 18 1 23 ++
  FixedArrayAllocateNone.program 23 (FixedArrayReuse.program 23 1) 1 ++
  [.localGet 28, .localSet 19] ++ FixedArrayResult.lengthStoreLocalProgram 19 18 ++
  [.constI64 0, .localSet 20, .block 0 0 [.loop 0 0 mapBody]] ++
  finishOwnedProgram 19 13

def rejectProgram : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 21 ++
  FixedArrayAllocateNone.program 21 (FixedArrayReuse.program 21 1) 1 ++
  [.localGet 26, .localSet 17] ++ FixedArrayResult.lengthStoreProgram 17 0 ++
  finishOwnedProgram 17 14

theorem prepare_shape : func6 = func6.take 21 ++
    [.iff 0 0 acceptProgram rejectProgram, .localGet 15, .localGet 16] := rfl

def prepareFrame (count bound owner ptr ok : UInt64) : Locals :=
  { params := [.i64 count, .i64 bound, .i64 owner, .i64 ptr]
    locals := [.i64 count, .i64 bound, .i64 owner, .i64 ptr, .i64 ok] ++ List.replicate 20 (.i64 0)
    values := [] }

def prepareResult (initial : Store Unit) (ptr base allocations : UInt64)
    (input output : Array UInt64) : AssertionF Unit := fun final frame =>
  frame.get 15 = some (.i64 (base+48)) ∧ frame.get 16 = some (.i64 (base+48)) ∧ frame.values = [] ∧
  UInt64Array.At final (base+48) output ∧ UInt64Array.At final ptr input ∧
  final.mem.pages = initial.mem.pages ∧
  Memory.WritesRange (clipInitialize initial base output.size allocations) final
    (base+48).toNat ((base+48).toNat+8*(output.size+1))

def acceptAllocationFrame (count bound owner ptr : UInt64) (size : Nat)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 owner, .i64 ptr]
    (mapFrame count bound owner ptr 0 size 0 0 0 0 []).locals [] need previous current capacity next result

def rejectSaved (count bound owner ptr : UInt64) : List Value :=
  [.i64 count, .i64 bound, .i64 owner, .i64 ptr, .i64 0] ++ List.replicate 12 (.i64 0)

def rejectAllocationFrame (count bound owner ptr : UInt64)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 owner, .i64 ptr]
    (rejectSaved count bound owner ptr)
    [.i64 0, .i64 0] need previous current capacity next result

#print axioms prepare_shape
end Project.TinyGpt2Checked.Spec
