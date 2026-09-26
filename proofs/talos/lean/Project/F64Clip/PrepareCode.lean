import Project.F64Clip.Map
import Project.F64Clip.AllocationMemory
import Project.ProofKit.FixedArrayReuse

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit

def acceptProgram : Wasm.Program :=
  [.localGet 2, .localSet 16, .localGet 16, .wrapI64, .load64 0, .localSet 17] ++
  FixedArrayCapacity.localProgram 17 1 22 ++
  FixedArrayAllocateNone.program 22 (FixedArrayReuse.program 22 1) 1 ++
  [.localGet 27, .localSet 18] ++ FixedArrayResult.lengthStoreLocalProgram 18 17 ++
  [.constI64 0, .localSet 19, .block 0 0 [.loop 0 0 mapBody]] ++
  FixedArrayResult.finishProgram 18 12 14 ++ [.localGet 12, .localSet 15]

def rejectProgram : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 20 ++
  FixedArrayAllocateNone.program 20 (FixedArrayReuse.program 20 1) 1 ++
  [.localGet 25, .localSet 16] ++ FixedArrayResult.lengthStoreProgram 16 0 ++
  FixedArrayResult.finishProgram 16 13 14 ++ [.localGet 13, .localSet 15]

theorem prepare_shape : func6 = func6.take 21 ++
    [.iff 0 0 acceptProgram rejectProgram, .localGet 15] := rfl

def prepareFrame (count bound ptr ok : UInt64) : Locals :=
  { params := [.i64 count, .i64 bound, .i64 ptr]
    locals := [.i64 count, .i64 bound, .i64 0, .i64 ptr, .i64 ok] ++ List.replicate 20 (.i64 0)
    values := [] }

def prepareResult (initial : Store Unit) (ptr base allocations : UInt64)
    (input output : Array UInt64) : AssertionF Unit := fun final frame =>
  frame.get 15 = some (.i64 (base+48)) ∧ frame.values = [] ∧
  UInt64Array.At final (base+48) output ∧ UInt64Array.At final ptr input ∧
  final.mem.pages = initial.mem.pages ∧
  Memory.WritesRange (clipInitialize initial base output.size allocations) final
    (base+48).toNat ((base+48).toNat+8*(output.size+1))

def acceptAllocationFrame (count bound ptr : UInt64) (size : Nat)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 ptr]
    (mapFrame count bound ptr 0 size 0 0 0 0 []).locals [] need previous current capacity next result

def rejectSaved (count bound ptr : UInt64) : List Value :=
  [.i64 count, .i64 bound, .i64 0, .i64 ptr, .i64 0] ++ List.replicate 12 (.i64 0)

def rejectAllocationFrame (count bound ptr : UInt64)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 ptr]
    (rejectSaved count bound ptr)
    [.i64 0, .i64 0] need previous current capacity next result

#print axioms prepare_shape
end Project.F64Clip.Spec
