import Project.F64Clip.Map
import Project.F64Clip.AllocationMemory
import Project.ProofKit.FixedArrayReuse

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit

def acceptProgram : Wasm.Program :=
  [.localGet 2, .localSet 15, .localGet 15, .wrapI64, .load64 0, .localSet 16] ++
  FixedArrayCapacity.localProgram 16 1 21 ++
  FixedArrayAllocateNone.program 21 (FixedArrayReuse.program 21 1) 1 ++
  [.localGet 26, .localSet 17] ++ FixedArrayResult.lengthStoreLocalProgram 17 16 ++
  [.constI64 0, .localSet 18, .block 0 0 [.loop 0 0 mapBody]] ++
  FixedArrayResult.finishProgram 17 12 14

def rejectProgram : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 19 ++
  FixedArrayAllocateNone.program 19 (FixedArrayReuse.program 19 1) 1 ++
  [.localGet 24, .localSet 15] ++ FixedArrayResult.lengthStoreProgram 15 0 ++
  FixedArrayResult.finishProgram 15 13 14

theorem prepare_shape : func6 = func6.take 21 ++
    [.iff 0 0 acceptProgram rejectProgram, .localGet 14] := rfl

def prepareFrame (count bound ptr ok : UInt64) : Locals :=
  { params := [.i64 count, .i64 bound, .i64 ptr]
    locals := [.i64 count, .i64 bound, .i64 0, .i64 ptr, .i64 ok] ++ List.replicate 19 (.i64 0)
    values := [] }

def prepareResult (initial : Store Unit) (ptr base allocations : UInt64)
    (input output : Array UInt64) : AssertionF Unit := fun final frame =>
  frame.get 14 = some (.i64 (base+48)) ∧ frame.values = [] ∧
  UInt64Array.At final (base+48) output ∧ UInt64Array.At final ptr input ∧
  final.mem.pages = initial.mem.pages ∧
  Memory.WritesRange (clipInitialize initial base output.size allocations) final
    (base+48).toNat ((base+48).toNat+8*(output.size+1))

def acceptAllocationFrame (count bound ptr : UInt64) (size : Nat)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 ptr]
    (mapFrame count bound ptr 0 size 0 0 0 0 []).locals [] need previous current capacity next result

def rejectSaved (count bound ptr : UInt64) : List Value :=
  [.i64 count, .i64 bound, .i64 0, .i64 ptr, .i64 0] ++ List.replicate 11 (.i64 0)

def rejectAllocationFrame (count bound ptr : UInt64)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 count, .i64 bound, .i64 ptr]
    (rejectSaved count bound ptr)
    [.i64 0, .i64 0] need previous current capacity next result

#print axioms prepare_shape
end Project.F64Clip.Spec
