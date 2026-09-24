import Project.ClobLimit.HeapAppendAllocate
import Project.ClobLimit.HeapAppendMemory

namespace Project.ClobLimit.HeapAppendBounds
open Wasm Project.Common Project.Clob Project.ProofKit Project.ClobLimit
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.Allocation

theorem need_eq (ctx : Context)
    (h32 : orderArrayBytes (ctx.result.book.length + 1) + 7 < 4294967296) :
    HeapAppendAllocate.need ctx = orderArrayBytesU (ctx.result.book.length + 1) := by
  let n := ctx.result.book.length + 1
  have hn : n < UInt64.size := by
    dsimp [n]; unfold orderArrayBytes fixedArrayBytes at h32
    rw [size_eq]; omega
  have hb : orderArrayBytes n + 7 < UInt64.size := by
    rw [size_eq]; dsimp [n]; omega
  have hr := fixedArrayBytesU_round n 5 hn (by decide) hb
  have hv := fixedArrayBytesU_toNat n 5 hn (by decide) (by
    change orderArrayBytes n < UInt64.size
    omega)
  have hSmall : ¬orderArrayBytesU n < 8 := by
    rw [UInt64.lt_iff_toNat_lt]
    change ¬(fixedArrayBytesU n 5).toNat < 8
    rw [hv]
    unfold fixedArrayBytes
    omega
  unfold HeapAppendAllocate.need FixedArrayCapacity.normalizedCapacity
    FixedArrayCapacity.unnormalizedCapacity
  change (if (orderArrayBytesU n + 7) / 8 * 8 < 8 then 8 else
    (orderArrayBytesU n + 7) / 8 * 8) = orderArrayBytesU n
  rw [hr, if_neg hSmall]

theorem need_toNat (ctx : Context)
    (h32 : orderArrayBytes (ctx.result.book.length + 1) + 7 < 4294967296) :
    (HeapAppendAllocate.need ctx).toNat = orderArrayBytes (ctx.result.book.length + 1) := by
  rw [need_eq ctx h32]
  apply fixedArrayBytesU_toNat _ 5
  · unfold orderArrayBytes fixedArrayBytes at h32
    rw [size_eq]; omega
  · decide
  · change orderArrayBytes (ctx.result.book.length + 1) < UInt64.size
    rw [size_eq]; omega

#print axioms need_eq
#print axioms need_toNat
end Project.ClobLimit.HeapAppendBounds
