import Project.ProofKit.Array
import Project.ProofKit.FixedArrayAllocator

namespace Project.ProofKit.FixedArraySingleton

open Wasm

def resultSuffix : Wasm.Program :=
  [
  .localGet 5,
  .wrapI64,
  .constI64 1,
  .store64 0,
  .localGet 2,
  .localSet 8,
  .localGet 5,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 8,
  .store64 0,
  .localGet 5,
  .localSet 3,
  .localGet 3,
  .localSet 4
  ]

def resultStore (st : Store Unit) (heapTop allocs value : UInt64) : Store Unit :=
  let allocated := FixedArrayAllocator.allocStore st heapTop 16 1 allocs
  { allocated with
    mem := (allocated.mem.write64 (heapTop + 48).toUInt32 1).write64
      (heapTop + 48 + 8).toUInt32 value }

def resultFrame (frame : Locals) (heapTop value : UInt64) : Locals :=
  let allocated := FixedArrayAllocator.allocFrame frame heapTop 16
  { allocated with
    locals := ((allocated.locals.set 7 (.i64 value)).set 2
      (.i64 (heapTop + 48))).set 3 (.i64 (heapTop + 48)) }

theorem resultStore_at (st : Store Unit) (heapTop allocs value : UInt64)
    (hFitMemory : heapTop.toNat + 48 + 16 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536) :
    UInt64Array.At (resultStore st heapTop allocs value) (heapTop + 48) #[value] := by
  have hFacts := Allocation.bumpFacts heapTop 16 st.mem.pages hFitMemory hPages
  have hRootAddressNat :
      (heapTop + 48).toUInt32.toNat = heapTop.toNat + 48 := by
    simpa using hFacts.wordAddress_toNat 0 (by decide)
  have hPayloadAddressNat :
      (heapTop + 48 + 8).toUInt32.toNat = heapTop.toNat + 56 := by
    simpa using hFacts.wordAddress_toNat 1 (by decide)
  apply UInt64Array.singleton
  · rw [hFacts.rootToNat]
    exact hFacts.fit32
  · rw [hFacts.rootToNat]
    simpa [resultStore, FixedArrayAllocator.allocStore_pages,
      Wasm.Mem.write64_pages] using hFitMemory
  · change
      (((FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.write64
        (heapTop + 48).toUInt32 1).write64
        (heapTop + 48 + 8).toUInt32 value).read64
        (heapTop + 48).toUInt32 = 1
    calc
      _ = ((FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.write64
          (heapTop + 48).toUInt32 1).read64 (heapTop + 48).toUInt32 :=
        Project.ProofKit.Memory.read64_write64_disjoint _ _ _ _
          (Or.inl (by omega))
      _ = 1 := Wasm.Mem.read64_write64_same ..
  · change
      (((FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.write64
        (heapTop + 48).toUInt32 1).write64
        (heapTop + 48 + 8).toUInt32 value).read64
        (heapTop + 48 + 8).toUInt32 = value
    exact Wasm.Mem.read64_write64_same ..

set_option Elab.async false in
theorem region_result_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop allocs value : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 14)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[8]? = some (.i64 16))
    (hValueLocal : frame.locals[1]? = some (.i64 value))
    (hFitMemory : heapTop.toNat + 48 + 16 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : UInt64Array.At (resultStore st heapTop allocs value)
        (heapTop + 48) #[value] →
      wp module_ rest Q (resultStore st heapTop allocs value)
        (resultFrame frame heapTop value) env) :
    wp module_ (FixedArrayAllocator.region 1 ++ resultSuffix ++ rest)
      Q st frame env := by
  have hValueGet : frame.locals[1] = .i64 value := by
    have h := hValueLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hFacts := Allocation.bumpFacts heapTop 16 st.mem.pages hFitMemory hPages
  have hRootAddress := hFacts.wordAddress 0 (by decide)
  have hPayloadAddress := hFacts.wordAddress 1 (by decide)
  have hRootAddressNat := hFacts.wordAddress_toNat 0 (by decide)
  have hPayloadAddressNat := hFacts.wordAddress_toNat 1 (by decide)
  have hRootAddressDirect :
      UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
        (heapTop + 48).toUInt32 := by
    simpa using hRootAddress
  have hPayloadAddressDirect :
      UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
        (heapTop + 48 + 8).toUInt32 := by
    have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by
      omega
    simpa [Nat.mod_eq_of_lt hRoot64] using hPayloadAddress
  rw [List.append_assoc]
  apply FixedArrayAllocator.region_spec module_ env st frame heapTop 16 1 allocs
    hParams hLocals hValues hCapacityLocal (by decide) hFitMemory hPages
    hMemory32 hHeapTop hFreeList hAllocs Q (resultSuffix ++ rest)
  have hRootBound :
      (heapTop + 48 + UInt64.ofNat (8 * 0)).toUInt32.toNat + 8 ≤
        (FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 := by
    rw [FixedArrayAllocator.allocStore_pages, hRootAddressNat]
    omega
  have hPayloadBound :
      (heapTop + 48 + UInt64.ofNat (8 * 1)).toUInt32.toNat + 8 ≤
        (FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 := by
    rw [FixedArrayAllocator.allocStore_pages, hPayloadAddressNat]
    omega
  have hRootBoundMod :
      (heapTop.toNat + 48) % 4294967296 + 8 ≤
        (FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), FixedArrayAllocator.allocStore_pages]
    omega
  have hPayloadBoundMod :
      (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
        (FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega), FixedArrayAllocator.allocStore_pages]
    omega
  have hRootSafe :
      ¬(FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 <
        (heapTop.toNat + 48) % 4294967296 + 8 := by
    omega
  have hPayloadSafe :
      ¬(FixedArrayAllocator.allocStore st heapTop 16 1 allocs).mem.pages * 65536 <
        (heapTop.toNat + 48 + 8) % 4294967296 + 8 := by
    omega
  unfold resultSuffix
  wp_alloc_run [FixedArrayAllocator.allocFrame, hParams, hLocals, hValues,
    hValueGet, hRootAddress, hPayloadAddress, hRootAddressDirect,
    hPayloadAddressDirect, hRootBound, hPayloadBound, hRootBoundMod,
    hPayloadBoundMod, hRootSafe, hPayloadSafe]
  simpa [resultStore, resultFrame, FixedArrayAllocator.allocFrame, hValues] using
    hNext (resultStore_at st heapTop allocs value hFitMemory hPages)

end Project.ProofKit.FixedArraySingleton
