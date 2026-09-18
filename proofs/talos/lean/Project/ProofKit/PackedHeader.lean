import Project.ProofKit.FixedArrayHeaderExec

namespace Project.ProofKit.PackedHeader
open Wasm Project.ProofKit.Memory Project.ProofKit.Allocation
open Project.ProofKit.FixedArrayHeader

def headerMem (mem : Mem) (base capacity : UInt64) : Mem :=
  (((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 0).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) 0).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0

def program (pointerLocal capacityLocal : Nat) : Wasm.Program :=
  [.localGet pointerLocal, .constI64 48, .subI64, .wrapI64,
    .constI64 5501223100278326855, .store64 0,
   .localGet pointerLocal, .constI64 40, .subI64, .wrapI64,
    .constI64 1, .store64 0,
   .localGet pointerLocal, .constI64 32, .subI64, .wrapI64,
    .localGet capacityLocal, .store64 0,
   .localGet pointerLocal, .constI64 24, .subI64, .wrapI64,
    .constI64 0, .store64 0,
   .localGet pointerLocal, .constI64 16, .subI64, .wrapI64,
    .constI64 0, .store64 0,
   .localGet pointerLocal, .constI64 8, .subI64, .wrapI64,
    .constI64 0, .store64 0]

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal capacityLocal : Nat)
    (base capacity : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 (base + 48)))
    (hCapacity : frame.get capacityLocal = some (.i64 capacity))
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hFit : base.toNat + 48 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := headerMem store.mem base capacity } frame env) :
    wp module_ (program pointerLocal capacityLocal ++ rest) Q store frame env := by
  obtain ⟨h40, h32, h24, h16, h8⟩ := headerOffsets base hFit32
  have h48 : (base + 48 - 48).toNat = base.toNat := by
    rw [root_sub_toNat base 48 hFit32 (by decide)]
    rfl
  have hBound (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (base + 48 - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [toUInt32_toNat, root_sub_toNat base offset hFit32 hHigh]
    omega
  unfold program
  apply writeConst_spec module_ env store frame pointerLocal (base + 48) 48 _
    hValues hPointer (hBound 48 (by decide) (by decide))
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 40 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 40 (by decide) (by decide)
  refine writeLocal_spec module_ env _ frame pointerLocal capacityLocal (base + 48) 32 capacity
    hValues hPointer hCapacity ?_ _ _ ?_
  · exact hBound 32 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 24 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 24 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 16 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 16 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 8 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 8 (by decide) (by decide)
  simpa only [headerMem, toUInt32_eq_ofNat, h48, h40, h32, h24, h16, h8]
    using hNext

theorem reads (mem : Mem) (base capacity : UInt64) :
    let written := headerMem mem base capacity
    written.read64 (UInt32.ofNat (base.toNat % 4294967296)) = 5501223100278326855 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 8) % 4294967296)) = 1 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 16) % 4294967296)) = capacity ∧
    written.read64 (UInt32.ofNat ((base.toNat + 24) % 4294967296)) = 0 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 32) % 4294967296)) = 0 ∧
    written.read64 (UInt32.ofNat ((base.toNat + 40) % 4294967296)) = 0 := by
  dsimp only
  unfold headerMem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat first
      | rw [read64_write64_disjoint _ _ _ _ (by
          simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_mod]
          omega)]
      | exact read64_write64 ..

theorem bytes_outside (mem : Mem) (base capacity : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (headerMem mem base capacity).bytes address = mem.bytes address := by
  unfold headerMem
  repeat rw [write64_bytes_outside _ _ _ (by
    simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_mod]
    omega)]

#print axioms program_spec
#print axioms reads
#print axioms bytes_outside

end Project.ProofKit.PackedHeader
