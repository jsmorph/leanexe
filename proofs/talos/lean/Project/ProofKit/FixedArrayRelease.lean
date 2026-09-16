import Project.FixedArrayAllocation
import Project.Runtime.FixedArraySpec
import Project.Runtime.FreeList
import Project.ProofKit.MemoryRoundtrip

namespace Project.ProofKit.FixedArrayRelease
open Wasm Project.Clob Project.Runtime Memory

def store (initial : Store Unit) (root head releases frees : UInt64) : Store Unit :=
  { initial with
    mem := (initial.mem.write64 (root - 40).toUInt32 0).write64 (root - 8).toUInt32 head
    globals :=
      { globals := ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
          (.i64 (frees + 1))).set 1 (.i64 root) } }

theorem exact (env : HostEnv Unit) (module_ : Wasm.Module) (id : Nat)
    (initial : Store Unit) (root capacity head releases frees : UInt64) (length stride : Nat)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? =
      some { releaseFuncDef id with typeIdx := typeIdx })
    (hImport : module_.imports[id]? = none)
    (hLength32 : length < 4294967296) (hStride32 : stride < 4294967296)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat + 8 ≤ initial.mem.pages * 65536)
    (hHeader : FreshFixedArrayAt initial root capacity (UInt64.ofNat stride))
    (hLength : initial.mem.read64 root.toUInt32 = UInt64.ofNat length)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env module_ id initial [.i64 root]
      (fun final values => values = [] ∧ final = store initial root head releases frees) := by
  obtain ⟨hMagic, hRc, _, hKind, hStride, hMask⟩ := hHeader
  have hCall := release_frees_fixed_array_zero_mask_full env module_ id initial
    root head releases frees length stride hFunction hImport hLength32 hStride32
    hRoot hRoot32 hFit hMagic hRc hKind hLength hStride hMask hHead hReleases hFrees
  apply hCall.mono
  rintro final values ⟨hValues, hMem, hGlobals, hStore⟩
  refine ⟨hValues, ?_⟩
  have hGlobals' : final.globals =
      { globals := ((initial.globals.globals.set 4 (.i64 (releases + 1))).set 5
        (.i64 (frees + 1))).set 1 (.i64 root) } := congrArg Globals.mk hGlobals
  rw [hStore, hMem, hGlobals']
  rfl

@[simp] theorem pages (initial : Store Unit) (root head releases frees : UInt64) :
    (store initial root head releases frees).mem.pages = initial.mem.pages := rfl

theorem memoryCap (initial : Store Unit) (root head releases frees : UInt64)
    (module_ : Wasm.Module) (index : Nat) :
    (store initial root head releases frees).memoryCap module_ index =
      initial.memoryCap module_ index := rfl

theorem bytes_outside (initial : Store Unit) (root head releases frees : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < root.toNat - 48 ∨ root.toNat ≤ address) :
    (store initial root head releases frees).mem.bytes address = initial.mem.bytes address := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h40 : (40 : UInt64).toNat = 40 := rfl
  have hAddress (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat = root.toNat - offset.toNat := by
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold store
  dsimp only
  rw [write64_bytes_outside _ _ _ (by rw [hAddress 8 (by decide) (by decide)]; omega),
    write64_bytes_outside _ _ _ (by rw [hAddress 40 (by decide) (by decide)]; omega)]

theorem freeListAt (initial : Store Unit) (root capacity releases frees : UInt64)
    (nodes : List FreeNode) (hRoot : 48 ≤ root.toNat)
    (hRoot32 : root.toNat + capacity.toNat < 4294967296)
    (hFit : root.toNat + capacity.toNat ≤ initial.mem.pages * 65536)
    (hCapacity : initial.mem.read64 (root - 32).toUInt32 = capacity)
    (hList : FreeListAt initial.mem nodes)
    (hSep : ∀ node ∈ nodes, regionsDisjoint ({ root, capacity } : FreeNode).region node.region) :
    FreeListAt (store initial root (freeHead nodes) releases frees).mem
      ({ root, capacity } :: nodes) := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h32 : (32 : UInt64).toNat = 32 := rfl
  have h40 : (40 : UInt64).toNat = 40 := rfl
  have hList40 := hList.frame_write64_disjoint (writer := { root, capacity })
    (writeOffset := 40) (value := 0) hRoot hRoot32 (by decide) (by decide) hSep
  have hList8 := hList40.frame_write64_disjoint (writer := { root, capacity })
    (writeOffset := 8) (value := freeHead nodes) hRoot hRoot32 (by decide) (by decide) hSep
  have hAddress (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (root - offset).toUInt32.toNat = root.toNat - offset.toNat := by
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
  change FreeListAt ((initial.mem.write64 (root - 40).toUInt32 0).write64
    (root - 8).toUInt32 (freeHead nodes)) ({ root, capacity } :: nodes)
  refine .cons hRoot hRoot32 hFit ?_ ?_ ?_ hSep hList8
  · change ((initial.mem.write64 (root - 40).toUInt32 0).write64
      (root - 8).toUInt32 (freeHead nodes)).read64 (root - 40).toUInt32 = 0
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 8 (by decide) (by decide), hAddress 40 (by decide) (by decide)]
      omega)]
    exact read64_write64 ..
  · change ((initial.mem.write64 (root - 40).toUInt32 0).write64
      (root - 8).toUInt32 (freeHead nodes)).read64 (root - 32).toUInt32 = capacity
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 8 (by decide) (by decide), hAddress 32 (by decide) (by decide)]
      omega)]
    rw [read64_write64_disjoint _ _ _ _ (by
      rw [hAddress 40 (by decide) (by decide), hAddress 32 (by decide) (by decide)]
      omega)]
    exact hCapacity
  · exact read64_write64 ..

#print axioms exact
#print axioms bytes_outside
#print axioms freeListAt

end Project.ProofKit.FixedArrayRelease
