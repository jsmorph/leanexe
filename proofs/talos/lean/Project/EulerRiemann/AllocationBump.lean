import Project.EulerRiemann.AllocationHeader

namespace Project.EulerRiemann.Execution
open Wasm Project.Clob Project.ProofKit.Allocation Project.ProofKit.MemoryGrowth

def allocationFrame (params saved : List Wasm.Value)
    (need previous current capacity next result : UInt64) : Locals :=
  { params := params
    locals := saved ++ [.i64 need, .i64 previous, .i64 current,
      .i64 capacity, .i64 next, .i64 result]
    values := [] }

def bumpPrefix : Wasm.Program :=
  [.globalGet 0, .constI64 48, .addI64, .localGet 47, .addI64,
    .localTee 50, .globalGet 0, .ltUI64, .iff 0 0 [.unreachable] [],
    .localGet 50, .constI64 1, .subI64, .constI64 65536, .divUI64,
    .constI64 1, .addI64, .localSet 51]

def bumpInstall : Wasm.Program :=
  [.globalGet 0, .constI64 48, .addI64, .localSet 52, .localGet 50, .globalSet 0]

theorem sweep_bump_parts : sweepBump =
    bumpPrefix ++ ensureProgram 51 ++ bumpInstall ++
      Project.ProofKit.FixedArrayHeader.program 52 47 7 := rfl

theorem bumpPrefix_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (base need previous current capacity next result : UInt64)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame params saved need previous current (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) result) env) :
    wp Project.EulerRiemann.«module» (bumpPrefix ++ rest) Q store
      (allocationFrame params saved need previous current capacity next result) env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  have hNoOverflow := top_not_lt_base base need hFit32
  unfold bumpPrefix
  simp only [List.cons_append, List.nil_append]
  simp [wp_simp, allocationFrame, hParams, hPrefix, hGlobalLength, hGlobalRead]
  refine wp_iff_cons rfl ?_
  simp [hNoOverflow]
  simpa [wp_simp, allocationFrame, hParams, hPrefix, List.set_append, List.getElem?_append]
    using hNext

theorem bumpInstall_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (base need previous current top pages result : UInt64)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q
      { store with globals := { globals := store.globals.globals.set 0 (.i64 top) } }
      (allocationFrame params saved need previous current top pages (base + 48)) env) :
    wp Project.EulerRiemann.«module» (bumpInstall ++ rest) Q store
      (allocationFrame params saved need previous current top pages result) env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  unfold bumpInstall
  simpa [wp_simp, allocationFrame, hParams, hPrefix, List.set_append,
    List.getElem?_append, hGlobal, hGlobalLength, hGlobalRead] using hNext

def bumpPages (base need : UInt64) : Nat :=
  (base.toNat + 48 + need.toNat - 1) / 65536 + 1

theorem bumpPages_le (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) :
    bumpPages base need ≤ 65536 := by
  unfold bumpPages
  omega

theorem bumpPages_word (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) :
    UInt64.ofNat (bumpPages base need) = (base + 48 + need - 1) / 65536 + 1 := by
  have hBound := bumpPages_le base need hFit32
  have h64 : bumpPages base need < UInt64.size := by
    change bumpPages base need < 18446744073709551616
    omega
  apply UInt64.toNat.inj
  rw [UInt64.toNat_ofNat_of_lt' h64, pagesNeeded_toNat base need hFit32]
  rfl

theorem bumpPages_fit (store : Store Unit) (base need : UInt64) :
    base.toNat + 48 + need.toNat ≤
      (ensured store (bumpPages base need)).mem.pages * 65536 := by
  rw [ensured_pages]
  have hPages := Nat.le_max_right store.mem.pages (bumpPages base need)
  have hTotal : base.toNat + 48 + need.toNat ≤ bumpPages base need * 65536 := by
    unfold bumpPages
    omega
  exact hTotal.trans (Nat.mul_le_mul_right 65536 hPages)

def bumpStore (store : Store Unit) (base need : UInt64) : Store Unit :=
  fixedArrayAllocBumpStore (ensured store (bumpPages base need)) base need 7

theorem sweep_bump_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (base need previous current capacity next result : UInt64)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : bumpPages base need ≤ store.memoryCap Project.EulerRiemann.«module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (bumpStore store base need)
      (allocationFrame params saved need previous current (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wp Project.EulerRiemann.«module» (sweepBump ++ rest) Q store
      (allocationFrame params saved need previous current capacity next result) env := by
  rw [sweep_bump_parts]
  simp only [List.append_assoc]
  apply bumpPrefix_spec env store params saved hParams hPrefix base need previous current
    capacity next result hGlobal hFit32
  refine ensureProgram_spec _ env store _ 51 (bumpPages base need) rfl rfl ?_
    hPages (bumpPages_le base need hFit32) hCap _ _ ?_
  · simp [allocationFrame, Locals.get, hParams, hPrefix, bumpPages_word base need hFit32]
  refine bumpInstall_spec env _ params saved hParams hPrefix base need previous current
    (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1) result ?_ _ _ ?_
  · unfold ensured
    split <;> exact hGlobal
  refine Project.ProofKit.FixedArrayHeader.program_spec _ env _ _ 52 47 base need 7 rfl
    ?_ ?_ (by omega) ?_ _ _ ?_
  · simp [allocationFrame, Locals.get, hParams, hPrefix]
  · simp [allocationFrame, Locals.get, hParams, hPrefix]
  · exact le_trans (by omega) (bumpPages_fit store base need)
  · exact hNext

theorem bumpStore_pages (store : Store Unit) (base need : UInt64) :
    (bumpStore store base need).mem.pages = max store.mem.pages (bumpPages base need) := by
  simp only [bumpStore, fixedArrayAllocBumpStore_pages, ensured_pages]

theorem bumpStore_globals (store : Store Unit) (base need : UInt64) :
    (bumpStore store base need).globals.globals =
      store.globals.globals.set 0 (.i64 (base + 48 + need)) := by
  unfold bumpStore fixedArrayAllocBumpStore ensured
  split <;> rfl

theorem bumpStore_fresh (store : Store Unit) (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) :
    FreshFixedArrayAt (bumpStore store base need) (base + 48) need 7 := by
  exact Project.ProofKit.FixedArrayHeader.fresh
    (ensured store (bumpPages base need)) base need 7 (by omega)

theorem bumpStore_bytes_outside (store : Store Unit) (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) (address : Nat)
    (hOutside : address < base.toNat ∨ base.toNat + 48 ≤ address) :
    (bumpStore store base need).mem.bytes address = store.mem.bytes address := by
  change (fixedArrayHeaderMem (ensured store (bumpPages base need)).mem base need 7).bytes
    address = store.mem.bytes address
  rw [Project.ProofKit.FixedArrayHeader.bytes_outside _ base need 7 (by omega) address hOutside,
    ensured_bytes]

theorem gridAt_bump (store : Store Unit) (base need pointer : UInt64)
    (grid : Array Traversal.Cell) (hGrid : Memory.GridAt store pointer grid)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hDisjoint : pointer.toNat + 8 * (7 * grid.size + 1) ≤ base.toNat ∨
      base.toNat + 48 ≤ pointer.toNat) :
    Memory.GridAt (bumpStore store base need) pointer grid := by
  apply hGrid.frame
  · rw [bumpStore_pages]
    exact Nat.le_max_left ..
  · intro address hLow hHigh
    exact bumpStore_bytes_outside store base need hFit32 address (by omega)

#print axioms sweep_bump_parts
#print axioms bumpPrefix_spec
#print axioms bumpInstall_spec
#print axioms bumpPages_le
#print axioms bumpPages_word
#print axioms bumpPages_fit
#print axioms sweep_bump_spec
#print axioms bumpStore_pages
#print axioms bumpStore_globals
#print axioms bumpStore_fresh
#print axioms bumpStore_bytes_outside
#print axioms gridAt_bump

end Project.EulerRiemann.Execution
