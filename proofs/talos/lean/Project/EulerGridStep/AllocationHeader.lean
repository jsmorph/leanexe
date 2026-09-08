import Project.EulerGridStep.HeaderStores
import Project.EulerGridStep.FieldShape
import Project.ProofKit.FixedArrayAllocatorWindow

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow

def fieldBumpBody : Wasm.Program :=
  match (fieldAcceptedBody[32]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def allocationHeaderProgram (rootLocal capacityLocal : Nat) : Wasm.Program :=
  headerConstStore rootLocal 48 5501223100278326855 ++ headerConstStore rootLocal 40 1 ++
  headerLocalStore rootLocal capacityLocal 32 ++ headerConstStore rootLocal 24 2 ++
  headerConstStore rootLocal 16 1 ++ headerConstStore rootLocal 8 0

def fieldHeaderStores : Wasm.Program := allocationHeaderProgram 24 19

theorem field_bump_header_shape : fieldBumpBody =
    fieldBumpBody.take 28 ++ fieldHeaderStores := rfl

def fieldAllocationRegion : Wasm.Program :=
  [.constI64 0, .localSet 24, .constI64 0, .localSet 20, .globalGet 1, .localSet 21] ++
  search 10 1 ++ [.localGet 24, .constI64 0, .eqI64, .iff 0 0 fieldBumpBody []] ++
  [.globalGet 2, .constI64 1, .addI64, .globalSet 2, .localGet 24, .localSet 14]

theorem field_allocation_shape : (fieldAcceptedBody.drop 22).take 17 =
    fieldAllocationRegion := rfl

def writeAllocationHeader (initial : Store Unit) (root capacity : UInt64) : Store Unit :=
  writeHeaderWord (writeHeaderWord (writeHeaderWord
    (writeHeaderWord (writeHeaderWord (writeHeaderWord initial root 48 5501223100278326855)
      root 40 1) root 32 capacity) root 24 2) root 16 1) root 8 0

theorem headerAddress_bound (root offset : UInt64) (pages : Nat)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hOffset : 8 ≤ offset.toNat ∧ offset.toNat ≤ 48)
    (hFit : root.toNat ≤ pages * 65536) :
    (root - offset).toUInt32.toNat + 8 ≤ pages * 65536 := by
  rw [Memory.toUInt32_toNat, Memory.toNat_sub_of_le _ _ (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Six exact metadata stores, with the entire remaining store and locals preserved. -/
theorem allocation_header_program_spec (rootLocal capacityLocal : Nat)
    (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (root capacity : UInt64)
    (hRoot : frame.get rootLocal = some (.i64 root))
    (hCapacity : frame.get capacityLocal = some (.i64 capacity)) (hValues : frame.values = [])
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q (writeAllocationHeader initial root capacity) frame env) :
    wp m (allocationHeaderProgram rootLocal capacityLocal ++ rest) Q initial frame env := by
  have hBound (offset : UInt64) (ho : 8 ≤ offset.toNat ∧ offset.toNat ≤ 48) :=
    headerAddress_bound root offset initial.mem.pages hRoot48 hRoot32 ho hFit
  simp only [allocationHeaderProgram, List.append_assoc]
  apply header_const_store_spec rootLocal root 48 5501223100278326855 m env _ frame hRoot hValues
    (hBound 48 (by decide)) Q _
  apply header_const_store_spec rootLocal root 40 1 m env _ frame hRoot hValues
    (by simpa only [writeHeaderWord_pages] using hBound 40 (by decide)) Q _
  apply header_local_store_spec rootLocal capacityLocal root 32 capacity m env _ frame hRoot hCapacity hValues
    (by simpa only [writeHeaderWord_pages] using hBound 32 (by decide)) Q _
  apply header_const_store_spec rootLocal root 24 2 m env _ frame hRoot hValues
    (by simpa only [writeHeaderWord_pages] using hBound 24 (by decide)) Q _
  apply header_const_store_spec rootLocal root 16 1 m env _ frame hRoot hValues
    (by simpa only [writeHeaderWord_pages] using hBound 16 (by decide)) Q _
  apply header_const_store_spec rootLocal root 8 0 m env _ frame hRoot hValues
    (by simpa only [writeHeaderWord_pages] using hBound 8 (by decide)) Q _
  exact hNext

/-- Six exact metadata stores, with the entire remaining store and locals preserved. -/
theorem allocation_header_spec (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (root capacity : UInt64)
    (hRoot : frame.get 24 = some (.i64 root))
    (hCapacity : frame.get 19 = some (.i64 capacity)) (hValues : frame.values = [])
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q (writeAllocationHeader initial root capacity) frame env) :
    wp m (fieldHeaderStores ++ rest) Q initial frame env := by
  exact allocation_header_program_spec 24 19 m env initial frame root capacity
    hRoot hCapacity hValues hRoot48 hRoot32 hFit Q rest hNext

#print axioms field_bump_header_shape
#print axioms field_allocation_shape
#print axioms allocation_header_program_spec
#print axioms allocation_header_spec
end Project.EulerGridStep.Execution
