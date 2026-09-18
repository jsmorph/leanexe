import Project.PackedGenerate.Loop
import Project.ProofKit.PackedAllocate
import Project.ProofKit.PackedCapacity
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.Annotation

namespace Project.PackedGenerate.Entry
open Wasm Project.ProofKit

def searchFit : Wasm.Program :=
  (Annotation.resolve func0 [⟨29, .block⟩, ⟨0, .loop⟩, ⟨23, .thenBranch⟩]).getD []

theorem emitted_allocation : (func0.drop 23).take 15 =
    PackedAllocate.program 10 searchFit := rfl

def entryFrame (count : Nat) (offset : UInt32) : Locals :=
  { params := [.i64 (UInt64.ofNat count), .i64 offset.toUInt64]
    locals := List.replicate 14 (.i64 0) }

def sizeFrame (count : Nat) (offset : UInt32) : Locals :=
  { params := [.i64 (UInt64.ofNat count), .i64 offset.toUInt64]
    locals := [.i64 (UInt64.ofNat (4 * count)), .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 (UInt64.ofNat (4 * count)), .i64 4,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }

def saved (count : Nat) : List Value :=
  [.i64 (UInt64.ofNat (4 * count)), .i64 0, .i64 0, .i64 0,
    .i64 0, .i64 0, .i64 (UInt64.ofNat (4 * count)), .i64 4]

theorem size_prefix (env : HostEnv Unit) (store : Store Unit)
    (count : Nat) (offset : UInt32) (hcount : 4 * count ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (sizeFrame count offset) env) :
    wp «module» (func0.take 11 ++ rest) Q store (entryFrame count offset) env := by
  have hsplit : func0.take 11 =
      [.localGet 0, .localSet 8, .constI64 4, .localSet 9] ++
      CheckedNatMul.program 8 9 ++ [.localSet 2, .localGet 2, .localSet 8] := rfl
  have hproduct : UInt64.ofNat count * 4 = UInt64.ofNat (4 * count) := by
    simp [Nat.mul_comm]
  rw [hsplit]
  simp only [List.append_assoc]
  simp [entryFrame, wp_simp, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  apply CheckedNatMul.program_spec 8 9 «module» env store _ (UInt64.ofNat count) 4 []
  · rfl
  · rfl
  · rfl
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  simpa [sizeFrame, wp_simp, hproduct] using hNext

theorem capacity_prefix (env : HostEnv Unit) (store : Store Unit)
    (count : Nat) (offset : UInt32) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store
      (FixedArraySearch.frame [.i64 (UInt64.ofNat count), .i64 offset.toUInt64]
        (saved count) [] (PackedCapacity.capacity (UInt64.ofNat (4 * count))) 0 0 0 0 0) env) :
    wp «module» ((func0.drop 11).take 12 ++ rest) Q store (sizeFrame count offset) env := by
  have hregion : (func0.drop 11).take 12 = PackedCapacity.program 8 10 := rfl
  rw [hregion]
  apply PackedCapacity.program_spec 8 10 (UInt64.ofNat (4 * count))
    «module» env store (sizeFrame count offset)
  · rfl
  · rfl
  · change 2 ≤ 10; decide
  · change 10 < 16; decide
  exact hNext

#print axioms size_prefix
#print axioms capacity_prefix

theorem return_suffix (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer length : UInt64) (hparams : frame.params.length = 2)
    (hlocals : frame.locals.length = 14) (hvalues : frame.values = [])
    (hpointer : frame.get 9 = some (.i64 pointer))
    (hlength : frame.get 2 = some (.i64 length))
    (Q : Assertion Unit)
    (hNext : ∀ result, result.values = [.i64 length, .i64 pointer] →
      Q (.Fallthrough store result)) :
    wp «module» (func0.drop 43) Q store frame env := by
  have hreturn : func0.drop 43 =
      [.localGet 9, .localSet 4, .localGet 4, .localSet 5, .localGet 4, .localSet 6,
        .localGet 2, .localSet 7, .localGet 6, .localGet 7] := rfl
  have hp := Frame.internal_getElem_of_get frame 2 7 (.i64 pointer)
    hparams (by omega) hpointer
  have hl := Frame.internal_getElem_of_get frame 2 0 (.i64 length)
    hparams (by omega) hlength
  rw [hreturn]
  simp [wp_simp, Locals.get, Locals.set?, hparams, hlocals, hvalues, hp, hl]
  exact hNext _ rfl

def bufferStore (initial : Store Unit) (base : UInt64) (count : Nat)
    (allocations : UInt64) : Store Unit :=
  FixedArrayAllocateNone.counted
    (PackedAllocate.allocated initial base (PackedCapacity.capacity (UInt64.ofNat (4 * count))))
    allocations

def ReturnState (count : Nat) (frame : Locals) : Prop :=
  frame.get 2 = some (.i64 (UInt64.ofNat (4 * count))) ∧
  frame.params.length = 2 ∧ frame.locals.length = 14

theorem body_spec (env : HostEnv Unit) (initial : Store Unit)
    (count : Nat) (offset : UInt32) (base allocations : UInt64)
    (nodes : List Project.Runtime.FreeNode)
    (hcount : 4 * count ≤ 2^32)
    (hGlobal0 : initial.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : initial.globals.globals[1]? = some (.i64 (Project.Runtime.freeHead nodes)))
    (hGlobal2 : initial.globals.globals[2]? = some (.i64 allocations))
    (hList : Project.Runtime.FreeListAt initial.mem nodes)
    (hNone : Project.Runtime.takeFirstFit (PackedCapacity.capacity (UInt64.ofNat (4 * count))) nodes = none)
    (hFit32 : base.toNat + 48 + PackedCapacity.capacityNat (4 * count) ≤ 2^32)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) ≤
      initial.memoryCap «module» 0)
    (Q : Assertion Unit)
    (hDone : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (4 * count)), .i64 (base + 48)] →
      PackedMemory.ByteArrayAt final.mem (base + 48).toNat
        (LeanExe.Examples.Packed.makeWords count offset) →
      Memory.WritesRange (bufferStore initial base count allocations) final
        (base + 48).toNat ((base + 48).toNat + 4 * count) →
      Q (.Fallthrough final result)) :
    wp «module» func0 Q initial (entryFrame count offset) env := by
  have hcapacity := PackedCapacity.capacity_toNat (4 * count) hcount
  have hspace := PackedCapacity.capacityNat_ge (4 * count)
  have hroot : (base + 48).toNat = base.toNat + 48 := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
    omega
  have hfit : (base + 48).toNat + 4 * count ≤ 2^32 := by omega
  have hmemory : (base + 48).toNat + 4 * count ≤
      (bufferStore initial base count allocations).mem.pages * 65536 := by
    have h := FixedArrayBump.requiredPages_fit initial base
      (PackedCapacity.capacity (UInt64.ofNat (4 * count)))
    rw [hcapacity] at h
    exact le_trans (by omega) h
  have hsplit : func0 = func0.take 11 ++ (func0.drop 11).take 12 ++
      (func0.drop 23).take 15 ++ func0.drop 38 := rfl
  rw [hsplit]
  simp only [List.append_assoc]
  apply size_prefix env initial count offset hcount
  apply capacity_prefix env initial count offset
  rw [emitted_allocation]
  apply PackedAllocate.program_spec «module» env initial
    [.i64 (UInt64.ofNat count), .i64 offset.toUInt64] (saved count) [] 10 rfl searchFit
    base (PackedCapacity.capacity (UInt64.ofNat (4 * count))) 0 0 0 0 0 allocations nodes
    hGlobal0 hGlobal1 hGlobal2 hList hNone
  · rwa [hcapacity]
  · exact hPages
  · rfl
  · exact hCap
  intro previous
  have hsetup : func0.drop 38 = [.localGet 15, .localSet 9, .constI64 0, .localSet 3] ++
      (func0.drop 42).take 1 ++ func0.drop 43 := rfl
  rw [hsetup]
  simp only [List.append_assoc]
  simp [wp_simp, FixedArraySearch.frame, saved, -UInt64.ofNat_mul]
  refine Loop.generated_loop_spec env (bufferStore initial base count allocations) _
    (base + 48) count offset ?_ ?_ hfit hmemory (ReturnState count) ?_ ?_ Q _ ?_
  · exact ⟨rfl, rfl, rfl, rfl, by change 3 < 16; decide⟩
  · rfl
  · exact ⟨rfl, rfl, rfl⟩
  · intro next index hvalid h
    exact ⟨(FixedArrayCopy.counterFrame_get_ne _ _ _ _ _ (by decide)).trans h.1,
      (FixedArrayCopy.counterFrame_params_length ..).trans h.2.1,
      (FixedArrayCopy.counterFrame_locals_length ..).trans h.2.2⟩
  intro final result hready _ hreturn hbytes hwrites
  apply return_suffix env final result (base + 48) (UInt64.ofNat (4 * count))
    hreturn.2.1 hreturn.2.2 hready.1 hready.2.2.2.1 hreturn.1
  intro result hvalues
  exact hDone final result hvalues hbytes hwrites

#print axioms return_suffix
#print axioms body_spec

end Project.PackedGenerate.Entry
