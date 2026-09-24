import Project.ClobLimit.HeapAppendOutcome
import Project.ClobLimit.HeapAppendResult

namespace Project.ClobLimit.HeapAppend
open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit Project.ProofKit
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.AllocatorFrame
open Project.ClobMatchFuel.Allocation Project.EulerRiemann.Execution

set_option maxRecDepth 1048576
set_option Elab.async false in
theorem spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : HeapRunMatch.OutputData)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data)
    (hOutput : HeapRunMatch.OutputAt ctx st data)
    (hRemaining : ctx.result.remaining ≠ 0)
    (h32 : data.g0.toNat + 48 + orderArrayBytes (ctx.result.book.length + 1) < 4294967296)
    (hFit : data.g0.toNat + 48 + orderArrayBytes (ctx.result.book.length + 1) ≤ st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, HeapAppendOutcome.At st final ctx data.toOutputData order →
      ∀ frame, HeapAppendResult.LocalsAt frame (HeapAppendOutcome.root ctx data.toOutputData)
        data.trades → wp «module» rest Q final frame env) :
    wp «module» (HeapAppendProgram.program ++ rest) Q st base env := by
  let requested := HeapAppendAllocate.need ctx
  let root := HeapAppendOutcome.root ctx data.toOutputData
  let capacity := HeapAppendOutcome.capacity ctx data.toOutputData
  let raw := HeapAppendMemory.allocated st ctx data.toOutputData requested
  have geo := HeapResidualFacts.of_output hOutput hRemaining
  have hn : requested.toNat = orderArrayBytes (ctx.result.book.length + 1) :=
    HeapAppendBounds.need_toNat ctx (by omega)
  have ha := HeapAppendMemory.facts st ctx data.toOutputData requested hOutput geo
    (by rw [hn]; exact h32) (by rw [hn]; exact hFit)
  have hSize : ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ capacity.toNat := by
    have hc := ha.capacity
    rw [hn] at hc
    change _ ≤ (allocatedCapacity requested data.nodes).toNat
    unfold orderArrayBytes fixedArrayBytes at hc
    omega
  have hr48 : 48 ≤ root.toNat := ha.root48
  have hr32 : root.toNat + ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296 := by
    have hc : root.toNat + capacity.toNat < 4294967296 := ha.root32
    omega
  have hrFit : root.toNat + ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ raw.mem.pages * 65536 := by
    have hc : root.toNat + capacity.toNat ≤ raw.mem.pages * 65536 := ha.fits
    omega
  have hRoot : root - 48 + 48 = root := by simp
  have hRootNat : (root - 48 + 48).toNat = (root - 48).toNat + 48 := by
    rw [hRoot, toNat_sub_le root 48 (by exact hr48)]
    change root.toNat = root.toNat - 48 + 48
    omega
  have hSource32 : data.book.toNat + (ctx.result.book.length * 5 + 1) * 8 < 4294967296 := by
    have hb := geo.book32
    unfold fixedArrayBytes at hb
    omega
  have hSourceFit : data.book.toNat + (ctx.result.book.length * 5 + 1) * 8 ≤ raw.mem.pages * 65536 := by
    rw [ha.pages]
    have hb := geo.bookBelow
    have hc := geo.bookCapacity
    unfold fixedArrayBytes at hc
    omega
  have hDisjoint : data.book.toNat + (ctx.result.book.length * 5 + 1) * 8 ≤ root.toNat ∨
      root.toNat + ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤ data.book.toNat := by
    have hs := ha.bookSeparated
    have hb := geo.book48
    have hc := geo.bookCapacity
    simp only [regionsDisjoint, allocatedNode, fixedArrayRegion, FreeNode.region] at hs
    unfold fixedArrayBytes at hc
    change ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
      (allocatedCapacity requested data.nodes).toNat at hSize
    dsimp only [requested] at hs hSize
    dsimp only [root, HeapAppendOutcome.root]
    omega
  simp only [HeapAppendProgram.program, List.append_assoc]
  apply HeapAppendAllocate.spec env st base order ctx data hOrder hOutput geo
    (by intro _; rw [hn]; exact ⟨Nat.le_of_lt h32, hFit⟩)
  intro previous current scratchCapacity next
  apply HeapAppendHeader.spec env raw base order ctx data previous current scratchCapacity next root hOrder
    (by rw [toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]; omega)
  let prepared := HeapAppendFrames.headerFrame base ctx previous current scratchCapacity next root
  let initialized := HeapAppendHeader.initialized raw root ctx.result.book.length
  have hf := HeapAppendFrames.header_facts base order ctx data previous current scratchCapacity next root hOrder
  have hh := HeapAppendHeader.facts raw ctx data.toOutputData requested ha geo hSize
  have hInitializedPages : initialized.mem.pages = raw.mem.pages := Mem.write64_pages ..
  have hp : prepared.params.length = 6 := hf.stores.params
  have hl : prepared.locals.length = 55 := hf.stores.locals
  have hCounter : prepared.validIndex 47 := by simp [Locals.validIndex, hp, hl]
  have hTotal : UInt64.ofNat ctx.result.book.length * 5 = UInt64.ofNat (ctx.result.book.length * 5) := by simp
  have hSourceLocal : prepared.locals[36]'(by omega) = .i64 data.book := getElem_of_some (hi := by change _ < prepared.locals.length; omega) hf.source
  have hTargetLocal : prepared.locals[40]'(by omega) = .i64 root := getElem_of_some (hi := by change _ < prepared.locals.length; omega) hf.stores.target
  have hPrefixLocal : prepared.locals[38]'(by omega) =
      .i64 (UInt64.ofNat ctx.result.book.length * 5) := getElem_of_some (hi := by change _ < prepared.locals.length; omega) hf.total
  apply HeapAppendCopy.spec 42 46 44 47 «module» env initialized prepared data.book root capacity
    ctx.result.book hCounter (by decide) (by decide) (by decide) hf.stores.values
    (by simp [Locals.get, hp, hl, hSourceLocal])
    (by simp [Locals.get, hp, hl, hTargetLocal])
    (by simp [Locals.get, hp, hl, hPrefixLocal])
    hSource32 hr48 hr32 (by rw [hInitializedPages]; exact hSourceFit)
    (by rw [hInitializedPages]; exact hrFit) hDisjoint hh.fresh hh.length hh.sourceOrders
  intro copied hCopy
  have hCopiedLocals := hf.counter (ctx.result.book.length * 5) hCounter
  simp only [LimitEntry.residualFinishProg, List.append_assoc]
  apply HeapAppendFinish.store_spec env initialized copied
    (FixedArrayCopy.counterFrame prepared 47 (ctx.result.book.length * 5) hCounter)
    (root - 48) capacity data.book ctx.result.book { order with oqty := ctx.result.remaining }
    (by simpa only [hRoot] using hCopiedLocals.stores)
    (by simpa only [hRoot] using hCopy) hRootNat
    (by simpa only [hRoot] using hr48) (by simpa only [hRoot] using hr32)
    (by rw [hRoot, hInitializedPages]; exact hrFit)
  intro final hFinish
  apply HeapAppendResult.spec env final _ root order ctx data hCopiedLocals
  exact hNext final (HeapAppendOutcome.of_finish st final ctx data.toOutputData order geo ha hSize hFinish)

#print axioms spec
end Project.ClobLimit.HeapAppend
