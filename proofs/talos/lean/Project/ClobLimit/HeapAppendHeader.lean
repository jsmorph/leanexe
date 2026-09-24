import Project.ClobLimit.HeapAppendMemory
import Project.ClobLimit.HeapAppendFrames

namespace Project.ClobLimit.HeapAppendHeader
open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit Project.ProofKit
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.AllocatorFrame
open Project.ClobMatchFuel.Allocation Project.EulerRiemann.Execution

def initialized (st : Store Unit) (root : UInt64) (n : Nat) : Store Unit :=
  { st with mem := st.mem.write64 root.toUInt32 (UInt64.ofNat (n + 1)) }

set_option maxRecDepth 1048576
set_option Elab.async false in
theorem spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context) (data : HeapRunMatch.OutputData)
    (previous current capacity next root : UInt64)
    (hOrder : LimitResidualPrepare.OrderLocalsAt base order ctx data)
    (hBound : root.toUInt32.toNat + 8 ≤ st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (initialized st root ctx.result.book.length)
      (HeapAppendFrames.headerFrame base ctx previous current capacity next root) env) :
    wp «module» (HeapAppendProgram.headerProgram ++ rest) Q st
      (HeapAppendAllocate.resultFrame base ctx previous current capacity next root) env := by
  have hp := hOrder.fields.params
  have hl := hOrder.fields.locals
  have hn := getElem_of_some hOrder.appendLength
  simp only [HeapAppendProgram.headerProgram, List.cons_append, List.nil_append]
  simp [wp_simp, HeapAppendAllocate.resultFrame, FixedArraySearch.frame, hp, hl, hn]
  rw [toUInt32_toNat] at hBound
  rw [if_neg (Nat.not_lt.mpr hBound)]
  simpa [initialized, HeapAppendFrames.headerFrame, HeapAppendAllocate.resultFrame,
    FixedArraySearch.frame, hp, hl, toUInt32_eq_ofNat] using hNext

structure Facts (before after : Store Unit) (root capacity source : UInt64)
    (os : List OrderL) : Prop where
  pages : after.mem.pages = before.mem.pages
  fresh : FreshOrderArrayAt after root capacity
  length : after.mem.read64 root.toUInt32 = UInt64.ofNat (os.length + 1)
  sourceOrders : OrdersAt after source os
  outside : MemEqOutsideFlatWords before after root ((os.length + 1) * 5)

theorem facts (st : Store Unit) (ctx : Context) (data : Project.ClobMatchFuel.LoopResult.OutputData)
    (need : UInt64) (h : HeapAppendMemory.Facts initial st ctx data need)
    (geo : HeapResidualFacts.Geometry ctx initial data)
    (hSize : ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
      (allocatedCapacity need data.nodes).toNat) :
    Facts st (initialized st (allocatedRoot data.g0 need data.nodes) ctx.result.book.length)
      (allocatedRoot data.g0 need data.nodes) (allocatedCapacity need data.nodes)
      data.book ctx.result.book := by
  let root := allocatedRoot data.g0 need data.nodes
  have hRootNat : root.toUInt32.toNat = root.toNat := by
    rw [toUInt32_toNat, Nat.mod_eq_of_lt (by have := h.root32; dsimp [root]; omega)]
  have hOutside : MemEqOutsideFlatWords st (initialized st root ctx.result.book.length)
      root ((ctx.result.book.length + 1) * 5) := by
    intro address hAddress
    exact Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by rw [hRootNat]; omega)
  have hSep : regionsDisjoint (flatWordsRegion root ((ctx.result.book.length + 1) * 5))
      (fixedArrayRegion data.book data.bookCapacity) := by
    have hh := h.bookSeparated
    have hr := h.root48
    have hb := geo.book48
    simp only [regionsDisjoint, fixedArrayRegion, allocatedNode, FreeNode.region] at hh
    simp only [regionsDisjoint, flatWordsRegion, fixedArrayRegion, root]
    omega
  refine {
    pages := Mem.write64_pages ..
    fresh := FreshFixedArrayAt.write64_data h.fresh h.root48 (by rw [hRootNat])
    length := Mem.read64_write64_same ..
    sourceOrders := ?_
    outside := hOutside }
  exact (OwnedOrderArrayAt.frame_outsideFlatWords
    (after := initialized st root ctx.result.book.length) geo.book48 geo.book32 geo.bookCapacity
    (Mem.write64_pages ..) hSep hOutside h.bookOwned).2

#print axioms spec
#print axioms facts
end Project.ClobLimit.HeapAppendHeader
