import Project.ClobLimit.LimitResidualAllocCopy
import Project.ClobPostOnly.AppendStore

/-!
# Residual book finalization facts

The final five stores append one order after the copied flat-word prefix.  The
shared append-store semantics reconstruct the extended represented book.  The
same writes preserve the fresh header and the memory outside the new payload.
-/

namespace Project.ClobLimit.LimitResidualFinishFacts

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobLimit.LimitResidualCopyInvariant
  Project.ClobPostOnly.AppendStore

def finishStore (st : Store Unit) (g0 : UInt64) (n : Nat)
    (order : OrderL) : Store Unit :=
  appendOrderStore st g0 n order

structure FinishState (st0 st : Store Unit) (g0 capacity source : UInt64)
    (os : List OrderL) (order : OrderL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  bookOwned : OwnedOrderArrayAt st (g0 + 48) capacity (os ++ [order])
  outside : MemEqOutsideFlatWords st0 st (g0 + 48)
    ((os.length + 1) * 5)

theorem finish
    {st0 st1 : Store Unit} {g0 capacity source : UInt64}
    {os : List OrderL} {order : OrderL}
    (hState : CopyState st0 st1 (g0 + 48) source capacity os
      (os.length * 5))
    (hRoot : (g0 + 48).toNat = g0.toNat + 48)
    (hTarget48 : 48 ≤ (g0 + 48).toNat)
    (hTarget32 : (g0 + 48).toNat +
      ((os.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : (g0 + 48).toNat +
      ((os.length + 1) * 5 + 1) * 8 ≤ st0.mem.pages * 65536) :
    FinishState st0 (finishStore st1 g0 os.length order) g0 capacity source
      os order := by
  have hAddr (field : Nat) (hField1 : 1 ≤ field) (hField5 : field ≤ 5) :
      g0.toNat + 48 + (os.length * 5 + field) * 8 < 4294967296 := by
    rw [← hRoot]
    omega
  have hData (field : Nat) (hField1 : 1 ≤ field) (hField5 : field ≤ 5) :
      (g0 + 48).toNat ≤
        (UInt32.ofNat
          ((g0.toNat + 48 + (os.length * 5 + field) * 8) %
            4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (hAddr field hField1 hField5), hRoot]
    omega
  have hFresh1 := FreshFixedArrayAt.write64_data (value := order.oid)
    hState.fresh hTarget48 (hData 1 (by omega) (by omega))
  have hFresh2 := FreshFixedArrayAt.write64_data (value := order.otrader)
    hFresh1 hTarget48 (hData 2 (by omega) (by omega))
  have hFresh3 := FreshFixedArrayAt.write64_data (value := order.oside)
    hFresh2 hTarget48 (hData 3 (by omega) (by omega))
  have hFresh4 := FreshFixedArrayAt.write64_data (value := order.oprice)
    hFresh3 hTarget48 (hData 4 (by omega) (by omega))
  have hFresh5 := FreshFixedArrayAt.write64_data (value := order.oqty)
    hFresh4 hTarget48 (hData 5 (by omega) (by omega))
  have hOutside1 := hState.outside.write64
    (value := order.oid) hTarget32 (slot := os.length * 5 + 1) (by omega)
  have hOutside2 := hOutside1.write64
    (value := order.otrader) hTarget32 (slot := os.length * 5 + 2)
    (by omega)
  have hOutside3 := hOutside2.write64
    (value := order.oside) hTarget32 (slot := os.length * 5 + 3)
    (by omega)
  have hOutside4 := hOutside3.write64
    (value := order.oprice) hTarget32 (slot := os.length * 5 + 4)
    (by omega)
  have hOutside5 := hOutside4.write64
    (value := order.oqty) hTarget32 (slot := os.length * 5 + 5)
    (by omega)
  have hStoreAddr :
      g0.toNat + 48 + (os.length * 5 + 5) * 8 < 4294967296 :=
    hAddr 5 (by omega) (by omega)
  have hReads := appendOrderStore_reads st1 g0 os.length order hStoreAddr
  have hBook : OrdersAt (finishStore st1 g0 os.length order) (g0 + 48)
      (os ++ [order]) := by
    apply OrdersAt.ofFlatWords
    · have hRead := appendOrderStore_read_before st1 g0 os.length order
          (UInt32.ofNat ((g0 + 48).toNat % 4294967296)) hStoreAddr
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega), hRoot]
            omega)
      calc
        _ = st1.mem.read64
            (UInt32.ofNat ((g0 + 48).toNat % 4294967296)) := by
          simpa only [finishStore] using hRead
        _ = UInt64.ofNat (os.length + 1) := by
          rw [← toUInt32_eq_ofNat]
          exact hState.length
        _ = UInt64.ofNat (os ++ [order]).length := by simp
    · simp only [finishStore, appendOrderStore, Mem.write64_pages,
        hState.pages]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · intro j hj field hField
      by_cases hOld : j < os.length
      · have hGet : (os ++ [order])[j]! = os[j]! := by
          rw [getBang_eq hj, getBang_eq hOld]
          exact List.getElem_append_left hOld
        rw [hGet]
        calc
          orderWord (finishStore st1 g0 os.length order) (g0 + 48)
              (j * 5 + field) =
              orderWord st1 (g0 + 48) (j * 5 + field) := by
            unfold orderWord
            apply appendOrderStore_read_before st1 g0 os.length order _
              hStoreAddr
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega), hRoot]
            omega
          _ = orderWord st0 source (j * 5 + field) :=
            hState.copied _ (by omega)
          _ = os[j]!.word field :=
            hState.sourceInitial.orderWord_eq j field hOld hField
      · have hjEq : j = os.length := by
          simp at hj
          omega
        subst j
        have hGet : (os ++ [order])[os.length]! = order := by
          simp [getElem!_pos]
        rw [hGet]
        obtain ⟨h1, h2, h3, h4, h5⟩ := hReads
        interval_cases field
        · unfold orderWord
          rw [hRoot]
          simpa only [finishStore, OrderL.word] using h1
        · unfold orderWord
          rw [hRoot]
          simpa only [finishStore, OrderL.word] using h2
        · unfold orderWord
          rw [hRoot]
          simpa only [finishStore, OrderL.word] using h3
        · unfold orderWord
          rw [hRoot]
          simpa only [finishStore, OrderL.word] using h4
        · unfold orderWord
          rw [hRoot]
          simpa only [finishStore, OrderL.word] using h5
    · intro j hj field hField
      have hj' : j < os.length + 1 := by simpa using hj
      simp only [finishStore, appendOrderStore, Mem.write64_pages]
      rw [Nat.mod_eq_of_lt (by omega), hState.pages]
      omega
  refine {
    pages := by
      simp [finishStore, appendOrderStore, hState.pages]
    globals := hState.globals
    bookOwned := ⟨?_, hBook⟩
    outside := ?_ }
  · simpa only [finishStore, appendOrderStore, hRoot] using hFresh5
  · simpa only [finishStore, appendOrderStore, hRoot] using hOutside5

end Project.ClobLimit.LimitResidualFinishFacts
