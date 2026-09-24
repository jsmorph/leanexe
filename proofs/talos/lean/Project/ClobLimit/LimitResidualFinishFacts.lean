import Project.ClobLimit.LimitResidualCopyInvariant
import Project.ClobLimit.OrderAppendStore

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
  Project.ClobLimit.OrderAppendStore

def finishStore (st : Store Unit) (target : UInt64) (n : Nat)
    (order : OrderL) : Store Unit :=
  appendOrderStore st target n order

structure FinishState (st0 st : Store Unit) (target capacity source : UInt64)
    (os : List OrderL) (order : OrderL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  bookOwned : OwnedOrderArrayAt st target capacity (os ++ [order])
  outside : MemEqOutsideFlatWords st0 st target
    ((os.length + 1) * 5)

theorem finish
    {st0 st1 : Store Unit} {target capacity source : UInt64}
    {os : List OrderL} {order : OrderL}
    (hState : CopyState st0 st1 target source capacity os
      (os.length * 5))
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat +
      ((os.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat +
      ((os.length + 1) * 5 + 1) * 8 ≤ st0.mem.pages * 65536) :
    FinishState st0 (finishStore st1 target os.length order) target capacity source
      os order := by
  have hAddr (field : Nat) (hField1 : 1 ≤ field) (hField5 : field ≤ 5) :
      target.toNat + (os.length * 5 + field) * 8 < 4294967296 := by
    omega
  have hData (field : Nat) (hField1 : 1 ≤ field) (hField5 : field ≤ 5) :
      target.toNat ≤
        (UInt32.ofNat
          ((target.toNat + (os.length * 5 + field) * 8) %
            4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (hAddr field hField1 hField5)]
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
      target.toNat + (os.length * 5 + 5) * 8 < 4294967296 :=
    hAddr 5 (by omega) (by omega)
  have hReads := appendOrderStore_reads st1 target os.length order hTarget48 hStoreAddr
  have hBook : OrdersAt (finishStore st1 target os.length order) target
      (os ++ [order]) := by
    apply OrdersAt.ofFlatWords
    · have hRead := appendOrderStore_read_before st1 target os.length order
          (UInt32.ofNat (target.toNat % 4294967296)) hTarget48 hStoreAddr
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)]
            omega)
      calc
        _ = st1.mem.read64
            (UInt32.ofNat (target.toNat % 4294967296)) := by
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
          orderWord (finishStore st1 target os.length order) target
              (j * 5 + field) =
              orderWord st1 target (j * 5 + field) := by
            unfold orderWord
            apply appendOrderStore_read_before st1 target os.length order _
              hTarget48 hStoreAddr
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)]
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
          simpa only [finishStore, OrderL.word] using h1
        · unfold orderWord
          simpa only [finishStore, OrderL.word] using h2
        · unfold orderWord
          simpa only [finishStore, OrderL.word] using h3
        · unfold orderWord
          simpa only [finishStore, OrderL.word] using h4
        · unfold orderWord
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
  · simpa only [finishStore, appendOrderStore] using hFresh5
  · simpa only [finishStore, appendOrderStore] using hOutside5

end Project.ClobLimit.LimitResidualFinishFacts
