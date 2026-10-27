import Verified.Bytes.BuildCode
import Verified.Bytes.StoreWord
import Verified.Bytes.Overlay

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

theorem wp_buildLoop {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {count root : UInt64} {output initial : LeanExe.Bytes}
    {base : Nat} {element rest : Program} {Q : Assertion Unit} {aborts : Bool}
    (P : Nat → Heap → Store Unit → Locals → Prop)
    (hHeap : heap.At store) (hBuffer : Heap.Buffer heap store root initial)
    (hSize : output.data.size = initial.data.size)
    (hLength : output.data.size = count.toNat)
    (hCount : s.get base = some (.i64 count))
    (hRoot : s.get (base + 1) = some (.i64 root))
    (hLow : s.params.length ≤ base + 2) (hHigh : base + 2 < s.positions)
    (hTrap : TrapOK aborts Q)
    (hInitial : P 0 heap store (setLocal { s with values := s.values } (base + 2) (.i64 0)))
    (hElement : ∀ (i : Nat) (hi : i < output.data.size)
        (heapI : Heap) (st : Store Unit) (si : Locals),
      heapI.At st → Heap.Buffer heapI st root (overlay output initial hSize i) →
      Frame base s si → si.get base = some (.i64 count) →
      si.get (base + 1) = some (.i64 root) →
      si.get (base + 2) = some (.i64 (UInt64.ofNat i)) → si.values = s.values →
      P i heapI st si → ∀ (tail : Program) (Post : Assertion Unit),
      TrapOK aborts Post →
      (∀ (heapE : Heap) (stE : Store Unit) (se : Locals) (value : UInt64),
        heapE.At stE → Heap.Buffer heapE stE root (overlay output initial hSize i) →
        Frame (base + 3) si se → value.toUInt8 = output.data[i] →
        P (i + 1) heapE (writeByte stE root (UInt64.ofNat i) value.toUInt8)
          (setLocal { se with values := si.values } (base + 2) (.i64 (UInt64.ofNat (i + 1)))) →
        wp m tail Post stE
          { se with values := .i64 value :: .i32 (root + UInt64.ofNat i).toUInt32 :: si.values }
          host) →
      wp m (element ++ tail) Post st
        { si with values := .i32 (root + UInt64.ofNat i).toUInt32 :: si.values } host)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals), heap'.At store' →
      Heap.Buffer heap' store' root output → Frame base s s' →
      s'.get base = some (.i64 count) → s'.get (base + 1) = some (.i64 root) →
      s'.get (base + 2) = some (.i64 (UInt64.ofNat output.data.size)) →
      P output.data.size heap' store' s' → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (buildLoopCode base (base + 1) (base + 2) element ++ rest) Q store s host := by
  have hBound : output.data.size < 2 ^ 32 := by rw [hSize]; exact hBuffer.size_lt
  simp only [buildLoopCode, List.cons_append, List.nil_append, wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hLow (Locals.lt_total hHigh) ?_
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ heapI i, i ≤ output.data.size ∧ heapI.At st ∧
      Heap.Buffer heapI st root (overlay output initial hSize i) ∧ Frame base s si ∧
      si.get base = some (.i64 count) ∧ si.get (base + 1) = some (.i64 root) ∧
      si.get (base + 2) = some (.i64 (UInt64.ofNat i)) ∧ si.values = s.values ∧
      P i heapI st si)
    (fun _ si => match si.get (base + 2) with
      | some (.i64 i) => output.data.size - i.toNat
      | _ => 0)
    ?_ ?_
  · refine ⟨heap, 0, Nat.zero_le _, hHeap, ?_, Frame.setValues hLow (by omega) hHigh,
      ?_, ?_, ?_, rfl, hInitial⟩
    · simpa only [overlay_zero] using hBuffer
    · rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values]
      exact hCount
    · rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values]
      exact hRoot
    · exact Locals.get_setLocal_same hLow (Locals.lt_total hHigh)
  · rintro st si ⟨heapI, i, hi, hHeapI, hBufferI, hFrameI, hCountI, hRootI, hIndexI,
      hValuesI, hPI⟩
    have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
      change i < 18446744073709551616
      omega)
    simp only [wp_localGet_cons, Locals.get_values, hIndexI, hCountI, wp_geUI64_cons,
      wp_br_if_cons]
    by_cases hDone : count ≤ UInt64.ofNat i
    · have hEqual : i = output.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, ← hLength] at hDone
        omega
      subst i
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte,
        List.take_zero, List.drop_zero, List.nil_append]
      rw [overlay_all] at hBufferI
      change wp m rest Q st { si with values := s.values } host
      rw [← hValuesI]
      exact hNext heapI st si hHeapI hBufferI hFrameI hCountI hRootI hIndexI hPI hValuesI
    · have hLess : i < output.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, ← hLength] at hDone
        omega
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte,
        hRootI, wp_addI64_cons, wp_wrapI64_cons, wrap_toUInt32]
      refine hElement i hLess heapI st si hHeapI hBufferI hFrameI hCountI hRootI hIndexI
        hValuesI hPI _ _ (by cases aborts <;> exact hTrap) ?_
      intro heapE stE se value hHeapE hBufferE hFrameE hValue hPE
      have hOutput : (UInt64.ofNat i).toNat < (overlay output initial hSize i).data.size := by
        rw [hi64, overlay_size, ← hSize]
        exact hLess
      refine wp_storeWord hHeapE hBufferE hOutput ?_
      have hWrite := hBufferE.write hHeapE (UInt64.ofNat i) hOutput value.toUInt8
      have hBufferNext : Heap.Buffer heapE (writeByte stE root (UInt64.ofNat i) value.toUInt8)
          root (overlay output initial hSize (i + 1)) := by
        simpa only [hi64, hValue, overlay_succ output initial hSize i (by omega)] using hWrite.2
      have hCountE : se.get base = some (.i64 count) :=
        (hFrameE.below base (by omega)).1.trans hCountI
      have hRootE : se.get (base + 1) = some (.i64 root) :=
        (hFrameE.below (base + 1) (by omega)).1.trans hRootI
      have hIndexE : se.get (base + 2) = some (.i64 (UInt64.ofNat i)) :=
        (hFrameE.below (base + 2) (by omega)).1.trans hIndexI
      have hLowE : se.params.length ≤ base + 2 := by rw [hFrameE.params, hFrameI.params]; exact hLow
      have hHighE : base + 2 < se.positions := by rw [hFrameE.positions, hFrameI.positions]; exact hHigh
      simp only [wp_localGet_cons, Locals.get_values, hIndexE, wp_constI64_cons, wp_addI64_cons]
      refine wp_localSet_local (s := se) (vs := si.values) hLowE (Locals.lt_total hHighE) ?_
      have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        rw [UInt64.ofNat_add]
        rfl
      have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
        UInt64.toNat_ofNat_of_lt' (by change i + 1 < 18446744073709551616; omega)
      rw [hSucc, wp_br_cons]
      dsimp only
      have hIndexNext := Locals.get_setLocal_same
        (s := { se with values := si.values }) (v := .i64 (UInt64.ofNat (i + 1)))
        hLowE (Locals.lt_total hHighE)
      refine ⟨⟨heapE, i + 1, hLess, hWrite.1, hBufferNext,
        hFrameI.trans ((hFrameE.mono (by omega)).trans
          (Frame.setValues hLowE (by omega) hHighE)), ?_, ?_, hIndexNext, hValuesI, hPE⟩, ?_⟩
      · rw [Locals.get_setLocal_ne (s := { se with values := si.values }) hLowE (by omega),
          Locals.get_values]
        exact hCountE
      · rw [Locals.get_setLocal_ne (s := { se with values := si.values }) hLowE (by omega),
          Locals.get_values]
        exact hRootE
      · simp only [hIndexNext, hSucc64, hi64]
        omega

end Verified.Bytes
