import Verified.Bytes.CopyByte
import Verified.Bytes.Overlay

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

theorem wp_copy {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {source destination : UInt64} {input output : LeanExe.Bytes}
    {sourceSlot destinationSlot countSlot indexSlot : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hSource : At store.mem source input)
    (hDestination : Heap.Buffer heap store destination output)
    (hSize : input.data.size = output.data.size)
    (hApart : source.toNat + input.data.size ≤ destination.toNat ∨
      destination.toNat + output.data.size ≤ source.toNat)
    (hSourceLocal : s.get sourceSlot = some (.i64 source))
    (hDestinationLocal : s.get destinationSlot = some (.i64 destination))
    (hCount : s.get countSlot = some (.i64 (UInt64.ofNat input.data.size)))
    (hSourceIndex : sourceSlot ≠ indexSlot) (hDestinationIndex : destinationSlot ≠ indexSlot)
    (hCountIndex : countSlot ≠ indexSlot)
    (hLow : s.params.length ≤ indexSlot) (hHigh : indexSlot < s.params.length + s.locals.length)
    (hNext : ∀ (store' : Store Unit) (s' : Locals), heap.At store' →
      Memory.WritesRange store store' destination.toNat (destination.toNat + output.data.size) →
      Heap.Buffer heap store' destination input → s'.params = s.params →
      s'.locals.length = s.locals.length →
      (∀ j, j ≠ indexSlot → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (copyCode sourceSlot destinationSlot countSlot indexSlot ++ rest) Q store s host := by
  have hInputSize : input.data.size < 2 ^ 32 := by
    rw [hSize]
    exact hDestination.size_lt
  simp only [copyCode, List.cons_append, List.nil_append,
    wp_constI64_cons]
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow0 : ({ s with values := s.values } : Locals).params.length ≤ indexSlot := hLow
  refine wp_block_cons ?_
  refine wp_loop_cons
    (fun st si => ∃ i, i ≤ input.data.size ∧ heap.At st ∧
      Memory.WritesRange store st destination.toNat (destination.toNat + output.data.size) ∧
      Heap.Buffer heap st destination (overlay input output hSize i) ∧
      si.params = s.params ∧ si.locals.length = s.locals.length ∧
      (∀ j, j ≠ indexSlot → si.get j = s.get j) ∧
      si.get indexSlot = some (.i64 (UInt64.ofNat i)))
    (fun _ si => match si.get indexSlot with
      | some (.i64 i) => input.data.size - i.toNat
      | _ => 0)
    ?_ ?_
  · refine ⟨0, Nat.zero_le _, hHeap, Memory.WritesRange.refl ..,
      by simpa only [overlay_zero] using hDestination, rfl, ?_, ?_, ?_⟩
    · simp [setLocal]
    · intro j hj
      rw [Locals.get_setLocal_ne hLow0 hj, Locals.get_values]
    · exact Locals.get_setLocal_same hLow0 hHigh
  · rintro st si ⟨i, hi, hHeapNow, hWrites, hDestinationNow, hParams, hLocals, hOther, hIndex⟩
    have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
      change i < 18446744073709551616
      omega)
    have hCount64 : (UInt64.ofNat input.data.size).toNat = input.data.size :=
      UInt64.toNat_ofNat_of_lt' (by change input.data.size < 18446744073709551616; omega)
    simp only [wp_localGet_cons, Locals.get_values, hIndex, hOther countSlot hCountIndex,
      hCount, wp_geUI64_cons, wp_br_if_cons]
    by_cases hDone : UInt64.ofNat input.data.size ≤ UInt64.ofNat i
    · have hEqual : i = input.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, hCount64] at hDone
        omega
      subst i
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte,
        List.take_zero, List.drop_zero, List.nil_append]
      rw [overlay_all] at hDestinationNow
      exact hNext st _ hHeapNow hWrites hDestinationNow hParams hLocals
        (fun j hj => hOther j hj) rfl
    · have hLess : i < input.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, hCount64] at hDone
        omega
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte]
      have hLessOutput : i < output.data.size := by rw [← hSize]; exact hLess
      have hOutput : (UInt64.ofNat i).toNat < (overlay input output hSize i).data.size := by
        rw [hi64, overlay_size]
        exact hLessOutput
      refine wp_copyByte hHeapNow (hSource.writesRange hWrites hApart) hDestinationNow
        (by rw [hi64]; exact hLess) hOutput
        ((hOther sourceSlot hSourceIndex).trans hSourceLocal)
        ((hOther destinationSlot hDestinationIndex).trans hDestinationLocal) hIndex ?_
      simp only [hi64]
      let st' := writeByte st destination (UInt64.ofNat i) input.data[i]
      have hWrite := hDestinationNow.write hHeapNow (UInt64.ofNat i) hOutput input.data[i]
      have hDestinationNext : Heap.Buffer heap st' destination
          (overlay input output hSize (i + 1)) := by
        simpa only [hi64, overlay_succ input output hSize i hLessOutput] using hWrite.2
      have hWriteRange := hDestinationNow.write_range (UInt64.ofNat i) hOutput input.data[i]
      rw [overlay_size] at hWriteRange
      have hWritesNext := hWrites.trans hWriteRange
      simp only [wp_localGet_cons, hIndex, wp_constI64_cons, wp_addI64_cons]
      have hLowI : si.params.length ≤ indexSlot := by rw [hParams]; exact hLow
      have hHighI : indexSlot < si.params.length + si.locals.length := by
        rw [hParams, hLocals]
        exact hHigh
      refine wp_localSet_local (s := si) (vs := si.values) hLowI hHighI ?_
      rw [wp_br_cons]
      dsimp only
      have hLowI' : ({ si with values := si.values } : Locals).params.length ≤ indexSlot := hLowI
      have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        rw [UInt64.ofNat_add]
        rfl
      have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
        UInt64.toNat_ofNat_of_lt' (by change i + 1 < 18446744073709551616; omega)
      refine ⟨⟨i + 1, hLess, hWrite.1, hWritesNext, hDestinationNext,
        hParams, ?_, ?_, ?_⟩, ?_⟩
      · simp [setLocal, hLocals]
      · intro j hj
        rw [Locals.get_values, Locals.get_setLocal_ne hLowI' hj, Locals.get_values]
        exact hOther j hj
      · rw [Locals.get_setLocal_same hLowI' hHighI, hSucc]
      · simp only [Locals.get_setLocal_same hLowI' hHighI, hSucc, hSucc64]
        omega

end Verified.Bytes
