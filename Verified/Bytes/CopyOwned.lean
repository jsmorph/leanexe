import Verified.Bytes.Copy

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_copyOwned {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {source length : UInt64} {input : LeanExe.Bytes}
    {sourceSlot lengthSlot base : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hSource : At store.mem source input)
    (hRegion : heap.Region (source.toNat, input.data.size))
    (hLength : length.toNat = input.data.size)
    (hSourceLocal : s.get sourceSlot = some (.i64 source))
    (hLengthLocal : s.get lengthSlot = some (.i64 length))
    (hSourceBelow : sourceSlot < base) (hLengthBelow : lengthSlot < base)
    (hBase : s.params.length ≤ base) (hRoom : base + 2 ≤ s.positions)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocationCost input.data.size))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (root : UInt64),
      Step heap store (fun _ => True) heap' store' (regions store' root) →
      Rep heap' store' root length input → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + allocationCost input.data.size →
      wp m rest Q store' { s' with values := .i64 length :: .i64 root :: s.values } host) :
    wp m (copyOwnedCode sourceSlot lengthSlot base ++ rest) Q store s host := by
  have hSize : input.data.size < 2 ^ 32 := by
    have := hSource.memory
    have := hHeap.pages
    omega
  have hLength32 : length.toNat ≤ 4294967296 := by omega
  simp only [copyOwnedCode, List.cons_append, List.nil_append, wp_localGet_cons,
    hLengthLocal, wp_constI64_cons, wp_eqI64_cons]
  refine wp_iff_cons rfl ?_
  by_cases hZero : length = 0
  · subst length
    have hEmpty : input.data.size = 0 := hLength.symm
    have hRep : Rep heap store 0 0 input := ⟨hLength, Or.inl ⟨rfl, hEmpty⟩⟩
    simpa [wp_simp, regions, allocationCost, hEmpty] using
      hNext heap store s 0 (by simpa [regions] using Step.refl hHeap (fun _ => True))
        hRep (Frame.refl base s) (by simp [allocationCost, hEmpty])
  · have hPositive : 0 < input.data.size := by
      have : length.toNat ≠ 0 := fun h => hZero (UInt64.toNat_inj.mp h)
      omega
    simp only [hZero, ite_false]
    rw [ite_eq_right (by decide : ¬ ((0 : UInt32) ≠ 0))]
    simp only [wp_localGet_cons, hLengthLocal]
    refine wp_allocate hm hHeap hLength32 hCap
      (by rw [← allocationCost_eq (by omega : length.toNat ≠ 0) hLength32, hLength])
      (hTrap.imp fun _ h => h)
      fun heap1 store1 root bytes hBytesSize hAllocated hBuffer _ hTop => ?_
    obtain ⟨hSource1, hFresh⟩ := hSource.step hAllocated hRegion hPositive trivial
    have hApart : source.toNat + input.data.size ≤ root.toNat ∨
        root.toNat + bytes.data.size ≤ source.toNat := by
      have := hFresh _ (List.mem_singleton_self _)
      have := hBuffer.object.base
      have := hBuffer.capacity
      simp only [regionsDisjoint, block] at *
      omega
    have hLow : ({ s with values := s.values } : Locals).params.length ≤ base := hBase
    have hHigh : base < s.params.length + s.locals.length := by
      have := Locals.lt_total (by omega : base < s.positions)
      exact this
    refine wp_localSet_local (s := s) (vs := s.values) hBase hHigh ?_
    let s1 := setLocal { s with values := s.values } base (.i64 root)
    have hFrame : Frame base s s1 := Frame.setValues hBase (Nat.le_refl _) (by omega)
    have hSource1Local : s1.get sourceSlot = some (.i64 source) := by
      rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values]
      exact hSourceLocal
    have hLength1Local : s1.get lengthSlot = some (.i64 (UInt64.ofNat input.data.size)) := by
      rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values, hLengthLocal,
        ← hLength, UInt64.ofNat_toNat]
    have hRootLocal : s1.get base = some (.i64 root) := Locals.get_setLocal_same hLow hHigh
    refine wp_copy hAllocated.at_ hSource1 hBuffer (hLength.symm.trans hBytesSize.symm) hApart
      hSource1Local hRootLocal hLength1Local (by omega) (by omega) (by omega)
      (by dsimp [s1, setLocal]; omega)
      (Locals.lt_total (by rw [hFrame.positions]; omega))
      fun store2 s2 hHeap2 hWrites hOutput hParams hLocals hOther hValues => ?_
    have hCapacity := hBuffer.capacity_writesRange hWrites
    have hCopyFrame : Frame base s1 s2 := Frame.ofOthers hParams hLocals hOther (by omega)
      (by rw [hFrame.positions]; omega)
    have hWriteStep : Step heap1 store1
        (fun r => regionsDisjoint r (block store1 root)) heap1 store2 [] :=
      Step.ofWritesRange hHeap2 hWrites
        (by have := hBuffer.object.base; simp only [block]; omega)
        (by have := hBuffer.object.base; have := hBuffer.capacity; simp only [block]; omega)
    have hStep := hAllocated.writeFresh hWriteStep (List.mem_singleton_self _)
    have hStep' : Step heap store (fun _ => True) heap1 store2 (regions store2 root) := by
      simpa only [regions, ite_eq_right hOutput.nonzero, block_eq hCapacity] using hStep
    have hRep : Rep heap1 store2 root length input := ⟨hLength, Or.inr hOutput⟩
    have hLength2 : s2.get lengthSlot = some (.i64 length) := by
      rw [hOther lengthSlot (by omega), hLength1Local, ← hLength, UInt64.ofNat_toNat]
    have hRoot2 : s2.get base = some (.i64 root) := by
      rw [hOther base (by omega)]
      exact hRootLocal
    simp only [wp_localGet_cons, hRoot2, Locals.get_values, hLength2]
    have hFinal := hNext heap1 store2 s2 root hStep' hRep (hFrame.trans hCopyFrame) hTop
    simpa [hValues, s1, setLocal, wp_simp] using hFinal

end Verified.Bytes
