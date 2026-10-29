import Verified.AlignedWriters
import Verified.Bytes.CopyOwned
import Verified.Bytes.Literal
import Verified.BytesLiteralCorrect

/-!
Buffers under the flag.  A buffer's bytes are read and written one at a time, so only the
allocation of its object makes 64-bit accesses, inside `alloc`, and the block it returns starts and
ends at multiples of 8 (`wpX_allocate`).  The byte loop of `copyCode` is free of 64-bit accesses
and calls, so `wpX_append_free` carries `wp_copy`.  `wpX_copyOwned` is `wp_copyOwned`, the copy
of a buffer into a new object, under the flag; an owned buffer's alignment is that of its nonzero
root's block.
-/

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.Pipeline.Bytes LeanExe.ProofKit LeanExe.Runtime

/-- `wp_allocate` under the flag. -/
theorem wpX_allocate {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (hHeapAl : strict = true → heap.Aligned)
    (h32 : count.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize count).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (bytes : LeanExe.Bytes),
      bytes.data.size = count.toNat →
      Step heap store (fun _ => True) heap' store' [block store' root] →
      Heap.Buffer heap' store' root bytes →
      AllocShape heap heap' count (capacityAt store' root) →
      heap'.top.toNat ≤ heap.top.toNat + c →
      (strict = true → root.toNat % 8 = 0 ∧ capacityAt store' root % 8 = 0 ∧ heap'.Aligned) →
      wpX strict m rest Q store' { s with values := .i64 root :: vs } host) :
    wpX strict m (.call 0 :: rest) Q store { s with values := .i64 count :: vs } host := by
  refine wpX_alloc hm hRt hAt hHeapAl h32 hCap hc hTrap fun hFits hTop => ?_
  have hBlock := hAt.allocate_block 1 hFits
  have hCapacity := allocated_capacity (allocSize count) heap.free
  refine hNext _ _ _ (snapshot _ _ count.toNat) (snapshot_size ..)
    (Step.allocate 1 hAt hFits) (block_snapshot hBlock ?_ _ ?_) ?_ hTop
    (fun hs => ⟨(hHeapAl hs).root (allocSize_mod8 count), by
      rw [hBlock.capacity_eq]; exact (hHeapAl hs).capacity_alloc (allocSize_mod8 count),
      (hHeapAl hs).allocate (allocSize_mod8 count)⟩)
  · have := allocSize_minimum count
    omega
  · have := le_allocSize h32
    omega
  · rw [hBlock.capacity_eq]
    exact Heap.allocate_shape h32 hFits

/-- `wp_copy` under the flag. -/
theorem wpX_copy {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit}
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
      wpX strict m rest Q store' s' host) :
    wpX strict m (copyCode sourceSlot destinationSlot countSlot indexSlot ++ rest) Q store s
      host := by
  refine wpX_append_free rfl ?_
  have := wp_copy (m := m) (host := host) (rest := []) (Q := ThenX strict m rest Q host)
    hHeap hSource hDestination hSize hApart hSourceLocal hDestinationLocal hCount hSourceIndex
    hDestinationIndex hCountIndex hLow hHigh
    fun store' s' h1 h2 h3 h4 h5 h6 h7 => wp_nil.mpr (hNext store' s' h1 h2 h3 h4 h5 h6 h7)
  rwa [List.append_nil] at this

/-- `wp_copyOwned` under the flag. -/
theorem wpX_copyOwned {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {source length : UInt64} {input : LeanExe.Bytes}
    {sourceSlot lengthSlot base : Nat} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hHeapAl : strict = true → heap.Aligned)
    (hSource : At store.mem source input)
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
      (length = 0 → root = 0) →
      (strict = true → heap'.Aligned ∧
        (root ≠ 0 → root.toNat % 8 = 0 ∧ capacityAt store' root % 8 = 0)) →
      wpX strict m rest Q store' { s' with values := .i64 length :: .i64 root :: s.values } host) :
    wpX strict m (copyOwnedCode sourceSlot lengthSlot base ++ rest) Q store s host := by
  have hSize : input.data.size < 2 ^ 32 := by
    have := hSource.memory
    have := hHeap.pages
    omega
  have hLength32 : length.toNat ≤ 4294967296 := by omega
  simp only [copyOwnedCode, List.cons_append, List.nil_append, wpX_localGet_cons,
    hLengthLocal, wpX_constI64_cons, wpX_eqI64_cons]
  refine wpX_iff_cons rfl ?_
  by_cases hZero : length = 0
  · subst length
    have hEmpty : input.data.size = 0 := hLength.symm
    have hRep : Rep heap store 0 0 input := ⟨hLength, Or.inl ⟨rfl, hEmpty⟩⟩
    simp only [Locals.get] at hLengthLocal
    simpa [hLengthLocal, regions, allocationCost, hEmpty] using
      hNext heap store s 0 (by simpa [regions] using Step.refl hHeap (fun _ => True))
        hRep (Frame.refl base s) (by simp [allocationCost, hEmpty]) (fun _ => rfl)
        (fun hs => ⟨hHeapAl hs, fun h => absurd rfl h⟩)
  · have hPositive : 0 < input.data.size := by
      have : length.toNat ≠ 0 := fun h => hZero (UInt64.toNat_inj.mp h)
      omega
    simp only [hZero, ite_false]
    rw [ite_eq_right (by decide : ¬ ((0 : UInt32) ≠ 0))]
    simp only [wpX_localGet_cons, hLengthLocal]
    refine wpX_allocate hm hRt hHeap hHeapAl hLength32 hCap
      (by rw [← allocationCost_eq (by omega : length.toNat ≠ 0) hLength32, hLength])
      (hTrap.imp fun _ h => h)
      fun heap1 store1 root bytes hBytesSize hAllocated hBuffer _ hTop hAlA => ?_
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
    refine wpX_localSet_local (s := s) (vs := s.values) hBase hHigh ?_
    let s1 := setLocal { s with values := s.values } base (.i64 root)
    have hFrame : Frame base s s1 := Frame.setValues hBase (Nat.le_refl _) (by omega)
    have hSource1Local : s1.get sourceSlot = some (.i64 source) := by
      rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values]
      exact hSourceLocal
    have hLength1Local : s1.get lengthSlot = some (.i64 (UInt64.ofNat input.data.size)) := by
      rw [Locals.get_setLocal_ne hLow (by omega), Locals.get_values, hLengthLocal,
        ← hLength, UInt64.ofNat_toNat]
    have hRootLocal : s1.get base = some (.i64 root) := Locals.get_setLocal_same hLow hHigh
    refine wpX_copy hAllocated.at_ hSource1 hBuffer (hLength.symm.trans hBytesSize.symm) hApart
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
    simp only [Locals.get] at hLength2
    simp only [wpX_localGet_cons, hRoot2, Locals.get_values]
    have hFinal := hNext heap1 store2 s2 root hStep' hRep (hFrame.trans hCopyFrame) hTop
      (fun h => absurd h hZero)
      (fun hs => ⟨(hAlA hs).2.2, fun _ => ⟨(hAlA hs).1, by rw [hCapacity]; exact (hAlA hs).2.1⟩⟩)
    simpa [hValues, s1, setLocal, hLength2] using hFinal


/-- `wp_literal` under the flag. -/
theorem wpX_literal {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {pool : LiteralPool} {bytes : Literal} {offset base : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hHeapAl : strict = true → heap.Aligned)
    (hPool : pool.Static heap store)
    (hOffset : literalOffset pool.values bytes = some offset) (hNonempty : bytes ≠ [])
    (hBase : s.params.length ≤ base) (hRoom : base + 4 ≤ s.positions)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocationCost bytes.length))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (root : UInt64),
      Step heap store (fun _ => True) heap' store' (regions store' root) →
      Rep heap' store' root (UInt64.ofNat bytes.length) bytes.value →
      Frame base s s' → heap'.top.toNat ≤ heap.top.toNat + allocationCost bytes.length →
      (strict = true → heap'.Aligned ∧
        (root ≠ 0 → root.toNat % 8 = 0 ∧ capacityAt store' root % 8 = 0)) →
      wpX strict m rest Q store'
        { s' with values := .i64 (UInt64.ofNat bytes.length) :: .i64 root :: s.values } host) :
    wpX strict m (literalCode (UInt64.ofNat (pool.base + offset)) bytes base ++ rest) Q
      store s host := by
  obtain ⟨hSource, hRegion⟩ := hPool.literal hOffset hNonempty
  have hLength : (UInt64.ofNat bytes.length).toNat = bytes.value.data.size := by
    have hSize : bytes.value.data.size = bytes.length := by
      simp [Literal.value, ByteArray.size]
    have hBound := hSource.memory
    have hPages := hHeap.pages
    rw [hSize]
    exact UInt64.toNat_ofNat_of_lt' (by change bytes.length < 2 ^ 64; omega)
  simp only [literalCode, List.cons_append, List.nil_append,
    wpX_constI64_cons]
  refine wpX_localSet_local (s := s) (vs := s.values) hBase
    (Locals.lt_total (by omega)) ?_
  let s1 := setLocal { s with values := s.values } base
    (.i64 (UInt64.ofNat (pool.base + offset)))
  have hFrame1 : Frame base s s1 := Frame.setValues hBase le_rfl (by omega)
  have hSource1 : s1.get base = some (.i64 (UInt64.ofNat (pool.base + offset))) :=
    Locals.get_setLocal_same hBase (Locals.lt_total (by omega))
  have hLow : s1.params.length ≤ base + 1 := by rw [hFrame1.params]; omega
  have hHigh : base + 1 < s1.positions := by rw [hFrame1.positions]; omega
  simp only [wpX_constI64_cons]
  refine wpX_localSet_local (s := s1) (vs := s.values) hLow (Locals.lt_total hHigh) ?_
  let s2 := setLocal { s1 with values := s.values } (base + 1)
    (.i64 (UInt64.ofNat bytes.length))
  have hFrame2 : Frame base s1 s2 := Frame.setValues hLow (by omega) hHigh
  have hSource2 : s2.get base = some (.i64 (UInt64.ofNat (pool.base + offset))) := by
    rw [Locals.get_setLocal_ne (s := { s1 with values := s.values }) hLow
      (by omega : base ≠ base + 1), Locals.get_values]
    exact hSource1
  have hLength2 : s2.get (base + 1) = some (.i64 (UInt64.ofNat bytes.length)) :=
    Locals.get_setLocal_same hLow (Locals.lt_total hHigh)
  show wpX strict m _ Q store s2 host
  refine wpX_copyOwned hm hRt hHeap hHeapAl hSource hRegion hLength hSource2 hLength2
    (by omega) (by omega) (by rw [hFrame2.params, hFrame1.params]; omega)
    (by rw [hFrame2.positions, hFrame1.positions]; omega) hCap
    (by simpa only [Literal.value, ByteArray.size, List.size_toArray] using hTrap)
    fun heap' store' s' root hStep hRep hFrame hTop _ hAlC => ?_
  have hNext' := hNext heap' store' s' root hStep hRep
    (hFrame1.trans (hFrame2.trans (hFrame.mono (by omega))))
    (by simpa only [Literal.value, ByteArray.size, List.size_toArray] using hTop) hAlC
  simpa only [s2, s1, setLocal] using hNext'


end Verified.Bytes

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- An owned buffer whose nonzero root's block starts and ends at multiples of 8 is aligned. -/
theorem Ty.AlignedVal.bytesOwned {store : Store Unit} {root l : UInt64} {v : LeanExe.Bytes}
    (h : root ≠ 0 → root.toNat % 8 = 0 ∧ capacityAt store root % 8 = 0) :
    Ty.AlignedVal .owned store .bytes [.i64 root, .i64 l] v := by
  intro r hr
  by_cases h0 : root = 0
  · subst h0
    simp [Ty.regions, Ty.blocks, Bytes.roots] at hr
  · simp only [Ty.regions, Ty.blocks, Bytes.roots, h0, ite_false, List.map_cons, List.map_nil,
      List.mem_singleton] at hr
    subst hr
    obtain ⟨hp, hc⟩ := h h0
    simp only [block]
    exact ⟨by omega, fun _ => by omega⟩

theorem specX_bytesLiteral {strict : Bool} {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {pool : Bytes.LiteralPool} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) (bytes : List UInt8)
    (hCover : (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).Covered pool) :
    ∀ (env : Env Γ) slots paid live, CodeSpecX strict m funs flags bounds fits host pv
      (Expr.bytesLiteral (S := S) (Γ := Γ) bytes) env slots paid live pool := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  by_cases hEmpty : bytes = []
  · subst bytes
    have hRep : Ty.bytes.Rep .owned heap store [.i64 0, .i64 0] (Bytes.Literal.value []) :=
      ⟨0, 0, rfl, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hAfter : After env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) []).uses i) live
        base heap store s .bytes .owned (Bytes.Literal.value []) heap store s [.i64 0, .i64 0] :=
      After.refl hAt hVars (fun i hi => by simp [hi]) hRep rfl
        (fun _ _ _ _ _ _ _ _ hb => nomatch hb)
    have hDone := hNext heap store s [.i64 0, .i64 0] hAfter
      (fun hs => ⟨(hAl hs).live_mono (fun i hi => by simp [hi]), Ty.AlignedVal.bytesNull⟩)
      (fun _ => Nat.le_add_right _ _)
    simpa [Expr.code, Expr.denote] using hDone
  · have hMember : bytes ∈ pool.values := hCover (by simp [Expr.literals, hEmpty])
    obtain ⟨offset, hOffset⟩ := Bytes.literalOffset_exists hMember
    have hWidth : base + 4 ≤ h := by simpa only [Expr.width, ite_eq_right hEmpty] using hRoom
    simp only [Expr.code, hEmpty, ite_false, hOffset]
    refine Bytes.wpX_literal hm hRt hAt (fun hs => (hAl hs).1) hSafe.static hOffset hEmpty hBase
      (by rw [hh]; exact hWidth) hCap
      (hTrap.alloc (by simp [Expr.aborts]) fun _ hw => hw.mono (by simp [Expr.allocs]))
      fun heap' store' s' root hStep hRep hFrame hTop hAlL => ?_
    have hBlocks : Mode.owned.fresh store' Ty.bytes
        [.i64 root, .i64 (UInt64.ofNat bytes.length)] (Bytes.Literal.value bytes) = Bytes.regions store' root :=
      Bytes.roots_regions store' root (UInt64.ofNat bytes.length)
    have hHold : Holds env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).uses i)
        base heap' store' s' :=
      (hVars.step hStep (fun _ _ _ _ _ _ _ _ => trivial)).agree hFrame
    have hAfter : After env slots
        (fun i => live i || (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).uses i) live
        base heap store s .bytes .owned (Bytes.Literal.value bytes) heap' store' s'
        [.i64 root, .i64 (UInt64.ofNat bytes.length)] := by
      refine ⟨?_, hFrame, hHold.live_mono (fun i hi => by simp [hi]),
        ⟨root, UInt64.ofNat bytes.length, rfl, hRep⟩, ?_⟩
      · rw [hBlocks]
        exact hStep.mono (fun _ _ => trivial) (fun _ hi => hi)
      · intro u y hy _ words hWords hLength block hBlock region hRegion
        obtain ⟨hSame, hFresh⟩ := hVars.regions_after hStep
          (by simp [hy]) ((hVars.hold_agree hFrame (by simp [hy]) hLength).mp hWords)
          hLength (fun _ _ => trivial)
        rw [hSame] at hRegion
        exact regionsDisjoint_symm (hFresh region hRegion block (by
          simpa only [← hBlocks, Ty.regions, Mode.fresh] using hBlock))
    have hDone := hNext heap' store' s' [.i64 root, .i64 (UInt64.ofNat bytes.length)] hAfter
      (fun hs => ⟨HoldsA.after hVars (hAl hs) hAfter (fun i hi => by simp [hi]) (hAlL hs).1,
        Ty.AlignedVal.bytesOwned (hAlL hs).2⟩)
      fun _ => top_unpaid rfl (by simp only [Expr.allocs]; omega)
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using hDone


end Verified
