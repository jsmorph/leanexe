import Verified.AlignedWriters
import Verified.Bytes.Copy
import Verified.Bytes.LiteralCode
import Verified.ExprSpec
import LeanExe.TalosCompat
import Verified.Bytes.LiteralFrame
import Verified.ArgsCorrect
import Verified.Bytes.AfterWrite
import Verified.Bytes.BuildCode
import Verified.LocalFrame
import LeanExe.Pipeline.Aborts
import Verified.Bytes.StoreWord
import Verified.Bytes.Overlay

/-!
Buffers under the flag.  A buffer's bytes are read and written one at a time, so only the
allocation of its object makes 64-bit accesses, inside `alloc`, and the block it returns starts and
ends at multiples of 8 (`wpX_allocate`).  The byte loop of `copyCode` is free of 64-bit accesses
and calls, so `wpX_append_free` transfers `wp_copy`.  `wpX_copyOwned` is `wp_copyOwned`, the copy
of a buffer into a new object, under the flag; an owned buffer's alignment is that of its nonzero
root's block.  `specX_bytesSet` writes one byte into an owned buffer, which keeps its block, so its
alignment persists (`Ty.AlignedVal.bytesBlock`).
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

theorem wp_allocate {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {count : UInt64} {vs : List Value} {rest : Program}
    {Q : Assertion Unit} {c : Nat} (hAt : heap.At store) (h32 : count.toNat ≤ 4294967296)
    (hCap : store.memoryCap m 0 ≤ 65535) (hc : allocCost (allocSize count).toNat ≤ c)
    (hTrap : TrapOK (!decide (heap.Within store m c)) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (root : UInt64) (bytes : LeanExe.Bytes),
      bytes.data.size = count.toNat →
      Step heap store (fun _ => True) heap' store' [block store' root] →
      Heap.Buffer heap' store' root bytes →
      AllocShape heap heap' count (capacityAt store' root) →
      heap'.top.toNat ≤ heap.top.toNat + c →
      wp m rest Q store' { s with values := .i64 root :: vs } host) :
    wp m (.call 0 :: rest) Q store { s with values := .i64 count :: vs } host :=
  wpX_allocate (strict := false) hm nofun hAt nofun h32 hCap hc hTrap
    (fun heap' store' root bytes a1 a2 a3 a4 a5 _ => hNext heap' store' root bytes a1 a2 a3 a4 a5)

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
      (length = 0 → root = 0) →
      wp m rest Q store' { s' with values := .i64 length :: .i64 root :: s.values } host) :
    wp m (copyOwnedCode sourceSlot lengthSlot base ++ rest) Q store s host :=
  wpX_copyOwned (strict := false) hm nofun hHeap nofun hSource hRegion hLength hSourceLocal
    hLengthLocal hSourceBelow hLengthBelow hBase hRoom hCap hTrap
    (fun heap' store' s' root a1 a2 a3 a4 a5 _ => hNext heap' store' s' root a1 a2 a3 a4 a5)

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

theorem wp_literal {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {pool : LiteralPool} {bytes : Literal} {offset base : Nat}
    {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hPool : pool.Static heap store)
    (hOffset : literalOffset pool.values bytes = some offset) (hNonempty : bytes ≠ [])
    (hBase : s.params.length ≤ base) (hRoom : base + 4 ≤ s.positions)
    (hCap : store.memoryCap m 0 ≤ 65535)
    (hTrap : TrapOK (!decide (heap.Within store m (allocationCost bytes.length))) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (root : UInt64),
      Step heap store (fun _ => True) heap' store' (regions store' root) →
      Rep heap' store' root (UInt64.ofNat bytes.length) bytes.value →
      Frame base s s' → heap'.top.toNat ≤ heap.top.toNat + allocationCost bytes.length →
      wp m rest Q store'
        { s' with values := .i64 (UInt64.ofNat bytes.length) :: .i64 root :: s.values } host) :
    wp m (literalCode (UInt64.ofNat (pool.base + offset)) bytes base ++ rest) Q
      store s host :=
  wpX_literal (strict := false) hm nofun hHeap nofun hPool hOffset hNonempty hBase hRoom hCap hTrap
    (fun heap' store' s' root a1 a2 a3 a4 _ => hNext heap' store' s' root a1 a2 a3 a4)

/-- `wp_storeWord` under the flag. -/
theorem wpX_storeWord {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {root index value : UInt64} {bytes : LeanExe.Bytes}
    {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Heap.Buffer heap store root bytes)
    (hi : index.toNat < bytes.data.size)
    (hNext : wpX strict m rest Q (writeByte store root index value.toUInt8)
      { s with values := vs } host) :
    wpX strict m (.wrapI64 :: .store8 0 :: rest) Q store
      { s with values := .i64 value :: .i32 (root + index).toUInt32 :: vs } host :=
  wpX_append_free (P := [.wrapI64, .store8 0]) rfl
    (wp_storeWord (m := m) (host := host) (rest := []) (Q := ThenX strict m rest Q host) hHeap h hi
      (wp_nil.mpr hNext))

/-- `wp_buildLoop` under the flag. -/
theorem wpX_buildLoop {strict : Bool} {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
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
        wpX strict m tail Post stE
          { se with values := .i64 value :: .i32 (root + UInt64.ofNat i).toUInt32 :: si.values }
          host) →
      wpX strict m (element ++ tail) Post st
        { si with values := .i32 (root + UInt64.ofNat i).toUInt32 :: si.values } host)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals), heap'.At store' →
      Heap.Buffer heap' store' root output → Frame base s s' →
      s'.get base = some (.i64 count) → s'.get (base + 1) = some (.i64 root) →
      s'.get (base + 2) = some (.i64 (UInt64.ofNat output.data.size)) →
      P output.data.size heap' store' s' → s'.values = s.values →
      wpX strict m rest Q store' s' host) :
    wpX strict m (buildLoopCode base (base + 1) (base + 2) element ++ rest) Q store s host := by
  have hBound : output.data.size < 2 ^ 32 := by rw [hSize]; exact hBuffer.size_lt
  simp only [buildLoopCode, List.cons_append, List.nil_append, wpX_constI64_cons]
  refine wpX_localSet_local (s := s) (vs := s.values) hLow (Locals.lt_total hHigh) ?_
  refine wpX_block_cons ?_
  refine wpX_loop_cons
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
    simp only [wpX_localGet_cons, Locals.get_values, hIndexI, hCountI, wpX_geUI64_cons,
      wpX_br_if_cons]
    by_cases hDone : count ≤ UInt64.ofNat i
    · have hEqual : i = output.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, ← hLength] at hDone
        omega
      subst i
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte,
        List.take_zero, List.drop_zero, List.nil_append]
      rw [overlay_all] at hBufferI
      change wpX strict m rest Q st { si with values := s.values } host
      rw [← hValuesI]
      exact hNext heapI st si hHeapI hBufferI hFrameI hCountI hRootI hIndexI hPI hValuesI
    · have hLess : i < output.data.size := by
        rw [UInt64.le_iff_toNat_le, hi64, ← hLength] at hDone
        omega
      simp (config := { decide := true }) only [ge_iff_le, hDone, ↓reduceIte,
        hRootI, wpX_addI64_cons, wpX_wrapI64_cons, wrap_toUInt32]
      refine hElement i hLess heapI st si hHeapI hBufferI hFrameI hCountI hRootI hIndexI
        hValuesI hPI _ _ (by cases aborts <;> exact hTrap) ?_
      intro heapE stE se value hHeapE hBufferE hFrameE hValue hPE
      have hOutput : (UInt64.ofNat i).toNat < (overlay output initial hSize i).data.size := by
        rw [hi64, overlay_size, ← hSize]
        exact hLess
      refine wpX_storeWord hHeapE hBufferE hOutput ?_
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
      simp only [wpX_localGet_cons, Locals.get_values, hIndexE, wpX_constI64_cons, wpX_addI64_cons]
      refine wpX_localSet_local (s := se) (vs := si.values) hLowE (Locals.lt_total hHighE) ?_
      have hSucc : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
        rw [UInt64.ofNat_add]
        rfl
      have hSucc64 : (UInt64.ofNat (i + 1)).toNat = i + 1 :=
        UInt64.toNat_ofNat_of_lt' (by change i + 1 < 18446744073709551616; omega)
      rw [hSucc, wpX_br_cons]
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
    wp m (buildLoopCode base (base + 1) (base + 2) element ++ rest) Q store s host :=
  wpX_buildLoop (strict := false) P hHeap hBuffer hSize hLength hCount hRoot hLow hHigh hTrap
    hInitial hElement hNext

theorem wpX_build_zero {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {count destination index : Nat} {element rest : Program} {Q : Assertion Unit}
    (hCount : s.get count = some (.i64 0))
    (hNext : wpX strict m rest Q store { s with values := .i64 0 :: .i64 0 :: s.values } host) :
    wpX strict m (buildCode count destination index element ++ rest) Q store s host := by
  simp only [buildCode, List.cons_append, List.nil_append, wpX_localGet_cons, hCount,
    wpX_constI64_cons, wpX_geUI64_cons]
  refine wpX_iff_cons rfl ?_
  simp (config := { decide := true }) only [↓reduceIte, wpX_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons,
    hCount, wpX_constI64_cons, wpX_eqI64_cons]
  refine wpX_iff_cons rfl ?_
  simp only [Locals.get] at hCount
  simpa [hCount] using hNext

theorem wp_build_zero {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {count destination index : Nat} {element rest : Program} {Q : Assertion Unit}
    (hCount : s.get count = some (.i64 0))
    (hNext : wp m rest Q store { s with values := .i64 0 :: .i64 0 :: s.values } host) :
    wp m (buildCode count destination index element ++ rest) Q store s host :=
  wpX_build_zero (strict := false) hCount hNext

theorem wpX_build_overflow {strict : Bool} {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {length : UInt64} {count destination index : Nat} {element rest : Program}
    {Q : Assertion Unit} (hCount : s.get count = some (.i64 length))
    (hLarge : 4294967296 ≤ length) (hTrap : TrapOK true Q) :
    wpX strict m (buildCode count destination index element ++ rest) Q store s host := by
  simp only [buildCode, List.cons_append, List.nil_append, wpX_localGet_cons, hCount,
    wpX_constI64_cons, wpX_geUI64_cons]
  refine wpX_iff_cons rfl ?_
  simp (config := { decide := true }) only [ge_iff_le, hLarge, ↓reduceIte]
  rw [wpX_unreachable_cons]
  exact hTrap _

theorem wp_build_overflow {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {length : UInt64} {count destination index : Nat} {element rest : Program}
    {Q : Assertion Unit} (hCount : s.get count = some (.i64 length))
    (hLarge : 4294967296 ≤ length) (hTrap : TrapOK true Q) :
    wp m (buildCode count destination index element ++ rest) Q store s host :=
  wpX_build_overflow (strict := false) hCount hLarge hTrap

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

theorem spec_bytesLiteral {S : List Sig} {Γ : List Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit}
    {pv : List Value} {pool : Bytes.LiteralPool} (hm : Runtime m) (bytes : List UInt8)
    (hCover : (Expr.bytesLiteral (S := S) (Γ := Γ) bytes).Covered pool) :
    ∀ (env : Env Γ) slots paid live, CodeSpec m funs flags bounds fits host pv
      (Expr.bytesLiteral (S := S) (Γ := Γ) bytes) env slots paid live pool :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_bytesLiteral (strict := false) hm nofun bytes hCover env slots
      paid live)

/-- The capacity of an aligned owned buffer at a nonzero root is a multiple of 8. -/
theorem Ty.AlignedVal.bytesCap {store : Store Unit} {root l : UInt64} {v : LeanExe.Bytes}
    (h : Ty.AlignedVal .owned store .bytes [.i64 root, .i64 l] v) (h0 : root ≠ 0) :
    capacityAt store root % 8 = 0 := by
  have := (h (block store root) (by simp [Ty.regions, Ty.blocks, Bytes.roots, h0])).2 rfl
  simp only [block] at this
  omega

variable {pool : Bytes.LiteralPool}

theorem specX_bytesBuild {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) (hRA : strict = true → ReleaseAligned m)
    (hRt : strict = true → AllocAligned m) {Γ : List Ty} {count : Expr S Γ .word}
    {elem : Expr S (.word :: Γ) .word}
    (countSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv count env
      slots paid live)
    (elemSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv elem env
      slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv (Expr.bytesBuild count elem)
      env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom hPlace
    rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hc := Nat.le_max_left count.width (3 + elem.width)
  have he := Nat.le_max_right count.width (3 + elem.width)
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  let all := fun i => live i || elem.uses (i + 1)
  let n := (count.denote funs env).toNat
  let output := LeanExe.Bytes.build (count.denote funs env)
    fun i => elem.denote funs (.cons i env)
  let countCost := count.allocs funs flags bounds (slots.map Slot.mode) paid all env
  let bodyCost := fun k => elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode)
    (false :: paid) (shift 1 all) (.cons (UInt64.ofNat k) env)
  have hBodyCost (k : Nat) : bodyCost k =
      elem.allocs funs flags bounds (.borrowed :: slots.map Slot.mode) (false :: paid)
        (shift 1 all) (.cons (UInt64.ofNat k) env) := rfl
  let countPot := dyingPot store s env slots paid (fun i => all i || count.uses i) all
  have hT : (Expr.bytesBuild count elem).allocs funs flags bounds (slots.map Slot.mode)
      paid live env = countCost + Bytes.allocationCost n + sumBelow bodyCost n := rfl
  have hOutputSize : output.data.size = n := LeanExe.Bytes.data_size_build ..
  have hdK : (Expr.bytesBuild count elem).fits funs fits env = true →
      count.fits funs fits env = true ∧
        ∀ k, k < n → elem.fits funs fits (.cons (UInt64.ofNat k) env) = true := fun hd => by
    simp only [Expr.fits, Bool.and_eq_true] at hd
    exact ⟨hd.1, allBelow_get hd.2⟩
  have hTrapW : ¬heap.Within store m
      (dyingPot store s env slots paid (fun i => live i || (Expr.bytesBuild count elem).uses i)
          live +
        (Expr.bytesBuild count elem).allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      TrapOK true Q := fun hw => hTrap.of_imp fun _ => by simp [trapFlag, Expr.aborts, hw]
  have hCountIn : ∀ i, (all i || count.uses i) = true →
      (live i || (Expr.bytesBuild count elem).uses i) = true := fun i hi => by
    simp only [Expr.uses]
    exact live_seq _ _ _ hi
  have hDk : countPot ≤ dyingPot store s env slots paid
      (fun i => live i || (Expr.bytesBuild count elem).uses i) live :=
    dyingPot_mono hCountIn fun i hi => by simp [all, hi]
  have hDe : ∀ (v : UInt64) (st' : Store Unit) (s' : Locals) (sl : Slot),
      dyingPot st' s' (Env.cons (t := .word) v env) (sl :: slots) (false :: paid)
        (fun j => shift 1 all j || elem.uses j) (shift 1 all) = 0 := fun _ _ _ _ =>
    dyingPot_eq_zero_unpaid fun j h0 h1 => by
      match j with
      | 0 => rfl
      | k + 1 =>
        have hk : ¬k + 1 < 1 := by omega
        simp only [shift, hk, ↓reduceIte, Nat.add_sub_cancel] at h0 h1
        simp only [all] at h0 h1
        revert h0 h1
        cases live k <;> cases elem.uses (k + 1) <;> simp
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  refine countSpec env slots paid all h base heap store s hh hpv
    (hVars.live_mono hCountIn) hAt (fun hs => (hAl hs).live_mono hCountIn)
    (hSafe.mono hCountIn) hCap hBase (by omega) hPlace.1 _ _
    (hTrap.part (fun hd => by simp only [Bool.not_eq_true'] at hd; simp [Expr.fits, hd])
      (fun _ => by simp [Expr.aborts]) fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlK hTopK => ?_
  have hRepK := a1.rep
  simp only [Ty.rep_word] at hRepK
  subst hRepK
  have e1 := a1.toEvolves rfl
  have hp1 : s1.params = s.params := e1.frame.params
  have hh1 : s1.positions = h := e1.frame.positions.trans hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hLow1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
    show s1.params.length ≤ base
    rw [hp1]
    exact hBase
  have hHigh1 : base < s1.positions := by rw [hh1]; omega
  refine wpX_localSet_local hLow1 (Locals.lt_total hHigh1) ?_
  set s2 := setLocal { s1 with values := s.values } base (.i64 (count.denote funs env)) with hs2
  have f2 : Frame base s1 s2 := Frame.setValues hLow1 le_rfl hHigh1
  have hN2 : s2.get base = some (.i64 (count.denote funs env)) :=
    Locals.get_setLocal_same hLow1 (Locals.lt_total hHigh1)
  have hh2 : s2.positions = h := f2.positions.trans hh1
  have hp2 : s2.params = s.params := f2.params.trans hp1
  have hVars1 : Holds env slots all base heap1 store1 s2 := e1.holds.agree f2
  have hFinish : ∀ (heapF : Heap) (storeF : Store Unit) (sf : Locals) (root : UInt64),
      After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
        heap store s .bytes .owned output heapF storeF sf [.i64 root, .i64 (count.denote funs env)] →
      (strict = true → heapF.Aligned ∧ Ty.AlignedVal .owned storeF .bytes
        [.i64 root, .i64 (count.denote funs env)] output) →
      ((Expr.bytesBuild count elem).fits funs fits env = true →
        heapF.top.toNat ≤ heap.top.toNat + countPot + countCost + Bytes.allocationCost n +
          sumBelow bodyCost n) →
      wpX strict m (releaseWhere Γ slots (fun i => elem.uses (i + 1) && !live i) ++ rest) Q storeF
        { sf with values := .i64 (count.denote funs env) :: .i64 root :: s.values } host := by
    intro heapF storeF sf root aF hAlF hTopF
    refine After.releaseX hm hRA (s1 := sf) (live := live)
      (sel := fun i => elem.uses (i + 1) && !live i) hVars aF
      (fun hs => ⟨HoldsA.after hVars (hAl hs) aF
        (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi) (hAlF hs).1, (hAlF hs).2⟩)
      (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi)
      (fun i hi => by simp only [Bool.and_eq_true] at hi; simp [all, hi.1])
      (fun i hi => by simp [all, hi]) fun heap' store' a' hTopR _ hAl' => ?_
    have hDone := hNext heap' store' sf [.i64 root, .i64 (count.denote funs env)] a' hAl'
      fun hd => top_unpaid rfl (by
        have := hTopF hd
        have := congrArg UInt64.toNat hTopR
        rw [hT]
        omega)
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] using hDone
  by_cases hZero : count.denote funs env = 0
  · have hn : n = 0 := by simp only [n, hZero, UInt64.toNat_zero]
    have hEmpty : output.data.size = 0 := hOutputSize.trans hn
    have aZero : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all
        base heap store s .bytes .owned output heap1 store1 s2 [.i64 0, .i64 (count.denote funs env)] := by
      refine ⟨?_, e1.frame.trans f2, hVars1,
        ⟨0, count.denote funs env, rfl, ⟨by rw [hZero, UInt64.toNat_zero, hEmpty],
          Or.inl ⟨rfl, hEmpty⟩⟩⟩, ?_⟩
      · simpa only [Mode.fresh, Ty.blocks, Bytes.roots, ↓reduceIte, List.map_nil] using
          (e1.step.mono (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) fun _ h => h)
      · intro _ _ _ _ _ _ _ _ hb
        exact nomatch hb
    refine Bytes.wpX_build_zero (by simpa only [hZero] using hN2) ?_
    have hDone := hFinish heap1 store1 s2 0 aZero
      (fun hs => ⟨(hAlK hs).1.1, Ty.AlignedVal.bytesNull⟩) fun hd => by
      have := hTopK (hdK hd).1
      simp only [n, hZero, UInt64.toNat_zero, sumBelow, Bytes.allocationCost]
      omega
    simpa only [hZero, hs2, setLocal] using hDone
  by_cases hBig : 4294967296 ≤ count.denote funs env
  · refine Bytes.wpX_build_overflow hN2 hBig (hTrapW fun hw => ?_)
    have hLarge := UInt64.le_iff_toNat_le.mp hBig
    simp only [UInt64.reduceToNat] at hLarge
    have hn : n ≠ 0 := by dsimp only [n]; omega
    have hCost := Bytes.allocationCost_ge hn
    unfold Heap.Within at hw
    rw [hT] at hw
    dsimp only [n] at hCost hw
    omega
  have h32 : (count.denote funs env).toNat < 4294967296 := by
    have hLess := UInt64.not_le.mp hBig
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] using hLess
  simp only [Bytes.buildCode, List.cons_append, List.nil_append, wpX_localGet_cons,
    hN2, wpX_constI64_cons, wpX_geUI64_cons]
  refine wpX_iff_cons rfl ?_
  simp (config := { decide := true }) only [ge_iff_le, hBig, ↓reduceIte, wpX_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons,
    hN2, wpX_constI64_cons, wpX_eqI64_cons]
  refine wpX_iff_cons rfl ?_
  simp only [hZero, ite_false]
  rw [ite_eq_right (by decide : ¬((0 : UInt32) ≠ 0))]
  simp only [wpX_localGet_cons, hN2]
  have hLowD : s2.params.length ≤ base + 1 := by rw [hp2]; omega
  have hHighD : base + 1 < s2.positions := by rw [hh2]; omega
  refine Bytes.wpX_allocate hm hRt e1.step.at_ (fun hs => (hAlK hs).1.1) (by omega)
    (by rw [e1.step.cap m]; exact hCap)
    (c := Bytes.allocationCost n)
    (by rw [← Bytes.allocationCost_eq (by exact fun hz => hZero (UInt64.toNat_inj.mp hz)) (by omega)])
    ((hTrap.alloc (by simp [Expr.aborts]) fun hd hw => by
      have := hTopK (hdK (fits_of_not hd)).1
      exact hw.shift (c1 := countPot + countCost) (by omega) (by rw [hT]; omega)
        (e1.step.cap m)).imp fun _ ht => ht)
    fun heap2 store2 root initial hSize hStepA hBuffer _ hTopA hAlA => ?_
  have hRootAl : strict = true → root.toNat % 8 = 0 := fun hs => (hAlA hs).1
  refine wpX_localSet_local (s := s2) (vs := s2.values) hLowD (Locals.lt_total hHighD) ?_
  set s3 := setLocal { s2 with values := s2.values } (base + 1) (.i64 root) with hs3
  have f3 : Frame base s2 s3 := Frame.setValues hLowD (by omega) hHighD
  have hN3 : s3.get base = some (.i64 (count.denote funs env)) := by
    rw [Locals.get_setLocal_ne (s := { s2 with values := s2.values }) hLowD (by omega),
      Locals.get_values]
    exact hN2
  have hRoot3 : s3.get (base + 1) = some (.i64 root) :=
    Locals.get_setLocal_same hLowD (Locals.lt_total hHighD)
  have hh3 : s3.positions = h := f3.positions.trans hh2
  have hp3 : s3.params = s.params := f3.params.trans hp2
  have hVars3 : Holds env slots all base heap1 store1 s3 := hVars1.agree f3
  have a0 : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
      heap store s .bytes .owned initial heap2 store2 s3
      [.i64 root, .i64 (count.denote funs env)] := by
    refine ⟨?_, e1.frame.trans (f2.trans f3),
      hVars3.step hStepA (fun _ _ _ _ _ _ _ _ => trivial),
      ⟨root, count.denote funs env, rfl, hSize.symm, Or.inr hBuffer⟩, ?_⟩
    · simpa only [Mode.fresh, Ty.blocks, Bytes.roots, ite_eq_right hBuffer.nonzero,
        List.map_cons, List.map_nil] using
        ((e1.step.trans hStepA fun _ hr => ⟨hr, fun _ => trivial⟩).mono
          (fun _ hr => hr.mono fun i h1 h2 => ⟨hCountIn i h1, h2⟩) fun _ hi => hi)
    · intro u y hy _ wy hwy hly b hb c hc
      obtain ⟨hSame, hFresh⟩ := hVars3.regions_after hStepA hy hwy hly fun _ _ => trivial
      rw [hSame] at hc
      exact regionsDisjoint_symm (hFresh c hc b (by
        simpa only [Ty.regions, Ty.blocks, Bytes.roots, ite_eq_right hBuffer.nonzero,
          List.map_cons, List.map_nil] using hb))
  have hSizes : output.data.size = initial.data.size := hOutputSize.trans hSize.symm
  let P := fun i heapI st si =>
    After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
      heap store s .bytes .owned (Bytes.overlay output initial hSizes i) heapI st si
      [.i64 root, .i64 (count.denote funs env)] ∧
    ((Expr.bytesBuild count elem).fits funs fits env = true →
      heapI.top.toNat ≤ heap.top.toNat + countPot + countCost + Bytes.allocationCost n +
        sumBelow bodyCost i) ∧
    (strict = true → heapI.Aligned ∧ Ty.AlignedVal .owned st .bytes
      [.i64 root, .i64 (count.denote funs env)] (Bytes.overlay output initial hSizes i))
  refine Bytes.wpX_buildLoop P hStepA.at_ hBuffer hSizes hOutputSize hN3 hRoot3
    (by rw [hp3]; omega) (by rw [hh3]; omega) (hTrap.imp fun _ ht => ht) ?_ ?_ ?_
  · refine ⟨?_, fun hd => ?_,
      fun hs => ⟨(hAlA hs).2.2, Ty.AlignedVal.bytesOwned fun _ => ⟨(hAlA hs).1, (hAlA hs).2.1⟩⟩⟩
    · simpa only [Bytes.overlay_zero] using a0.reframe
        (Frame.setValues (s := s3) (vs := s3.values) (by rw [hp3]; omega) (by omega)
          (by rw [hh3]; omega))
    · have := hTopK (hdK hd).1
      simp only [sumBelow]
      omega
  · intro i hi heapI st si hHeapI hBufferI hFrameI hNi hRooti hIdxi hValuesI hPI
      tail Post hTrapPost hNextE
    obtain ⟨aI, hInv, hAlP⟩ := hPI
    have hiN : i < n := by rw [← hOutputSize]; exact hi
    have hi64 : (UInt64.ofNat i).toNat = i :=
      UInt64.toNat_ofNat_of_lt' (by change i < 18446744073709551616; dsimp only [n] at hiN; omega)
    have holdIdx : LocalsHold si (base + 2) Ty.word.types [.i64 (UInt64.ofNat i)] := by
      intro j hj
      obtain rfl : j = 0 := by simpa using hj
      simpa [Ty.types, slotIndex] using hIdxi
    have hhi : si.positions = h := aI.frame.positions.trans hh
    have hLE : ∀ j, (shift 1 all (j + 1) || elem.uses (j + 1)) = true → all j = true :=
      fun j hj => by simp only [shift_add] at hj; exact live_dup _ _ hj
    have hVarsI : Holds env slots all (base + 2) heapI st si := aI.holds.mono (by omega)
    have hVarsE := (Holds.push (t := .word) (v := UInt64.ofNat i) (mode := .borrowed)
      (live' := fun j => shift 1 all j || elem.uses j) (hVarsI.live_mono hLE)
      holdIdx rfl (Holds.Apart.ofScalar rfl)).mono (base' := base + 3) (by simp [Ty.width])
    have hSafeI := (hSafe.after hVars aI (fun i hi => by
      simp only [Expr.uses]
      exact live_build _ _ _ hi)).1
    have hSafeE : pool.Safe (.cons (UInt64.ofNat i) env)
        (⟨base + 2, .borrowed⟩ :: slots) (fun j => shift 1 all j || elem.uses j) heapI st si :=
      (hSafeI.mono hLE).push holdIdx
        (show Ty.word.Rep .borrowed heapI st [.i64 (UInt64.ofNat i)] (UInt64.ofNat i) from rfl)
        (by simp [Mode.fresh])
    refine elemSpec _ _ (false :: paid) (shift 1 all) h (base + 3) heapI st
      { si with values := .i32 (root + UInt64.ofNat i).toUInt32 :: si.values } hhi
      (aI.frame.params.trans hpv) (hVarsE.agree Frame.ofValues) hHeapI
      (fun hs => (HoldsA.push ((HoldsA.after hVars (hAl hs) aI
        (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi) (hAlP hs).1).live_mono hLE)
        holdIdx rfl (Ty.AlignedVal.scalar rfl)).values _)
      (hSafeE.values _)
      (by rw [aI.step.cap m]; exact hCap)
      (by show si.params.length ≤ base + 3; rw [aI.frame.params]; omega) (by omega)
      hPlace.2 tail Post
      ((hTrapPost.part (fun hd => by
          cases hw : (Expr.bytesBuild count elem).fits funs fits env
          · rfl
          · exact absurd ((hdK hw).2 i hiN) (by simpa using hd))
        (fun _ => by simp [Expr.aborts]) fun hd hw => hw.of_le (by
          have := hInv (fits_of_not hd)
          have := sumBelow_mono bodyCost (show i + 1 ≤ n by omega)
          simp only [sumBelow] at this
          rw [hDe]
          simp only [List.map_cons]
          rw [← hBodyCost i]
          rw [hT]
          omega) (aI.step.cap m)).imp fun _ ht => ht)
      fun heapE stE sE wsE aE hAlE hTopE => ?_
    have hRE := aE.rep
    simp only [Ty.rep_word] at hRE
    subst hRE
    have aE1 := After.bind (base := base + 2) hVarsI
      (After.refl (t := .word) (mode := .borrowed) (v := UInt64.ofNat i)
        (ws := [.i64 (UInt64.ofNat i)]) aI.step.at_ hVarsI (fun _ hi => hi) rfl rfl
        (Holds.Apart.ofScalar rfl))
      (Frame.refl _ _) holdIdx aE.ofValues hLE (fun _ hi => hi) fun _ hi => hi
    have aE2 := aE1.lower aI.holds (by omega) fun _ hi => hi
    obtain ⟨hStep, hFrame, hRep, hApart, -⟩ := After.seq hVars aI aE2
      (fun i hi => by simp only [Expr.uses]; exact live_build _ _ _ hi) fun _ hi => hi
    have aI2 : After env slots (fun i => live i || (Expr.bytesBuild count elem).uses i) all base
        heap store s .bytes .owned (Bytes.overlay output initial hSizes i) heapE stE sE
        [.i64 root, .i64 (count.denote funs env)] :=
      ⟨hStep.mono (fun _ hi => hi) fun _ hb => List.mem_append_left _ hb,
        hFrame, aE2.holds, hRep, hApart⟩
    have hOutput : (UInt64.ofNat i).toNat < (Bytes.overlay output initial hSizes i).data.size := by
      rw [hi64, Bytes.overlay_size, ← hSizes]
      exact hi
    have hValue : (elem.denote funs (.cons (UInt64.ofNat i) env)).toUInt8 = output.data[i] := by
      simp only [output, LeanExe.Bytes.build, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
    have hBufferE := aI2.bytes_rep.buffer.resolve_left fun hz => by
      have := hz.2
      rw [Bytes.overlay_size, hSize] at this
      have hn : (count.denote funs env).toNat ≠ 0 :=
        fun hz => hZero (UInt64.toNat_inj.mp hz)
      exact hn this
    refine hNextE heapE stE sE _ aE.step.at_ hBufferE aE.frame.values hValue ?_
    refine ⟨?_, fun hd => ?_, fun hs => ⟨(hAlE hs).1.1, Ty.AlignedVal.bytesOwned fun h0 =>
      ⟨hRootAl hs, by
        rw [(hBufferE.write_step aE.step.at_ (UInt64.ofNat i) hOutput
          (elem.denote funs (.cons (UInt64.ofNat i) env)).toUInt8).2]
        exact Ty.AlignedVal.bytesCap (After.alignedSeq' aI aE2 (hAlP hs).2) h0⟩⟩⟩
    · have hWrite := aI2.writeByte hOutput
        (elem.denote funs (.cons (UInt64.ofNat i) env)).toUInt8
      have hLowE : sE.params.length ≤ base + 2 := by rw [aE.frame.params, aI.frame.params]; omega
      have hHighE : base + 2 < sE.positions := by
        rw [aE.frame.positions, Locals.positions_values, hhi]
        omega
      simpa only [hi64, hValue, Bytes.overlay_succ output initial hSizes i (by omega)] using
        hWrite.reframe (Frame.setValues hLowE (by omega) hHighE)
    · have := hInv hd
      have hE := hTopE ((hdK hd).2 i hiN)
      rw [hDe] at hE
      simp only [List.map_cons] at hE
      rw [← hBodyCost i] at hE
      simp only [sumBelow]
      omega
  · intro heapF storeF sf hHeapF hOutput hFrameF hCountF hRootF _ hPF hValuesF
    obtain ⟨aF, hTopF, hAlF⟩ := hPF
    rw [Bytes.overlay_all] at aF hAlF
    simp only [wpX_localGet_cons, hRootF, wpX_nil]
    simp only [List.take_zero, List.drop_zero, List.nil_append, List.take_succ_cons,
      List.take_zero, List.nil_append, List.cons_append, Locals.get_values, hCountF]
    have hDone := hFinish heapF storeF sf root aF hAlF (by simpa only [hOutputSize] using hTopF)
    simpa only [hs3, hs2, setLocal, hValuesF] using hDone

theorem spec_bytesBuild {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S}
    {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hm : Runtime m) {Γ : List Ty} {count : Expr S Γ .word}
    {elem : Expr S (.word :: Γ) .word}
    (countSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv count env
      slots paid live)
    (elemSpec : ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv elem env
      slots paid live) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv (Expr.bytesBuild count elem)
      env slots paid live :=
  fun env slots paid live =>
    CodeSpecX.false_iff.mp (specX_bytesBuild (strict := false) hm nofun nofun
      (fun env slots paid live => CodeSpecX.false_iff.mpr (countSpec env slots paid live))
      (fun env slots paid live => CodeSpecX.false_iff.mpr (elemSpec env slots paid live)) env slots
      paid live)


/-- An owned buffer stays aligned when the block of its root keeps its place and capacity. -/
theorem Ty.AlignedVal.bytesBlock {store store' : Store Unit} {root l : UInt64}
    {v v' : LeanExe.Bytes} (h : Ty.AlignedVal .owned store .bytes [.i64 root, .i64 l] v)
    (hBlock : block store' root = block store root) :
    Ty.AlignedVal .owned store' .bytes [.i64 root, .i64 l] v' := by
  intro r hr
  by_cases h0 : root = 0
  · subst h0
    simp [Ty.regions, Ty.blocks, Bytes.roots] at hr
  · simp only [Ty.regions, Ty.blocks, Bytes.roots, h0, ite_false, List.map_cons, List.map_nil,
      List.mem_singleton] at hr
    subst hr
    rw [hBlock]
    exact h _ (by simp [Ty.regions, Ty.blocks, Bytes.roots, h0])

/-- `x.set i v` of a buffer: the position in local `base`, the value in local `base + 1`, the
buffer as owned, with its root in local `base + 2` and its length in local `base + 3`, which is
`x`'s own block when `x` is owned and dies, and, when the position is below the length, the write
of the value's low byte at the root plus the position. -/
theorem specX_bytesSet {strict : Bool} {S : List Sig} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    (hCopy : CopyCodeX strict m host) {Γ : List Ty} (x : Var Γ .bytes) {i v : Expr S Γ .word}
    (iSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host
      pv i env slots paid live)
    (vSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host
      pv v env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.bytesSet x i v) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
    hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hcw : copyWidth Ty.bytes = 4 := rfl
  have hi := Nat.le_max_left i.width (max (1 + v.width) (2 + copyWidth Ty.bytes))
  have hv := (Nat.le_max_left (1 + v.width) (2 + copyWidth Ty.bytes)).trans
    (Nat.le_max_right i.width _)
  have hx := (Nat.le_max_right (1 + v.width) (2 + copyWidth Ty.bytes)).trans
    (Nat.le_max_right i.width _)
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  have hT : (Expr.bytesSet x i v).allocs funs flags bounds (slots.map Slot.mode) paid live env =
      i.allocs funs flags bounds (slots.map Slot.mode) paid
          (fun j => live j || j == x.index || v.uses j) env +
        v.allocs funs flags bounds (slots.map Slot.mode) paid (fun j => live j || j == x.index)
          env +
        x.ownedCost (slots.map Slot.mode) live (env.get x) := rfl
  have hdS : (Expr.bytesSet x i v).fits funs fits env = true →
      i.fits funs fits env = true ∧ v.fits funs fits env = true :=
    fun hd => by simpa [Expr.fits] using hd
  have hUnpaid : (Expr.bytesSet x i v).paid flags (slots.map Slot.mode) paid live = false := rfl
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc, List.cons_append, List.nil_append]
  -- The position, in local `base`.
  have hIn : ∀ k, ((live k || k == x.index || v.uses k) || i.uses k) = true →
      (live k || (Expr.bytesSet x i v).uses k) = true := fun k h => by
    simp only [Expr.uses]; exact set_live_index _ _ _ _ h
  -- The variables that die in the position, in the value, and at the write: the buffer, when it
  -- dies there.
  have hDiv : dyingPot store s env slots paid
        (fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => live k || k == x.index || v.uses k) +
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) +
      dyingPot store s env slots paid (fun k => live k || k == x.index) live ≤
      dyingPot store s env slots paid (fun k => live k || (Expr.bytesSet x i v).uses k) live := by
    rw [dyingPot_split _ (fun k => live k || k == x.index || v.uses k) live
      (fun k h => hIn k (by simp [h])) (fun k h => by simp [h]),
      dyingPot_split (fun k => live k || k == x.index || v.uses k) (fun k => live k || k == x.index)
        live (fun k h => by simp [h]) (fun k h => by simp [h]),
      dyingPot_congr (L0 := fun k => live k || (Expr.bytesSet x i v).uses k)
        (L0' := fun k => (live k || k == x.index || v.uses k) || i.uses k)
        (fun k => by simp only [Expr.uses, Bool.or_comm, Bool.or_left_comm])
        fun _ => rfl]
    omega
  refine iSpec env slots paid _ h base heap store s hh hpv
    (hVars.live_mono hIn) hAt (fun hs => (hAl hs).live_mono hIn) (hSafe.mono hIn) hCap hBase
    (by omega) hPlace.1 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun _ hw => hw.mono (by rw [hT]; omega))
    fun heap1 store1 s1 ws1 a1 hAlI hTopI => ?_
  have hR1 := a1.rep
  simp only [Ty.rep_word] at hR1
  subst hR1
  refine After.storeWordX a1 le_rfl hBase (by rw [hh]; omega) fun e1 hI1 => ?_
  set s1' : Locals := setLocal { s1 with values := s.values } base (.i64 (i.denote funs env))
    with hs1'
  have hp1 := e1.frame.params
  have hh1 := e1.frame.positions.trans hh
  -- The value, in local `base + 1`.
  have hDv : ∀ s1'' : Locals, Evolves env slots (fun k => (live k || k == x.index || v.uses k) ||
        i.uses k) (fun k => live k || k == x.index || v.uses k) base heap store s heap1 store1
        s1'' →
      dyingPot store1 s1'' env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) =
      dyingPot store s env slots paid (fun k => (live k || k == x.index) || v.uses k)
        (fun k => live k || k == x.index) := fun _ e =>
    dyingPot_evolves (hVars.live_mono hIn) e (fun k h => by simp [h]) _ _ fun _ h => h
  have hAlV0 := fun (hs : strict = true) => HoldsA.evolves (hVars.live_mono hIn)
    ((hAl hs).live_mono hIn) e1 (fun k h => by simp [h]) (hAlI hs).1.1
  refine vSpec env slots paid _ h (base + 1) heap1 store1 _ hh1
    (hp1.trans hpv) (e1.holds.mono (Nat.le_succ base)) e1.step.at_ hAlV0
    ((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk]))
    (by rw [e1.step.cap m]; exact hCap)
    (by rw [hp1]; omega) (by omega) hPlace.2 _ _
    (hTrap.part (fun h => by simp only [Bool.not_eq_true'] at h; simp [Expr.fits, h])
      (fun _ => by simp [Expr.aborts])
      fun hd hw => by
        have := hTopI (hdS (fits_of_not hd)).1
        rw [hDv _ e1]
        exact hw.shift (c1 := dyingPot store s env slots paid
            (fun k => (live k || k == x.index || v.uses k) || i.uses k)
            (fun k => live k || k == x.index || v.uses k) +
            i.allocs funs flags bounds (slots.map Slot.mode) paid
              (fun j => live j || j == x.index || v.uses j) env)
          (by omega) (by rw [hT]; omega) (e1.step.cap m))
    fun heap2 store2 s2 ws2 a2 hAlV hTopV => ?_
  have hR2 := a2.rep
  simp only [Ty.rep_word] at hR2
  subst hR2
  refine After.storeWordX a2 le_rfl (by rw [hp1]; omega) (by rw [hh1]; omega) fun e2 hV2 => ?_
  set s2' : Locals := setLocal { s2 with values := s1'.values } (base + 1)
    (.i64 (v.denote funs env)) with hs2'
  have hp2 := e2.frame.params.trans hp1
  have hh2 := e2.frame.positions.trans hh1
  have hI2 := (e2.frame.below base (by omega)).1.trans hI1
  -- The buffer as owned, with its root in local `base + 2` and its length in local `base + 3`.
  refine specX_ownedVar hCopy x hh2 (hp2.trans hpv)
    ((e2.holds.mono (by omega)) : Holds env slots (fun k => live k || k == x.index) (base + 2)
      heap2 store2 _) e2.step.at_
    (fun hs => HoldsA.evolves (e1.holds.mono (Nat.le_succ base)) (hAlV0 hs) e2
      (fun k h => by simp [h]) (hAlV hs).1.1)
    (((hSafe.mono hIn).evolves (hVars.live_mono hIn) e1 (fun k hk => by simp [hk])).evolves
      (e1.holds.mono (Nat.le_succ base)) e2 (fun k hk => by simp [hk]))
    (by rw [e2.step.cap m, e1.step.cap m]; exact hCap)
    (by rw [hp2]; omega) (by omega)
    (hTrap.alloc (by simp [Expr.aborts]) fun hd hw => hw.of_le (by
      have := hTopI (hdS (fits_of_not hd)).1; have h2 := hTopV (hdS (fits_of_not hd)).2
      rw [hDv _ e1] at h2
      rw [hT]; omega)
      (by rw [e2.step.cap m, e1.step.cap m]))
    fun heap3 store3 s3 ws3 a3 hAlO hTopO _ => ?_
  obtain ⟨root, len, hws, -⟩ := a3.rep
  subst hws
  have hRep3 := a3.bytes_rep
  have hLen : len.toNat = (env.get x).data.size := hRep3.length_eq
  have hp3 : s3.params = s.params := a3.frame.params.trans hp2
  have hh3 : s3.positions = h := a3.frame.positions.trans hh2
  show wpX strict m _ Q store3 { s3 with values := .i64 len :: .i64 root :: s2'.values } host
  -- The length, in local `base + 3`, and the root, in local `base + 2`.
  have hLow3 : s3.params.length ≤ base + 3 := by rw [hp3]; omega
  have hHigh3 : base + 3 < s3.positions := by rw [hh3]; omega
  refine wpX_localSet_local hLow3 (Locals.lt_total hHigh3) ?_
  set s3a : Locals := setLocal { s3 with values := .i64 root :: s2'.values } (base + 3)
    (.i64 len) with hs3a
  have hLow3a : s3a.params.length ≤ base + 2 := by
    show s3.params.length ≤ _; rw [hp3]; omega
  have hHigh3a : base + 2 < s3a.positions := by
    rw [hs3a, Locals.positions_setLocal, Locals.positions_values, hh3]; omega
  have hL3a : s3a.get (base + 3) = some (.i64 len) :=
    Locals.get_setLocal_same (s := { s3 with values := .i64 root :: s2'.values }) hLow3
      (Locals.lt_total hHigh3)
  show wpX strict m (.localSet (base + 2) :: _) Q store3
    { s3a with values := .i64 root :: s2'.values } host
  refine wpX_localSet_local hLow3a (Locals.lt_total hHigh3a) ?_
  set s4 : Locals := setLocal { s3a with values := s2'.values } (base + 2) (.i64 root) with hs4
  have hF4 : Frame (base + 2) s3 s4 :=
    (Frame.setValues hLow3 (by omega) hHigh3).trans (Frame.setValues hLow3a le_rfl hHigh3a)
  have hR4 : s4.get (base + 2) = some (.i64 root) :=
    Locals.get_setLocal_same (s := { s3a with values := s2'.values }) hLow3a
      (Locals.lt_total hHigh3a)
  have hL4 : s4.get (base + 3) = some (.i64 len) :=
    (Locals.get_setLocal_ne (s := { s3a with values := s2'.values }) hLow3a (by omega)).trans
      hL3a
  have hI4 : s4.get base = some (.i64 (i.denote funs env)) :=
    (hF4.below base (by omega)).1.trans ((a3.frame.below base (by omega)).1.trans hI2)
  have hV4 : s4.get (base + 1) = some (.i64 (v.denote funs env)) :=
    (hF4.below (base + 1) (by omega)).1.trans ((a3.frame.below (base + 1) (by omega)).1.trans hV2)
  have a4 := a3.reframe hF4
  -- The rest of the code, from the buffer after the write or without it.
  have hFinish : ∀ (store5 : Store Unit) (value : LeanExe.Bytes),
      After env slots (fun k => live k || k == x.index) live (base + 2) heap2 store2 s2' .bytes
        .owned value heap3 store5 s4 [.i64 root, .i64 len] →
      value = (env.get x).set (i.denote funs env) (v.denote funs env) →
      block store5 root = block store3 root →
      wpX strict m rest Q store5 { s4 with values := .i64 len :: .i64 root :: s.values } host := by
    intro store5 value aX hValue hBlock
    subst hValue
    have aX1 := aX.lower e2.holds (by omega) fun k h => by simp [h]
    have aX2 := After.prepend (e1.holds.mono (Nat.le_succ base)) e2 aX1
      (fun k h => by simp [h]) fun k h => by simp [h]
    have aX3 := After.prepend (hVars.live_mono hIn) e1 (aX2.lower e1.holds (Nat.le_succ base)
      fun k h => by simp [h]) (fun k h => by simp [h]) fun k h => by simp [h]
    exact hNext heap3 store5 s4 [.i64 root, .i64 len] (aX3.liveIn hIn)
      (fun hs => ⟨HoldsA.after hVars (hAl hs) (aX3.liveIn hIn) (fun k h => by simp [h])
          (hAlO hs).1.1, Ty.AlignedVal.bytesBlock (hAlO hs).2 hBlock⟩)
      fun hd => by
        have := hTopI (hdS hd).1; have h2 := hTopV (hdS hd).2
        rw [hDv _ e1] at h2
        rw [hUnpaid, hT]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        omega
  have hLess : i.denote funs env < len ↔ (i.denote funs env).toNat < (env.get x).data.size := by
    rw [UInt64.lt_iff_toNat_lt, hLen]
  show wpX strict m _ Q store3 s4 host
  simp only [wpX_localGet_cons, Locals.get_values, hI4, hL4, wpX_ltUI64_cons]
  refine wpX_iff_cons rfl ?_
  by_cases hc : (i.denote funs env).toNat < (env.get x).data.size
  · -- The write of the value's low byte.
    rw [ite_eq_left (by simp [hLess.mpr hc])]
    have hBuffer : Heap.Buffer heap3 store3 root (env.get x) :=
      hRep3.buffer.resolve_left fun hEmpty => by have := hEmpty.2; omega
    simp only [wpX_localGet_cons, Locals.get_values, hR4, hI4, wpX_addI64_cons]
    rw [wpX_wrapI64_cons]
    simp only [wrap_toUInt32, wpX_localGet_cons, Locals.get_values, hV4]
    refine Bytes.wpX_storeWord a3.step.at_ hBuffer hc ?_
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons,
      Locals.get_values, hR4, hL4]
    exact hFinish _ _ (a4.writeByte hc (v.denote funs env).toUInt8)
      (by unfold LeanExe.Bytes.set; rw [dite_eq_left hc] <;> rfl)
      (block_eq (hBuffer.write_step a3.step.at_ (i.denote funs env) hc
        (v.denote funs env).toUInt8).2)
  · rw [ite_eq_right (by simp [hLess, hc])]
    rw [wpX_nil]
    dsimp only
    simp only [List.take_zero, List.drop_zero, List.nil_append, wpX_localGet_cons,
      Locals.get_values, hR4, hL4]
    exact hFinish _ _ a4 (by unfold LeanExe.Bytes.set; rw [dite_eq_right hc]) rfl

end Verified
