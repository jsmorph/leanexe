import Verified.TreeMatchLocals
import Verified.TreeMatchDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_openTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {h base : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hh : s.positions = h) (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get base = some (.i64 p)) (hLow : s.params.length ≤ base + 1)
    (hRoom : base + shape.bindWidth r ≤ s.positions)
    (hNext : ∀ s', Frame (base + 1) s s' → s'.values = s.values →
      Holds (Env.treeFields shape r words arrays buffers children .nil)
        (shape.slots r base mode [])
        (fun _ => true) (base + shape.bindWidth r) heap (treeDetachStore mode store p) s' →
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap (treeDetachStore mode store p) [] →
      (∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
        LocalsHold s' ((shape.slots r base mode []).getD x.index default).loc t.types ws →
        ws.length = t.width →
        ∀ b ∈ t.regions ((shape.slots r base mode []).getD x.index default).mode
          (treeDetachStore mode store p) ws
            ((Env.treeFields shape r words arrays buffers children .nil).get x),
          b ∈ (Ty.tree shape).regions mode store [.i64 p]
            (.node r words arrays buffers children)) →
      wp m rest Q (treeDetachStore mode store p) s' host) :
    wp m (treeLoadFields h base (shape.wordTypes r) (base + 1) (base + 1 + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps base (shape.kinds r) (base + 1 + shape.words r + shape.children r)
        (base + 1 + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++
      (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) Q store s host := by
  obtain ⟨hAt', hHeader, hStep, hChildren, hArrays, hRecordBuffers, hApart, hReads, hRegions⟩ :=
    treeNode_detach hAt hNode
  have hRun := wp_loadTree (m := m) (host := host) (Q := Q)
    (rest := (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) hh hAt
    hPtr hNode hLow (by omega) (by simp only [TreeShape.bindWidth, TreeShape.bindCount] at hRoom; omega)
    (fun s' hFrame hStack hPtr' hWordLocals hChildLocals hArrayLocals hBufferLocals => by
    have hold := LocalsHold.treeFields hPtr' (by rw [hFrame.positions]; exact hWordLocals)
      hChildLocals hArrayLocals hBufferLocals
    have hRep := treeFields_rep (words := words) (buffers := buffers) hHeader hChildren hArrays
      (fun i => (hRecordBuffers i).rep)
    have hPrefix := Holds.treePrefix (buffers := buffers) hHeader hChildren hArrays
      (fun i => (hRecordBuffers i).rep) hApart hold
    have hPointers : ∀ i, store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) :=
      fun i => (hReads ⟨_, shape.fieldSlot_lt r true i⟩).symm
    have hArrayPtrs : ∀ i, store.mem.read64
        (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapArraySlot (shape.kinds r) i)) :=
      fun i => (hReads ⟨_, shape.heapArraySlot_lt_width r i⟩).symm
    refine wp_detachTree hAt hNode hPtr'
      (hNext s' hFrame hStack hPrefix hStep ?_)
    intro t x ws hLocal hLength b hr
    rw [← hRegions]
    have hRootReads : ∀ i, store.mem.read64 (slotAddress p (shape.fieldStart +
        (shape.fields r).length + heapBufferSlot (shape.kinds r) i)) =
        (treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)) :=
      fun i => (hReads ⟨_, by have := shape.heapBufferSlot_lt_width r i; omega⟩).symm
    have hLengthReads : ∀ i, store.mem.read64 (slotAddress p (shape.fieldStart +
        (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)) =
        (treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)) :=
      fun i => (hReads ⟨_, shape.heapBufferSlot_lt_width r i⟩).symm
    have hDetachBuffers : ∀ i, RecordBuffer heap (treeDetachStore mode store p)
        ((treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))
        ((treeDetachStore mode store p).mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)))
        (buffers i) := fun i => by
      rw [← hRootReads, ← hLengthReads]
      exact hRecordBuffers i
    exact treeFields_variable_regions hDetachBuffers hPointers hArrayPtrs hRootReads
      hLengthReads hRep hold t x ws hLocal hLength b hr)
  simpa only [List.append_assoc] using hRun

end Verified
