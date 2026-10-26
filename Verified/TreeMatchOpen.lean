import Verified.TreeMatchLocals
import Verified.TreeMatchDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_openTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64} {base : Nat}
    {words : Fin (shape.words r) → UInt64} {children : Fin (shape.children r) → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node r words children).toNode)
    (hPtr : s.get base = some (.i64 p)) (hLow : s.params.length ≤ base + 1)
    (hRoom : base + 1 + (shape.fields r).length ≤ s.positions)
    (hNext : ∀ s', Frame (base + 1) s s' → s'.values = s.values →
      Holds (Env.treeFields shape r words children .nil) (shape.slots r base mode [])
        (fun _ => true) (base + shape.bindCount r) heap (treeDetachStore mode store p) s' →
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap (treeDetachStore mode store p) [] →
      (∀ (t : Ty) (x : Var (shape.context r []) t) (ws : List Value),
        LocalsHold s' ((shape.slots r base mode []).getD x.index default).loc t.types ws →
        ws.length = t.width →
        ∀ b ∈ t.regions ((shape.slots r base mode []).getD x.index default).mode
          (treeDetachStore mode store p) ws ((Env.treeFields shape r words children .nil).get x),
          b ∈ (Ty.tree shape).regions mode store [.i64 p] (.node r words children)) →
      wp m rest Q (treeDetachStore mode store p) s' host) :
    wp m (treeLoadFields base (base + 1) (base + 1 + shape.words r) shape.fieldStart
      (shape.fields r) ++
      (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) Q store s host := by
  obtain ⟨hAt', hHeader, hStep, hChildren, hApart, hReads, hRegions⟩ := treeNode_detach hAt hNode
  have hRun := wp_loadTree (m := m) (host := host) (Q := Q)
    (rest := (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) hAt hPtr
    hNode hLow (by omega) hRoom
    (fun s' hFrame hStack hPtr' hWordLocals hChildLocals => by
    have hold := LocalsHold.treeFields hPtr' hWordLocals hChildLocals
    have hRep := treeFields_rep (words := words) hHeader hChildren
    have hPrefix := Holds.treePrefix hHeader hChildren hApart hold
    have hPointers : ∀ i, store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)) :=
      fun i => (hReads ⟨_, shape.fieldSlot_lt r true i⟩).symm
    refine wp_detachTree hAt hNode hPtr'
      (hNext s' hFrame hStack hPrefix hStep ?_)
    intro t x ws hLocal hLength b hr
    rw [← hRegions]
    exact treeFields_variable_regions hPointers hRep hold t x ws hLocal hLength b hr)
  simpa only [List.append_assoc] using hRun

end Verified
