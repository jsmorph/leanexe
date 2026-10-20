import Verified.TreeMatchLocals
import Verified.TreeMatchDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_openTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {mode : Mode} {p : UInt64} {base : Nat}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node words children).toNode)
    (hPtr : s.get base = some (.i64 p)) (hLow : s.params.length ≤ base + 1)
    (hRoom : base + 1 + shape.fields.length ≤ s.positions)
    (hNext : ∀ s', Frame (base + 1) s s' → s'.values = s.values →
      Holds (Env.treeFields shape words children .nil) (shape.slots base mode [])
        (fun _ => true) (base + shape.bindCount) heap (treeDetachStore mode store p) s' →
      Step heap store (fun r => mode = .owned → regionsDisjoint r (block store p))
        heap (treeDetachStore mode store p) [] →
      (∀ (t : Ty) (x : Var (shape.context []) t) (ws : List Value),
        LocalsHold s' ((shape.slots base mode []).getD x.index default).loc t.types ws →
        ws.length = t.width →
        ∀ r ∈ t.regions ((shape.slots base mode []).getD x.index default).mode
          (treeDetachStore mode store p) ws ((Env.treeFields shape words children .nil).get x),
          r ∈ (Ty.tree shape).regions mode store [.i64 p] (.node words children)) →
      wp m rest Q (treeDetachStore mode store p) s' host) :
    wp m (treeLoadFields base (base + 1) (base + 1 + shape.words) 0 shape.fields ++
      (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) Q store s host := by
  obtain ⟨hAt', hHeader, hStep, hChildren, hApart, hReads, hRegions⟩ := treeNode_detach hAt hNode
  have hRun := wp_loadTree (m := m) (host := host) (Q := Q)
    (rest := (if mode = .owned then headerStore base 8 [.constI64 0] else []) ++ rest) hAt hPtr hNode hLow (by omega) hRoom
    (fun s' hFrame hStack hPtr' hWordLocals hChildLocals => by
    have hold := LocalsHold.treeFields hPtr' hWordLocals hChildLocals
    have hRep := treeFields_rep (words := words) hHeader hChildren
    have hPrefix := Holds.treePrefix hHeader hChildren hApart hold
    have hPointers : ∀ i, store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val) =
        (treeDetachStore mode store p).mem.read64
          (slotAddress p (fieldPosition true shape.fields i).val) :=
      fun i => (hReads (fieldPosition true shape.fields i)).symm
    refine wp_detachTree hAt hNode hPtr'
      (hNext s' hFrame hStack hPrefix hStep ?_)
    intro t x ws hLocal hLength r hr
    rw [← hRegions]
    exact treeFields_variable_regions hPointers hRep hold t x ws hLocal hLength r hr)
  simpa only [List.append_assoc] using hRun

end Verified
