import Verified.TreeContextMoves
import Verified.TailState
import Verified.EnvRegions

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem treeFields_separate {store : Store Unit} {shape : TreeShape} {mode : Mode} {p : UInt64}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    {pointers : Fin shape.children → UInt64}
    (hApart : mode = .owned → (block store p ::
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten).Pairwise
        regionsDisjoint) :
    Separate store
      (Env.moves store (paramMode (shape.context []) (shape.modes mode []))
        (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
          (List.ofFn fun i => Value.i64 (pointers i))))
        (Env.treeFields shape words children .nil))
      (Env.reads store (paramMode (shape.context []) (shape.modes mode []))
        (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
          (List.ofFn fun i => Value.i64 (pointers i))))
        (Env.treeFields shape words children .nil)) := by
  rw [treeFields_moves]
  cases mode
  · exact Separate.nil
  · rw [treeFields_reads_owned]
    refine ⟨?_, nofun⟩
    simpa only [List.map_cons, List.map_flatten, List.map_ofFn, Function.comp_def,
      Node.pointers_blocks] using
      hApart rfl

theorem TreeShape.context_width (shape : TreeShape) :
    widthSum (shape.context []) = shape.bindCount := by
  simp [TreeShape.context, widthSum, Ty.width, TreeShape.bindCount, Nat.add_assoc]

theorem Holds.treePrefix {heap : Heap} {store : Store Unit} {s : Locals}
    {shape : TreeShape} {mode : Mode} {base : Nat} {p : UInt64}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    {pointers : Fin shape.children → UInt64}
    (hHeader : mode.header shape heap store p)
    (hChildren : ∀ i, mode.node heap store (pointers i) (children i).toNode)
    (hApart : mode = .owned → (block store p ::
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten).Pairwise
        regionsDisjoint)
    (hold : LocalsHold s base ((shape.context []).flatMap Ty.types)
      (.i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
        (List.ofFn fun i => Value.i64 (pointers i))))) :
    Holds (Env.treeFields shape words children .nil) (shape.slots base mode [])
      (fun _ => true) (base + shape.bindCount) heap store s := by
  have h := Holds.ofEnvRep (treeFields_rep hHeader hChildren)
    (treeFields_separate hApart) hold
  rw [shape.paramSlots, shape.context_width] at h
  exact h

theorem treeFields_regions_subset (store : Store Unit) (shape : TreeShape) (mode : Mode)
    (p : UInt64) (words : Fin shape.words → UInt64) (children : Fin shape.children → Tree shape) :
    let pointers := fun i => store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val)
    let ws := .i64 p :: ((List.ofFn fun i => Value.i64 (words i)) ++
      (List.ofFn fun i => Value.i64 (pointers i)))
    ∀ r ∈ (Env.moves store (paramMode (shape.context []) (shape.modes mode [])) ws
        (Env.treeFields shape words children .nil)).map (block store) ++
      Env.reads store (paramMode (shape.context []) (shape.modes mode [])) ws
        (Env.treeFields shape words children .nil),
      r ∈ (Ty.tree shape).regions mode store [.i64 p] (.node words children) := by
  intro pointers ws r hr
  dsimp only [ws] at hr
  erw [treeFields_moves, treeFields_reads] at hr
  cases mode
  · simp only [List.map_nil, List.nil_append] at hr
    change r ∈ Node.slotRegions store p (.record (treeSlots shape.fields words
      (fun i => (children i).toNode)))
    erw [Node.slotRegions, treeSlots_regions_read]
    apply List.mem_cons_of_mem
    simp only [Nat.zero_add]
    convert hr using 1 <;> rfl
  · simp only [List.map_cons, List.map_flatten, List.map_ofFn, Function.comp_def,
      Node.pointers_blocks, List.append_nil] at hr
    change r ∈ Node.blocks store p (.record (treeSlots shape.fields words
      (fun i => (children i).toNode)))
    erw [Node.blocks, treeSlots_blocks_read]
    simp only [Nat.zero_add]
    convert hr using 1 <;> rfl

end Verified
