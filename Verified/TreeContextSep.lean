import Verified.TreeContextMoves
import Verified.TailState
import Verified.EnvRegions

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem treeFields_separate {store : Store Unit} {shape : TreeShape} {r : Fin shape.records}
    {mode : Mode} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape}
    {pointers : Fin (shape.children r) → UInt64}
    (hApart : mode = .owned → (block store p ::
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten).Pairwise
        regionsDisjoint) :
    Separate store
      (Env.moves store (paramMode (shape.context r []) (shape.modes r mode []))
        (.i64 p :: (shape.wordValues r words ++
          (List.ofFn fun i => Value.i64 (pointers i))))
        (Env.treeFields shape r words children .nil))
      (Env.reads store (paramMode (shape.context r []) (shape.modes r mode []))
        (.i64 p :: (shape.wordValues r words ++
          (List.ofFn fun i => Value.i64 (pointers i))))
        (Env.treeFields shape r words children .nil)) := by
  rw [treeFields_moves]
  cases mode
  · exact Separate.nil
  · rw [treeFields_reads_owned]
    refine ⟨?_, nofun⟩
    simpa only [List.map_cons, List.map_flatten, List.map_ofFn, Function.comp_def,
      Node.pointers_blocks] using
      hApart rfl

theorem widthSum_fn {n : Nat} (ts : Fin n → Ty) (hWidth : ∀ i, (ts i).width = 1)
    (Γ : List Ty) : widthSum (tysOfFn n ts ++ Γ) = n + widthSum Γ := by
  induction n with
  | zero => simp [tysOfFn]
  | succ n ih =>
    simp only [tysOfFn, List.cons_append, widthSum_cons, hWidth 0,
      ih (fun i => ts i.succ) (fun i => hWidth i.succ)]
    omega

theorem TreeShape.context_width (shape : TreeShape) (r : Fin shape.records) :
    widthSum (shape.context r []) = shape.bindCount r := by
  simp only [TreeShape.context, widthSum_cons, widthSum_fn _ (shape.wordTy_width r)]
  simp [widthSum, Ty.width, TreeShape.bindCount, Nat.add_assoc]

theorem Holds.treePrefix {heap : Heap} {store : Store Unit} {s : Locals}
    {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {base : Nat} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape}
    {pointers : Fin (shape.children r) → UInt64}
    (hHeader : mode.header shape r heap store p)
    (hChildren : ∀ i, mode.node heap store (pointers i) (children i).toNode)
    (hApart : mode = .owned → (block store p ::
      (List.ofFn fun i => (children i).toNode.blocks store (pointers i)).flatten).Pairwise
        regionsDisjoint)
    (hold : LocalsHold s base ((shape.context r []).flatMap Ty.types)
      (.i64 p :: (shape.wordValues r words ++
        (List.ofFn fun i => Value.i64 (pointers i))))) :
    Holds (Env.treeFields shape r words children .nil) (shape.slots r base mode [])
      (fun _ => true) (base + shape.bindCount r) heap store s := by
  have h := Holds.ofEnvRep (treeFields_rep hHeader hChildren)
    (treeFields_separate hApart) hold
  rw [shape.paramSlots r, shape.context_width r] at h
  exact h

theorem treeFields_regions_subset (store : Store Unit) (shape : TreeShape)
    (r : Fin shape.records) (mode : Mode) (p : UInt64)
    (words : (i : Fin (shape.words r)) → (shape.elem r i).denote)
    (children : Fin (shape.children r) → Tree shape) :
    let pointers := fun i => store.mem.read64
      (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val))
    let ws := .i64 p :: (shape.wordValues r words ++
      (List.ofFn fun i => Value.i64 (pointers i)))
    ∀ b ∈ (Env.moves store (paramMode (shape.context r []) (shape.modes r mode [])) ws
        (Env.treeFields shape r words children .nil)).map (block store) ++
      Env.reads store (paramMode (shape.context r []) (shape.modes r mode [])) ws
        (Env.treeFields shape r words children .nil),
      b ∈ (Ty.tree shape).regions mode store [.i64 p] (.node r words children) := by
  intro pointers ws b hr
  dsimp only [ws] at hr
  erw [treeFields_moves, treeFields_reads] at hr
  cases mode
  · simp only [List.map_nil, List.nil_append] at hr
    change b ∈ Node.slotRegions store p (.record (shape.recordSlots r (shape.slotWords r words)
      (fun i => (children i).toNode)))
    erw [Node.slotRegions, recordSlots_regions, treeSlots_regions_read]
    apply List.mem_cons_of_mem
    convert hr using 1 <;> rfl
  · simp only [List.map_cons, List.map_flatten, List.map_ofFn, Function.comp_def,
      Node.pointers_blocks, List.append_nil] at hr
    change b ∈ Node.blocks store p (.record (shape.recordSlots r (shape.slotWords r words)
      (fun i => (children i).toNode)))
    erw [Node.blocks, recordSlots_blocks, treeSlots_blocks_read]
    convert hr using 1 <;> rfl

end Verified
