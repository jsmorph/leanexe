import Library.Trees.WordTree.Compiled
import Library.Trees.Search.Proof
import Mathlib.Data.Tree.Basic
import Verified.Master

namespace Library.Trees.WordTree

open LeanExe.Pipeline
open Library.Trees.Search (keys algorithmT algorithmT_snd)

theorem size_export :
    ({ name := "size", funcIdx := 10 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sum_export :
    ({ name := "sum", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem height_export :
    ({ name := "height", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem incr_export :
    ({ name := "incr", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem setKey_export :
    ({ name := "setKey", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem insert_export :
    ({ name := "insert", funcIdx := 14 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem leftChild_export :
    ({ name := "leftChild", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem splitRoot_export :
    ({ name := "splitRoot", funcIdx := 9 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The tree as a Mathlib `BinaryTree`, with the same shape and the same key at each node. -/
def KeyTree.toBinaryTree : KeyTree → BinaryTree UInt64
  | .leaf => .nil
  | .node l k r => .node k l.toBinaryTree r.toBinaryTree

/-- The number of nodes at which the search for `x` in `t`, with words compared as unsigned
numbers, continues into a subtree. -/
def KeyTree.searchDepth (x : UInt64) : KeyTree → Nat
  | .leaf => 0
  | .node l k r =>
    if x < k then l.searchDepth x + 1 else if k < x then r.searchDepth x + 1 else 0

/-- A frames condition `F` that fails with no frames, and that holds for a node with `k + 1` frames
exactly when it holds for both subtrees with `k`, holds with `k` frames exactly when the tree's
height is below `k`. -/
theorem fits_iff_height {F : Nat → KeyTree → Bool} (h0 : ∀ t, F 0 t = false)
    (hs : ∀ k t, F (k + 1) t = KeyTree.casesOn t true fun l _ r => F k l && F k r) :
    ∀ k t, F k t = true ↔ t.toBinaryTree.height < k
  | 0, t => by simp [h0 t]
  | k + 1, t => by
    rw [hs]
    cases t with
    | leaf => simp [KeyTree.toBinaryTree]
    | node l _ r =>
      simp [KeyTree.toBinaryTree, fits_iff_height h0 hs k l, fits_iff_height h0 hs k r]

theorem insert_fits : ∀ (k : Nat) (x : UInt64) (t : KeyTree),
    compiled.insert.fits k (x, { val := t }) = true ↔ t.searchDepth x < k
  | 0, x, t => by simp [show compiled.insert.fits 0 (x, { val := t }) = false from rfl]
  | k + 1, x, t => by
    rw [compiled.insert.fits_eq]
    cases t with
    | leaf => simp [KeyTree.searchDepth]
    | node l y r =>
      by_cases h : x < y
      · simp [KeyTree.searchDepth, h, insert_fits k x l]
      · by_cases h' : y < x
        · simp [KeyTree.searchDepth, h, h', insert_fits k x r]
        · simp [KeyTree.searchDepth, h, h']

/-- `t.size` is the number of nodes of `t` modulo `2 ^ 64`. -/
theorem size_eq (t : KeyTree) : t.size = UInt64.ofNat t.toBinaryTree.numNodes := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    simp only [KeyTree.size, KeyTree.toBinaryTree, BinaryTree.numNodes, ihl, ihr,
      UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl]
    ac_rfl

/-- `t.sum` is the sum of the keys of `t` modulo `2 ^ 64`. -/
theorem sum_eq (t : KeyTree) : t.sum = (keys t).sum := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr => simp [KeyTree.sum, keys, ihl, ihr, UInt64.add_assoc]

theorem max_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    max (UInt64.ofNat a) (UInt64.ofNat b) = UInt64.ofNat (max a b) := by
  show (if UInt64.ofNat a ≤ UInt64.ofNat b then UInt64.ofNat b else UInt64.ofNat a) = _
  have hle : UInt64.ofNat a ≤ UInt64.ofNat b ↔ a ≤ b := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' ha, UInt64.toNat_ofNat_of_lt' hb]
  by_cases h : a ≤ b
  · simp only [hle.mpr h, ↓reduceIte, Nat.max_eq_right h]
  · simp only [mt hle.mp h, ↓reduceIte, Nat.max_eq_left (Nat.le_of_not_le h)]

/-- `t.height` is the height of `t`, for a tree of height below `2 ^ 64`. -/
theorem height_eq (t : KeyTree) (h : t.toBinaryTree.height < 2 ^ 64) :
    t.height = UInt64.ofNat t.toBinaryTree.height := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    simp only [KeyTree.toBinaryTree, BinaryTree.height] at h ⊢
    rw [KeyTree.height, ihl (by omega), ihr (by omega), max_ofNat (by omega) (by omega)]
    simp only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl]

/-- `t.incr` is `t` with 1 added to each key modulo `2 ^ 64`. -/
theorem incr_eq (t : KeyTree) : t.incr.toBinaryTree = t.toBinaryTree.map (· + 1) := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr => simp [KeyTree.incr, KeyTree.toBinaryTree, BinaryTree.map, ihl, ihr]

/-- The export `size`, called on a tree of words of height below 1,000, returns its number of
nodes modulo `2 ^ 64`. -/
theorem size_master :
    Verified.Master compiled.module compiled.tables "size" (compiled.size.bound 1000)
      (fun t : KeyTree => t.toBinaryTree.height < 1000)
      (fun t y => y = UInt64.ofNat t.toBinaryTree.numNodes) :=
  .of_trapFree (.ofA compiled.size.trapFree) nofun size_export
    (fun t _ _ hD h =>
      ⟨(fits_iff_height (fun _ => rfl) compiled.size.fits_eq 1000 t).mpr hD, h⟩)
    (fun _ _ _ _ _ h => h) fun _ _ _ t _ _ => size_eq t

#print axioms size_master

/-- The export `sum`, called on a tree of words of height below 1,000, returns the sum of its keys
modulo `2 ^ 64`. -/
theorem sum_master :
    Verified.Master compiled.module compiled.tables "sum" (compiled.sum.bound 1000)
      (fun t : KeyTree => t.toBinaryTree.height < 1000) (fun t y => y = (keys t).sum) :=
  .of_trapFree (.ofA compiled.sum.trapFree) nofun sum_export
    (fun t _ _ hD h =>
      ⟨(fits_iff_height (fun _ => rfl) compiled.sum.fits_eq 1000 t).mpr hD, h⟩)
    (fun _ _ _ _ _ h => h) fun _ _ _ t _ _ => sum_eq t

#print axioms sum_master

/-- The export `height`, called on a tree of words of height below 1,000, returns its height. -/
theorem height_master :
    Verified.Master compiled.module compiled.tables "height" (compiled.height.bound 1000)
      (fun t : KeyTree => t.toBinaryTree.height < 1000)
      (fun t y => y = UInt64.ofNat t.toBinaryTree.height) :=
  .of_trapFree (.ofA compiled.height.trapFree) nofun height_export
    (fun t _ _ hD h =>
      ⟨(fits_iff_height (fun _ => rfl) compiled.height.fits_eq 1000 t).mpr hD, h⟩)
    (fun _ _ _ _ _ h => h) fun _ _ _ t _ hD => height_eq t (by omega)

#print axioms height_master

/-- The export `incr`, called on a tree of words of height below 1,000 that the caller moves,
returns the tree of the same shape with 1 added to each key modulo `2 ^ 64`. -/
theorem incr_master :
    Verified.Master compiled.module compiled.tables "incr" (compiled.incr.bound 1000)
      (fun t : Moved KeyTree => t.val.toBinaryTree.height < 1000)
      (fun t (y : KeyTree) => y.toBinaryTree = t.val.toBinaryTree.map (· + 1)) :=
  .of_trapFree (.ofA compiled.incr.trapFree) nofun incr_export
    (fun t _ _ hD h => ⟨(fits_iff_height (F := fun k t => compiled.incr.fits k { val := t })
      (fun _ => rfl) (fun k t => compiled.incr.fits_eq k t) 1000 t.val).mpr hD, h⟩)
    (fun _ _ _ _ _ h => h) fun _ _ _ t _ _ => incr_eq t.val

#print axioms incr_master

/-- The export `setKey`, called on a word `k` and a tree of words that the caller moves, returns
the tree with the root's key replaced by `k`, and an empty tree for an empty tree. -/
theorem setKey_master :
    Verified.Master compiled.module compiled.tables "setKey" compiled.setKey.bound (fun _ => True)
      (fun (x : UInt64 × Moved KeyTree) (y : KeyTree) => y = match x.2.val with
        | .leaf => .leaf
        | .node l _ r => .node l x.1 r) :=
  .of_trapFree (.ofA compiled.setKey.trapFree) nofun setKey_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ ⟨_, ⟨t⟩⟩ _ _ => by cases t <;> rfl

#print axioms setKey_master

/-- The export `insert`, called on a word `x` and a tree of words that the caller moves, on which
the search for `x` continues into a subtree at fewer than 1,000 nodes, returns the tree after the
insertion of Algorithm T. -/
theorem insert_master :
    Verified.Master compiled.module compiled.tables "insert" (compiled.insert.bound 1000)
      (fun x : UInt64 × Moved KeyTree => x.2.val.searchDepth x.1 < 1000)
      (fun x y => y = (algorithmT x.1 x.2.val).2) :=
  .of_trapFree (.ofA compiled.insert.trapFree) nofun insert_export
    (fun x _ _ hD h => ⟨(insert_fits 1000 x.1 x.2.val).mpr hD, h⟩) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => (algorithmT_snd x.1 x.2.val).symm

#print axioms insert_master

/-- The export `leftChild`, called on a tree of words that the caller moves, returns the root's
left subtree, and an empty tree for an empty tree. -/
theorem leftChild_master :
    Verified.Master compiled.module compiled.tables "leftChild" compiled.leftChild.bound
      (fun _ => True)
      (fun (t : Moved KeyTree) (y : KeyTree) => y.toBinaryTree = t.val.toBinaryTree.left) :=
  .of_trapFree (.ofA compiled.leftChild.trapFree) nofun leftChild_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ ⟨t⟩ _ _ => by cases t <;> rfl

#print axioms leftChild_master

/-- The export `splitRoot`, called on a tree of words that the caller moves, returns the root's
left and right subtrees, and two empty trees for an empty tree. -/
theorem splitRoot_master :
    Verified.Master compiled.module compiled.tables "splitRoot" compiled.splitRoot.bound
      (fun _ => True)
      (fun (t : Moved KeyTree) (y : KeyTree × KeyTree) =>
        y.1.toBinaryTree = t.val.toBinaryTree.left ∧
          y.2.toBinaryTree = t.val.toBinaryTree.right) :=
  .of_trapFree (.ofA compiled.splitRoot.trapFree) nofun splitRoot_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ ⟨t⟩ _ _ => by cases t <;> exact ⟨rfl, rfl⟩

#print axioms splitRoot_master

end Library.Trees.WordTree
