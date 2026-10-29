import LeanExe.ProofKit.AlignedTransfer
import LeanExe.ProofKit.AlignedFlag
import LeanExe.ProofKit.FixedArraySearchNone

/-!
The free-list search of `alloc` under `wpA`: the ports of `readProgram_spec`, which loads the
size and link words of the current free block, and of `noneProgram_spec`, the search that finds
no block.  Both loads are aligned when the block's root is a multiple of 8.  The guard and the
advance step make no 64-bit access, so their `wp` specifications apply through
`wpA_append_accessFree`.
-/

namespace LeanExe.ProofKit.FixedArraySearch
open Wasm LeanExe.Runtime LeanExe.ProofKit Memory

theorem readProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (need previous root capacity next result oldCapacity oldNext : UInt64)
    (hRoot : 48 ≤ root.toNat) (hRoot32 : root.toNat ≤ 4294967296)
    (hFit : root.toNat ≤ store.mem.pages * 65536) (hRootAl : root.toNat % 8 = 0)
    (hCapacityRead : store.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : store.mem.read64 (root - 8).toUInt32 = next)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q store
      (frame params saved tail need previous root capacity next result) env) :
    wpA module_ (readProgram start ++ rest) Q store
      (frame params saved tail need previous root oldCapacity oldNext result) env := by
  have hCapacityRead' : store.mem.read64 (root.toUInt32 - 32) = capacity := by
    simpa using hCapacityRead
  have hNextRead' : store.mem.read64 (root.toUInt32 - 8) = next := by
    simpa using hNextRead
  have hs32 : (root.toUInt32 - 32).toNat = root.toNat - 32 := by
    simpa using toUInt32_sub_toNat (p := root) (k := 32) (by simp; omega) (by simp; omega)
  have hs8 : (root.toUInt32 - 8).toNat = root.toNat - 8 := by
    simpa using toUInt32_sub_toNat (p := root) (k := 8) (by simp; omega) (by simp; omega)
  subst start
  simp [readProgram, wpA_simp, wp_simp, frame, Nat.add_assoc,
    Nat.reducePow, ← toUInt32_eq_ofNat, hCapacityRead', hNextRead']
  wpA_close
  simpa [frame] using hNext

theorem noneProgram_specA (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (need capacity next : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt initial.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hRoots : ∀ node ∈ nodes, node.root.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64, wpA module_ rest Q initial
      (frame params saved tail need previous 0 capacity next 0) env) :
    wpA module_ (program start fitProgram ++ rest) Q initial
      (frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  subst start
  simp only [program, List.cons_append, List.nil_append]
  apply wpA_block_cons
  apply wpA_loop_cons (Inv := noneInvariant initial params saved tail need nodes)
    (μ := measure (params.length + saved.length) nodes)
  · exact ⟨0, capacity, next, [], nodes, rfl, by simp, hList,
      (takeFirstFit_none_iff need nodes).mp hNone, rfl⟩
  · rintro store locals ⟨previous, oldCapacity, oldNext, visited, remaining, rfl,
      hSplit, hRemaining, hSmall, rfl⟩
    cases remaining with
    | nil =>
      simpa [body, guardProgram, wpA_simp, wp_simp, frame, freeHead,
        Nat.add_assoc] using hNext previous oldCapacity oldNext
    | cons node restNodes =>
      have hRoot := hRemaining.head_ne_zero
      simp only [freeHead] at hRoot
      have hNodeAl : node.root.toNat % 8 = 0 :=
        hRoots node (by rw [hSplit]; exact List.mem_append_right _ List.mem_cons_self)
      cases hRemaining with
      | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
        have hCapSmall := hSmall node List.mem_cons_self
        have hNotFit : ¬need ≤ node.capacity := by
          rw [UInt64.le_iff_toNat_le]
          rw [UInt64.lt_iff_toNat_lt] at hCapSmall
          omega
        simp only [body, List.append_assoc]
        refine wpA_append_accessFree (by rfl) ?_
        rw [← List.append_nil (guardProgram _)]
        refine guardProgram_spec module_ env store _ _ node.root rfl hRoot ?_ ?_ _ _
          (wp_nil.mpr ?_)
        · simp [frame, Locals.get, freeHead, Nat.add_assoc]
        · simp [frame, Locals.get, Nat.add_assoc]
        apply readProgram_specA module_ env store params saved tail _ rfl need previous node.root
          node.capacity (freeHead restNodes) 0 oldCapacity oldNext hp (by omega) (by omega)
          hNodeAl hCapacity hNodeNext
        simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
        refine wpA_iff_cons rfl ?_
        rw [ite_eq_right (by simp [hNotFit]), ← List.append_nil (advanceProgram _)]
        refine wpA_append_accessFree (by rfl) ?_
        apply advanceProgram_spec module_ env store params saved tail _ rfl need previous node.root
          node.capacity (freeHead restNodes) 0 _ []
        simp [wpA_simp, wp_simp]
        have hSplitNext : nodes = (visited ++ [node]) ++ restNodes := by
          simpa [List.append_assoc] using hSplit
        refine ⟨⟨node.root, node.capacity, freeHead restNodes, visited ++ [node], restNodes,
          rfl, hSplitNext, hTail, ?_, rfl⟩, ?_⟩
        · intro other hOther
          exact hSmall other (List.mem_cons_of_mem _ hOther)
        · have hBefore := hList.scanRemaining_suffix hSplit
          have hAfter := hList.scanRemaining_suffix hSplitNext
          simp only [freeHead, List.length_cons] at hBefore
          simp [measure, frame, Locals.get, Nat.add_assoc, hAfter]
          simpa only [freeHead, hBefore] using Nat.lt_succ_self restNodes.length

end LeanExe.ProofKit.FixedArraySearch
