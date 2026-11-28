module

public import Verified.Wasi.ScratchContext

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem block_low {store : Store Unit} {root : UInt64} (base : 4096 + 48 ≤ root.toNat) :
    regionsDisjoint ABI.low (block store root) := by
  left
  dsimp only [ABI.low, block]
  omega

mutual

theorem node_blocks_low {heap : Heap} {store : Store Unit} :
    ∀ (root : UInt64) (value : Node), NodeOwned heap store root value →
      ∀ region ∈ value.blocks store root, regionsDisjoint ABI.low region
  | _, .null, _, _, member => nomatch member
  | root, .record slots, ⟨header, fields⟩, region, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact block_low header.base
      · exact slots_blocks_low root 0 slots fields region member

theorem slots_blocks_low {heap : Heap} {store : Store Unit} :
    ∀ (root : UInt64) (index : Nat) (slots : List LeanExe.Pipeline.Slot),
      SlotsOwned heap store root index slots →
      ∀ region ∈ slotsBlocks store root index slots, regionsDisjoint ABI.low region
  | _, _, [], _, _, member => nomatch member
  | root, index, .word _ :: rest, ⟨_, fields⟩, region, member =>
      slots_blocks_low root (index + 1) rest fields region member
  | root, index, .child value :: rest, ⟨child, fields⟩, region, member => by
      rcases List.mem_append.mp member with member | member
      · exact node_blocks_low _ value child region member
      · exact slots_blocks_low root (index + 1) rest fields region member
  | root, index, .array _ :: rest, ⟨array, fields⟩, region, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact block_low array.base
      · exact slots_blocks_low root (index + 1) rest fields region member
  | root, index, .bytes data :: rest, ⟨buffer, fields⟩, region, member => by
      rcases List.mem_append.mp member with member | member
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp member
        rcases buffer with ⟨-, hEmpty⟩ | ⟨-, buffer⟩
        · simp [bufferRoots, hEmpty] at hq
        · have : q = store.mem.read64 (slotAddress root index) := by
            unfold bufferRoots at hq
            split at hq <;> simp_all
          subst this
          exact block_low buffer.object.base
      · exact slots_blocks_low root (index + 1) rest fields region member

end

theorem owned_low {heap : Heap} {store : Store Unit} :
    {type : Ty} → {words : List Value} → {value : type.denote} →
      type.Rep .owned heap store words value →
      ∀ region ∈ type.regions .owned store words value, regionsDisjoint ABI.low region
  | .elem _, _, _, _, _, member => nomatch member
  | .bytes, _, _, ⟨root, length, rfl, rep⟩, region, member => by
      apply bytes_low rep region
      simpa only [Ty.regions, Ty.blocks, Bytes.roots_regions] using member
  | .pair first second, _, value, ⟨firstWords, secondWords, rfl, firstRep, secondRep, _⟩,
      region, member => by
      rw [Ty.regions_append firstRep.length] at member
      rcases List.mem_append.mp member with member | member
      · exact owned_low firstRep region member
      · exact owned_low secondRep region member
  | .array _, _, _, ⟨root, rfl, rep⟩, region, member => by
      obtain rfl : region = block store root := by
        simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using member
      exact block_low rep.base
  | .tree _, _, value, ⟨root, rfl, rep⟩, region, member =>
      node_blocks_low root value.toNode rep.1 region member
  | .treeHeader _ _, _, _, ⟨root, rfl, rep⟩, region, member => by
      obtain rfl : region = block store root := by
        simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using member
      obtain ⟨_, _, header, _⟩ := rep
      exact block_low header.base

theorem ResultTy.Rep.low {result : ResultTy} {heap : Heap} {store : Store Unit}
    {words : List Value} {value : result.denote} (rep : result.Rep heap store words value) :
    ∀ region ∈ result.fresh store words value, regionsDisjoint ABI.low region := by
  cases result with
  | unit => exact nofun
  | value type => exact owned_low rep

end Verified.Wasi
