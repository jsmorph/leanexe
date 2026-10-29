import Verified.AlignedTreeHeaderCopy
import Verified.AlignedBytes
import Verified.AlignedWriters
import Verified.AlignedRuntime

/-!
The copy of a value under the flag.  `wpX_copyCode` is `wp_copyCode` with `wpX strict` for
`wp`: from an aligned heap and an aligned value, the copy's accesses are aligned, and it leaves an
aligned heap and an aligned owned copy.  Each case calls the flagged port of its original: a
buffer `Bytes.wpX_copyOwned`, an array `wpX_copyArray`, a tree `wpX_copyTree`, and a detached
header `wpX_copyTreeHeader`.  A tree's copy reads the source's slots, whose regions start at
multiples of 8 in either mode by `Ty.AlignedVal.toBorrowed`.  `copyCodeX` gives `CopyCodeX` for
every runtime, whose allocation is aligned by `Runtime.allocAligned`.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `wp_copyCode` under the flag. -/
theorem wpX_copyCode {strict : Bool} {m : Module} (hm : Runtime m)
    (hRt : strict = true → AllocAligned m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {h src base : Nat} {mode : Mode}
      {ws : List Value} {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → store.memoryCap m 0 ≤ 65535 →
    TrapOK (!decide (heap.Within store m (t.copyCost v))) Q → s.positions = h →
    t.Rep mode heap store ws v → LocalsHold s src t.types ws → src + t.width ≤ base →
    s.params.length ≤ base → base + t.copyScratch ≤ s.positions →
    (strict = true → heap.Aligned ∧ Ty.AlignedVal mode store t ws v) →
    (∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws' : List Value),
      Step heap store (fun _ => True) heap' store' (t.blocks store' ws' v) →
      t.Rep .owned heap' store' ws' v → Frame base s s' →
      heap'.top.toNat ≤ heap.top.toNat + t.copyCost v →
      (strict = true → heap'.Aligned ∧ Ty.AlignedVal .owned store' t ws' v) →
      wpX strict m rest Q store' { s' with values := ws'.reverse ++ s.values } host) →
    wpX strict m (copyCode h t src base ++ rest) Q store s host
  | .elem e, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, _, _, hh, hRep, hold, _, _,
      _, hAl, hNext => by
    have hRep' : ws = e.values v := hRep
    subst hRep'
    simp only [copyCode]
    exact wpX_loadCode _ (by rw [e.values_length, e.types_length]) hh hold
      (hNext heap store s _ (Step.refl hAt _) rfl (Frame.refl base s) (Nat.le_add_right _ _)
        fun hs => ⟨(hAl hs).1, fun r hr => by simp [Ty.regions, Ty.blocks] at hr⟩)
  | .bytes, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, _, hRep, hold,
      hSrc, hBase, hRoom, hAl, hNext => by
    obtain ⟨root, length, rfl, hBytes⟩ := hRep
    have hRoot : s.get src = some (.i64 root) := by simpa [Ty.types, slotIndex] using hold 0 (by simp)
    have hLength : s.get (src + 1) = some (.i64 length) := by
      simpa [Ty.types, slotIndex] using hold 1 (by simp)
    simp only [copyCode]
    exact Bytes.wpX_copyOwned hm hRt hAt (fun hs => (hAl hs).1) (hBytes.toAt hAt)
      hBytes.payload_region hBytes.length_eq hRoot hLength (by change src + 2 ≤ base at hSrc; omega)
      (by change src + 2 ≤ base at hSrc; omega) hBase hRoom hCap hTrap
      fun heap' store' s' root' hStep hRep hFrame hTop _ hAl' =>
        hNext heap' store' s' [.i64 root', .i64 length]
          (by simpa only [Ty.blocks, Bytes.roots_regions] using hStep)
          ⟨root', length, rfl, hRep⟩ hFrame hTop
          fun hs => ⟨(hAl' hs).1, Ty.AlignedVal.bytesOwned (hAl' hs).2⟩
  | .array e, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, _, hRep, hold,
      hSrc, hBase, hRoom, hAl, hNext => by
    obtain ⟨ptr, rfl, ha⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [copyCode]
    exact wpX_copyArray hm hRt hAt (fun hs => (hAl hs).1)
      (fun hs => Ty.AlignedVal.array ha (hAl hs).2) hCap
      (by simp only [Elem.words_size, Ty.copyCost, allocCost]; omega) hTrap ha.borrow h0
      (by simp [Ty.width] at hSrc; omega) hBase
      (by simpa [Ty.copyScratch, Ty.scalar] using hRoom) fun heap' store' s' ptr' hStep hOwned hF
        hTop hAl' => hNext heap' store' s' [.i64 ptr'] hStep ⟨ptr', rfl, hOwned⟩ hF hTop
          fun hs => ⟨(hAl' hs).2.2, Ty.AlignedVal.ownedArray (hAl' hs).1 (hAl' hs).2.1⟩
  | .tree shape, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, _, hRep,
      hold, hSrc, hBase, hRoom, hAl, hNext => by
    obtain ⟨ptr, rfl, hBorrow⟩ := hRep.borrow
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    have hCost : nodeCopyCost v.toNode = (Ty.tree shape).copyCost v := v.copyCost_eq.symm
    simp only [copyCode]
    refine wpX_copyTree hm hRt hAt hCap v.toNode_layout hBorrow (by rw [hCost]; exact hTrap) h0
      (by simp only [Ty.width] at hSrc; omega) hBase
      (by simpa only [Ty.copyScratch, treeCopyScratch] using hRoom) (fun hs => (hAl hs).1)
      (fun hs r hr => (Ty.AlignedVal.toBorrowed hRep (hAl hs).2 r hr).1) ?_
    intro heap' store' s' ptr' hStep hOwned hApart hFrame hTop hAl'
    rw [hCost] at hTop
    exact hNext heap' store' s' [.i64 ptr'] hStep ⟨ptr', rfl, hOwned, hApart⟩ hFrame hTop
      fun hs => ⟨(hAl' hs).1, fun b hb => ⟨((hAl' hs).2 b hb).1, fun _ => ((hAl' hs).2 b hb).2⟩⟩
  | .treeHeader shape r, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, _,
      _, _, _, hBase, hRoom, hAl, hNext => by
    simp only [copyCode]
    exact wpX_copyTreeHeader hm hRt hAt hCap hTrap hBase hRoom (fun hs => (hAl hs).1)
      (fun heap' store' s' ptr hStep hOwned hFrame hTop hAl' =>
        hNext heap' store' s' [.i64 ptr] hStep ⟨ptr, rfl, hOwned⟩ hFrame hTop fun hs => by
          obtain ⟨hp, hc, hHeap'⟩ := hAl' hs
          refine ⟨hHeap', fun b hb => ?_⟩
          simp only [Ty.regions, Ty.blocks, List.mem_singleton] at hb
          subst hb
          simp only [block]
          exact ⟨by omega, fun _ => by omega⟩)
  | .pair a b, heap, store, s, h, src, base, mode, ws, v, rest, Q, hAt, hCap, hTrap, hh, hRep,
      hold, hSrc, hBase, hRoom, hAl, hNext => by
    obtain ⟨first, second, rfl, h1, h2, -⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ :=
      (LocalsHold.append (hl1.trans a.types_length.symm)).mp hold
    rw [hl1] at hold2
    simp only [copyCode, List.append_assoc]
    have hScratch : ∀ c : Ty, (c = a ∨ c = b) → c.copyScratch ≤ (Ty.pair a b).copyScratch := by
      intro c hc
      rcases hc with rfl | rfl
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    refine wpX_copyCode hm hRt a hAt hCap (hTrap.within fun hw => hw.mono (Nat.le_add_right _ _))
      hh h1 hold1 (by simp [Ty.width] at hSrc; omega) hBase
      (by have := hScratch a (Or.inl rfl); omega) (fun hs => ⟨(hAl hs).1, (hAl hs).2.fst hl1⟩)
      fun heap1 store1 s1 ws1 hStep1 hRep1 hF1 hTop1 hAl1 => ?_
    have hR2 := (h2.step hStep1 fun _ _ => trivial).1
    refine wpX_copyCode hm hRt b hStep1.at_ (by rw [hStep1.cap m]; exact hCap)
      (hTrap.within fun hw => Heap.Within.after hw hTop1 (hStep1.cap m))
      (s := { s1 with values := ws1.reverse ++ s.values }) (by simp [hF1.positions, hh]) hR2
      ((LocalsHold.frame (s' := { s1 with values := ws1.reverse ++ s.values })
        (hF1.trans Frame.ofValues) (h2.length.trans b.types_length.symm)
        (by rw [Ty.types_length]; simp [Ty.width] at hSrc; omega)).mpr hold2)
      (by simp [Ty.width] at hSrc; omega)
      (by show s1.params.length ≤ base; rw [hF1.params]; exact hBase)
      (by simp only [Locals.positions_values, hF1.positions]; have := hScratch b (Or.inr rfl); omega)
      (fun hs => ⟨(hAl1 hs).1,
        Ty.AlignedVal.step hStep1 h2 (fun _ _ => trivial) ((hAl hs).2.snd hl1)⟩)
      fun heap2 store2 s2 ws2 hStep2 hRep2 hF2 hTop2 hAl2 => ?_
    obtain ⟨hRep1', hSame1, hFresh1⟩ := hRep1.step hStep2 fun _ _ => trivial
    have hBlocks1 : a.blocks store2 ws1 v.1 = a.blocks store1 ws1 v.1 := hSame1
    have hStep := hStep1.transBoth (keep := fun _ => True) hStep2
      fun _ _ => ⟨trivial, fun _ => trivial⟩
    refine hNext heap2 store2 s2 (ws1 ++ ws2) ?_
      ⟨ws1, ws2, rfl, hRep1', hRep2, fun _ x hx y hy => ?_⟩
      (hF1.trans hF2.values) (by show _ ≤ _ + (a.copyCost v.1 + b.copyCost v.2); omega)
      (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.pair hRep1.length
        (Ty.AlignedVal.step hStep2 hRep1 (fun _ _ => trivial) (hAl1 hs).2) (hAl2 hs).2⟩)
      |> fun h => by
        simpa [List.reverse_append, List.append_assoc] using h
    · rw [Ty.blocks_append hRep1.length, hBlocks1]
      exact hStep
    · rw [hBlocks1] at hx
      exact hFresh1 x hx y hy

/-- The copy of every runtime meets `CopyCodeX`. -/
theorem copyCodeX {strict : Bool} {m : Module} (hm : Runtime m) {host : HostEnv Unit} :
    CopyCodeX strict m host :=
  wpX_copyCode hm fun _ => Runtime.allocAligned hm

end Verified
