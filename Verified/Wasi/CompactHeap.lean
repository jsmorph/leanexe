import Verified.Wasi.CompactRep

/-! The compaction in the pure module: from any heap that represents a compactable value, the code
leaves a heap whose top is the base plus at most the value's copy cost, whose free list is empty,
and which represents the value by blocks at or above the base. -/

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- The heap with top `top` and no free block. -/
def resetHeap (heap : Heap) (top : UInt64) : Heap := { heap with top, free := [] }

@[simp] theorem resetHeap_top (heap : Heap) (top : UInt64) : (resetHeap heap top).top = top := rfl
@[simp] theorem resetHeap_free (heap : Heap) (top : UInt64) : (resetHeap heap top).free = [] := rfl

/-- The globals of the reset heap. -/
def resetGlobals (heap : Heap) (top : UInt64) : List Value :=
  [.i64 top, .i64 0, .i64 heap.allocs, .i64 heap.frees]

/-- A heap with no free block whose top lies in memory holds at a store whose globals reset the
top and the free list. -/
theorem resetHeap_at {heap : Heap} {store : Store Unit} {top : UInt64}
    (hBase : 4096 ≤ top.toNat) (hTop : top.toNat ≤ store.mem.pages * 65536)
    (hPages : store.mem.pages ≤ 65535) :
    (resetHeap heap top).At { store with globals := { globals := resetGlobals heap top } } :=
  ⟨rfl, .nil, hBase, hTop, hPages, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- A reset to a top at least the old one keeps every region of the heap. -/
theorem _root_.Verified.Step.reset {heap : Heap} {store : Store Unit} (h : heap.At store) {top : UInt64}
    (hBase : 4096 ≤ top.toNat) (hTop : top.toNat ≤ store.mem.pages * 65536)
    (hGrow : heap.top.toNat ≤ top.toNat) :
    Step heap store (fun _ => True) (resetHeap heap top)
      { store with globals := { globals := resetGlobals heap top } } [] :=
  ⟨resetHeap_at hBase hTop h.pages, rfl, fun r hr _ _ =>
    ⟨fun _ _ _ => rfl, ⟨by have := hr.below; simp only [resetHeap]; omega,
      fun _ h => nomatch h⟩, fun _ h => nomatch h⟩⟩

/-- `global 1 := 0`: the free list empties. -/
theorem wp_emptyFree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {rest : Program} {Q : Assertion Unit} (hG : store.globals.globals = heap.globals)
    (hNext : wp m rest Q { store with globals := { globals := resetGlobals heap heap.top } } s host) :
    wp m (.constI64 0 :: .globalSet 1 :: rest) Q store s host := by
  simp only [wp_constI64_cons, wp_globalSet_cons, hG, Heap.globals, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ]
  exact hNext

/-- The top rounded up to a word: the code stores it in local `i` and in global 0. -/
theorem wp_roundTop {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {i : Nat} {rest : Program} {Q : Assertion Unit}
    (hG : store.globals.globals = resetGlobals heap heap.top)
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length)
    (hNext : wp m rest Q
      { store with globals := { globals := resetGlobals heap ((heap.top + 7) / 8 * 8) } }
      (setLocal { s with values := s.values } i (.i64 ((heap.top + 7) / 8 * 8))) host) :
    wp m (.globalGet 0 :: .constI64 7 :: .addI64 :: .constI64 8 :: .divUI64 :: .constI64 8 ::
      .mulI64 :: .localSet i :: .localGet i :: .globalSet 0 :: rest) Q store s host := by
  simp only [wp_globalGet_cons, hG, resetGlobals, List.getElem?_cons_zero]
  simp (config := { decide := true }) only [wp_constI64_cons, wp_addI64_cons, wp_divUI64_cons,
    wp_mulI64_cons, ↓reduceIte]
  refine wp_localSet_local (s := s) (vs := s.values) hLow hHigh ?_
  have hLow' : ({ s with values := s.values } : Locals).params.length ≤ i := hLow
  simp only [wp_localGet_cons, Locals.get_setLocal_same hLow' hHigh, wp_globalSet_cons, hG,
    resetGlobals, List.getElem?_cons_zero, List.set_cons_zero]
  exact hNext

/-- `global 0 := top` and `global 1 := 0` from a heap at the store's globals. -/
theorem wp_resetTop {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {top : UInt64} {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hG : store.globals.globals = heap.globals)
    (hNext : wp m rest Q { store with globals := { globals := resetGlobals heap top } }
      { s with values := vs } host) :
    wp m (.globalSet 0 :: .constI64 0 :: .globalSet 1 :: rest) Q store
      { s with values := .i64 top :: vs } host := by
  simp only [wp_globalSet_cons, wp_constI64_cons, hG, Heap.globals, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ]
  exact hNext

/-- The blocks of an owned compactable value lie above the reserved area and below the top, each
with a positive size. -/
theorem _root_.Verified.Ty.Rep.blocks_inside {heap : Heap} {store : Store Unit} (t : Ty)
    (ht : t.compactable = true) :
    ∀ {ws : List Value} {v : t.denote}, t.Rep .owned heap store ws v →
      ∀ b ∈ t.blocks store ws v, 4096 ≤ b.1 ∧ 0 < b.2 ∧ b.1 + b.2 ≤ heap.top.toNat := by
  induction t with
  | elem => intro ws v _ b hb; exact nomatch hb
  | array e =>
    rintro ws xs ⟨ptr, rfl, owned⟩ b hb
    have owned : heap.Owned store ptr (e.words xs) := owned
    simp only [Ty.blocks, List.mem_singleton] at hb
    subst hb
    have := owned.base
    have := owned.below
    simp only [block]
    omega
  | bytes =>
    rintro ws value ⟨root, length, rfl, rep⟩ b hb
    simp only [Ty.blocks, Bytes.roots] at hb
    split at hb
    · simp at hb
    · rename_i hZero
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      have allocated : Bytes.Allocated heap store root value := by
        rcases rep.buffer with ⟨h, _⟩ | h
        · exact absurd h hZero
        · exact h
      have := allocated.object.base
      have := allocated.object.below
      simp only [block]
      omega
  | pair a b iha ihb =>
    rintro ws v ⟨first, second, rfl, repA, repB, _⟩ x hx
    obtain ⟨ha, hb⟩ := Ty.compactable_pair ht
    rw [Ty.blocks_append repA.length] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact iha ha repA x hx
    · exact ihb hb repB x hx
  | _ => simp [Ty.compactable] at ht

/-- The rounded top as the code computes it. -/
theorem roundTop_toNat {top : UInt64} (h : top.toNat < 4294967296) :
    ((top + 7) / 8 * 8).toNat = roundWord top.toNat := by
  rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add]
  simp only [UInt64.reduceToNat]
  unfold roundWord
  omega

/-- The compaction of the compactable value whose words positions `loc` on hold.  The code traps
only at `unreachable`, and only when the copy finds no room above the rounded top.  Otherwise the
heap afterwards has no free block, ends at most the value's copy cost above `base`, represents the
value by the words at `loc` with its blocks at or above `base`, and keeps every byte below `base`.
The locals below `loc` and the local `aux`, which holds `base`, keep their values. -/
theorem wp_compactCode {m : Module} (hm : Runtime m) {host : HostEnv Unit} {t : Ty}
    (ht : t.compactable = true)
    {heap : Heap} {store : Store Unit} {s : Locals} {h loc aux : Nat} {ws : List Value}
    {v : t.denote} {base : UInt64} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hRep : t.Rep .owned heap store ws v) (hold : LocalsHold s loc t.types ws)
    (hh : s.positions = h) (hParams : s.params.length ≤ loc)
    (hLoc : loc + t.width ≤ aux) (hRoom : aux + 5 + t.copyScratch ≤ h)
    (hBase : s.get aux = some (.i64 base)) (hBaseLow : 4096 ≤ base.toNat)
    (hBaseTop : base.toNat ≤ heap.top.toNat)
    (hTrap : TrapOK (!decide (roundWord heap.top.toNat + t.copyCost v ≤
      65536 * store.memoryCap m 0)) Q)
    (hNext : ∀ (heap' : Heap) (store' : Store Unit) (s' : Locals) (ws' : List Value),
      heap'.At store' → heap'.free = [] →
      base.toNat ≤ heap'.top.toNat → heap'.top.toNat ≤ base.toNat + t.copyCost v →
      t.Rep .owned heap' store' ws' v → (∀ b ∈ t.blocks store' ws' v, base.toNat ≤ b.1) →
      (∀ a, a < base.toNat → store'.mem.bytes a = store.mem.bytes a) →
      store'.memoryCaps = store.memoryCaps →
      Frame loc s s' → LocalsHold s' loc t.types ws' → s'.get aux = some (.i64 base) →
      s'.values = s.values →
      wp m rest Q store' s' host) :
    wp m (compactCode h t loc aux ++ rest) Q store s host := by
  have hTop0 := hAt.top
  have hPages0 := hAt.pages
  have hBase0 := hAt.base
  have hTop32 : heap.top.toNat < 4294967296 := by omega
  have hTotal : 3 * s.positions ≤ s.params.length + s.locals.length := by
    simp only [Locals.positions]; omega
  have hW := hRep.length
  have hT8 : ((heap.top + 7) / 8 * 8).toNat = roundWord heap.top.toNat := roundTop_toNat hTop32
  have hT8Le := roundWord_le heap.top.toNat
  have hT8Mem : roundWord heap.top.toNat ≤ store.mem.pages * 65536 :=
    roundWord_le_of_mod hTop0 (by omega)
  have hStep2 := Step.reset hAt (top := (heap.top + 7) / 8 * 8) (by omega) (by omega) (by omega)
  have hRep2 := (hRep.step hStep2 fun _ _ => trivial).1
  have hLow1 : s.params.length ≤ aux + 1 := by omega
  have hHigh1 : aux + 1 < s.params.length + s.locals.length := by omega
  have hLow1' : ({ s with values := s.values } : Locals).params.length ≤ aux + 1 := hLow1
  have hS1 := Locals.get_setLocal_same (v := .i64 ((heap.top + 7) / 8 * 8)) hLow1' hHigh1
  have hF1 : Frame (aux + 1) s
      (setLocal { s with values := s.values } (aux + 1) (.i64 ((heap.top + 7) / 8 * 8))) :=
    Frame.setValues hLow1 le_rfl (by omega)
  simp only [compactCode, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_emptyFree hAt.globals ?_
  refine wp_roundTop (heap := heap) rfl hLow1 hHigh1 ?_
  generalize hT : (heap.top + 7) / 8 * 8 = T8 at hT8 hStep2 hRep2 hS1 hF1 ⊢
  generalize hs1 : setLocal { s with values := s.values } (aux + 1) (.i64 T8) = s1 at hS1 hF1 ⊢
  have hAt2 := hStep2.at_
  have hs1Pos : s1.positions = h := hF1.positions.trans hh
  have hp1 : s1.params = s.params := hF1.params
  have hv1 : s1.values = s.values := by rw [← hs1]; rfl
  have hHold1 : LocalsHold s1 loc t.types ws :=
    (LocalsHold.frame hF1 (by rw [hW, Ty.types_length]) (by rw [Ty.types_length]; omega)).mpr hold
  -- The copy, above the rounded top.
  refine wp_copyCode hm t hAt2 hCap
    (hTrap.within fun hw => by
      unfold Heap.Within
      rw [resetHeap_top, hT8]
      exact hw)
    hs1Pos hRep2 hHold1 (by omega) (by rw [hp1]; omega) (by rw [hs1Pos]; omega)
    fun heap2 store3 s3 ws3 hStep3 hRep3 hF3 hTop3 => ?_
  have hAt3 := hStep3.at_
  have hW3 := hRep3.length
  have hTop3n : heap2.top.toNat ≤ T8.toNat + t.copyCost v := by simpa using hTop3
  have hPages3 := hAt3.pages
  have hTop3' := hAt3.top
  -- The copy's blocks lie between the rounded top and the new top, and the copy keeps the bytes
  -- below the rounded top.
  have hRegion : (resetHeap heap T8).Region (0, T8.toNat) :=
    ⟨show 0 + T8.toNat ≤ T8.toNat by omega, fun _ h => nomatch h⟩
  obtain ⟨hKeepBytes, hRegion3, hFresh⟩ :=
    hStep3.keeps _ hRegion (show 0 < T8.toNat by rw [hT8]; omega) trivial
  have hT8Top3 : T8.toNat ≤ heap2.top.toNat := by have := hRegion3.below; simpa using this
  have hInside : ∀ b ∈ t.blocks store3 ws3 v, T8.toNat ≤ b.1 ∧ b.1 + b.2 ≤ heap2.top.toNat := by
    intro b hb
    obtain ⟨_, hPos, hBelow⟩ := Ty.Rep.blocks_inside t ht hRep3 b hb
    have hApart := hFresh b hb
    simp only [regionsDisjoint] at hApart
    omega
  have hs3Pos : s3.positions = h := hF3.positions.trans hs1Pos
  have hp3 : s3.params = s.params := hF3.params.trans hp1
  -- The store of the copy's words over the old ones.
  rw [hv1]
  refine wp_storeCode ws3 h loc t.types s3 s.values hRep3.typed hs3Pos
    (by rw [hp3]; omega) (by rw [Ty.types_length, hs3Pos]; omega) fun s4 hF4 hold4 hAbove4 => ?_
  have hs4Pos : s4.positions = h := hF4.positions.trans hs3Pos
  have hp4 : s4.params = s.params := hF4.params.trans hp3
  have hAux4 (j : Nat) (hj : aux ≤ j) (hj5 : j < aux + 5) : s4.get j = s1.get j := by
    rw [(hAbove4 j (by rw [Ty.types_length]; omega) (by rw [hs3Pos]; omega)).1]
    exact (hF3.below j hj5).1
  have hBase4 : s4.get aux = some (.i64 base) := by
    rw [hAux4 aux le_rfl (by omega), ← hs1, Locals.get_setLocal_ne hLow1' (by omega)]
    exact hBase
  have hStart4 : s4.get (aux + 1) = some (.i64 T8) := by
    rw [hAux4 (aux + 1) (by omega) (by omega)]; exact hS1
  -- The count of the copy's bytes.
  have hG3 : store3.globals.globals = heap2.globals := hAt3.globals
  simp only [wp_globalGet_cons, hG3, Heap.globals, List.getElem?_cons_zero, wp_localGet_cons,
    Locals.get_values, hStart4, wp_subI64_cons]
  have hLow2 : s4.params.length ≤ aux + 2 := by rw [hp4]; omega
  have hHigh2 : aux + 2 < s4.params.length + s4.locals.length :=
    Locals.lt_total (by rw [hs4Pos]; omega)
  refine wp_localSet_local (s := s4) (vs := s.values) hLow2 hHigh2 ?_
  have hn : (heap2.top - T8).toNat = heap2.top.toNat - T8.toNat :=
    Memory.toNat_sub_of_le _ _ hT8Top3
  have hLow2' : ({ s4 with values := s.values } : Locals).params.length ≤ aux + 2 := hLow2
  have hS5n := Locals.get_setLocal_same (v := .i64 (heap2.top - T8)) hLow2' hHigh2
  generalize hn' : heap2.top - T8 = n at hn hS5n ⊢
  generalize hs5 : setLocal { s4 with values := s.values } (aux + 2) (.i64 n) = s5 at hS5n ⊢
  have hS5 (j : Nat) (hj : j ≠ aux + 2) : s5.get j = s4.get j := by
    rw [← hs5, Locals.get_setLocal_ne hLow2' hj]; rfl
  have hF5 : Frame loc s4 s5 := by
    rw [← hs5]; exact Frame.setValues hLow2 (by omega) (by rw [hs4Pos]; omega)
  have hs5Pos : s5.positions = h := hF5.positions.trans hs4Pos
  have hp5 : s5.params = s.params := hF5.params.trans hp4
  have hv5 : s5.values = s.values := by rw [← hs5]; rfl
  -- The move of the copy's bytes down to the base.
  have hRound3 : T8.toNat + roundWord n.toNat ≤ store3.mem.pages * 65536 := by
    rw [hn, hT8]
    have := roundWord_mod heap.top.toNat
    have := roundWord_le_of_mod hTop3' (by omega)
    unfold roundWord at *
    omega
  refine wp_moveCode (dst := aux) (src := aux + 1) (count := aux + 2) (index := aux + 3)
    (by rw [hS5 aux (by omega)]; exact hBase4) (by rw [hS5 (aux + 1) (by omega)]; exact hStart4)
    hS5n (by omega) (by omega) (by omega) (by rw [hp5]; omega)
    (Locals.lt_total (by rw [hs5Pos]; omega))
    (by rw [hT8]; omega) hRound3 (by omega) fun store4 s6 hWrites hMoved hp6 hl6 hOther6 hv6 => ?_
  have hStore4 : store4 = { store3 with mem := store4.mem } := hWrites.1
  have hPages4 : store4.mem.pages = store3.mem.pages := hWrites.2.1
  have hS6 (j : Nat) (hj : j ≠ aux + 3) : s6.get j = s5.get j := hOther6 j hj
  have hF6 : Frame loc s5 s6 :=
    Frame.ofOthers hp6 hl6 hOther6 (by omega) (by rw [hs5Pos]; omega)
  have hs6Pos : s6.positions = h := hF6.positions.trans hs5Pos
  have hp6' : s6.params = s.params := hp6.trans hp5
  -- The distance of the move.
  simp only [wp_localGet_cons, Locals.get_values, hS6 (aux + 1) (by omega),
    hS5 (aux + 1) (by omega), hStart4, hS6 aux (by omega), hS5 aux (by omega), hBase4,
    wp_subI64_cons]
  have hLow6 : s6.params.length ≤ aux + 4 := by rw [hp6']; omega
  have hHigh6 : aux + 4 < s6.params.length + s6.locals.length :=
    Locals.lt_total (by rw [hs6Pos]; omega)
  refine wp_localSet_local (s := s6) (vs := s6.values) hLow6 hHigh6 ?_
  have hDeltaNat : (T8 - base).toNat = T8.toNat - base.toNat :=
    Memory.toNat_sub_of_le _ _ (by rw [hT8]; omega)
  have hLow6' : ({ s6 with values := s6.values } : Locals).params.length ≤ aux + 4 := hLow6
  have hS7d := Locals.get_setLocal_same (v := .i64 (T8 - base)) hLow6' hHigh6
  generalize hd : T8 - base = delta at hDeltaNat hS7d ⊢
  generalize hs7 : setLocal { s6 with values := s6.values } (aux + 4) (.i64 delta) = s7 at hS7d ⊢
  have hS7 (j : Nat) (hj : j ≠ aux + 4) : s7.get j = s6.get j := by
    rw [← hs7, Locals.get_setLocal_ne hLow6' hj]
  have hF7 : Frame loc s6 s7 := by
    rw [← hs7]; exact Frame.setValues hLow6 (by omega) (by rw [hs6Pos]; omega)
  have hs7Pos : s7.positions = h := hF7.positions.trans hs6Pos
  have hp7 : s7.params = s.params := hF7.params.trans hp6'
  have hv7 : s7.values = s.values := by rw [← hs7]; exact hv6.trans hv5
  have hold7 : LocalsHold s7 loc t.types ws3 := by
    intro k hk
    have hk' : k < t.width := by rw [hW3] at hk; exact hk
    have hSlot : slotIndex h (loc + k) (t.types.getD k .i64) ≠ aux + 2 ∧
        slotIndex h (loc + k) (t.types.getD k .i64) ≠ aux + 3 ∧
        slotIndex h (loc + k) (t.types.getD k .i64) ≠ aux + 4 := by
      cases t.types.getD k .i64 <;> simp only [slotIndex] <;> omega
    have := hold4 k hk
    rw [hs4Pos] at this
    rw [hs7Pos, hS7 _ hSlot.2.2, hS6 _ hSlot.2.1, hS5 _ hSlot.1]
    exact this
  -- The roots lose the distance.
  refine wp_relocateCode (store0 := store3) t ht hRep3 hold7 hS7d (Or.inr (by omega))
    (by rw [hp7]; omega) (by rw [hs7Pos]; omega) fun s8 hold8 hp8 hl8 same8 hv8 => ?_
  have hS8 (j : Nat) (hj : loc + t.width ≤ j) : s8.get j = s7.get j := same8 j (Or.inr hj)
  have hF8 : Frame loc s7 s8 :=
    ⟨hp8, hl8, fun j hj => ⟨same8 j (Or.inl hj), same8 _ (Or.inr (by rw [hs7Pos]; omega))⟩,
      fun j hj => same8 _ (Or.inr (by rw [hs7Pos]; omega))⟩
  -- The top past the moved blocks, and the free list empty again.
  have hG4 : store4.globals.globals = heap2.globals := by rw [hStore4]; exact hG3
  simp only [wp_localGet_cons, Locals.get_values, hS8 aux (by omega), hS7 aux (by omega),
    hS6 aux (by omega), hS5 aux (by omega), hBase4, hS8 (aux + 2) (by omega),
    hS7 (aux + 2) (by omega), hS6 (aux + 2) (by omega), hS5n, wp_addI64_cons]
  refine wp_resetTop (heap := heap2) (s := s8) (top := base + n) (vs := s8.values) hG4 ?_
  have hTop' : (base + n).toNat = base.toNat + n.toNat := by
    rw [UInt64.toNat_add]
    have : base.toNat + n.toNat < 18446744073709551616 := by rw [hn]; omega
    omega
  have hAt5 : (resetHeap heap2 (base + n)).At
      { store4 with globals := { globals := resetGlobals heap2 (base + n) } } :=
    resetHeap_at (by rw [hTop']; omega) (by rw [hTop', hPages4, hn, hT8]; omega)
      (by rw [hPages4]; exact hPages3)
  have hMovedStore : Moved store3 { store4 with globals := { globals := resetGlobals heap2 (base + n) } }
      T8.toNat heap2.top.toNat delta.toNat :=
    ⟨fun a ha1 ha2 => by
      have := hMoved (a - T8.toNat) (by have := roundWord_le n.toNat; omega)
      rw [show base.toNat + (a - T8.toNat) = a - delta.toNat by rw [hDeltaNat]; omega,
        show T8.toNat + (a - T8.toNat) = a by omega] at this
      exact this, hPages4⟩
  obtain ⟨hRep5, hBlocks5⟩ := Ty.Rep.relocate (heap' := resetHeap heap2 (base + n)) hMovedStore
    (by rw [hDeltaNat]; omega)
    (by simp only [resetHeap_top]; rw [hTop', hDeltaNat, hn]; omega) rfl t ht hRep3 hInside
  refine hNext (resetHeap heap2 (base + n)) _ { s8 with values := s8.values }
    (relocateWords delta t ws3) hAt5 rfl
    (by simp only [resetHeap_top]; rw [hTop']; omega)
    (by simp only [resetHeap_top]; rw [hTop', hn]; omega) hRep5 ?_ ?_ ?_ ?_ hold8 ?_ ?_
  · intro b hb
    rw [hBlocks5] at hb
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
    have := hInside b0 hb0
    show base.toNat ≤ b0.1 - delta.toNat
    rw [hDeltaNat]
    omega
  · intro a ha
    change store4.mem.bytes a = store.mem.bytes a
    rw [hWrites.2.2 a (Or.inl ha)]
    exact hKeepBytes a (Nat.zero_le _) (by show a < 0 + T8.toNat; rw [hT8]; omega)
  · change store4.memoryCaps = store.memoryCaps
    rw [hStore4]
    exact hStep3.caps
  · exact ((hF1.mono (by omega)).trans ((hF3.mono (by omega)).trans
      (hF4.trans (hF5.trans (hF6.trans (hF7.trans hF8))))))
  · show s8.get aux = some (.i64 base)
    rw [hS8 aux (by omega), hS7 aux (by omega), hS6 aux (by omega), hS5 aux (by omega)]
    exact hBase4
  · exact hv8.trans hv7

end Verified.Wasi
