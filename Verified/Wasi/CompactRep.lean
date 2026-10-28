import Verified.Wasi.CompactMove

/-! A value whose blocks move down by `d` bytes, and whose roots lose `d`, keeps its
representation in a heap that ends past the moved blocks and has no free block. -/

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `store'` holds at `a - delta` the byte that `store` holds at `a`, for each address `a` of
`[lo, hi)`, and has the pages of `store`. -/
structure Moved (store store' : Store Unit) (lo hi delta : Nat) : Prop where
  bytes : ∀ a, lo ≤ a → a < hi → store'.mem.bytes (a - delta) = store.mem.bytes a
  pages : store'.mem.pages = store.mem.pages

/-- Two words whose bytes agree are equal. -/
theorem read64_shift {m1 m2 : Mem} {x y : UInt32}
    (h : ∀ i, i < 8 → m1.bytes (y.toNat + i) = m2.bytes (x.toNat + i)) :
    m1.read64 y = m2.read64 x := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  have h6 := h 6 (by omega)
  have h7 := h 7 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h0
  simp only [Mem.read64]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- A moved word: the word at `y`, `delta` below `x`, is the word at `x` before the move. -/
theorem Moved.read64 {store store' : Store Unit} {lo hi delta : Nat}
    (moved : Moved store store' lo hi delta) {x y : UInt32}
    (hy : y.toNat + delta = x.toNat) (hlo : lo ≤ x.toNat) (hhi : x.toNat + 8 ≤ hi) :
    store'.mem.read64 y = store.mem.read64 x :=
  read64_shift fun i hi => by
    rw [show y.toNat + i = x.toNat + i - delta by omega]
    exact moved.bytes _ (by omega) (by omega)

theorem sub_toNat {x d : UInt64} (h : d.toNat ≤ x.toNat) : (x - d).toNat = x.toNat - d.toNat :=
  Memory.toNat_sub_of_le x d h

/-- A moved array: the words of an array that lies in `[lo, hi)` are those of the array `d` bytes
below. -/
theorem arrayAt_relocate {store store' : Store Unit} {ptr d : UInt64} {words : Array UInt64}
    {lo hi : Nat} (h : UInt64Array.At store ptr words) (moved : Moved store store' lo hi d.toNat)
    (hlo : lo ≤ ptr.toNat) (hhi : ptr.toNat + 8 * (words.size + 1) ≤ hi) (hd : d.toNat ≤ lo) :
    UInt64Array.At store' (ptr - d) words := by
  have hp := sub_toNat (x := ptr) (d := d) (by omega)
  have hFit := h.1
  have hMem := h.2.1
  refine ⟨by omega, by rw [moved.pages]; omega, ?_, fun i hi => ?_⟩
  · rw [← h.2.2.1]
    apply moved.read64
    · rw [Memory.toUInt32_toNat, Memory.toUInt32_toNat, hp]
      omega
    · rw [Memory.toUInt32_toNat]; omega
    · rw [Memory.toUInt32_toNat]; omega
  · rw [← h.2.2.2 i hi]
    have hOld := h.elementAddress_toNat i hi
    have hNew : ((ptr - d) + UInt64.ofNat (8 * (i + 1))).toUInt32.toNat =
        ptr.toNat - d.toNat + 8 * (i + 1) := by
      rw [address_toNat (by omega), hp]
    apply moved.read64
    · rw [hNew, hOld]; omega
    · rw [hOld]; omega
    · rw [hOld]; omega

/-- A moved header word: the header word `k` bytes before the payload at `ptr - d` is the one
before `ptr`. -/
theorem Moved.header {store store' : Store Unit} {lo hi : Nat} {ptr d k : UInt64}
    (moved : Moved store store' lo hi d.toNat) (hk : 8 ≤ k.toNat) (hk48 : k.toNat ≤ 48)
    (hlo : lo ≤ ptr.toNat - 48) (hhi : ptr.toNat ≤ hi) (hd : d.toNat ≤ lo)
    (hFit : ptr.toNat < 4294967296) (hBase : 48 ≤ ptr.toNat) :
    store'.mem.read64 ((ptr - d) - k).toUInt32 = store.mem.read64 (ptr - k).toUInt32 := by
  have hp := sub_toNat (x := ptr) (d := d) (by omega)
  have hNew : ((ptr - d) - k).toUInt32.toNat = ptr.toNat - d.toNat - k.toNat := by
    rw [headerAddress_toNat (ptr := ptr - d) (k := k) (by rw [hp]; omega) (by rw [hp]; omega), hp]
  have hOld : (ptr - k).toUInt32.toNat = ptr.toNat - k.toNat :=
    headerAddress_toNat (ptr := ptr) (k := k) (by omega) hFit
  apply moved.read64
  · rw [hNew, hOld]; omega
  · rw [hOld]; omega
  · rw [hOld]; omega

/-- An owned array moved down by `d` bytes is owned at `ptr - d` in a heap that ends past its
block and has no free block. -/
theorem _root_.LeanExe.Pipeline.Heap.Owned.relocate {heap heap' : Heap} {store store' : Store Unit} {ptr d : UInt64}
    {words : Array UInt64} {lo hi : Nat}
    (h : heap.Owned store ptr words) (moved : Moved store store' lo hi d.toNat)
    (hlo : lo ≤ ptr.toNat - 48) (hhi : ptr.toNat + capacityAt store ptr ≤ hi)
    (low : 4096 + d.toNat ≤ lo) (top : hi - d.toNat ≤ heap'.top.toNat) (free : heap'.free = []) :
    heap'.Owned store' (ptr - d) words ∧ capacityAt store' (ptr - d) = capacityAt store ptr := by
  have hBase := h.base
  have hAddress := h.address
  have hWords := h.capacity
  have hp := sub_toNat (x := ptr) (d := d) (by omega)
  have hHeader (k : UInt64) (hk : 8 ≤ k.toNat) (hk48 : k.toNat ≤ 48) :=
    moved.header (ptr := ptr) hk hk48 hlo (by omega) (by omega) (by omega) (by omega)
  have hCapacity : capacityAt store' (ptr - d) = capacityAt store ptr := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  refine ⟨⟨arrayAt_relocate h.values moved (by omega) (by omega) (by omega), by omega, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hCapacity⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hCapacity]; exact hWords
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.childMask
  · rw [hCapacity, hp]; omega
  · rw [hCapacity, hp]; omega
  · intro node hNode
    rw [free] at hNode
    exact nomatch hNode

/-- A byte string's block moved down by `d` bytes is allocated at `root - d` in a heap that ends
past its block and has no free block. -/
theorem _root_.LeanExe.Pipeline.Heap.Buffer.relocate {heap heap' : Heap}
    {store store' : Store Unit} {root d : UInt64} {bytes : LeanExe.Bytes} {lo hi : Nat}
    (h : Heap.Buffer heap store root bytes) (moved : Moved store store' lo hi d.toNat)
    (hlo : lo ≤ root.toNat - 48) (hhi : root.toNat + capacityAt store root ≤ hi)
    (low : 4096 + d.toNat ≤ lo) (top : hi - d.toNat ≤ heap'.top.toNat) (free : heap'.free = []) :
    Heap.Buffer heap' store' (root - d) bytes ∧
      capacityAt store' (root - d) = capacityAt store root := by
  have hBase := h.object.base
  have hAddress := h.object.address
  have hSize := h.capacity
  have hp := sub_toNat (x := root) (d := d) (by omega)
  have hHeader (k : UInt64) (hk : 8 ≤ k.toNat) (hk48 : k.toNat ≤ 48) :=
    moved.header (ptr := root) hk hk48 hlo (by omega) (by omega) (by omega) (by omega)
  have hCapacity : capacityAt store' (root - d) = capacityAt store root := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  refine ⟨⟨⟨by rw [hp]; omega, by rw [hCapacity, hp]; omega, by rw [hCapacity, hp]; omega,
      fun node hNode => by rw [free] at hNode; exact nomatch hNode⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun i hi => ?_⟩, hCapacity⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hCapacity]; exact h.minimum
  · rw [hCapacity]; exact hSize
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.childMask
  · rw [hp, show root.toNat - d.toNat + i = root.toNat + i - d.toNat by omega,
      moved.bytes _ (by omega) (by omega)]
    exact h.contents i hi

theorem regionsDisjoint_relocate {x y : Nat × Nat} {d : Nat} (hx : d ≤ x.1) (hy : d ≤ y.1)
    (h : regionsDisjoint x y) : regionsDisjoint (x.1 - d, x.2) (y.1 - d, y.2) := by
  simp only [regionsDisjoint] at h ⊢
  omega

/-- The representation of a compactable value whose blocks lie in `[lo, hi)` after the move of
`[lo, hi)` down by `d` bytes: the relocated words represent it in a heap that ends past the moved
range and has no free block, and its blocks are the old blocks `d` bytes lower. -/
theorem _root_.Verified.Ty.Rep.relocate {heap heap' : Heap} {store store' : Store Unit} {lo hi : Nat} {d : UInt64}
    (moved : Moved store store' lo hi d.toNat) (low : 4096 + d.toNat ≤ lo)
    (top : hi - d.toNat ≤ heap'.top.toNat) (free : heap'.free = []) (t : Ty)
    (ht : t.compactable = true) :
    ∀ {ws : List Value} {v : t.denote}, t.Rep .owned heap store ws v →
      (∀ b ∈ t.blocks store ws v, lo ≤ b.1 ∧ b.1 + b.2 ≤ hi) →
      t.Rep .owned heap' store' (relocateWords d t ws) v ∧
        t.blocks store' (relocateWords d t ws) v =
          (t.blocks store ws v).map fun b => (b.1 - d.toNat, b.2) := by
  induction t with
  | elem e =>
    intro ws v rep _
    exact ⟨rep, rfl⟩
  | array e =>
    rintro ws xs ⟨ptr, rfl, owned⟩ inside
    have hBlock := inside (block store ptr) (by simp [Ty.blocks])
    have hBase := (owned : heap.Owned store ptr (e.words xs)).base
    simp only [block] at hBlock
    obtain ⟨owned', capacity⟩ := Heap.Owned.relocate owned moved (by omega) (by omega) low top free
    have hp := sub_toNat (x := ptr) (d := d) (by omega)
    refine ⟨⟨ptr - d, rfl, owned'⟩, ?_⟩
    simp only [relocateWords, Ty.blocks, List.map_cons, List.map_nil, block, capacity, hp,
      List.cons.injEq, Prod.mk.injEq, and_true]
    omega
  | bytes =>
    rintro ws value ⟨root, length, rfl, rep⟩ inside
    by_cases hZero : root = 0
    · subst hZero
      have hEmpty : value.data.size = 0 := by
        rcases rep.buffer with ⟨_, h⟩ | h
        · exact h
        · exact absurd rfl h.nonzero
      refine ⟨⟨0, length, by simp [relocateWords], rep.length_eq, Or.inl ⟨rfl, hEmpty⟩⟩, ?_⟩
      simp [relocateWords, Ty.blocks, Bytes.roots]
    · have allocated : Heap.Buffer heap store root value := by
        rcases rep.buffer with ⟨h, _⟩ | h
        · exact absurd h hZero
        · exact h
      have hBlock := inside (block store root) (by simp [Ty.blocks, Bytes.roots, hZero])
      have hBase := allocated.object.base
      simp only [block] at hBlock
      obtain ⟨allocated', capacity⟩ :=
        allocated.relocate moved (by omega) (by omega) low top free
      have hp := sub_toNat (x := root) (d := d) (by omega)
      have hNonzero : root - d ≠ 0 := allocated'.nonzero
      refine ⟨⟨root - d, length, by simp [relocateWords, hZero], rep.length_eq, Or.inr allocated'⟩,
        ?_⟩
      simp only [relocateWords, hZero, ↓reduceIte, Ty.blocks, Bytes.roots, hNonzero, List.map_cons,
        List.map_nil, block, capacity, hp, List.cons.injEq, Prod.mk.injEq, and_true]
      omega
  | pair a b iha ihb =>
    rintro ws v ⟨first, second, rfl, repA, repB, apart⟩ inside
    obtain ⟨ha, hb⟩ := Ty.compactable_pair ht
    have hl := repA.length
    have hBlocks := Ty.blocks_append (store := store) (second := second) (p := v) hl
    rw [hBlocks] at inside
    obtain ⟨repA', blocksA⟩ := iha ha repA fun x hx => inside x (List.mem_append_left _ hx)
    obtain ⟨repB', blocksB⟩ := ihb hb repB fun x hx => inside x (List.mem_append_right _ hx)
    have hWords : relocateWords d (.pair a b) (first ++ second) =
        relocateWords d a first ++ relocateWords d b second := by
      simp only [relocateWords, List.take_left' hl, List.drop_left' hl]
    have hl' : (relocateWords d a first).length = a.width :=
      relocateWords_length d a first hl
    rw [hWords]
    refine ⟨⟨_, _, rfl, repA', repB', fun _ x hx y hy => ?_⟩, ?_⟩
    · rw [blocksA] at hx
      rw [blocksB] at hy
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
      have := inside x0 (List.mem_append_left _ hx0)
      have := inside y0 (List.mem_append_right _ hy0)
      exact regionsDisjoint_relocate (by omega) (by omega) (apart rfl x0 hx0 y0 hy0)
    · rw [Ty.blocks_append hl', blocksA, blocksB, hBlocks, List.map_append]
  | _ => simp [Ty.compactable] at ht

/-- Locals that agree with `s` at every position outside `[lo, hi)` hold what `s` holds at
positions outside it. -/
theorem _root_.Verified.LocalsHold.outside {s s' : Locals} {loc lo hi : Nat} {tys : List ValueType}
    {ws : List Value} (hold : LocalsHold s loc tys ws) (hPositions : s'.positions = s.positions)
    (same : ∀ j, (j < lo ∨ hi ≤ j) → s'.get j = s.get j)
    (hApart : loc + ws.length ≤ lo ∨ hi ≤ loc) (hTop : hi ≤ s.positions) :
    LocalsHold s' loc tys ws := by
  intro k hk
  rw [hPositions, same (slotIndex s.positions (loc + k) (tys.getD k .i64))
    (by cases tys.getD k .i64 <;> simp only [slotIndex] <;> omega)]
  exact hold k hk

/-- The subtraction of the word `d` of local `delta` from the roots of the compactable value whose
words positions `loc` on hold: the positions hold the relocated words, and no other local
changes. -/
theorem wp_relocateCode {α : Type} {m : Module} {host : HostEnv α} {store : Store α} {d : UInt64}
    {delta : Nat} {heap : Heap} {store0 : Store Unit} (t : Ty) (ht : t.compactable = true) :
    ∀ {s : Locals} {loc : Nat} {ws : List Value} {v : t.denote} {rest : Program}
      {Q : Assertion α},
    t.Rep .owned heap store0 ws v → LocalsHold s loc t.types ws →
    s.get delta = some (.i64 d) → (delta < loc ∨ loc + t.width ≤ delta) →
    s.params.length ≤ loc → loc + t.width ≤ s.positions →
    (∀ s', LocalsHold s' loc t.types (relocateWords d t ws) → s'.params = s.params →
      s'.locals.length = s.locals.length →
      (∀ j, (j < loc ∨ loc + t.width ≤ j) → s'.get j = s.get j) → s'.values = s.values →
      wp m rest Q store s' host) →
    wp m (relocateCode delta t loc ++ rest) Q store s host := by
  induction t with
  | elem e =>
    intro s loc ws v rest Q rep hold _ _ _ _ next
    simpa only [relocateCode, List.nil_append] using
      next s (by simpa [relocateWords] using hold) rfl rfl (fun _ _ => rfl) rfl
  | array e =>
    rintro s loc ws xs rest Q ⟨ptr, rfl, _⟩ hold hDelta hApart hLow hHigh next
    have hPtr : s.get loc = some (.i64 ptr) := LocalsHold.word hold
    have hTotal := Locals.lt_total (s := s) (i := loc) (by simp only [Ty.width] at hHigh; omega)
    simp only [relocateCode, List.cons_append, List.nil_append, wp_localGet_cons, hPtr,
      Locals.get_values, hDelta, wp_subI64_cons]
    refine wp_localSet_local (s := s) (vs := s.values) hLow hTotal ?_
    have hLow' : ({ s with values := s.values } : Locals).params.length ≤ loc := hLow
    refine next _ (fun k hk => ?_) rfl (by simp [setLocal]) (fun j hj => ?_) rfl
    · have hk0 : k = 0 := by simp [relocateWords] at hk; omega
      subst hk0
      simpa [relocateWords, slotIndex, Ty.types] using
        Locals.get_setLocal_same (v := .i64 (ptr - d)) hLow' hTotal
    · rw [Locals.get_setLocal_ne hLow' (by simp only [Ty.width] at hj; omega)]
  | bytes =>
    rintro s loc ws value rest Q ⟨root, length, rfl, _⟩ hold hDelta hApart hLow hHigh next
    have hRoot : s.get loc = some (.i64 root) := by
      simpa [Ty.types, slotIndex] using hold 0 (by simp)
    have hLength : s.get (loc + 1) = some (.i64 length) := by
      simpa [Ty.types, slotIndex] using hold 1 (by simp)
    have hTotal := Locals.lt_total (s := s) (i := loc) (by simp only [Ty.width] at hHigh; omega)
    simp only [relocateCode, List.cons_append, List.nil_append, wp_localGet_cons, hRoot,
      wp_constI64_cons, wp_neI64_cons, wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    by_cases hZero : root = 0
    · subst hZero
      simp (config := { decide := true }) only [↓reduceIte, wp_nil, List.take_zero,
        List.drop_zero, List.nil_append]
      exact next _ (by simpa [relocateWords] using hold) rfl rfl (fun _ _ => rfl) rfl
    · simp (config := { decide := true }) only [ne_eq, hZero, not_false_eq_true, ↓reduceIte,
        wp_localGet_cons, Locals.get_values, hRoot, hDelta, wp_subI64_cons]
      refine wp_localSet_local (s := s) (vs := s.values) hLow hTotal ?_
      have hLow' : ({ s with values := s.values } : Locals).params.length ≤ loc := hLow
      simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append]
      refine next _ (fun k hk => ?_) rfl (by simp [setLocal]) (fun j hj => ?_) rfl
      · have hk2 : k < 2 := by simpa [relocateWords] using hk
        match k, hk2 with
        | 0, _ =>
          simpa [relocateWords, hZero, slotIndex, Ty.types] using
            Locals.get_setLocal_same (v := .i64 (root - d)) hLow' hTotal
        | 1, _ =>
          change (setLocal { s with values := s.values } loc (.i64 (root - d))).get (loc + 1) = _
          rw [Locals.get_setLocal_ne hLow' (by omega), Locals.get_values, hLength]
          simp [relocateWords, hZero]
        | k + 2, h => exact absurd h (by omega)
      · rw [Locals.get_values, Locals.get_setLocal_ne hLow' (by simp only [Ty.width] at hj; omega)]
  | pair a b iha ihb =>
    rintro s loc ws v rest Q ⟨first, second, rfl, repA, repB, _⟩ hold hDelta hApart hLow hHigh
      next
    obtain ⟨ha, hb⟩ := Ty.compactable_pair ht
    have hl := repA.length
    have hlb := repB.length
    obtain ⟨holdA, holdB⟩ :=
      (LocalsHold.append (hl.trans a.types_length.symm)).mp (by simpa [Ty.types] using hold)
    rw [hl] at holdB
    simp only [Ty.width] at hApart hHigh
    simp only [relocateCode, List.append_assoc]
    refine iha ha repA holdA hDelta (by omega) hLow (by omega) fun s1 holdA1 hp1 hl1 same1 hv1 => ?_
    have hPos1 : s1.positions = s.positions := by simp [Locals.positions, hp1, hl1]
    have holdB1 : LocalsHold s1 (loc + a.width) b.types second :=
      holdB.outside hPos1 same1 (by omega) (by omega)
    have hDelta1 : s1.get delta = some (.i64 d) := by rw [same1 _ (by omega)]; exact hDelta
    refine ihb hb repB holdB1 hDelta1 (by omega) (by rw [hp1]; omega) (by rw [hPos1]; omega)
      fun s2 holdB2 hp2 hl2 same2 hv2 => ?_
    have hPos2 : s2.positions = s1.positions := by simp [Locals.positions, hp2, hl2]
    have holdA2 : LocalsHold s2 loc a.types (relocateWords d a first) :=
      holdA1.outside hPos2 same2
        (by rw [relocateWords_length d a first hl]; omega) (by rw [hPos1]; omega)
    have hWords : relocateWords d (.pair a b) (first ++ second) =
        relocateWords d a first ++ relocateWords d b second := by
      simp only [relocateWords, List.take_left' hl, List.drop_left' hl]
    refine next s2 ?_ (hp2.trans hp1) (hl2.trans hl1) (fun j hj => ?_) (hv2.trans hv1)
    · rw [hWords]
      simp only [Ty.types]
      refine (LocalsHold.append (by rw [relocateWords_length d a first hl, a.types_length])).mpr
        ⟨holdA2, ?_⟩
      rw [relocateWords_length d a first hl]
      exact holdB2
    · simp only [Ty.width] at hj
      rw [same2 j (by omega), same1 j (by omega)]
  | _ => simp [Ty.compactable] at ht

end Verified.Wasi
