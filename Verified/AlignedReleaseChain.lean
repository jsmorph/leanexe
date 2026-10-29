import Verified.AlignedRelease
import Verified.AlignedSpec

/-!
The release chain under the flag.  `wpX_release`, `Bytes.wpX_release`, `wpX_releaseNode`, and
`wpX_releaseHeader` call `release` through the three fields of `ReleaseAligned`; `wpX_releaseCode`
releases an owned value of any type, `wpX_releaseVars` the owned variables that die, and
`readReleaseX` proves `ReadReleaseX` from them.  `HoldsA.step` carries the invariant of the
variables that stay live across a step, by `Ty.AlignedVal.step`.  Each theorem is its original
with `wpX strict` for `wp`, the invariant's premises under `strict = true`, and the alignment of
the heap after the release for the continuation.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## The invariant across steps -/

section

variable {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
  {heap : Heap} {store : Store Unit} {s : Locals}

theorem HoldsA.live_mono (h : HoldsA env slots live heap store s) {live' : Nat → Bool}
    (hLive : ∀ i, live' i = true → live i = true) : HoldsA env slots live' heap store s :=
  ⟨h.1, fun t x hx => h.2 t x (hLive _ hx)⟩

theorem HoldsA.values (h : HoldsA env slots live heap store s) (vs : List Value) :
    HoldsA env slots live heap store { s with values := vs } := h

/-- The invariant after a step that keeps the regions of the live variables and leaves an
aligned heap. -/
theorem HoldsA.step (h : Holds env slots live base heap store s)
    (hA : HoldsA env slots live heap store s) {keep : Nat × Nat → Prop} {heap' : Heap}
    {store' : Store Unit} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh) (hAl : heap'.Aligned)
    (hKeep : ∀ (u : Ty) (y : Var Γ u), live y.index = true → ∀ wy,
      LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
      ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y), keep c) :
    HoldsA env slots live heap' store' s := by
  refine ⟨hAl, fun t x hx ws hold hl => ?_⟩
  obtain ⟨_, ws', hold', hRep⟩ := h.1 t x hx
  obtain rfl := LocalsHold.unique hold hold' (hl.trans hRep.length.symm)
  exact (hA.2 t x hx ws hold hl).step hStep hRep (hKeep t x hx ws hold hl)

end

/-- A block that starts and ends at multiples of 8 has an aligned pointer and capacity. -/
theorem block_aligned {store : Store Unit} {p : UInt64} (hp : 48 ≤ p.toNat)
    (h : (block store p).1 % 8 = 0 ∧ (block store p).2 % 8 = 0) :
    p.toNat % 8 = 0 ∧ capacityAt store p % 8 = 0 := by
  simp only [block] at h
  omega

/-! ## The calls of `release` -/

/-- `wp_release` under the flag: an owned array. -/
theorem wpX_release {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {ptr : UInt64} {xs : Array UInt64} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned)
    (hPtrAl : strict = true → ptr.toNat % 8 = 0 ∧ capacityAt store ptr % 8 = 0)
    (hOwned : heap.Owned store ptr xs)
    (hNext : (strict = true → (heap.release ptr (store.mem.read64 (ptr - 32).toUInt32)).Aligned) →
      wpX strict m rest Q (heap.releaseStore store ptr) { s with values := vs } host) :
    wpX strict m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  cases strict
  · exact wp_release hm hAt hOwned (hNext nofun)
  · obtain ⟨⟨N, hN⟩, hAl'⟩ := (hRA rfl).leaf host heap store ptr vs hAt (hHeapAl rfl)
      hOwned.object hOwned.magic hOwned.count hOwned.childMask (hPtrAl rfl).1 (hPtrAl rfl).2
    have hRun := ((release_run hm.imports hm.release host heap store ptr xs hAt hOwned).runs
      (aborts := false)).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release)
      (by rfl) vs
    refine wpA_call_runs ⟨hRun, N, hN⟩ trivial fun st' out hPost => ?_
    obtain ⟨out', rfl, rfl, rfl⟩ := hPost
    simpa using hNext fun _ => hAl'

/-- `Bytes.wp_release` under the flag: a buffer, whose root may be 0. -/
theorem Bytes.wpX_release {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {root length : UInt64} {bytes : LeanExe.Bytes}
    {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (hHeapAl : strict = true → heap.Aligned)
    (hRootAl : strict = true → root ≠ 0 → root.toNat % 8 = 0 ∧ capacityAt store root % 8 = 0)
    (h : Bytes.Rep heap store root length bytes)
    (hNext : (strict = true → (Bytes.releasedHeap heap store root).Aligned) →
      wpX strict m rest Q (Bytes.releasedStore heap store root) { s with values := vs } host) :
    wpX strict m (.call 1 :: rest) Q store { s with values := .i64 root :: vs } host := by
  cases strict
  · exact Bytes.wp_release hm hHeap h (hNext nofun)
  · have hAligned : (∃ N, ∀ fuel ≥ N, AlignedRun fuel m 1 store (.i64 root :: vs) host) ∧
        (Bytes.releasedHeap heap store root).Aligned := by
      rcases h.buffer with ⟨rfl, _⟩ | hBuffer
      · exact ⟨(hRA rfl).null host store vs, by simpa [Bytes.releasedHeap] using hHeapAl rfl⟩
      · obtain ⟨hp, hc⟩ := hRootAl rfl hBuffer.nonzero
        obtain ⟨hRun, hAl'⟩ := (hRA rfl).leaf host heap store root vs hHeap (hHeapAl rfl)
          hBuffer.object hBuffer.magic hBuffer.count hBuffer.childMask hp hc
        exact ⟨hRun, by simpa [Bytes.releasedHeap, hBuffer.nonzero] using hAl'⟩
    obtain ⟨⟨N, hN⟩, hAl'⟩ := hAligned
    have hRun := ((h.release_run hm.imports hm.release host hHeap).runs
      (aborts := false)).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release)
      (by rfl) vs
    refine wpA_call_runs ⟨hRun, N, hN⟩ trivial fun st' out hPost => ?_
    obtain ⟨out', rfl, rfl, rfl⟩ := hPost
    exact hNext fun _ => hAl'

/-- `wp_releaseNode` under the flag: the root of a value of a recursive type. -/
theorem wpX_releaseNode {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {ptr : UInt64} {value : Node} {vs : List Value}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned)
    (hBlocksAl : strict = true → ∀ b ∈ value.blocks store ptr, b.1 % 8 = 0 ∧ b.2 % 8 = 0)
    (hOwned : NodeOwned heap store ptr value)
    (hApart : (value.blocks store ptr).Pairwise regionsDisjoint)
    (hNext : ∀ heap' store',
      Step heap store (fun r => ∀ b ∈ value.blocks store ptr, regionsDisjoint r b)
        heap' store' [] → heap'.top = heap.top → (strict = true → heap'.Aligned) →
      wpX strict m rest Q store' { s with values := vs } host) :
    wpX strict m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  cases strict
  · exact wp_releaseNode hm hAt hOwned hApart fun heap' store' hStep hTop =>
      hNext heap' store' hStep hTop nofun
  · refine wpA_call_runs ((hRA rfl).tree host heap store ptr value vs hAt (hHeapAl rfl) hOwned
      hApart (hBlocksAl rfl)) trivial ?_
    rintro store' _ ⟨rfl, heap', hAt', hTop, hCaps, hKept, hAl'⟩
    have hStep : Step heap store (fun r => ∀ b ∈ value.blocks store ptr, regionsDisjoint r b)
        heap' store' [] :=
      ⟨hAt', hCaps, fun r hr hPos hKeep => ⟨(hKept r hr hPos hKeep).1,
        (hKept r hr hPos hKeep).2, nofun⟩⟩
    exact hNext heap' store' hStep hTop fun _ => hAl'

/-- `wp_releaseHeader` under the flag: a detached header. -/
theorem wpX_releaseHeader {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {heap : Heap}
    {shape : TreeShape} {r : Fin shape.records} {store : Store Unit} {s : Locals} {ptr : UInt64}
    {vs : List Value} {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hHeapAl : strict = true → heap.Aligned)
    (hBlockAl : strict = true → (block store ptr).1 % 8 = 0 ∧ (block store ptr).2 % 8 = 0)
    (hOwned : TreeHeader.Owned shape r heap store ptr)
    (hNext : ∀ heap' store', Step heap store (fun r => regionsDisjoint r (block store ptr))
      heap' store' [] → heap'.top = heap.top → (strict = true → heap'.Aligned) →
      wpX strict m rest Q store' { s with values := vs } host) :
    wpX strict m (.call 1 :: rest) Q store { s with values := .i64 ptr :: vs } host := by
  obtain ⟨words, _, hNode⟩ := hOwned
  have hBlocks : Node.blocks store ptr (.record (words.map Slot.word)) = [block store ptr] := by
    simp only [Node.blocks, wordSlots_blocks]
  refine wpX_releaseNode hm hRA hAt hHeapAl (fun hs b hb => ?_) hNode (by rw [hBlocks]; simp) ?_
  · rw [hBlocks, List.mem_singleton] at hb
    subst hb
    exact hBlockAl hs
  intro heap' store' hStep hTop hAl'
  exact hNext heap' store'
    (hStep.mono (fun r hr _ hb => by rw [hBlocks, List.mem_singleton] at hb; subst hb; exact hr)
      (fun _ h => h)) hTop hAl'

/-! ## The release of a value and of the variables that die -/

/-- `wp_releaseCode` under the flag. -/
theorem wpX_releaseCode {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} :
    (t : Ty) → ∀ {heap : Heap} {store : Store Unit} {s : Locals} {src : Nat} {ws : List Value}
      {v : t.denote} {rest : Program} {Q : Assertion Unit},
    heap.At store → (strict = true → heap.Aligned) →
    (strict = true → Ty.AlignedVal .owned store t ws v) →
    t.Rep .owned heap store ws v → LocalsHold s src t.types ws →
    (∀ (heap' : Heap) (store' : Store Unit),
      Step heap store (fun r => ∀ b ∈ t.blocks store ws v, regionsDisjoint r b) heap' store' [] →
      heap'.top = heap.top → (strict = true → heap'.Aligned) → wpX strict m rest Q store' s host) →
    wpX strict m (releaseCode t src ++ rest) Q store s host
  | .elem _, heap, store, _, _, _, _, _, _, hAt, hHeapAl, _, _, _, hNext => by
    simpa [releaseCode] using hNext heap store (Step.refl hAt _) rfl hHeapAl
  | .bytes, heap, store, s, src, ws, v, rest, Q, hAt, hHeapAl, hValAl, hRep, hold, hNext => by
    obtain ⟨root, length, rfl, hBytes⟩ := hRep
    have hRoot : s.get src = some (.i64 root) := by simpa [Ty.types, slotIndex] using hold 0 (by simp)
    simp only [releaseCode, List.cons_append, List.nil_append, wpX_localGet_cons, hRoot]
    refine Bytes.wpX_release hm hRA hAt hHeapAl (fun hs hne => ?_) hBytes fun hAl' => ?_
    · rcases hBytes.buffer with ⟨h0, _⟩ | hBuffer
      · exact absurd h0 hne
      · have hmem : block store root ∈ Ty.regions .owned store .bytes [.i64 root, .i64 length] v :=
          by simp [Ty.regions, Ty.blocks, Bytes.roots, hne]
        have hv := hValAl hs _ hmem
        exact block_aligned (by have := hBuffer.object.base; omega) ⟨hv.1, hv.2 rfl⟩
    · obtain ⟨hStep, hTop⟩ := hBytes.release_step hAt
      simpa using hNext _ _ (by simpa only [Ty.blocks, Bytes.roots_regions] using hStep) hTop hAl'
  | .array _, heap, store, s, src, ws, v, rest, Q, hAt, hHeapAl, hValAl, hRep, hold, hNext => by
    obtain ⟨ptr, rfl, hOwned⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [releaseCode, List.cons_append, List.nil_append, wpX_localGet_cons, h0]
    have hB : strict = true → (block store ptr).1 % 8 = 0 ∧ (block store ptr).2 % 8 = 0 :=
      fun hs => ⟨(hValAl hs _ (by simp [Ty.regions, Ty.blocks])).1,
        (hValAl hs _ (by simp [Ty.regions, Ty.blocks])).2 rfl⟩
    refine wpX_release hm hRA hAt hHeapAl
      (fun hs => block_aligned (by have := (show heap.Owned store ptr _ from hOwned).base; omega)
        (hB hs)) hOwned fun hAl' => ?_
    have := hNext _ _ ((releaseStep hAt hOwned).mono (fun r hr => hr _ (List.mem_singleton_self _))
      (fun _ h => h)) rfl hAl'
    simpa using this
  | .tree _, heap, store, s, src, ws, v, rest, Q, hAt, hHeapAl, hValAl, hRep, hold, hNext => by
    obtain ⟨ptr, rfl, hOwned, hApart⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [releaseCode, List.cons_append, List.nil_append, wpX_localGet_cons, h0]
    exact wpX_releaseNode hm hRA hAt hHeapAl
      (fun hs b hb => ⟨(hValAl hs b (by simpa [Ty.regions, Ty.blocks] using hb)).1,
        (hValAl hs b (by simpa [Ty.regions, Ty.blocks] using hb)).2 rfl⟩) hOwned hApart
      fun heap' store' hStep hTop hAl' => hNext heap' store' hStep hTop hAl'
  | .treeHeader _ _, heap, store, s, src, ws, v, rest, Q, hAt, hHeapAl, hValAl, hRep, hold,
      hNext => by
    obtain ⟨ptr, rfl, hOwned⟩ := hRep
    have h0 : s.get src = some (.i64 ptr) := LocalsHold.word hold
    simp only [releaseCode, List.cons_append, List.nil_append, wpX_localGet_cons, h0]
    refine wpX_releaseHeader hm hRA hAt hHeapAl
      (fun hs => ⟨(hValAl hs _ (by simp [Ty.regions, Ty.blocks])).1,
        (hValAl hs _ (by simp [Ty.regions, Ty.blocks])).2 rfl⟩) hOwned
      fun heap' store' hStep hTop hAl' => ?_
    exact hNext heap' store'
      (hStep.mono (fun r hr => hr _ (List.mem_singleton_self _)) (fun _ h => h)) hTop hAl'
  | .pair a b, heap, store, s, src, ws, v, rest, Q, hAt, hHeapAl, hValAl, hRep, hold, hNext => by
    obtain ⟨first, second, rfl, h1, h2, hd⟩ := hRep
    have hl1 := h1.length
    obtain ⟨hold1, hold2⟩ :=
      (LocalsHold.append (hl1.trans a.types_length.symm)).mp hold
    rw [hl1] at hold2
    have hRegions : Ty.regions .owned store (.pair a b) (first ++ second) v =
        a.regions .owned store first v.1 ++ b.regions .owned store second v.2 :=
      Ty.regions_append hl1
    have hVal1 : strict = true → Ty.AlignedVal .owned store a first v.1 := fun hs r hr =>
      hValAl hs r (by rw [hRegions]; exact List.mem_append_left _ hr)
    have hVal2 : strict = true → Ty.AlignedVal .owned store b second v.2 := fun hs r hr =>
      hValAl hs r (by rw [hRegions]; exact List.mem_append_right _ hr)
    simp only [releaseCode, List.append_assoc]
    refine wpX_releaseCode hm hRA a hAt hHeapAl hVal1 h1 hold1
      fun heap1 store1 hStep1 hTop1 hAl1 => ?_
    -- The second component's blocks lie apart from the first's, so the first release keeps them.
    have hKeep2 : ∀ r ∈ b.regions .owned store second v.2,
        (fun r => ∀ b ∈ a.blocks store first v.1, regionsDisjoint r b) r :=
      fun r hr x hx => regionsDisjoint_symm (hd rfl x hx r hr)
    obtain ⟨hR2, hSame2, -⟩ := h2.step hStep1 hKeep2
    have hBlocks2 : b.blocks store1 second v.2 = b.blocks store second v.2 := hSame2
    have hVal2' : strict = true → Ty.AlignedVal .owned store1 b second v.2 := fun hs =>
      (hVal2 hs).step hStep1 h2 hKeep2
    refine wpX_releaseCode hm hRA b hStep1.at_ hAl1 hVal2' hR2 hold2
      fun heap2 store2 hStep2 hTop2 hAl2 => ?_
    refine hNext heap2 store2 (hStep1.trans hStep2 fun r hr => ⟨fun x hx => ?_, fun _ x hx => ?_⟩)
      (hTop2.trans hTop1) hAl2
    · rw [Ty.blocks_append hl1] at hr
      exact hr x (List.mem_append_left _ hx)
    · rw [Ty.blocks_append hl1] at hr
      rw [hBlocks2] at hx
      exact hr x (List.mem_append_right _ hx)


/-- `wp_releaseVars` under the flag: the release of the owned variables among `is` keeps the
invariant of the variables that stay live. -/
theorem wpX_releaseVars {strict : Bool} {m : Module} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) {host : HostEnv Unit} {Γ : List Ty}
    {env : Env Γ} {slots : List Slot} {base : Nat} :
    (is : List Nat) → is.Nodup → ∀ {live : Nat → Bool} {heap : Heap} {store : Store Unit}
      {s : Locals} {rest : Program} {Q : Assertion Unit},
    Holds env slots live base heap store s → heap.At store →
    (strict = true → HoldsA env slots live heap store s) → (∀ i ∈ is, live i = true) →
    (∀ heap' store', Evolves env slots live (fun i => live i && !is.contains i) base heap store
      s heap' store' s → heap'.top = heap.top →
      (strict = true → HoldsA env slots (fun i => live i && !is.contains i) heap' store' s) →
      wpX strict m rest Q store' s host) →
    wpX strict m (is.flatMap (releaseVar Γ slots) ++ rest) Q store s host
  | [], _, live, heap, store, s, rest, Q, hVars, hAt, hA, _, hNext => by
    simpa using hNext heap store (Evolves.refl hAt hVars fun i _ h => by simpa using h) rfl
      fun hs => (hA hs).live_mono fun i h => by simpa using h
  | i :: is, hNodup, live, heap, store, s, rest, Q, hVars, hAt, hA, hLive, hNext => by
    have hi : i ∉ is := (List.nodup_cons.mp hNodup).1
    have hNodup' := (List.nodup_cons.mp hNodup).2
    let live1 := fun j => live j && j != i
    have hSub1 : ∀ j, live1 j = true → live j = true := fun j h => by
      simp only [live1, Bool.and_eq_true] at h; exact h.1
    -- The rest of the list, from the state after variable `i`.
    have hRest : ∀ heap1 store1, Evolves env slots live live1 base heap store s heap1 store1 s →
        heap1.top = heap.top → (strict = true → HoldsA env slots live1 heap1 store1 s) →
        wpX strict m (is.flatMap (releaseVar Γ slots) ++ rest) Q store1 s host := by
      intro heap1 store1 e1 hTop1 hA1
      refine wpX_releaseVars hm hRA is hNodup' e1.holds e1.step.at_ hA1 (fun j hj => ?_)
        fun heap2 store2 e2 hTop2 hA2 => ?_
      · simp only [live1, Bool.and_eq_true, bne_iff_ne]
        exact ⟨hLive j (List.mem_cons_of_mem _ hj), fun he => hi (he ▸ hj)⟩
      · have e := Evolves.trans hVars e1 e2 (fun j h => by
          simp only [Bool.and_eq_true] at h; exact h.1) hSub1
        have hEq : (fun j => live1 j && !is.contains j) =
            (fun j => live j && !(i :: is).contains j) := by
          funext j
          simp only [live1, List.contains_cons]
          cases live j <;> cases hj : (j == i) <;> simp_all [bne, beq_iff_eq]
        rw [hEq] at e hA2
        exact hNext heap2 store2 e (hTop2.trans hTop1) hA2
    simp only [List.flatMap_cons, List.append_assoc, releaseVar]
    cases hTy : Γ[i]? with
    | none =>
      simp only
      exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h) rfl
        fun hs => (hA hs).live_mono hSub1
    | some t =>
      simp only
      let x := Var.ofIndex Γ i hTy
      have hxi : x.index = i := Var.index_ofIndex Γ i hTy
      obtain ⟨hBelow, ws, hold, hRep⟩ := hVars.get x (by rw [hxi]; exact hLive i (by simp))
      have hValX : strict = true → Ty.AlignedVal (slots.getD x.index default).mode store t ws
          (env.get x) := fun hs =>
        (hA hs).2 t x (by rw [hxi]; exact hLive i (by simp)) ws hold hRep.length
      rw [hxi] at hold hRep hValX
      by_cases hOwned : (slots.getD i default).mode = .owned
      · simp only [hOwned, ↓reduceIte]
        rw [hOwned] at hRep hValX
        -- The regions of the variables that stay live lie apart from the blocks of `x`.
        have hKeepY : ∀ (u : Ty) (y : Var Γ u), live1 y.index = true → ∀ wy,
            LocalsHold s (slots.getD y.index default).loc u.types wy → wy.length = u.width →
            ∀ c ∈ u.regions (slots.getD y.index default).mode store wy (env.get y),
              ∀ b ∈ t.blocks store ws (env.get x), regionsDisjoint c b := by
          intro u y hy wy hwy hly c hc b hb
          have hne : x.index ≠ y.index := by
            rw [hxi]; intro he
            simp only [live1, Bool.and_eq_true, bne_iff_ne] at hy
            exact hy.2 he.symm
          exact regionsDisjoint_symm (hVars.2 t u x y (by rw [hxi]; exact hLive i (by simp))
            (hSub1 _ hy) hne (by rw [hxi]; exact hOwned) ws wy (by rw [hxi]; exact hold)
            hRep.length hwy hly b hb c hc)
        refine wpX_releaseCode hm hRA t hAt (fun hs => (hA hs).1) hValX hRep hold
          fun heap1 store1 hStep1 hTop1 hAl1 => hRest heap1 store1 ?_ hTop1 fun hs =>
            HoldsA.step (hVars.live_mono hSub1) ((hA hs).live_mono hSub1) hStep1 (hAl1 hs)
              hKeepY
        refine ⟨hStep1.mono (fun r hr b hb => hr t x (by rw [hxi]; exact hLive i (by simp))
            (by simp [live1, hxi]) (by rw [hxi]; exact hOwned) ws (by rw [hxi]; exact hold)
            (by rw [hRep.length]) b hb) (fun _ h => h), Frame.refl base s, ?_⟩
        exact (hVars.live_mono hSub1).step hStep1 hKeepY
      · simp only [hOwned, ↓reduceIte, List.nil_append]
        exact hRest heap store (Evolves.refl hAt hVars fun j _ h => hSub1 j h) rfl
          fun hs => (hA hs).live_mono hSub1

/-- `read_release` under the flag, from `ReleaseAligned`. -/
theorem readReleaseX {strict : Bool} {m : Module} {host : HostEnv Unit} (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) : ReadReleaseX strict m host := by
  intro Γ env slots live base heap store s vals rest Q t x hVars hAt hA hNext
  have hCode : (if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      releaseCode t (slots.getD x.index default).loc else []) =
      (if live x.index = false then [x.index] else []).flatMap (releaseVar Γ slots) := by
    cases live x.index <;> simp [releaseVar, x.getElem?_index]
  rw [hCode]
  have hLiveSub : ∀ k, live k = true →
      ((fun k => live k || k == x.index) k &&
        !(if live x.index = false then [x.index] else []).contains k) = true := fun k h => by
    split
    · next hx =>
      have hne : k ≠ x.index := fun he => by rw [he, hx] at h; exact nomatch h
      simp [h, hne]
    · simp [h]
  refine wpX_releaseVars hm hRA _ (by split <;> simp) (hVars.agree Frame.ofValues) hAt
    (fun hs => (hA hs).values _) (by split <;> simp)
    fun heap' store' e hTop hA' => hNext heap' store' ?_ hTop
      fun hs => ((hA' hs).live_mono hLiveSub).values s.values
  have e' := e.mono (live' := live) hLiveSub
  exact ⟨e'.step, e'.frame.values.trans Frame.ofValues,
    e'.holds.agree Frame.ofValues⟩

end Verified
