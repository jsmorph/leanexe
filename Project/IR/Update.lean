import Project.IR.Append
import Project.Pipeline.Records

/-!
The templates that update an owned array in its own block: `set!` writes one element, and the
caller's array becomes the result.
-/

namespace Project.IR

open Wasm Project.ProofKit Project.Pipeline Project.Runtime

variable {m : Module}

/-- Writing `v` into element `k` of an array keeps its length and its other elements. -/
theorem arrayAt_set {store : Store Unit} {p v : UInt64} {xs : Array UInt64} {k : Nat}
    (h : UInt64Array.At store p xs) (hk : k < xs.size) :
    UInt64Array.At
      { store with mem := store.mem.write64 (p + UInt64.ofNat (8 * (k + 1))).toUInt32 v } p
      (xs.set! k v) := by
  have hSize : (xs.set! k v).size = xs.size := by simp
  have hAddr := h.elementAddress_toNat k hk
  have hPtr := h.pointerAddress_toNat
  refine ⟨by rw [hSize]; exact h.1, by rw [hSize, Wasm.Mem.write64_pages]; exact h.2.1, ?_, ?_⟩
  · rw [hSize, Memory.read64_write64_disjoint _ _ _ _ (by rw [hAddr, hPtr]; omega)]
    exact h.lengthRead
  · intro i hi
    rw [hSize] at hi
    by_cases hik : i = k
    · subst hik
      rw [Memory.read64_write64]
      simp [Array.set!, Array.setIfInBounds, hk]
    · rw [Memory.read64_write64_disjoint _ _ _ _
        (by rw [hAddr, h.elementAddress_toNat i hi]; omega), h.elementRead i hi]
      simp [Array.set!, Array.setIfInBounds, hk, Array.getElem_set, Ne.symm hik]

/-- Writes the word in local `v` into element `k`, the word in local `k`, of the array at local
`src`, when `k` is below the array's length, which local `size` receives. -/
def Stmt.setInPlace (src size k v : Nat) : Stmt :=
  .seq (.arraySize size src) <|
  .ite (.ltU (.get k) (.get size))
    (.store (.bin .add (.get src) (.bin .mul (.bin .add (.get k) (.const 1)) (.const 8))) (.get v))
    .skip


/-- Writes inside the block of an owned array that leave it holding `ys`, which fit its
capacity, give `Stmt.AppendPost` with the array's own pointer: the allocator invariant, the
array owned, and every array apart from its block kept. -/
theorem Stmt.AppendPost.inPlace {heap : Heap} {initial store : Store Unit} {before state : State}
    {scratch : Nat} {locals : List Nat} {dst : Nat} {p : UInt64} {xs ys : Array UInt64}
    (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs)
    (hWrites : Memory.WritesRange initial store p.toNat (p.toNat + capacityAt initial p))
    (hValues : UInt64Array.At store p ys) (hFit : 8 * (ys.size + 1) ≤ capacityAt initial p)
    (hFrame : State.Frame scratch locals before state) (hDst : state.get dst = some (.i64 p)) :
    Stmt.AppendPost heap initial before scratch locals dst p ys store state := by
  have hBase := hOwned.base
  have hGlobals : store.globals = initial.globals := by rw [hWrites.1]
  obtain ⟨hOwned', hCapacity⟩ := hOwned.rewrite (store' := store)
    ⟨hGlobals, hWrites.2.1, fun a ha => hWrites.2.2 a ha⟩ hValues hFit
  have hBlock : block store p = block initial p := block_eq hCapacity
  -- Bytes of a region apart from the block keep their values.
  have hKeep : ∀ r : Nat × Nat, regionsDisjoint r (block initial p) →
      ∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a :=
    fun r hr a hLow hHigh => hWrites.2.2 a (by simp only [regionsDisjoint, block] at hr; omega)
  have hRegion := hOwned.region
  refine ⟨heap, p, hFrame, hDst, hHeap.writesApart hWrites fun node hNode => ?_, hOwned',
    by rw [hWrites.1], fun q ws hq hApart => ⟨hq.keep (le_of_eq hWrites.2.1.symm)
      (hKeep _ hApart) hq.region, by rw [hBlock]; exact hApart⟩,
    fun q ws hq hApart => ?_⟩
  · have := hOwned.separate node hNode
    simp only [regionsDisjoint] at this ⊢
    omega
  · obtain ⟨hq', hCap⟩ := hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ hApart) hq.region
    exact ⟨hq', hCap, by rw [hBlock]; exact hApart⟩

/-- `set!` in place: with the array at local `src` owned and the position and value in locals
`k` and `v`, the template leaves the owned array updated at the same pointer, and local `size`
holds the old length. -/
theorem Stmt.setInPlace_spec {scratch src size k v : Nat} {initial : Store Unit} {before : State}
    {heap : Heap} {p kw vw : UInt64} {xs : Array UInt64}
    (hSizeBelow : size < scratch) (hRoom : scratch ≤ before.params.length + before.locals.length)
    (hSrc : before.get src = some (.i64 p)) (hK : before.get k = some (.i64 kw))
    (hV : before.get v = some (.i64 vw)) (hSrcNe : src ≠ size) (hKNe : k ≠ size)
    (hVNe : v ≠ size) (hHeap : heap.At initial) (hOwned : heap.Owned initial p xs) :
    Triple m (Stmt.setInPlace src size k v) scratch
      (fun store state => store = initial ∧ state = before)
      (Stmt.AppendPost heap initial before scratch [size] src p (xs.set! kw.toNat vw)) := by
  have hArray := hOwned.values
  have hBase := hOwned.base
  have hCap := hOwned.capacity
  have hAddress := hOwned.address
  have hFit32 := hArray.1
  obtain ⟨s1, hSet⟩ := State.exists_set? (state := before) (index := size)
    (.i64 (UInt64.ofNat xs.size)) (by omega)
  have hFrame1 : State.Frame scratch [size] before s1 :=
    (State.Frame.refl _ _ before).set? hSet (.inl (by simp))
  have hSrc1 : s1.get src = some (.i64 p) := (State.get_set?_ne hSrcNe hSet).trans hSrc
  have hK1 : s1.get k = some (.i64 kw) := (State.get_set?_ne hKNe hSet).trans hK
  have hV1 : s1.get v = some (.i64 vw) := (State.get_set?_ne hVNe hSet).trans hV
  have hSize1 : s1.get size = some (.i64 (UInt64.ofNat xs.size)) := State.get_set?_same hSet
  have hSizeLt : xs.size < 536870912 := by omega
  have hSizeNat : (UInt64.ofNat xs.size).toNat = xs.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1)
    ((Stmt.arraySize_spec hArray hSrc (by omega)).mono (fun _ _ h => h)
      fun s st ⟨hs, hst⟩ => ⟨hs, by rw [hSet] at hst; exact (Option.some.inj hst).symm⟩) ?_
  by_cases hk : kw.toNat < xs.size
  · have hAddrEq : p + (kw + 1) * 8 = p + UInt64.ofNat (8 * (kw.toNat + 1)) := by
      congr 1
      apply UInt64.toNat.inj
      rw [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by
        simp [UInt64.size]; omega)]
      simp
      omega
    have hElem := hArray.elementAddress_toNat _ hk
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = s1)
      (PElse := fun _ _ => False) (Stmt.store_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨p + (kw + 1) * 8, s1, vw, s1, by simp [Expr.eval, hSrc1, hK1, U64Op.apply],
        by simp [Expr.eval, hV1], by rw [hAddrEq]; exact hArray.elementBound _ hk, ?_⟩
      rw [hAddrEq]
      refine Stmt.AppendPost.inPlace hHeap hOwned
        (Memory.WritesRange.write64 _ _ _ _ _ (by rw [hElem]; omega) (by rw [hElem]; omega))
        (arrayAt_set hArray hk) (by simp; omega) hFrame1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨true, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]
  · have hSame : xs.set! kw.toNat vw = xs := by simp [Array.set!, Array.setIfInBounds, hk]
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = s1) Triple.of_false
      (Stmt.skip_spec.mono (fun _ _ h => h) ?_)).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, hst⟩
      subst st
      rw [hSame]
      exact Stmt.AppendPost.inPlace hHeap hOwned (.refl _ _ _) hArray (by omega) hFrame1 hSrc1
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨false, s1, ?_, rfl, rfl⟩
      simp [Expr.eval, hK1, hSize1, UInt64.lt_iff_toNat_lt, hSizeNat, hk]

end Project.IR
