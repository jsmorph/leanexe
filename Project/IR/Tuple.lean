import Project.IR.Live
import Project.IR.Loop

/-!
Calls that return a nest of word arrays, `Array UInt64 × (Array UInt64 × …)`.  `Arrays`
lists the arrays of such a value and states what `Represent.owned` and `Represent.outside`
mean for it: each array owned, in pairwise disjoint blocks.  `Live.callTuple` runs a call
that consumes some live temporaries and returns a nest of arrays, which take their place,
and `Live.finish_tuple` gives the postcondition of `Func.implements_moves` for such a
result.  `Live.callPair` and `Live.finish_pair` are their case of two arrays.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module} {moved : List UInt64}

/-- The values of the arrays `ts`: their pointers, in order. -/
abbrev pointers (ts : List (UInt64 × Array UInt64)) : List Value := ts.map fun t => .i64 t.1

/-- A nest of word arrays, represented by the arrays' pointers in order: an owned nest is
a list of owned arrays in pairwise disjoint blocks, and it lies outside a region when each
of their blocks does. -/
class Arrays (β : Type) [Represent β] where
  arrays : β → List (Array UInt64)
  size : Nat
  length_arrays (y : β) : (arrays y).length = size
  values {heap : Heap} {store : Store Unit} {vs : List Value} {y : β} :
    Represent.owned heap store vs y →
      ∃ ts : List (UInt64 × Array UInt64), ts.map (·.2) = arrays y ∧ vs = pointers ts
  owned {heap : Heap} {store : Store Unit} {ts : List (UInt64 × Array UInt64)} {y : β} :
    ts.map (·.2) = arrays y →
      (Represent.owned heap store (pointers ts) y ↔ (∀ t ∈ ts, heap.Owned store t.1 t.2) ∧
        ts.Pairwise fun t u => regionsDisjoint (block store t.1) (block store u.1))
  outside {store : Store Unit} {ts : List (UInt64 × Array UInt64)} {y : β}
    {region : Nat × Nat} : ts.map (·.2) = arrays y →
      (Represent.outside store (pointers ts) y region ↔
        ∀ t ∈ ts, regionsDisjoint region (block store t.1))

/-- A pair lies outside a region when each component does. -/
theorem Represent.outside_prod [Represent α] [Represent β] {store : Store Unit}
    {vs : List Value} {a : α} {b : β} {region : Nat × Nat} :
    Represent.outside store vs (a, b) region ↔
      Represent.outside store (vs.take (Represent.width a)) a region ∧
        Represent.outside store (vs.drop (Represent.width a)) b region := by
  simp only [Represent.outside, Represent.blocks, List.mem_append]
  exact ⟨fun h => ⟨fun b hb => h b (.inl hb), fun b hb => h b (.inr hb)⟩,
    fun ⟨h1, h2⟩ b hb => hb.elim (h1 b) (h2 b)⟩

instance : Arrays (Array UInt64) where
  arrays xs := [xs]
  size := 1
  length_arrays _ := rfl
  values := by
    rintro _ _ _ xs ⟨p, rfl, -⟩
    exact ⟨[(p, xs)], rfl, rfl⟩
  owned := by
    intro heap store ts xs h
    obtain ⟨⟨p, _⟩, ts, rfl, rfl, hRest⟩ := List.map_eq_cons_iff.mp h
    obtain rfl := List.map_eq_nil_iff.mp hRest
    simp [Represent.owned]
  outside := by
    intro store ts xs region h
    obtain ⟨⟨p, _⟩, ts, rfl, rfl, hRest⟩ := List.map_eq_cons_iff.mp h
    obtain rfl := List.map_eq_nil_iff.mp hRest
    simp [Represent.outside_array]

instance [Represent β] [Arrays β] : Arrays (Array UInt64 × β) where
  arrays p := p.1 :: Arrays.arrays p.2
  size := Arrays.size β + 1
  length_arrays p := by simp [Arrays.length_arrays]
  values := by
    rintro _ _ _ ⟨xs, y⟩ ⟨_, second, rfl, ⟨p, rfl, -⟩, hSecond, -⟩
    obtain ⟨ts, hTs, rfl⟩ := Arrays.values hSecond
    exact ⟨(p, xs) :: ts, by simp [hTs], rfl⟩
  owned := by
    intro heap store ts ⟨xs, y⟩ h
    obtain ⟨⟨p, _⟩, ts, rfl, rfl, hTs⟩ := List.map_eq_cons_iff.mp h
    constructor
    · rintro ⟨_, second, hValues, ⟨q, rfl, hQ⟩, hSecond, hApart⟩
      simp only [pointers, List.map_cons, List.singleton_append, List.cons.injEq,
        Value.i64.injEq] at hValues
      obtain ⟨rfl, rfl⟩ := hValues
      obtain ⟨hOwned, hPairwise⟩ := (Arrays.owned hTs).mp hSecond
      exact ⟨List.forall_mem_cons.mpr ⟨hQ, hOwned⟩, List.pairwise_cons.mpr
        ⟨(Arrays.outside hTs).mp (hApart _ (List.mem_singleton_self _)), hPairwise⟩⟩
    · rintro ⟨hOwned, hPairwise⟩
      obtain ⟨hP, hOwned⟩ := List.forall_mem_cons.mp hOwned
      obtain ⟨hOut, hPairwise⟩ := List.pairwise_cons.mp hPairwise
      exact ⟨[.i64 p], pointers ts, rfl, ⟨p, rfl, hP⟩, (Arrays.owned hTs).mpr ⟨hOwned, hPairwise⟩,
        fun b hb => (List.mem_singleton.mp hb) ▸ (Arrays.outside hTs).mpr hOut⟩
  outside := by
    intro store ts ⟨xs, y⟩ region h
    obtain ⟨⟨p, _⟩, ts, rfl, rfl, hTs⟩ := List.map_eq_cons_iff.mp h
    rw [Represent.outside_prod]
    simp [Represent.width, Represent.outside_array, Arrays.outside hTs]

/-- `State.setAll` keeps the locals it does not set. -/
theorem State.setAll_get_ne {j : Nat} :
    ∀ {state next : State} {indices : List Nat} {values : List Value},
      j ∉ indices → state.setAll indices values = some next → next.get j = state.get j
  | _, _, [], [], _, h => by cases h; rfl
  | state, _, i :: is, v :: vs, hj, h => by
      cases hs : state.set? i v with
      | none => simp [State.setAll, hs] at h
      | some s =>
          simp only [State.setAll, hs, Option.bind_eq_bind, Option.bind_some] at h
          rw [State.setAll_get_ne (fun h' => hj (List.mem_cons_of_mem _ h')) h,
            State.get_set?_ne (fun h' => hj (List.mem_cons.mpr (.inl h'))) hs]
  | _, _, [], _ :: _, _, h => by simp [State.setAll] at h
  | _, _, _ :: _, [], _, h => by simp [State.setAll] at h

/-- After `State.setAll` of distinct locals, they hold the values. -/
theorem State.setAll_holds :
    ∀ {state next : State} {indices : List Nat} {values : List Value},
      indices.Nodup → state.setAll indices values = some next → next.Holds indices values
  | _, _, [], [], _, _ => .nil
  | state, _, i :: is, v :: vs, hNodup, h => by
      cases hs : state.set? i v with
      | none => simp [State.setAll, hs] at h
      | some s =>
          simp only [State.setAll, hs, Option.bind_eq_bind, Option.bind_some] at h
          exact .cons ((State.setAll_get_ne (List.nodup_cons.mp hNodup).1 h).trans
            (State.get_set?_same hs)) (State.setAll_holds (List.nodup_cons.mp hNodup).2 h)
  | _, _, [], _ :: _, _, h => by simp [State.setAll] at h
  | _, _, _ :: _, [], _, h => by simp [State.setAll] at h

theorem State.Frame.setAll {scratch : Nat} {writes : List Nat} {before : State} :
    ∀ {state next : State} {indices : List Nat} {values : List Value},
      State.Frame scratch writes before state → (∀ j ∈ indices, j ∈ writes ∨ scratch ≤ j) →
      state.setAll indices values = some next → State.Frame scratch writes before next
  | _, _, [], [], hFrame, _, h => by cases h; exact hFrame
  | state, _, i :: is, v :: vs, hFrame, hIn, h => by
      cases hs : state.set? i v with
      | none => simp [State.setAll, hs] at h
      | some s =>
          simp only [State.setAll, hs, Option.bind_eq_bind, Option.bind_some] at h
          exact State.Frame.setAll (hFrame.set? hs (hIn i List.mem_cons_self))
            (fun j hj => hIn j (List.mem_cons_of_mem _ hj)) h
  | _, _, [], _ :: _, _, _, h => by simp [State.setAll] at h
  | _, _, _ :: _, [], _, _, h => by simp [State.setAll] at h

theorem State.setAll_exists :
    ∀ {state : State} {indices : List Nat} {values : List Value},
      indices.length = values.length →
      (∀ j ∈ indices, j < state.params.length + state.locals.length) →
      ∃ next, state.setAll indices values = some next
  | state, [], [], _, _ => ⟨state, rfl⟩
  | state, i :: is, v :: vs, hLength, hIn => by
      obtain ⟨s, hs⟩ := State.exists_set? (state := state) v (hIn i List.mem_cons_self)
      have hFrame := (State.Frame.refl 0 [] state).set? hs (Or.inr (Nat.zero_le _))
      obtain ⟨next, h⟩ := State.setAll_exists (state := s) (indices := is) (values := vs)
        (by simpa using hLength) fun j hj => by
          rw [hFrame.params, hFrame.locals]; exact hIn j (List.mem_cons_of_mem _ hj)
      exact ⟨next, by simp [State.setAll, hs, h]⟩
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h

theorem State.Holds.reverse {state : State} {vars : List Nat} {values : List Value}
    (h : state.Holds vars.reverse values.reverse) : state.Holds vars values := by
  have aux : ∀ {l₁ : List Nat} {l₂ : List Value} {a₁ : List Nat} {a₂ : List Value},
      state.Holds l₁ l₂ → state.Holds a₁ a₂ → state.Holds (l₁.reverseAux a₁) (l₂.reverseAux a₂) := by
    intro l₁ l₂ a₁ a₂ h ha
    induction h generalizing a₁ a₂ with
    | nil => exact ha
    | cons hab _ ih => exact ih (.cons hab ha)
  simpa using aux h (a₁ := []) (a₂ := []) .nil

/-- A call to entry `idx`, which implements `g`, returns a nest of word arrays, and consumes
the temporaries `consumed`, leaves the arrays' pointers in the locals `results`; the arrays
take the place of the consumed temporaries.  The arrays the call reads lie apart from their
blocks. -/
theorem Live.callTuple [Represent α] [Represent β] [Arrays β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {consumed rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (consumed ++ rest))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hMoves : Represent.moves store vals x = consumed.map (·.1))
    (hReads : ∀ q ∈ Represent.reads vals x, ∀ t ∈ consumed, regionsDisjoint q (block store t.1))
    (hResults : results.length = Arrays.size β)
    (hRoom : ∀ r ∈ results, r < afterArgs.params.length + afterArgs.locals.length) :
    Triple m (.call idx args results) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ts, ts.map (·.2) = Arrays.arrays (g x) ∧
        Live heap0 initial moved heap' s (ts ++ rest) ∧
        afterArgs.setAll results.reverse (pointers ts).reverse = some st) := by
  have hMemC : ∀ t ∈ consumed, t ∈ consumed ++ rest := fun t ht => List.mem_append_left _ ht
  have hMemR : ∀ u ∈ rest, u ∈ consumed ++ rest := fun u hu => List.mem_append_right _ hu
  have hPair := hLive.pairwise
  rw [List.pairwise_append] at hPair
  obtain ⟨hPairC, hPairR, hCross⟩ := hPair
  have hKeep : ∀ region, (∀ t ∈ consumed, regionsDisjoint region (block store t.1)) →
      Apart store (Represent.moves store vals x) region := fun region h q hq => by
    rw [hMoves, List.mem_map] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    exact h t ht
  have hSep : Separate store (Represent.moves store vals x) (Represent.reads vals x) := by
    refine ⟨?_, fun q hq => hKeep q (hReads q hq)⟩
    rw [hMoves]
    simpa [List.pairwise_map] using hPairC
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed hSep
    (hLive.cap hCap) fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨ts, hTs, rfl⟩ := Arrays.values h
    have hLength : ts.length = Arrays.size β := by
      rw [← Arrays.length_arrays (g x), ← hTs, List.length_map]
    exact State.setAll_exists (by simp [hResults, hLength])
      fun r hr => hRoom r (List.mem_reverse.mp hr)
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeepB, hKeepO, hOutB, hOutO, hSet⟩
  obtain ⟨ts, hTs, rfl⟩ := Arrays.values hOwned'
  obtain ⟨hTsOwned, hTsPair⟩ := (Arrays.owned hTs).mp hOwned'
  have hApartRest : ∀ u ∈ rest, ∀ t ∈ consumed,
      regionsDisjoint (block store u.1) (block store t.1) :=
    fun u hu t ht => regionsDisjoint_symm (hCross t ht u hu)
  have hKeepT : ∀ u ∈ rest, heap'.Owned s u.1 u.2 ∧ block s u.1 = block store u.1 := fun u hu =>
    have h := hKeepO u.1 u.2 (hLive.tempsOwned u (hMemR u hu)) (hKeep _ (hApartRest u hu))
    ⟨h.1, block_eq h.2⟩
  have hOwnedKeep : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      Apart store (Represent.moves store vals x) (block store p) := fun p ws h hA => by
    refine hKeep _ fun t ht => ?_
    rw [block_eq (hLive.owned p ws h hA).2]
    exact hLive.apartO t (hMemC t ht) p ws h hA
  have hNewB : ∀ p ws, heap0.Borrowed initial p ws →
      Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      ∀ t ∈ ts, regionsDisjoint (p.toNat, 8 * (ws.size + 1)) (block s t.1) := fun p ws h hA =>
    (Arrays.outside hTs).mp (hOutB p ws (hLive.borrowed p ws h hA)
      (hKeep _ fun t ht => hLive.apartB t (hMemC t ht) p ws h hA))
  have hNewO : ∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
      ∀ t ∈ ts, regionsDisjoint (block initial p) (block s t.1) := fun p ws h hA => by
    have hD := (Arrays.outside hTs).mp (hOutO p ws (hLive.owned p ws h hA).1
      (hOwnedKeep p ws h hA))
    rw [block_eq (hLive.owned p ws h hA).2] at hD
    exact hD
  have hNewT : ∀ u ∈ rest, ∀ t ∈ ts, regionsDisjoint (block s t.1) (block s u.1) :=
    fun u hu t ht => by
      have hD := (Arrays.outside hTs).mp (hOutO u.1 u.2 (hLive.tempsOwned u (hMemR u hu))
        (hKeep _ (hApartRest u hu)))
      rw [(hKeepT u hu).2]
      exact regionsDisjoint_symm (hD t ht)
  refine ⟨heap', ts, hTs, ⟨hAt', hCaps'.trans hLive.caps,
    fun p ws h hA => hKeepB p ws (hLive.borrowed p ws h hA)
      (hKeep _ fun t ht => hLive.apartB t (hMemC t ht) p ws h hA),
    fun p ws h hA => ⟨(hKeepO p ws (hLive.owned p ws h hA).1 (hOwnedKeep p ws h hA)).1,
      (hKeepO p ws (hLive.owned p ws h hA).1 (hOwnedKeep p ws h hA)).2.trans
        (hLive.owned p ws h hA).2⟩,
    fun u hu => ?_, fun u hu p ws h hA => ?_, fun u hu p ws h hA => ?_, ?_⟩, hSet⟩
  · rcases List.mem_append.mp hu with hu | hu
    · exact hTsOwned u hu
    · exact (hKeepT u hu).1
  · rcases List.mem_append.mp hu with hu | hu
    · exact hNewB p ws h hA u hu
    · rw [(hKeepT u hu).2]; exact hLive.apartB u (hMemR u hu) p ws h hA
  · rcases List.mem_append.mp hu with hu | hu
    · exact hNewO p ws h hA u hu
    · rw [(hKeepT u hu).2]; exact hLive.apartO u (hMemR u hu) p ws h hA
  · refine List.pairwise_append.mpr ⟨hTsPair, ?_, fun t ht u hu => hNewT u hu t ht⟩
    refine List.Pairwise.imp_of_mem (fun {u v} hu hv h => ?_) hPairR
    rw [(hKeepT u hu).2, (hKeepT v hv).2]
    exact h

/-- `Live.callTuple` for a pair of word arrays, left in locals `r1` and `r2`. -/
theorem Live.callPair [Represent α] {idx : Nat} {g : α → Array UInt64 × Array UInt64}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch r1 r2 : Nat} {args : List ((type : ScalarType) × Expr type)}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {consumed rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (consumed ++ rest))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x)
    (hMoves : Represent.moves store vals x = consumed.map (·.1))
    (hReads : ∀ q ∈ Represent.reads vals x, ∀ t ∈ consumed, regionsDisjoint q (block store t.1))
    (hR1 : r1 < afterArgs.params.length + afterArgs.locals.length)
    (hR2 : r2 < afterArgs.params.length + afterArgs.locals.length) :
    Triple m (.call idx args [r1, r2]) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p1 p2, Live heap0 initial moved heap' s
        ((p1, (g x).1) :: (p2, (g x).2) :: rest) ∧
        st = (afterArgs.update r2 (.i64 p2)).update r1 (.i64 p1)) := by
  refine (Live.callTuple hImpl hImport hFunc (results := [r1, r2]) hParams hLive hCap hArgs
    hBorrowed hMoves hReads rfl fun r hr => ?_).mono (fun _ _ h => h) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hR1, hR2]
  rintro s st ⟨heap', ts, hTs, hL, hSet⟩
  obtain ⟨⟨p1, _⟩, ts, rfl, rfl, hTs1⟩ := List.map_eq_cons_iff.mp hTs
  obtain ⟨⟨p2, _⟩, ts, rfl, rfl, hTs2⟩ := List.map_eq_cons_iff.mp hTs1
  obtain rfl := List.map_eq_nil_iff.mp hTs2
  have hR1' : r1 < (afterArgs.update r2 (.i64 p2)).params.length +
      (afterArgs.update r2 (.i64 p2)).locals.length := by
    simp only [State.update_params_length, State.update_locals_length]; exact hR1
  refine ⟨heap', p1, p2, hL, ?_⟩
  simp only [pointers, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, State.setAll, State.set?_eq_update _ hR2,
    State.set?_eq_update _ hR1', Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet
  exact hSet.symm

/-- With the arrays of a nest `y` live, in order, a body that consumes the arrays at `moved`
ends with the facts that `Func.implements_moves` requires of a function returning `y`. -/
theorem Live.finish_tuple [Represent β] [Arrays β] {heap0 heap : Heap}
    {initial store : Store Unit} {ts : List (UInt64 × Array UInt64)} {y : β}
    (hTs : ts.map (·.2) = Arrays.arrays y) (hLive : Live heap0 initial moved heap store ts) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      Represent.owned heap' store (pointers ts) y ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        Represent.outside store (pointers ts) y (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        Represent.outside store (pointers ts) y (block initial p)) :=
  ⟨heap, hLive.at_, hLive.caps, hLive.borrowed, hLive.owned,
    (Arrays.owned hTs).mpr ⟨hLive.tempsOwned, hLive.pairwise⟩,
    fun p ws h hA => (Arrays.outside hTs).mpr fun t ht => hLive.apartB t ht p ws h hA,
    fun p ws h hA => (Arrays.outside hTs).mpr fun t ht => hLive.apartO t ht p ws h hA⟩

theorem Expr.evalResults_gets {mem : Mem} {scratch : Nat} {state : State} :
    ∀ {results : List Nat} {ts : List (UInt64 × Array UInt64)},
      state.Holds results (pointers ts) →
      Expr.evalResults mem scratch (results.map fun a => ⟨.u64, .get a⟩) state =
        some (pointers ts, state)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h =>
      Expr.evalResults_get (List.forall₂_cons.mp h).1
        (Expr.evalResults_gets (List.forall₂_cons.mp h).2)
  | [], _ :: _, h => by simp [State.Holds] at h
  | _ :: _, [], h => by simp [State.Holds] at h

/-- With the arrays of a nest `y` live, in order, and their pointers in the locals `results`,
a body that consumes the arrays at `moved` ends with the postcondition that
`Func.implements_moves` requires of a function whose results read those locals. -/
theorem Live.finish_results [Represent β] [Arrays β] {heap0 heap : Heap}
    {initial store : Store Unit} {ts : List (UInt64 × Array UInt64)} {y : β}
    {results : List Nat} {scratch : Nat} {state : State}
    (hTs : ts.map (·.2) = Arrays.arrays y) (hLive : Live heap0 initial moved heap store ts)
    (hResults : state.Holds results (pointers ts)) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      ∃ values next,
        Expr.evalResults store.mem scratch (results.map fun a => ⟨.u64, .get a⟩) state =
          some (values, next) ∧ Represent.owned heap' store values y ∧
        (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
          Represent.outside store values y (p.toNat, 8 * (ws.size + 1))) ∧
        (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
          Represent.outside store values y (block initial p)) := by
  obtain ⟨heap', hAt, hCaps, hB, hO, hOwned, hOB, hOO⟩ := Live.finish_tuple hTs hLive
  exact ⟨heap', hAt, hCaps, hB, hO, pointers ts, state, Expr.evalResults_gets hResults, hOwned,
    hOB, hOO⟩

/-- `Live.finish_tuple` for a pair of word arrays. -/
theorem Live.finish_pair {heap0 heap : Heap} {initial store : Store Unit} {p1 p2 : UInt64}
    {xs ys : Array UInt64} (hLive : Live heap0 initial moved heap store [(p1, xs), (p2, ys)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        heap'.Borrowed store p ws) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
      Represent.owned heap' store [.i64 p1, .i64 p2] (xs, ys) ∧
      (∀ p ws, heap0.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        Represent.outside store [.i64 p1, .i64 p2] (xs, ys) (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap0.Owned initial p ws → Apart initial moved (block initial p) →
        Represent.outside store [.i64 p1, .i64 p2] (xs, ys) (block initial p)) :=
  Live.finish_tuple (y := (xs, ys)) rfl hLive

end Project.IR
