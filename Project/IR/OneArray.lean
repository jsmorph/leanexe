import Project.IR.Live

/-!
Calls whose results are scalars followed by one array of records.  `OneArray` describes such a
result: an owned value is its scalars and the pointer of an owned array of words, whose block is
the value's only block.  `Live.callOne` runs a call with such a result, which may consume
temporaries, and `Live.finish_one` gives the postcondition of `Func.implements_moves` for a body
that returns one.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module} {moved : List UInt64}

/-- An array of records that the caller hands over: the call receives its words as owned and
consumes its block. -/
instance [Flat α γ] [Scalar γ] : Represent (Moved (Array α)) where
  width _ := 1
  borrowed heap store vs xs := Represent.borrowed heap store vs (Moved.mk (flatWords xs.val))
  owned heap store vs xs := Represent.owned heap store vs (Moved.mk (flatWords xs.val))
  blocks store vs xs := Represent.blocks store vs (Moved.mk (flatWords xs.val))
  reads _ _ _ := []
  moves store vs xs := Represent.moves store vs (Moved.mk (flatWords xs.val))

/-- A value represented by scalars followed by the pointer of one array of words.  An owned
value is those scalars and an owned array, whose block is the value's only block. -/
class OneArray (β : Type) [Represent β] where
  scalars : β → List Value
  words : β → Array UInt64
  owned_iff : ∀ heap store vs (y : β), Represent.owned heap store vs y ↔
    ∃ p, vs = scalars y ++ [.i64 p] ∧ heap.Owned store p (words y)
  blocks_eq : ∀ store (y : β) p, Represent.blocks store (scalars y ++ [.i64 p]) y = [block store p]

instance [Flat α γ] [Scalar γ] : OneArray (Array α) where
  scalars _ := []
  words := flatWords
  owned_iff _ _ _ _ := by simp [Represent.owned]
  blocks_eq _ _ _ := rfl

instance [Scalar σ] [Represent β] [OneArray β] : OneArray (σ × β) where
  scalars p := Scalar.values p.1 ++ OneArray.scalars p.2
  words p := OneArray.words p.2
  owned_iff heap store vs y := by
    constructor
    · rintro ⟨first, second, rfl, rfl, hSecond, -⟩
      obtain ⟨p, rfl, hp⟩ := (OneArray.owned_iff heap store second y.2).mp hSecond
      exact ⟨p, by simp, hp⟩
    · rintro ⟨p, rfl, hp⟩
      exact ⟨Scalar.values y.1, OneArray.scalars y.2 ++ [.i64 p], by simp, rfl,
        (OneArray.owned_iff heap store _ y.2).mpr ⟨p, rfl, hp⟩, fun _ hb => nomatch hb⟩
  blocks_eq store y p := by
    show Represent.blocks store _ y.1 ++ Represent.blocks store _ y.2 = _
    rw [show Represent.width y.1 = (Scalar.values y.1).length from rfl, List.append_assoc,
      List.take_left, List.drop_left, OneArray.blocks_eq]
    rfl

@[simp] theorem OneArray.scalars_array [Flat α γ] [Scalar γ] (xs : Array α) :
    OneArray.scalars xs = [] := rfl

@[simp] theorem OneArray.words_array [Flat α γ] [Scalar γ] (xs : Array α) :
    OneArray.words xs = flatWords xs := rfl

@[simp] theorem OneArray.scalars_pair [Scalar σ] [Represent β] [OneArray β] (y : σ × β) :
    OneArray.scalars y = Scalar.values y.1 ++ OneArray.scalars y.2 := rfl

@[simp] theorem OneArray.words_pair [Scalar σ] [Represent β] [OneArray β] (y : σ × β) :
    OneArray.words y = OneArray.words y.2 := rfl

/-- A call to entry `idx`, which implements `g` with a result of scalars and one array and
consumes the temporaries `consumed`, leaves the scalars and the array's pointer in the locals
`results`; the array takes the consumed temporaries' place among the live temporaries.  The
regions the call reads lie apart from the consumed blocks. -/
theorem Live.callOne [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
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
    (hReads : ∀ q ∈ Represent.reads store vals x, ∀ t ∈ consumed,
      regionsDisjoint q (block store t.1))
    (hSet : ∀ p, ∃ next,
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 p]).reverse = some next) :
    Triple m (.call idx args results) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial moved heap' s
        ((ptr, OneArray.words (g x)) :: rest) ∧
        afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 ptr]).reverse =
          some st) := by
  have hPair := (List.pairwise_append.mp hLive.pairwise).1
  refine (Stmt.callImplements_spec hImpl hImport hFunc hParams hArgs hLive.at_ hBorrowed
    ⟨by rw [hMoves, List.map_map]; exact List.pairwise_map.mpr hPair,
      fun r hr q hq => by
        rw [hMoves] at hq
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
        exact hReads r hr t ht⟩
    (hLive.cap hCap) fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := (OneArray.owned_iff heap' store' values (g x)).mp h
    exact hSet q
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeeps, hSet'⟩
  obtain ⟨q, rfl, hQ⟩ := (OneArray.owned_iff heap' s values (g x)).mp hOwned'
  rw [OneArray.blocks_eq] at hKeeps
  refine ⟨heap', q, Live.step (consumed := consumed) (news := [(q, OneArray.words (g x))]) hLive
    hAt' hCaps' (hKeeps.mono (fun b hb => by rw [hMoves, List.map_map] at hb; exact hb)
      fun b hb => hb) (fun u hu => ?_) (List.pairwise_singleton _ _), hSet'⟩
  rw [List.mem_singleton.mp hu]
  exact hQ

/-- `Live.callOne` followed by `next`. -/
theorem Live.callOne_seq [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
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
    (hReads : ∀ q ∈ Represent.reads store vals x, ∀ t ∈ consumed,
      regionsDisjoint q (block store t.1))
    (hSet : ∀ p, ∃ next,
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 p]).reverse = some next)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' ptr s st, Live heap0 initial moved heap' s
      ((ptr, OneArray.words (g x)) :: rest) →
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 ptr]).reverse = some st →
      Triple m next scratch (fun s' st' => s' = s ∧ st' = st) Q) :
    Triple m (.seq (.call idx args results) next) scratch (fun s st => s = store ∧ st = before)
      Q :=
  Stmt.seq_spec (Live.callOne hImpl hImport hFunc hParams hLive hCap hArgs hBorrowed hMoves
    hReads hSet)
    (Triple.of_forall fun s st ⟨heap', ptr, hL, hst⟩ => hNext heap' ptr s st hL hst)

/-- With one live array, a body that consumes the objects at `moved` ends with the facts that
`Func.implements_moves` requires of a function returning `y`, when the result expressions give
the scalars of `y` and the array's pointer. -/
theorem Live.finish_one [Represent β] [OneArray β] {heap0 heap : Heap}
    {initial store : Store Unit} {ptr : UInt64} {y : β}
    (hLive : Live heap0 initial moved heap store [(ptr, OneArray.words y)]) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      Represent.owned heap' store (OneArray.scalars y ++ [.i64 ptr]) y ∧
      heap0.Keeps initial (moved.map (block initial)) heap' store
        (Represent.blocks store (OneArray.scalars y ++ [.i64 ptr]) y) := by
  refine ⟨heap, hLive.at_, hLive.caps,
    (OneArray.owned_iff _ _ _ y).mpr ⟨ptr, rfl, hLive.tempsOwned _ (List.mem_singleton_self _)⟩,
    ?_⟩
  rw [OneArray.blocks_eq]
  exact hLive.keeps.mono (fun _ h => h) fun _ hb => hb

/-- `Live.finish_one` with the result expressions: they evaluate to the scalars of `y` and the
pointer of its array. -/
theorem Live.finish_results_one [Represent β] [OneArray β] {heap0 heap : Heap}
    {initial store : Store Unit} {ptr : UInt64} {y : β} {scratch : Nat}
    {results : List ((type : ScalarType) × Expr type)} {state : State}
    (hLive : Live heap0 initial moved heap store [(ptr, OneArray.words y)])
    (hEval : ∃ next, Expr.evalResults store.mem scratch results state =
      some (OneArray.scalars y ++ [Value.i64 ptr], next)) :
    ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      ∃ values next, Expr.evalResults store.mem scratch results state = some (values, next) ∧
        Represent.owned heap' store values y ∧
        heap0.Keeps initial (moved.map (block initial)) heap' store
          (Represent.blocks store values y) := by
  obtain ⟨heap', hAt, hCaps, hOwned, hKeeps⟩ := Live.finish_one hLive
  obtain ⟨next, hEval⟩ := hEval
  exact ⟨heap', hAt, hCaps, _, next, hEval, hOwned, hKeeps⟩

/-- A conditional whose test leaves the state: each branch runs from that state, under the
test's outcome. -/
theorem Stmt.ite_test {condition : Expr .bool} {thenStmt elseStmt : Stmt} {scratch : Nat}
    {store : Store Unit} {state : State} {b : Bool} {Q : Store Unit → State → Prop}
    (hCond : condition.eval store.mem scratch state = some (b, state))
    (hThen : b = true → Triple m thenStmt scratch (fun s st => s = store ∧ st = state) Q)
    (hElse : b = false → Triple m elseStmt scratch (fun s st => s = store ∧ st = state) Q) :
    Triple m (.ite condition thenStmt elseStmt) scratch (fun s st => s = store ∧ st = state) Q :=
  (Stmt.ite_spec (PThen := fun s st => s = store ∧ st = state ∧ b = true)
    (PElse := fun s st => s = store ∧ st = state ∧ b = false)
    (Triple.of_forall fun _ _ ⟨hs, hst, hb⟩ =>
      (hThen hb).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1.trans hs, h2.trans hst⟩) fun _ _ h => h)
    (Triple.of_forall fun _ _ ⟨hs, hst, hb⟩ =>
      (hElse hb).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1.trans hs, h2.trans hst⟩) fun _ _ h => h)).mono
    (fun _ _ ⟨hs, hst⟩ => ⟨b, state, hs ▸ hst ▸ hCond, by cases b <;> simp [hs]⟩)
    fun _ _ h => h

end Project.IR
