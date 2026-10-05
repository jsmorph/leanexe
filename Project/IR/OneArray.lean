import Project.IR.RepeatWhile

/-!
Calls whose results are scalars followed by one array of records.  `OneArray` describes such a
result: an owned value is its scalars and the pointer of an owned array of words, whose block is
the value's only block.  `Live.callOne` runs a call with such a result, which may consume
temporaries, and `Live.finish_one` gives the postcondition of `Func.implements_moves` for a body
that returns one.
-/

namespace Project.IR

open Wasm Project.Pipeline Project.Runtime

variable {m : Module} {a : Bool} {moved : List UInt64}

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

instance : OneArray (Array UInt64) where
  scalars _ := []
  words xs := xs
  owned_iff _ _ _ _ := by simp [Represent.owned]
  blocks_eq _ _ _ := rfl

@[simp] theorem OneArray.scalars_words (xs : Array UInt64) : OneArray.scalars xs = [] := rfl

@[simp] theorem OneArray.words_words (xs : Array UInt64) : OneArray.words xs = xs := rfl

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
`results`, under the heap conditions `Pre` and `Post`; the array takes the consumed temporaries' place among the live temporaries.  The
regions the call reads lie apart from the consumed blocks. -/
theorem Live.callOneA [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
    {Pre : α → Heap → Store Unit → Prop} {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hImpl : ImplementsA a m idx g Pre Post) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {consumed rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (consumed ++ rest))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x) (hPre : Pre x heap store)
    (hMoves : Represent.moves store vals x = consumed.map (·.1))
    (hReads : ∀ q ∈ Represent.reads store vals x, ∀ t ∈ consumed,
      regionsDisjoint q (block store t.1))
    (hSet : ∀ p, ∃ next,
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 p]).reverse = some next) :
    TripleA a m (.call idx args results) scratch (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' ptr, Live heap0 initial moved heap' s
        ((ptr, OneArray.words (g x)) :: rest) ∧
        afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 ptr]).reverse =
          some st ∧ Post x heap store heap' s) := by
  have hPair := (List.pairwise_append.mp hLive.pairwise).1
  refine (Stmt.callImplementsA_spec hImpl hImport hFunc hParams hArgs hLive.at_ hPre hBorrowed
    ⟨by rw [hMoves, List.map_map]; exact List.pairwise_map.mpr hPair,
      fun r hr q hq => by
        rw [hMoves] at hq
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
        exact hReads r hr t ht⟩
    (hLive.cap hCap) fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨q, rfl, -⟩ := (OneArray.owned_iff heap' store' values (g x)).mp h
    exact hSet q
  rintro s st ⟨heap', values, hAt', hOwned', hCaps', hKeeps, hSet', hPost⟩
  obtain ⟨q, rfl, hQ⟩ := (OneArray.owned_iff heap' s values (g x)).mp hOwned'
  rw [OneArray.blocks_eq] at hKeeps
  refine ⟨heap', q, Live.step (consumed := consumed) (news := [(q, OneArray.words (g x))]) hLive
    hAt' hCaps' (hKeeps.mono (fun b hb => by rw [hMoves, List.map_map] at hb; exact hb)
      fun b hb => hb) (fun u hu => ?_) (List.pairwise_singleton _ _), hSet', hPost⟩
  rw [List.mem_singleton.mp hu]
  exact hQ

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
  refine (Live.callOneA (a := true) hImpl.toA hImport hFunc hParams hLive hCap hArgs hBorrowed
    trivial hMoves hReads hSet).mono (fun _ _ h => h) ?_
  rintro s st ⟨heap', ptr, hL, hSet', -⟩
  exact ⟨heap', ptr, hL, hSet'⟩

/-- `Live.callOneA` followed by `next`, which receives `Post`. -/
theorem Live.callOne_seqA [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
    {Pre : α → Heap → Store Unit → Prop} {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hImpl : ImplementsA a m idx g Pre Post) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {scratch : Nat} {args : List ((type : ScalarType) × Expr type)} {results : List Nat}
    (hParams : args.length = f.numParams) {heap0 heap : Heap} {initial store : Store Unit}
    {consumed rest : List (UInt64 × Array UInt64)}
    (hLive : Live heap0 initial moved heap store (consumed ++ rest))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    {x : α} {before afterArgs : State} {vals : List Value}
    (hArgs : Expr.evalResults store.mem scratch args before = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap store vals x) (hPre : Pre x heap store)
    (hMoves : Represent.moves store vals x = consumed.map (·.1))
    (hReads : ∀ q ∈ Represent.reads store vals x, ∀ t ∈ consumed,
      regionsDisjoint q (block store t.1))
    (hSet : ∀ p, ∃ next,
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 p]).reverse = some next)
    {next : Stmt} {Q : Store Unit → State → Prop}
    (hNext : ∀ heap' ptr s st, Live heap0 initial moved heap' s
      ((ptr, OneArray.words (g x)) :: rest) →
      afterArgs.setAll results.reverse (OneArray.scalars (g x) ++ [Value.i64 ptr]).reverse = some st →
      Post x heap store heap' s →
      TripleA a m next scratch (fun s' st' => s' = s ∧ st' = st) Q) :
    TripleA a m (.seq (.call idx args results) next) scratch (fun s st => s = store ∧ st = before)
      Q :=
  Stmt.seq_spec (Live.callOneA hImpl hImport hFunc hParams hLive hCap hArgs hBorrowed hPre hMoves
    hReads hSet)
    (TripleA.of_forall fun s st ⟨heap', ptr, hL, hst, hPost⟩ => hNext heap' ptr s st hL hst hPost)

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
  Live.callOne_seqA (a := true) hImpl.toA hImport hFunc hParams hLive hCap hArgs hBorrowed trivial
    hMoves hReads hSet fun heap' ptr s st hL hst _ => hNext heap' ptr s st hL hst

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
    (hThen : b = true → TripleA a m thenStmt scratch (fun s st => s = store ∧ st = state) Q)
    (hElse : b = false → TripleA a m elseStmt scratch (fun s st => s = store ∧ st = state) Q) :
    TripleA a m (.ite condition thenStmt elseStmt) scratch (fun s st => s = store ∧ st = state) Q :=
  (Stmt.ite_spec (PThen := fun s st => s = store ∧ st = state ∧ b = true)
    (PElse := fun s st => s = store ∧ st = state ∧ b = false)
    (TripleA.of_forall fun _ _ ⟨hs, hst, hb⟩ =>
      (hThen hb).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1.trans hs, h2.trans hst⟩) fun _ _ h => h)
    (TripleA.of_forall fun _ _ ⟨hs, hst, hb⟩ =>
      (hElse hb).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1.trans hs, h2.trans hst⟩) fun _ _ h => h)).mono
    (fun _ _ ⟨hs, hst⟩ => ⟨b, state, hs ▸ hst ▸ hCond, by cases b <;> simp [hs]⟩)
    fun _ _ h => h

/-- The loop of `LeanExe.repeatWhile` over a state of scalars and one array, the newest live
temporary: the final state's array takes its place, or the loop aborts.  The state lives in the
locals `states`, its scalars and then its array's pointer.  The call of `idx`, which implements
`g`, receives arguments that represent `F x`, consumes exactly the state's array, and reads
regions apart from it; `g (F x)` is `step x`. -/
theorem Live.repeatWhileOneA [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
    {Pre : α → Heap → Store Unit → Prop} {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hImpl : ImplementsA a m idx g Pre Post) (Hold : Heap → Store Unit → Prop)
    (hHold : ∀ (x : α) (heap heap' : Heap) (s s' : Store Unit), Hold heap s →
      Post x heap s heap' s' → Hold heap' s') {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {scratch limit counter : Nat} {states : List Nat}
    (hLocals : (limit :: counter :: states).Nodup)
    (hBelow : ∀ j ∈ limit :: counter :: states, j < scratch)
    {before : State} (hRoom : scratch ≤ before.params.length + before.locals.length)
    {heap0 heap : Heap} {initial store : Store Unit} {rest : List (UInt64 × Array UInt64)}
    {fuel : Expr .u64} {n : UInt64}
    (hFuel : ∃ after, fuel.eval store.mem scratch before = some (n, after))
    {condition : Expr .bool} (cond : β → Bool) (step : β → β) (F : β → α)
    (hStep : ∀ x, g (F x) = step x) {x0 : β} {p0 : UInt64}
    (hLive : Live heap0 initial moved heap store ((p0, OneArray.words x0) :: rest))
    (hHolds0 : before.Holds states (OneArray.scalars x0 ++ [Value.i64 p0])) (hHold0 : Hold heap store)
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hLen : ∀ x : β, (OneArray.scalars x).length + 1 = states.length)
    (hCond : ∀ (s : Store Unit) (st : State) (x : β) (p : UInt64),
      st.Holds states (OneArray.scalars x ++ [Value.i64 p]) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ after, condition.eval s.mem scratch st = some (cond x, after))
    (hArgs : ∀ (heap' : Heap) (s : Store Unit) (st : State) (x : β) (p : UInt64),
      st.Holds states (OneArray.scalars x ++ [Value.i64 p]) →
      Live heap0 initial moved heap' s ((p, OneArray.words x) :: rest) → Hold heap' s →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ avals after, Expr.evalResults s.mem scratch args st = some (avals, after) ∧
        Represent.borrowed heap' s avals (F x) ∧ Pre (F x) heap' s ∧
        Represent.moves s avals (F x) = [p] ∧
        ∀ q ∈ Represent.reads s avals (F x), regionsDisjoint q (block s p)) :
    TripleA a m (.repeatWhile states limit counter fuel condition idx args) scratch
      (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p, Live heap0 initial moved heap' s
        ((p, OneArray.words (LeanExe.repeatWhile n x0 cond step)) :: rest) ∧
        st.Holds states (OneArray.scalars (LeanExe.repeatWhile n x0 cond step) ++ [Value.i64 p]) ∧
        State.Frame scratch (limit :: counter :: states) before st ∧ Hold heap' s) := by
  have hBlocks : ∀ s (x : β) (p : UInt64),
      Represent.blocks s (OneArray.scalars x ++ [Value.i64 p]) x = [block s p] :=
    fun s x p => OneArray.blocks_eq s x p
  -- The live facts at any state of the loop, from the loop's facts.
  have hLiveAt : ∀ (heap' : Heap) (s : Store Unit) (x : β) (p : UInt64), heap'.At s →
      s.memoryCaps = store.memoryCaps → heap'.Owned s p (OneArray.words x) →
      heap.Keeps store [block store p0] heap' s [block s p] →
      Live heap0 initial moved heap' s ((p, OneArray.words x) :: rest) :=
    fun heap' s x p hAt hCaps hOwned hKeeps =>
      Live.step (consumed := [(p0, OneArray.words x0)]) (news := [(p, OneArray.words x)])
        hLive hAt hCaps hKeeps (fun t ht => by rw [List.mem_singleton.mp ht]; exact hOwned)
        (List.pairwise_singleton _ _)
  refine (Stmt.repeatWhile_specA (heap0 := heap) (initial := store) (start := store)
    (gone := [block store p0]) (x0 := x0) hImpl Hold hHold hImport hFunc hParams hLocals
    hBelow hRoom hFuel cond step F hStep ?_ ?_ hHolds0 (hLive.cap hCap) ?_ ?_).mono
      (fun _ _ h => h) ?_
  · intro heap' s vals y hOwned
    obtain ⟨p, rfl, -⟩ := (OneArray.owned_iff heap' s vals y).mp hOwned
    have := hHolds0.length_eq
    simp only [List.length_append, List.length_singleton] at this ⊢
    rw [hLen y]
  · refine ⟨heap, hLive.at_, rfl, (OneArray.owned_iff heap store _ x0).mpr
      ⟨p0, rfl, hLive.tempsOwned _ (List.mem_cons_self ..)⟩, ?_⟩
    rw [hBlocks]
    exact ⟨fun r hr _ hApart => ⟨fun _ _ _ => rfl, hr, hApart⟩, hHold0⟩
  · intro s st x vals heap' hHolds hOwned hFrame
    obtain ⟨p, rfl, -⟩ := (OneArray.owned_iff heap' s vals x).mp hOwned
    exact hCond s st x p hHolds hFrame
  · intro s st x vals heap' hHolds hAt hCapsX hOwned hHoldX hKeeps hFrame
    obtain ⟨p, rfl, hP⟩ := (OneArray.owned_iff heap' s vals x).mp hOwned
    rw [hBlocks] at hKeeps ⊢
    obtain ⟨avals, after, hEval, hBorrowed, hPre, hMoves, hReads⟩ :=
      hArgs heap' s st x p hHolds (hLiveAt heap' s x p hAt hCapsX hP hKeeps) hHoldX hFrame
    refine ⟨avals, after, hEval, hBorrowed, hPre, ⟨?_, fun r hr q hq => ?_⟩, fun b hb => ?_⟩
    · rw [hMoves]; exact List.pairwise_singleton _ _
    · rw [hMoves, List.mem_singleton] at hq
      subst hq
      exact hReads r hr
    · rw [hMoves] at hb
      simpa using hb
  · rintro s st ⟨heap', vals, hAt, hCaps, hOwned, hKeeps, hHolds, hFrame, hHoldF⟩
    obtain ⟨p, rfl, hP⟩ := (OneArray.owned_iff heap' s vals _).mp hOwned
    rw [hBlocks] at hKeeps
    exact ⟨heap', p, hLiveAt heap' s _ p hAt hCaps hP hKeeps,
      hHolds, hFrame, hHoldF⟩

/-- The loop of `LeanExe.repeatWhile` over a state of scalars and one array, the newest live
temporary: the final state's array takes its place, or the loop aborts.  The state lives in the
locals `states`, its scalars and then its array's pointer.  The call of `idx`, which implements
`g`, receives arguments that represent `F x`, consumes exactly the state's array, and reads
regions apart from it; `g (F x)` is `step x`. -/
theorem Live.repeatWhileOne [Represent α] [Represent β] [OneArray β] {idx : Nat} {g : α → β}
    (hImpl : Implements m idx g) {f : Wasm.Function}
    (hImport : m.imports[idx]? = none) (hFunc : m.funcs[idx - m.imports.length]? = some f)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams)
    {scratch limit counter : Nat} {states : List Nat}
    (hLocals : (limit :: counter :: states).Nodup)
    (hBelow : ∀ j ∈ limit :: counter :: states, j < scratch)
    {before : State} (hRoom : scratch ≤ before.params.length + before.locals.length)
    {heap0 heap : Heap} {initial store : Store Unit} {rest : List (UInt64 × Array UInt64)}
    {fuel : Expr .u64} {n : UInt64}
    (hFuel : ∃ after, fuel.eval store.mem scratch before = some (n, after))
    {condition : Expr .bool} (cond : β → Bool) (step : β → β) (F : β → α)
    (hStep : ∀ x, g (F x) = step x) {x0 : β} {p0 : UInt64}
    (hLive : Live heap0 initial moved heap store ((p0, OneArray.words x0) :: rest))
    (hHolds0 : before.Holds states (OneArray.scalars x0 ++ [Value.i64 p0]))
    (hCap : initial.memoryCap m 0 ≤ 65535)
    (hLen : ∀ x : β, (OneArray.scalars x).length + 1 = states.length)
    (hCond : ∀ (s : Store Unit) (st : State) (x : β) (p : UInt64),
      st.Holds states (OneArray.scalars x ++ [Value.i64 p]) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ after, condition.eval s.mem scratch st = some (cond x, after))
    (hArgs : ∀ (heap' : Heap) (s : Store Unit) (st : State) (x : β) (p : UInt64),
      st.Holds states (OneArray.scalars x ++ [Value.i64 p]) →
      Live heap0 initial moved heap' s ((p, OneArray.words x) :: rest) →
      State.Frame scratch (limit :: counter :: states) before st →
      ∃ avals after, Expr.evalResults s.mem scratch args st = some (avals, after) ∧
        Represent.borrowed heap' s avals (F x) ∧ Represent.moves s avals (F x) = [p] ∧
        ∀ q ∈ Represent.reads s avals (F x), regionsDisjoint q (block s p)) :
    Triple m (.repeatWhile states limit counter fuel condition idx args) scratch
      (fun s st => s = store ∧ st = before)
      (fun s st => ∃ heap' p, Live heap0 initial moved heap' s
        ((p, OneArray.words (LeanExe.repeatWhile n x0 cond step)) :: rest) ∧
        st.Holds states (OneArray.scalars (LeanExe.repeatWhile n x0 cond step) ++ [Value.i64 p]) ∧
        State.Frame scratch (limit :: counter :: states) before st) := by
  refine (Live.repeatWhileOneA (a := true) hImpl.toA (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) hImport hFunc hParams hLocals hBelow hRoom hFuel cond step F
    hStep hLive hHolds0 trivial hCap hLen hCond
    (fun heap' s st x p hHolds hL _ hFrame => ?_)).mono (fun _ _ h => h) ?_
  · obtain ⟨avals, after, hEval, hBorrowed, hMoves, hReads⟩ := hArgs heap' s st x p hHolds hL hFrame
    exact ⟨avals, after, hEval, hBorrowed, trivial, hMoves, hReads⟩
  · rintro s st ⟨heap', p, hL, hHolds, hFrame, -⟩
    exact ⟨heap', p, hL, hHolds, hFrame⟩

end Project.IR
