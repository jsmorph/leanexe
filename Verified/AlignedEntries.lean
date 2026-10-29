import Verified.AlignedCorrect
import LeanExe.Pipeline.ImplementsAligned

/-!
The alignment statement for the functions of a compiled program.  `AlignedInput` of a call's
arguments gives the alignment that `FunAligned` takes: an aligned heap, and, by
`Env.AlignedVals.of_moves_reads`, aligned values, since an owned value's blocks start at its
pointers minus 48 and a borrowed value's regions are its reads.  `FunSpecX.implementsAligned` is
`ImplementsAligned` of a function whose code takes no call depth, at its call index, and
`entry_aligned` is `ImplementsAligned` of the exported entry of a function whose code takes it,
each with the parameters of the `ImplementsA` theorem that `verified_compile` emits there.  The
final heap and the result's blocks are aligned by `FunAligned`'s postcondition, `FunPost true`.
`wrapper_aligned` is `ImplementsTablesAligned`, the same statement for a wrapper, whose tables
need no premise because each starts at a multiple of 8.  `ImplementsAligned.lean` and
`ImplementsTablesAligned.lean` carry the theorems to the instances of Lean's types, as
`ImplementsA.lean` carries `ImplementsA`.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A context whose owned values' pointers and capacities and whose borrowed values' regions
start at multiples of 8 is aligned. -/
theorem Env.AlignedVals.of_moves_reads {store : Store Unit} :
    ∀ {Γ : List Ty} (modes : Nat → Mode) (ws : List Value) (env : Env Γ),
      (∀ p ∈ Env.moves store modes ws env, p.toNat % 8 = 0 ∧ capacityAt store p % 8 = 0) →
      (∀ r ∈ Env.reads store modes ws env, r.1 % 8 = 0) →
      Env.AlignedVals store modes ws env
  | _, _, _, .nil, _, _ => trivial
  | _, modes, ws, .cons (t := t) v env, hMoves, hReads => by
    refine ⟨fun r hr => ?_, Env.AlignedVals.of_moves_reads (fun i => modes (i + 1))
      (ws.drop t.width) env
      (fun p hp => hMoves p (by simp only [Env.moves]; exact List.mem_append_right _ hp))
      (fun r hr => hReads r (by simp only [Env.reads]; exact List.mem_append_right _ hr))⟩
    cases hm : modes 0 with
    | borrowed =>
      have hr' : r ∈ t.reads store (ws.take t.width) v := by simpa [Ty.regions, hm] using hr
      exact ⟨hReads r (by simp only [Env.reads, hm]; exact List.mem_append_left _ hr'), nofun⟩
    | owned =>
      have hr' : r ∈ (t.pointers store (ws.take t.width) v).map (block store) := by
        simpa [Ty.regions, hm, Ty.blocks_pointers] using hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
      obtain ⟨hq8, hc8⟩ := hMoves q (by simp only [Env.moves, hm]; exact List.mem_append_left _ hq)
      simp only [block]
      exact ⟨by omega, fun _ => by omega⟩

/-- `AlignedInput` of a call's arguments gives the alignment premises of `FunAligned`. -/
theorem AlignedInput.env {ps : List Ty} {ms : List Mode} {heap : Heap} {store : Store Unit}
    {ws : List Value} {x : Env ps}
    (h : @AlignedInput _ (Env.represent ps ms) heap store ws x) :
    heap.Aligned ∧ Env.AlignedVals store (paramMode ps ms) ws x :=
  ⟨h.1, Env.AlignedVals.of_moves_reads _ ws x h.2.1 h.2.2⟩

/-- `ImplementsAligned` of a function whose code takes no call depth, at its call index, with the
parameters of the `ImplementsA` that `ImplementsB.implementsA` gives from `FunSpec.implementsB`. -/
theorem FunSpecX.implementsAligned {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} {base : Nat}
    (hF : FunSpecX true m g idx F pf rf A Fi D ⟨base, []⟩) (hd : g.depth = false) :
    @ImplementsAligned _ _ (Env.represent g.params g.modes) (Ty.represent g.result) g.aborts m idx F
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap ws x hAt _ hRep hSep hCap hIn
  obtain ⟨hHeap, hVals⟩ := AlignedInput.env hIn
  have hRun := hF.2 rfl host hAt (Bytes.LiteralPool.Input.empty _ _ _ _ _) hRep hSep hCap hHeap
    hVals (d := 0) (fun h => by rw [hd] at h; exact nomatch h) []
  have hStack : ws.reverse ++ ((if g.depth then [Value.i64 0] else []) ++ []) = ws.reverse := by
    simp [hd]
  rw [hStack] at hRun
  refine ⟨hRun.2, (hRun.1.of_imp fun h => ?_).mono
    fun final values ⟨out, hv, heap', hAt', hOwned, hCaps, hRegions, _, hAl⟩ => ?_⟩
  · simp only [hd, Bool.false_and, Bool.false_or, Bool.or_false, Bool.and_eq_true] at h
    exact h.1
  · obtain ⟨hHeapAl, hV⟩ := hAl rfl
    rw [List.append_nil] at hv
    subst hv
    exact ⟨heap', hAt', hOwned, hCaps, hRegions, trivial, hHeapAl,
      fun b hb => ⟨(hV b hb).1, (hV b hb).2 rfl⟩⟩

/-- `wp_localGets` under the flag. -/
theorem wpX_localGets {strict : Bool} {m : Module} {host : HostEnv Unit} {Q : Assertion Unit}
    {store : Store Unit} {rest : Program} : (vs : List Value) → (k : Nat) → (s : Locals) →
    (∀ i (hi : i < vs.length), s.get (k + i) = some vs[i]) →
    wpX strict m rest Q store { s with values := vs.reverse ++ s.values } host →
    wpX strict m ((List.range' k vs.length).map Instruction.localGet ++ rest) Q store s host
  | [], _, s, _, h => by
    simp only [List.reverse_nil, List.nil_append, List.length_nil, List.range'_zero,
      List.map_nil] at h ⊢
    exact h
  | v :: vs, k, s, hget, h => by
    have h0 : s.get k = some v := hget 0 (by simp)
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.cons_append,
      wpX_localGet_cons, h0]
    refine wpX_localGets vs (k + 1) _ (fun i hi => ?_) ?_
    · rw [Locals.get_values, show k + 1 + i = k + (i + 1) by omega]
      exact hget (i + 1) (by simp; omega)
    · simpa using h

/-- `ImplementsAligned` of the exported entry of a function whose code takes the call depth:
the entry pushes depth 0 and the arguments and calls the function, whose run `FunAligned`
aligns. -/
theorem entry_aligned {m : Module} (hm : Runtime m) {g : Sig} {idx typeIdx e : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} {base : Nat}
    (hF : FunAligned m g idx F pf rf A Fi D ⟨base, []⟩) (hd : g.depth = true) (hD : D 0)
    (he : m.funcs[e]? = some (entryFunction g.params g.result idx typeIdx)) :
    @ImplementsAligned _ _ (Env.represent g.params g.modes) (Ty.represent g.result) true m e F
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) := by
  intro host store heap ws args hAt _ hRep hSep hCap hIn
  obtain ⟨hHeap, hVals⟩ := AlignedInput.env hIn
  have hLength : ws.length = widthSum g.params := hRep.length
  have hNum : (entryFunction g.params g.result idx typeIdx).numParams = widthSum g.params := by
    simp only [entryFunction, Function.numParams, flatMap_types_length]
  have hRun := (hF host hAt (Bytes.LiteralPool.Input.empty _ _ _ _ _) hRep hSep hCap hHeap hVals
    (d := 0) (fun _ => hD) []).of_imp (a' := true) fun _ => rfl
  simp only [hd, ↓reduceIte] at hRun
  refine (fun (h : RunsA true host m e store ws.reverse _) => ⟨h.2, h.1⟩) ?_
  apply RunsX.of_wpX_entry_for (strict := true) (f := entryFunction g.params g.result idx typeIdx)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
  rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
  simp only [entryFunction, List.cons_append, List.nil_append,
    wpX_constI64_cons, List.range_eq_range', flatMap_types_length, ← hLength]
  refine wpX_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
  refine wpX_call_runs (strict := true) hRun (TrapOK.of_msg fun _ => Iff.rfl)
    fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, _, hAl⟩ := hPost
  rw [wpX_nil]
  have hOut : out.length = g.result.width := by
    have := hOwned.length; rwa [List.length_reverse] at this
  have hTake : out.take g.result.types.length = out :=
    List.take_of_length_le (by rw [Ty.types_length, hOut])
  have hDrop : ws.reverse.drop (List.flatMap Ty.types g.params).length = [] :=
    List.drop_of_length_le (by rw [List.length_reverse, flatMap_types_length, hLength])
  dsimp only [Function.numParams]
  rw [List.append_nil, hTake, hDrop, List.append_nil]
  obtain ⟨hHeapAl, hV⟩ := hAl rfl
  exact ⟨heap', hAt', hOwned, hCaps, hRegions, trivial, hHeapAl,
    fun b hb => ⟨(hV b hb).1, (hV b hb).2 rfl⟩⟩

/-- A function's alignment theorem in the form of Lean's instances, as `ImplementsA.lean`: the
arguments' instances agree on what the call consumes and reads, and the result's on its blocks. -/
theorem ImplementsAligned.lean {ps : List Ty} {ms : List Mode} {r : Ty} {aborts : Bool}
    {m : Module} {entry : Nat} {f : Env ps → r.denote} {Pre : Env ps → Heap → Store Unit → Prop}
    {Post : Env ps → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : @ImplementsAligned _ _ (Env.represent ps ms) (Ty.represent r) aborts m entry f Pre Post) :
    @ImplementsAligned _ _ (argsInst ps ms) r.leanInst aborts m entry
      (fun y => f (Env.ofArgs ps ms y)) (fun y => Pre (Env.ofArgs ps ms y))
      (fun y => Post (Env.ofArgs ps ms y)) := by
  intro env store heap vs y hAt hPre hY hSep hCap hIn
  have hY' := (argsInst_borrowed ps ms).mp hY
  have hl := hY'.length
  have hSep' := hSep
  rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hSep'
  have hIn' : @AlignedInput _ (Env.represent ps ms) heap store vs (Env.ofArgs ps ms y) := by
    obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [argsInst_moves ps ms hl]; exact hp
    · rw [argsInst_reads ps ms hl]; exact hr
  obtain ⟨hA, hRun⟩ := h env store heap vs (Env.ofArgs ps ms y) hAt hPre hY' hSep' hCap hIn'
  refine ⟨hA, hRun.mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost, hHeapAl,
    hOut⟩ => ⟨heap', hAt', r.leanInst_owned.mpr hOwned, hCaps, fun rg hr hpos hAp => ?_, hPost,
    hHeapAl, fun b hb => hOut b (by rw [r.leanInst_blocks] at hb; exact hb)⟩⟩
  rw [argsInst_moves ps ms hl] at hAp
  obtain ⟨hb, hreg, hout⟩ := hRegions rg hr hpos hAp
  refine ⟨hb, hreg, ?_⟩
  simp only [Represent.outside, r.leanInst_blocks]
  exact hout

/-- The wrapper counterpart of `ImplementsAligned`: `ImplementsTables` from an aligned input, with
the alignment of every run's accesses, of the final heap, and of the result's blocks.  The tables
need no premise of their own, since the compiler places each at a multiple of 8
(`tableAddr_mod8`). -/
def ImplementsTablesAligned {α β : Type} [Represent α] [Represent β] (aborts : Bool)
    (m : Module) (entry : Nat) (f : α → β) (tables : List (UInt64 × Array UInt64))
    (Pre : α → Heap → Store Unit → Prop)
    (Post : α → Heap → Store Unit → Heap → Store Unit → Prop) : Prop :=
  ∀ (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params : List Value) (x : α),
    heap.At store → Pre x heap store →
    (∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
      Apart store (Represent.moves store params x) (t.1.toNat, 8 * (t.2.size + 1))) →
    Represent.borrowed heap store params x →
    Separate store (Represent.moves store params x) (Represent.reads store params x) →
    store.memoryCap m 0 ≤ 65535 → AlignedInput heap store params x →
    (∃ N, ∀ fuel ≥ N, AlignedRun fuel m entry store params.reverse env) ∧
    Runs aborts env m entry store params.reverse fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ Represent.owned heap' final values.reverse (f x) ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → Apart store (Represent.moves store params x) r →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ Represent.outside final values.reverse (f x) r) ∧
        Post x heap store heap' final ∧ heap'.Aligned ∧ AlignedOutput final values.reverse (f x)

/-- Each table starts at a multiple of 8. -/
theorem tableAddr_mod8 (tables : List (Array UInt64)) (k : Nat) :
    (tableAddr tables k).toNat % 8 = 0 := by
  unfold tableAddr
  rw [UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- `wp_constI64s` under the flag. -/
theorem wpX_constI64s {strict : Bool} {m : Module} {host : HostEnv Unit} {Q : Assertion Unit}
    {store : Store Unit} {rest : Program} : (addrs : List UInt64) → (s : Locals) →
    wpX strict m rest Q store { s with values := (addrs.map Value.i64).reverse ++ s.values } host →
    wpX strict m (addrs.map Instruction.constI64 ++ rest) Q store s host
  | [], s, h => by simpa using h
  | a :: as, s, h => by
    simp only [List.map_cons, List.cons_append, wpX_constI64_cons]
    refine wpX_constI64s as _ ?_
    simpa using h

/-- `ImplementsTablesAligned` of a wrapper, from the aligned runs of its callee: the wrapper
pushes the tables' addresses and its arguments and calls the callee, whose context, the tables
and the arguments, is aligned. -/
theorem wrapper_aligned {m : Module} (hm : Runtime m) {S : List Sig}
    {tables : List (Array UInt64)} (w : Wrapper S tables.length) {funs : Funs S}
    {flags : Flags S} {bounds : Nat → Bounds S} {fits : Nat → Fits S}
    {base : Nat} (hCalls : CallsX true m funs flags bounds fits ⟨base, []⟩) {e : Nat}
    (he : m.funcs[e]? = some (wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)) :
    @ImplementsTablesAligned _ _ (Env.represent w.params (w.modes.drop w.tables.length))
      (Ty.represent w.result) (w.aborts || w.depth) m e
      (fun env => funs.get w.callee (Env.withTables tables w.tables env))
      (w.tables.map fun k => (tableAddr tables k.val, tables[k])) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) := by
  intro host store heap ws args hAt _ hTables hRep hSep hCap hIn
  have hShift : (fun i => paramMode (List.replicate w.tables.length (.array .word) ++ w.params)
      w.modes (i + w.tables.length)) = paramMode w.params (w.modes.drop w.tables.length) :=
    funext fun i => paramMode_tables _ _ _ i
  have hB : ∀ i < w.tables.length,
      paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes i =
        .borrowed :=
    fun i hi => paramMode_tables_lt _ _ _ w.borrowed i hi
  have hT : ∀ k ∈ w.tables, heap.Borrowed store (tableAddr tables k.val) tables[k] := fun k hk =>
    (hTables _ (List.mem_map.mpr ⟨k, hk, rfl⟩)).1
  have hRep' := Env.withTables_rep w.tables hB hT (by rw [hShift]; exact hRep)
  have hMoves := Env.withTables_moves (store := store) (tables := tables) w.tables hB (ws := ws)
    (env := args)
  have hReads := Env.withTables_reads (store := store) (tables := tables) w.tables hB (ws := ws)
    (env := args)
  rw [hShift] at hMoves hReads
  have hSep' : Separate store
      (Env.moves store (paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes)
        ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables w.tables args))
      (Env.reads store (paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes)
        ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
        (Env.withTables tables w.tables args)) := by
    rw [hMoves, hReads]
    refine ⟨hSep.1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact (hTables _ (List.mem_map.mpr ⟨k, hk, rfl⟩)).2
    · exact hSep.2 r hr
  have hLength : ws.length = widthSum w.params := hRep.length
  have hInput' : @Bytes.LiteralPool.Input
      (Env (List.replicate w.tables.length (.array .word) ++ w.params))
      (Env.represent _ w.modes) ⟨base, []⟩ heap store
      ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
      (Env.withTables tables w.tables args) :=
    Bytes.LiteralPool.Input.empty _ _ _ _ _
  obtain ⟨hHeap, -⟩ := AlignedInput.env hIn
  have hVals : Env.AlignedVals store
      (paramMode (List.replicate w.tables.length (.array .word) ++ w.params) w.modes)
      ((w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) ++ ws)
      (Env.withTables tables w.tables args) := by
    refine Env.AlignedVals.of_moves_reads _ _ _ (fun p hp => ?_) (fun r hr => ?_)
    · rw [hMoves] at hp
      exact hIn.2.1 p hp
    · rw [hReads] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hr
        exact tableAddr_mod8 tables k.val
      · exact hIn.2.2 r hr
  have hRun := ((hCalls w.callee 0).2 rfl host hAt hInput' hRep' hSep' hCap hHeap hVals (d := 0)
    (fun _ => rfl) []).of_imp (a' := w.aborts || w.depth) fun h => by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr h
      · exact h
  have hNum : (wrapperFunction (w.tables.map fun k => tableAddr tables k.val) w.params w.result
      w.depth w.callee.callIndex e).numParams = widthSum w.params := by
    simp only [wrapperFunction, Function.numParams, flatMap_types_length]
  have hAddrs : (w.tables.map fun k : Fin tables.length => Value.i64 (tableAddr tables k.val)) =
      (w.tables.map fun k => tableAddr tables k.val).map Value.i64 := by
    simp only [List.map_map]; rfl
  refine (fun (h : RunsA (w.aborts || w.depth) host m e store ws.reverse _) => ⟨h.2, h.1⟩) ?_
  apply RunsX.of_wpX_entry_for (strict := true)
    (f := wrapperFunction (w.tables.map fun k => tableAddr tables k.val)
      w.params w.result w.depth w.callee.callIndex e)
    (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
  rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
  rw [hAddrs] at hRun
  simp only [wrapperFunction, List.append_assoc, List.range_eq_range', flatMap_types_length,
    ← hLength]
  refine wpX_constI64s _ _ ?_
  refine wpX_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
  have hStack : ws.reverse ++ ((((if w.depth then ([0] : List UInt64) else []) ++
        (w.tables.map fun k : Fin tables.length => tableAddr tables k.val)).map
          Value.i64).reverse ++
        []) =
      ((w.tables.map fun k : Fin tables.length => tableAddr tables k.val).map Value.i64 ++
        ws).reverse ++ ((if w.depth then [Value.i64 0] else []) ++ []) := by
    cases w.depth <;> simp [List.reverse_append]
  rw [← hStack] at hRun
  refine wpX_call_runs (strict := true) hRun (TrapOK.of_msg fun _ => Iff.rfl)
    fun st' vs hPost => ?_
  obtain ⟨out, rfl, heap', hAt', hOwned, hCaps, hRegions, _, hAl⟩ := hPost
  rw [wpX_nil]
  have hOut : out.length = w.result.width := by
    have := hOwned.length; rwa [List.length_reverse] at this
  have hTake : (out ++ []).take w.result.types.length = out := by
    rw [List.append_nil]; exact List.take_of_length_le (by rw [Ty.types_length, hOut])
  have hDrop : ws.reverse.drop (List.flatMap Ty.types w.params).length = [] :=
    List.drop_of_length_le (by rw [List.length_reverse, flatMap_types_length, hLength])
  dsimp only [Function.numParams]
  rw [hTake, hDrop, List.append_nil]
  obtain ⟨hHeapAl, hV⟩ := hAl rfl
  exact ⟨heap', hAt', hOwned, hCaps, fun r hr hpos hA =>
    hRegions r hr hpos (by rw [← hAddrs]; exact hMoves ▸ hA), trivial, hHeapAl,
    fun b hb => ⟨(hV b hb).1, (hV b hb).2 rfl⟩⟩

/-- A wrapper's alignment theorem in the form of Lean's instances, as `ImplementsTables.lean`. -/
theorem ImplementsTablesAligned.lean {ps : List Ty} {ms : List Mode} {r : Ty} {aborts : Bool}
    {m : Module} {entry : Nat} {f : Env ps → r.denote} {tables : List (UInt64 × Array UInt64)}
    {Pre : Env ps → Heap → Store Unit → Prop}
    {Post : Env ps → Heap → Store Unit → Heap → Store Unit → Prop}
    (h : @ImplementsTablesAligned _ _ (Env.represent ps ms) (Ty.represent r) aborts m entry f
      tables Pre Post) :
    @ImplementsTablesAligned _ _ (argsInst ps ms) r.leanInst aborts m entry
      (fun y => f (Env.ofArgs ps ms y)) tables (fun y => Pre (Env.ofArgs ps ms y))
      (fun y => Post (Env.ofArgs ps ms y)) := by
  intro env store heap vs y hAt hPre hTables hY hSep hCap hIn
  have hY' := (argsInst_borrowed ps ms).mp hY
  have hl := hY'.length
  have hSep' := hSep
  rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hSep'
  have hIn' : @AlignedInput _ (Env.represent ps ms) heap store vs (Env.ofArgs ps ms y) := by
    obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [argsInst_moves ps ms hl]; exact hp
    · rw [argsInst_reads ps ms hl]; exact hr
  have hTables' : ∀ t ∈ tables, heap.Borrowed store t.1 t.2 ∧
      Apart store (@Represent.moves _ (Env.represent ps ms) store vs (Env.ofArgs ps ms y))
        (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hTables t ht
    rw [argsInst_moves ps ms hl] at h2
    exact ⟨h1, h2⟩
  obtain ⟨hA, hRun⟩ := h env store heap vs (Env.ofArgs ps ms y) hAt hPre hTables' hY' hSep' hCap
    hIn'
  refine ⟨hA, hRun.mono fun final values ⟨heap', hAt', hOwned, hCaps, hRegions, hPost, hHeapAl,
    hOut⟩ => ⟨heap', hAt', r.leanInst_owned.mpr hOwned, hCaps, fun rg hr hpos hAp => ?_, hPost,
    hHeapAl, fun b hb => hOut b (by rw [r.leanInst_blocks] at hb; exact hb)⟩⟩
  rw [argsInst_moves ps ms hl] at hAp
  obtain ⟨hb, hreg, hout⟩ := hRegions rg hr hpos hAp
  refine ⟨hb, hreg, ?_⟩
  simp only [Represent.outside, r.leanInst_blocks]
  exact hout

end Verified
