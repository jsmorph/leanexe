import Verified.AlignedCorrect
import LeanExe.Pipeline.AlignedImplements

/-!
The alignment statement for the functions of a compiled program.  `AlignedInput` of a call's
arguments gives the alignment that `FunAligned` takes: an aligned heap, and, by
`Env.AlignedVals.of_moves_reads`, aligned values, since an owned value's blocks start at its
pointers minus 48 and a borrowed value's regions are its reads.  `FunSpecX.implementsAligned` is
`ImplementsAligned` of a function whose code takes no call depth, at its call index, and
`entry_aligned` is `ImplementsAligned` of the exported entry of a function whose code takes it.
`ImplementsAligned.lean` carries either to the instances of Lean's types, as `ImplementsA.lean`
carries `ImplementsA`.
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

/-- `ImplementsAligned` of a function whose code takes no call depth, at its call index. -/
theorem FunSpecX.implementsAligned {m : Module} {g : Sig} {idx : Nat}
    {F : Env g.params → g.result.denote} {pf : List Bool} {rf : Bool} {A : Env g.params → Nat}
    {Fi : Env g.params → Bool} {D : UInt64 → Prop} {base : Nat}
    (hF : FunSpecX true m g idx F pf rf A Fi D ⟨base, []⟩) (hd : g.depth = false)
    {Pre : Env g.params → Heap → Store Unit → Prop} :
    @ImplementsAligned _ (Env.represent g.params g.modes) m idx Pre := by
  intro host store heap ws x hAt _ hRep hSep hCap hIn
  obtain ⟨hHeap, hVals⟩ := AlignedInput.env hIn
  have hRun := hF.2 rfl host hAt (Bytes.LiteralPool.Input.empty _ _ _ _ _) hRep hSep hCap hHeap
    hVals (d := 0) (fun h => by rw [hd] at h; exact nomatch h) []
  have hStack : ws.reverse ++ ((if g.depth then [Value.i64 0] else []) ++ []) = ws.reverse := by
    simp [hd]
  rw [hStack] at hRun
  exact hRun.2

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
    (he : m.funcs[e]? = some (entryFunction g.params g.result idx typeIdx))
    {Pre : Env g.params → Heap → Store Unit → Prop} :
    @ImplementsAligned _ (Env.represent g.params g.modes) m e Pre := by
  intro host store heap ws args hAt _ hRep hSep hCap hIn
  obtain ⟨hHeap, hVals⟩ := AlignedInput.env hIn
  have hLength : ws.length = widthSum g.params := hRep.length
  have hNum : (entryFunction g.params g.result idx typeIdx).numParams = widthSum g.params := by
    simp only [entryFunction, Function.numParams, flatMap_types_length]
  have hRun := (hF host hAt (Bytes.LiteralPool.Input.empty _ _ _ _ _) hRep hSep hCap hHeap hVals
    (d := 0) (fun _ => hD) []).of_imp (a' := true) fun _ => rfl
  simp only [hd, ↓reduceIte] at hRun
  have hEntry : RunsX true true host m e store ws.reverse (fun _ _ => True) := by
    apply RunsX.of_wpX_entry_for (f := entryFunction g.params g.result idx typeIdx)
      (by rw [hm.imports, List.length_nil, Nat.sub_zero]; exact he) (hImp := by simp [hm.imports])
    rw [List.take_of_length_le (by rw [hNum, List.length_reverse, hLength]), List.reverse_reverse]
    simp only [entryFunction, List.cons_append, List.nil_append,
      wpX_constI64_cons, List.range_eq_range', flatMap_types_length, ← hLength]
    refine wpX_localGets ws 0 _ (fun i hi => by simp [Function.toLocals, hi]) ?_
    refine wpX_call_runs (strict := true) hRun (TrapOK.of_msg fun _ => Iff.rfl)
      fun st' vs _ => ?_
    rw [wpX_nil]
    trivial
  exact hEntry.2

/-- A function's alignment theorem in the form of Lean's instances, as `ImplementsA.lean`. -/
theorem ImplementsAligned.lean {ps : List Ty} {ms : List Mode} {m : Module} {entry : Nat}
    {Pre : Env ps → Heap → Store Unit → Prop}
    (h : @ImplementsAligned _ (Env.represent ps ms) m entry Pre) :
    @ImplementsAligned _ (argsInst ps ms) m entry (fun y => Pre (Env.ofArgs ps ms y)) := by
  intro env store heap vs y hAt hPre hY hSep hCap hIn
  have hY' := (argsInst_borrowed ps ms).mp hY
  have hl := hY'.length
  refine h env store heap vs (Env.ofArgs ps ms y) hAt hPre hY' ?_ hCap ?_
  · rw [argsInst_moves ps ms hl, argsInst_reads ps ms hl] at hSep
    exact hSep
  · obtain ⟨h1, h2, h3⟩ := hIn
    refine ⟨h1, fun p hp => h2 p ?_, fun r hr => h3 r ?_⟩
    · rw [argsInst_moves ps ms hl]; exact hp
    · rw [argsInst_reads ps ms hl]; exact hr

end Verified
