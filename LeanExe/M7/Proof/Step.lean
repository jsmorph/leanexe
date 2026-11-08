import LeanExe.M7.Proof.Program
import LeanExe.Pipeline.Implements

/-!
The call of a step from the compiler's theorem of the step, as `ReqRuns` states it on the C path
(`LeanExe/Native/Proof/Req.lean`).  A step takes the words of a state and the value that the last
request read and returns the words of the next state and a request, all of type `i64`.  `main`
keeps these words in its outgoing area, slot `i` for word `i`, so `step_call` states the call from
a state whose outgoing area holds the state's words and the value, `WordsAt`, and gives the
return with the outgoing area holding the words of the step's result.

`StepRep m k Rep tick` is what `step_rep` takes of Talos's run of the step, for a relation `Rep`
of a state, its words, a heap, and a store: from every store with a heap at it, words that `Rep`
relates to the state, and a memory cap that the compiler admits, the run returns words that `Rep`
relates to the next state, with the next request, at a store with a heap at it and the same memory
caps, and for a program with an area every run from some fuel on makes only aligned 64-bit
accesses inside memory.  A state that holds an array has words that name its object in the heap,
which the compiler's postcondition gives only as some words, so `Rep` relates them.
`StepCall m k words tick J` is the case of a state whose words are `words g` and of an invariant
`J` of the heap and the store alone, which `StepCall.rep` turns into `StepRep`.

`AreaHolds` states the store relation of the area for a program with one and nothing otherwise,
and `step_rep` and `step_call` carry it and the relation from the call to the return, so a loop's
invariant carries them from one call to the next.  `stepCall_of_implementsA` gives `StepCall` with
the invariant `True` from the compiler's theorem without a trap of a step whose program has no
area, and a program's own file gives it for a step with tables, as `crc_call` of
`tests/TestSupport/M7/Crc.lean` does.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph LeanExe.Pipeline

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-- The words `ws` lie in the slots of the outgoing area at SP, word `i` in slot `i`. -/
def WordsAt (s : State) (ws : List UInt64) : Prop :=
  ∀ i (hi : i < ws.length), ValAt s (8 * i) (.i64 ws[i])

theorem typed_i64 : ∀ ws : List UInt64,
    Typed (List.replicate ws.length .i64) (ws.map Value.i64)
  | [] => trivial
  | _ :: ws => ⟨trivial, typed_i64 ws⟩

/-- When the step `k` of `m` has an area, the machine holds the store `st` there, below the
stack's limit `lim`. -/
def AreaHolds (P : Platform) (m : Module) (k : Nat) (lim : UInt32) {α : Type} (st : Store α)
    (s : State) : Prop :=
  usesArea m k = true →
    ∃ gts, globalTypesOf m = some gts ∧ StoreRel P areaHeader lim areaPages gts st s

theorem AreaHolds.congr {P : Platform} {m : Module} {k : Nat} {lim : UInt32} {α : Type}
    {st : Store α} {s t : State} (h : AreaHolds P m k lim st s) (hk : KeepsBelow lim s t) :
    AreaHolds P m k lim st t :=
  fun hu => let ⟨gts, hg, hr⟩ := h hu; ⟨gts, hg, hr.congr hk⟩

/-- A program without an area holds every store. -/
theorem areaHolds_none {P : Platform} {m : Module} {k : Nat} {lim : UInt32} {α : Type}
    {st : Store α} {s : State} (h : usesArea m k = false) : AreaHolds P m k lim st s :=
  fun hu => absurd (h.symm.trans hu) (by decide)

theorem memoryCap_of_caps {st st' : Store Unit} {m : Module} {i : Nat}
    (h : st'.memoryCaps = st.memoryCaps) : st'.memoryCap m i = st.memoryCap m i := by
  unfold Store.memoryCap
  rw [h]

/-- The operand stack of a call of the step on the state `s` and the value `v`, top first. -/
def stepArgs {G : Type} (words : G → List UInt64) (s : G) (v : UInt64) : List Value :=
  ((words s ++ [v]).map Value.i64).reverse

/-- Talos's run of the step `k` of `m`, from every store with a heap at it, the invariant `J`, and a
memory cap that the compiler admits: for a program with an area, every run from some fuel on
makes only aligned 64-bit accesses inside memory, and the run returns the words of `tick s v` and
leaves a store with a heap at it, `J`, and the same memory caps. -/
def StepCall (m : Module) (k : Nat) {G : Type} (words : G → List UInt64)
    (tick : G → UInt64 → G × UInt64) (J : Heap → Store Unit → Prop) : Prop :=
  ∀ (heap : Heap) (st : Store Unit) (s : G) (v : UInt64), heap.At st → J heap st →
    st.memoryCap m 0 ≤ 65535 →
    (usesArea m k = true → ∃ N, ∀ fuel ≥ N, AlignedRun fuel m k st (stepArgs words s v) {}) ∧
    Runs false {} m k st (stepArgs words s v) fun final values =>
      ∃ heap' : Heap, heap'.At final ∧ J heap' final ∧ final.memoryCaps = st.memoryCaps ∧
        values.reverse = (words (tick s v).1 ++ [(tick s v).2]).map Value.i64

/-- Talos's run of the step `k` of `m`, from every store with a heap at it, words `ws` that `Rep`
relates to the state `s` there, and a memory cap that the compiler admits: for a program with an
area, every run from some fuel on makes only aligned 64-bit accesses inside memory, and the run
returns words that `Rep` relates to the state of `tick s v` and the request of `tick s v`, at a
store with a heap at it and the same memory caps. -/
def StepRep (m : Module) (k : Nat) {G : Type} (Rep : G → List UInt64 → Heap → Store Unit → Prop)
    (tick : G → UInt64 → G × UInt64) : Prop :=
  ∀ (heap : Heap) (st : Store Unit) (s : G) (ws : List UInt64) (v : UInt64), heap.At st →
    Rep s ws heap st → st.memoryCap m 0 ≤ 65535 →
    (usesArea m k = true →
      ∃ N, ∀ fuel ≥ N, AlignedRun fuel m k st ((ws ++ [v]).map Value.i64).reverse {}) ∧
    Runs false {} m k st ((ws ++ [v]).map Value.i64).reverse fun final values =>
      ∃ (heap' : Heap) (ws' : List UInt64), heap'.At final ∧ Rep (tick s v).1 ws' heap' final ∧
        final.memoryCaps = st.memoryCaps ∧ values.reverse = (ws' ++ [(tick s v).2]).map Value.i64

/-- Two statements of the same run, the first without a trap: from some fuel on the run returns
values that satisfy both postconditions.  A step's `trapFree` and `aligned` theorems state its
run so. -/
theorem _root_.Wasm.Runs.both {α : Type} {env : HostEnv α} {m : Module} {id : Nat}
    {st : Store α} {args : List Value} {P Q : Store α → List Value → Prop} {aborts : Bool}
    (h1 : Runs false env m id st args P) (h2 : Runs aborts env m id st args Q) :
    Runs false env m id st args fun s vs => P s vs ∧ Q s vs := by
  obtain ⟨N1, h1⟩ := h1
  obtain ⟨N2, h2⟩ := h2
  refine ⟨N1 + N2, fun fuel hf => ?_⟩
  rcases h1 fuel (by omega) with ⟨vs, s, hr, hp⟩ | ht
  · rcases h2 fuel (by omega) with ⟨vs', s', hr', hq⟩ | ht'
    · rw [hr] at hr'
      cases hr'
      exact .inl ⟨vs, s, hr, hp, hq⟩
    · cases aborts
      · exact ht'.elim
      · obtain ⟨s', hs'⟩ := ht'
        rw [hr] at hs'
        cases hs'
  · exact ht.elim

/-- `StepCall` is `StepRep` for the words `words g` of the state and the invariant `J`. -/
theorem StepCall.rep {m : Module} {k : Nat} {G : Type} {words : G → List UInt64}
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (h : StepCall m k words tick J) :
    StepRep m k (fun g ws heap st => ws = words g ∧ J heap st) tick := by
  rintro heap st s ws v hat ⟨rfl, hJ⟩ hcap
  obtain ⟨hal, hrun⟩ := h heap st s v hat hJ hcap
  exact ⟨hal, hrun.mono fun _ _ ⟨heap', hat', hJ', hcaps, hv⟩ =>
    ⟨heap', _, hat', ⟨rfl, hJ'⟩, hcaps, hv⟩⟩

/-- `StepCall` with the invariant `True` from the compiler's theorem of a step whose program has no
area, whose run states no trap. -/
theorem stepCall_of_implementsA {G : Type} [Scalar G] {m : Module} {k : Nat}
    {words : G → List UInt64} (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    {tick : G → UInt64 → G × UInt64} {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hna : usesArea m k = false) :
    StepCall m k words tick fun _ _ => True := by
  intro heap st s v hat _ hcap
  refine ⟨fun h => absurd (hna.symm.trans h) (by decide), ?_⟩
  have hb : Represent.borrowed heap st ((words s ++ [v]).map Value.i64) (s, v) := by
    show _ = Scalar.values s ++ Scalar.values v
    rw [hwords]
    simp [Scalar.values]
  refine (himpl {} st heap ((words s ++ [v]).map Value.i64) (s, v) hat (hPre _ _ _) hb
    Separate.nil hcap).mono fun final values ⟨heap', hat', hown, hcaps, _, _⟩ =>
      ⟨heap', hat', trivial, hcaps, ?_⟩
  have : values.reverse = Scalar.values (tick s v).1 ++ Scalar.values (tick s v).2 := hown
  rw [this, hwords]
  simp [Scalar.values]

/-- The call of the step `k` of the generator's program, whose run `hcall` states: from the step's
entry, with bit 0 of LR set, the stack that `StackOk` states for `stackBound m k` bytes, the store
in the area of a program with one, and words `ws` that `Rep` relates to the state `s`, with the
value `v`, in the outgoing area, the model returns to LR with bit 0 clear, with SP, LR, the device
trace, and the read count as they were, every byte from the end of the outgoing area's
`s0.length + 1` slots up unchanged, and words that `Rep` relates to the step's next state, with its
request, in the outgoing area.  The store after Talos's call again has a heap at it and the same
memory caps, and the machine holds it in the area. -/
theorem step_rep {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {is : List Instr} {Rep : G → List UInt64 → Heap → Store Unit → Prop}
    (hlen : ∀ g ws heap st, Rep g ws heap st → ws.length = s0.length)
    {tick : G → UInt64 → G × UInt64} (hcall : StepRep m k Rep tick) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hcap : st.memoryCap m 0 ≤ 65535) (s : G)
    {ws : List UInt64} (hR : Rep s ws heap st) (v : UInt64) (ms : State)
    (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit (s0.length + 1) (stackBound m k) ms)
    (hsr : AreaHolds P m k limit st ms) (hargs : WordsAt ms (ws ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 8 * (s0.length + 1) ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      ∃ (ws' : List UInt64) (st' : Store Unit) (heap' : Heap),
        Rep (tick s v).1 ws' heap' st' ∧ WordsAt ms' (ws' ++ [(tick s v).2]) ∧ heap'.At st' ∧
        st'.memoryCaps = st.memoryCaps ∧ AreaHolds P m k limit st' ms' := by
  obtain ⟨f, S, need, hk, hSl, hps, hrs, hneedk, hno, hyes, hsim⟩ :=
    step_sim (P := P) (σ := σ) hm hg hcode hev hcov
  have hwl : ws.length = s0.length := hlen _ _ _ _ hR
  have hl1 : (ws ++ [v]).length = s0.length + 1 := by simp [hwl]
  -- Talos's call
  obtain ⟨hal, N, hN⟩ := hcall heap st s ws v hat hR hcap
  obtain ⟨Na, hNa⟩ : ∃ Na, usesArea m k = true →
      ∀ fuel ≥ Na, AlignedRun fuel m k st ((ws ++ [v]).map Value.i64).reverse {} := by
    by_cases hu : usesArea m k = true
    · obtain ⟨Na, h⟩ := hal hu
      exact ⟨Na, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hu⟩
  rcases hN (N + Na) (by omega) with
    ⟨vals, final, hrun, heap', ws', hat', hR', hcaps, hvals⟩ | habs
  swap
  · exact habs.elim
  -- the store and the alignment for the simulation
  have hsrS : StoreOk P S st ms := fun A hA => by
    cases hu : usesArea m k
    · rw [hno hu] at hA
      cases hA
    · obtain ⟨-, A', hA', hgt⟩ := hyes hu
      obtain ⟨gts, hgt', hsr'⟩ := hsr hu
      rw [hA'] at hA
      cases hA
      rw [hgt] at hgt'
      cases hgt'
      rw [hSl]
      exact hsr'
  have halS : S.area.isSome = true →
      m.memIs64 = false ∧ AlignedRun (N + Na) m k st ((ws ++ [v]).map Value.i64).reverse {} :=
    fun h => by
      cases hu : usesArea m k
      · rw [hno hu] at h
        cases h
      · exact ⟨(hyes hu).1, hNa hu (N + Na) (by omega)⟩
  -- the simulation of the call
  generalize hvs : ((ws ++ [v]).map Value.i64).reverse = vs at hrun halS
  have hvsl : vs.length = s0.length + 1 := by rw [← hvs]; simp [hwl]
  have hcr : CallResult P σ code S f.params f.results vs (Wasm.run (N + Na) m k st vs) ms := by
    refine hsim (N + Na) st vs ms (by rw [hps, List.length_replicate]; omega) ?_ hpc hlr
      (by rw [hSl, hps, hrs, List.length_replicate, Nat.max_self, hneedk]; exact hstk) ?_ hsrS
      halS
    · have h1 := (typed_i64 (ws ++ [v])).reverse
      rw [List.reverse_replicate, hl1] at h1
      rw [hps, List.length_replicate, List.reverse_replicate, ← hvs,
        List.take_of_length_le (by simp [hwl])]
      exact h1
    · rw [hps, List.length_replicate, ← hvs, List.take_of_length_le (by simp [hwl])]
      intro i w hw
      rw [List.reverse_reverse, List.getElem?_map] at hw
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hw
      obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hx
      exact hargs i hi'
  rw [hrun] at hcr
  obtain ⟨ms', hr, hpc', hsp', hlr', htr', hrd', hmem', hlen', -, hargs', -, hsr'⟩ := hcr
  have hvl : vals.length = s0.length + 1 := by
    have := congrArg List.length hvals
    simp [hlen _ _ _ _ hR'] at this
    exact this
  rw [hrs, List.length_replicate, List.take_of_length_le (by omega)] at hargs'
  rw [hps, hrs, List.length_replicate, Nat.max_self] at hmem'
  refine ⟨ms', hr, hpc', hsp', hlr', htr', hrd', hmem', ws', final, heap', hR', fun i hi => ?_,
    hat', hcaps, fun hu => ?_⟩
  · apply hargs' i
    rw [hvals, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · obtain ⟨-, A, hA, hgt⟩ := hyes hu
    refine ⟨A.globals, hgt, ?_⟩
    have := hsr' A hA
    rwa [hSl] at this

/-- `step_rep` for a state whose words are `words s` and an invariant `J` of the heap and the
store: the model returns with the words of the step's result in the outgoing area and the store
after Talos's call, which keeps `J`, in the area. -/
theorem step_call {G : Type} {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {is : List Instr} {words : G → List UInt64} (hlen : ∀ g, (words g).length = s0.length)
    {tick : G → UInt64 → G × UInt64} {J : Heap → Store Unit → Prop}
    (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hJ : J heap st)
    (hcap : st.memoryCap m 0 ≤ 65535) (s : G) (v : UInt64) (ms : State)
    (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit (s0.length + 1) (stackBound m k) ms)
    (hsr : AreaHolds P m k limit st ms) (hargs : WordsAt ms (words s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 8 * (s0.length + 1) ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (words (tick s v).1 ++ [(tick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ J heap' st' ∧
        st'.memoryCaps = st.memoryCaps ∧ AreaHolds P m k limit st' ms' := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, _, st', heap', ⟨rfl, hJ'⟩, h8, hat', hcaps, hsr'⟩ :=
    step_rep (P := P) (σ := σ) (fun g _ _ _ h => by rw [h.1]; exact hlen g) hcall.rep hm hg
      hcode hev hcov hat hcap s ⟨rfl, hJ⟩ v ms hpc hlr hstk hsr hargs
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, h8, st', heap', hat', hJ', hcaps, hsr'⟩

end LeanExe.M7
