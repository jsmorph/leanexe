import LeanExe.M7.Proof.Step
import TestSupport.M7.Hist

/-!
The step theorems of the histogram step on the Cortex-M7: the calls of `histUsart3`, function 4
of `histCompiled.module`, and of `histCmsdk`, function 5, in the program that `genProgram`
generates with the code of `udivmod64`.  The step's state holds the counts in an owned array, so
its words are the array's pointer and the word of the phase and the reply, and `HistRep` relates
them: the heap owns at the pointer an array that holds the counts, the heap is aligned, `top` lies
within the memory's cap, and the pointer and the block's capacity are multiples of 8.

`hist_stepRep` derives `StepRep` with `HistRep` from the compiler's theorems of the step:
`trapFree`, whose precondition holds because the step's allocation bound is 0 at every argument
(`histUsart3_bound`), gives the result without a trap and a `top` that does not rise, and
`aligned` gives the aligned accesses, the aligned heap, and the aligned block of the result.  Both
describe the same run, which `Runs.both` joins, and the two heaps that they choose hold the same
`top`, the store's global 0.  `hist_step` instantiates `step_rep` with the kernel's evaluation of
`reachCovered`, `usesArea`, and the module's global types.
-/

namespace TestSupport.M7.Hist

open Wasm LeanExe.M7 LeanExe.Pipeline LeanExe.ProofKit

/-- The histogram step's allocation bound is 0 at every argument, since `set!` writes the owned
array in place. -/
theorem histUsart3_bound (x : Moved (Array UInt64) × UInt64 × UInt64) :
    histCompiled.histUsart3.bound x = 0 := by
  obtain ⟨⟨h⟩, s, v⟩ := x
  exact histCompiled.histUsart3.bound_eq h s v

theorem histCmsdk_bound (x : Moved (Array UInt64) × UInt64 × UInt64) :
    histCompiled.histCmsdk.bound x = 0 := by
  obtain ⟨⟨h⟩, s, v⟩ := x
  exact histCompiled.histCmsdk.bound_eq h s v

/-- The words `ws` of the state `g` at the heap `heap` and the store `st`: the pointer `p` of an
array that the heap owns and that holds the counts, and the word of the phase and the reply, in a
heap that is aligned and whose `top` lies within the memory's cap. -/
def HistRep (g : HistState) (ws : List UInt64) (heap : Heap) (st : Store Unit) : Prop :=
  ∃ p : UInt64, ws = [p, g.2] ∧ heap.Owned st p g.1 ∧ heap.Aligned ∧
    heap.Within st histCompiled.module 0 ∧ p.toNat % 8 = 0 ∧ capacityAt st p % 8 = 0

theorem histRep_length {g : HistState} {ws : List UInt64} {heap : Heap} {st : Store Unit}
    (h : HistRep g ws heap st) : ws.length = 2 := by
  obtain ⟨p, rfl, -⟩ := h
  rfl

/-- Two heaps at one store hold the same `top`, the store's global 0. -/
theorem top_of_at {heap heap' : Heap} {st : Store Unit} (h : heap.At st) (h' : heap'.At st) :
    heap'.top = heap.top := by
  have e : heap'.globals = heap.globals := h'.globals.symm.trans h.globals
  exact Value.i64.inj (List.cons.inj e).1

/-- A call of a histogram step from words that `HistRep` relates to the state: the compiler's
theorems `trapFree` and `aligned` of the step at the function `k`, whose allocation bound is 0. -/
theorem hist_stepRepOf {k : Nat}
    {f : HistState → UInt64 → HistState × UInt64}
    (bound : Moved (Array UInt64) × UInt64 × UInt64 → Nat)
    (hbound : ∀ x, bound x = 0)
    (htrap : ImplementsA false histCompiled.module k
      (fun x : Moved (Array UInt64) × UInt64 × UInt64 => f (x.1.val, x.2.1) x.2.2)
      (fun x heap store => heap.Within store histCompiled.module (bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + bound x))
    (hal : ImplementsAligned true histCompiled.module k
      (fun x : Moved (Array UInt64) × UInt64 × UInt64 => f (x.1.val, x.2.1) x.2.2)
      (fun _ _ _ => True) fun _ _ _ _ _ => True) :
    StepRep histCompiled.module k HistRep f := by
  rintro heap st g ws v hat ⟨p, rfl, hown, halh, hW, hp8, hc8⟩ hcap
  let x : Moved (Array UInt64) × UInt64 × UInt64 := (⟨g.1⟩, g.2, v)
  have hB : Represent.borrowed heap st [.i64 p, .i64 g.2, .i64 v] x :=
    ⟨[.i64 p], [.i64 g.2, .i64 v], rfl, ⟨p, rfl, hown⟩, rfl⟩
  have hmv : Represent.moves st [.i64 p, .i64 g.2, .i64 v] x = [p] := rfl
  have hrd : Represent.reads st [.i64 p, .i64 g.2, .i64 v] x = [] := rfl
  have hS : Separate st (Represent.moves st [.i64 p, .i64 g.2, .i64 v] x)
      (Represent.reads st [.i64 p, .i64 g.2, .i64 v] x) := by
    rw [hmv, hrd]
    exact ⟨List.pairwise_singleton _ _, nofun⟩
  have hI : AlignedInput heap st [.i64 p, .i64 g.2, .i64 v] x := by
    refine ⟨halh, ?_, ?_⟩
    · rw [hmv]
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact ⟨hp8, hc8⟩
    · rw [hrd]
      exact nofun
  obtain ⟨hAl, hA⟩ := hal {} st heap _ x hat trivial hB hS hcap hI
  have hT := htrap {} st heap _ x hat
    (show heap.Within st histCompiled.module (bound x) by rw [hbound]; exact hW) hB hS hcap
  have hargs : ([p, g.2] ++ [v]).map Value.i64 = [.i64 p, .i64 g.2, .i64 v] := rfl
  rw [hargs]
  refine ⟨fun _ => hAl, (hT.both hA).mono fun final values ⟨⟨heap', hat', _, hcaps, _, htop⟩,
    ⟨heap'', hat'', hrep, _, _, _, halh'', hout⟩⟩ => ?_⟩
  obtain ⟨first, second, hvs, ⟨f1, s1, hf, ⟨ptr, hptr, hown'⟩, hs1, -⟩, hs2, -⟩ := hrep
  subst hptr
  have hs1' : s1 = [.i64 (f g v).1.2] := hs1
  have hs2' : second = [.i64 (f g v).2] := hs2
  subst hs1' hs2' hf
  have hbl : Represent.blocks final values.reverse (f g v) = [block final ptr] := by
    rw [hvs]
    rfl
  have hblk := hout (block final ptr) (by rw [hbl]; exact List.mem_singleton_self _)
  have hbase := hown'.base
  simp only [block] at hblk
  refine ⟨heap'', [ptr, (f g v).1.2], hat'', ⟨ptr, rfl, hown', halh'', ?_, by omega, by omega⟩,
    hcaps, by rw [hvs]; rfl⟩
  have hc : final.memoryCap histCompiled.module 0 = st.memoryCap histCompiled.module 0 :=
    memoryCap_of_caps hcaps
  have ht := top_of_at hat' hat''
  unfold Heap.Within at hW ⊢
  replace htop : heap'.top.toNat ≤ heap.top.toNat + bound x := htop
  rw [hbound] at htop
  rw [ht, hc]
  omega

/-- Talos's run of `histUsart3Tick` keeps `HistRep`. -/
theorem hist_stepRep : StepRep histCompiled.module 4 HistRep histUsart3Tick :=
  hist_stepRepOf _ histUsart3_bound histCompiled.histUsart3.trapFree
    histCompiled.histUsart3.aligned

/-- Talos's run of `histCmsdkTick` keeps `HistRep`. -/
theorem histCmsdk_stepRep : StepRep histCompiled.module 5 HistRep histCmsdkTick :=
  hist_stepRepOf _ histCmsdk_bound histCompiled.histCmsdk.trapFree
    histCompiled.histCmsdk.aligned

/-- The functions that calls reach from the histogram steps have the forms that the simulation
covers. -/
theorem hist_covered :
    reachCovered histCompiled.module 4 = true ∧ reachCovered histCompiled.module 5 = true := by
  decide +kernel

/-- The histogram steps load from and store to the counts in linear memory, so their programs
have an area. -/
theorem hist_usesArea :
    usesArea histCompiled.module 4 = true ∧ usesArea histCompiled.module 5 = true := by
  decide +kernel

/-- The module has the allocator's four globals, all `i64`s. -/
theorem hist_globals :
    LeanExe.globalTypesOf histCompiled.module = some [.i64, .i64, .i64, .i64] := by
  decide +kernel

/-- The stack that a call of each histogram step uses, with the generator's frames. -/
theorem hist_stack :
    stackBound histCompiled.module 4 = 216 ∧ stackBound histCompiled.module 5 = 216 := by
  decide +kernel

/-- The call of `histUsart3Tick` in the generated program at the even address `base`, for initial
words `s0` of two words, from words that `HistRep` relates to the state and the store in the area
at DTCM's base. -/
theorem hist_step {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}
    {s0 : List UInt64} (hs0 : s0.length = 2) {base limit dev : UInt32} {is : List Instr}
    (hg : genProgram histCompiled.module 4 s0 base limit dev udivmod64 = .ok is)
    (hcode : CodeAt code base is) (hev : base.toNat % 2 = 0) {st : Store Unit} {heap : Heap}
    (hat : heap.At st) (hcap : st.memoryCap histCompiled.module 0 ≤ 65535) (g : HistState)
    {ws : List UInt64} (hR : HistRep g ws heap st) (v : UInt64) (ms : State)
    (hpc : ms.pc = after base (mainSize s0)) (hlr : ms.lr % 2 = 1)
    (hstk : StackOk P limit 3 (stackBound histCompiled.module 4) ms)
    (hsr : StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st ms)
    (hargs : WordsAt ms (ws ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 24 ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      ∃ (ws' : List UInt64) (st' : Store Unit) (heap' : Heap),
        HistRep (histUsart3Tick g v).1 ws' heap' st' ∧
        WordsAt ms' (ws' ++ [(histUsart3Tick g v).2]) ∧ heap'.At st' ∧
        st'.memoryCaps = st.memoryCaps ∧
        StoreRel P areaHeader limit areaPages [.i64, .i64, .i64, .i64] st' ms' := by
  obtain ⟨ms', h1, h2, h3, h4, h5, h6, h7, ws', st', heap', hR', hw, hat', hcaps, hsr'⟩ :=
    step_rep (P := P) (σ := σ) (fun _ _ _ _ h => by rw [histRep_length h, hs0]) hist_stepRep
      rfl hg hcode hev hist_covered.1 hat hcap g hR v ms hpc hlr (by rw [hs0]; exact hstk)
      (fun _ => ⟨_, hist_globals, hsr⟩) hargs
  rw [hs0] at h7
  obtain ⟨gts, hgt, hr⟩ := hsr' hist_usesArea.1
  rw [hist_globals, Option.some.injEq] at hgt
  subst hgt
  exact ⟨ms', h1, h2, h3, h4, h5, h6, h7, ws', st', heap', hR', hw, hat', hcaps, hr⟩

end TestSupport.M7.Hist
