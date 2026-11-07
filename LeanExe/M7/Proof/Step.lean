import LeanExe.M7.Proof.Program
import LeanExe.Pipeline.Implements

/-!
The call of a step from the compiler's theorem of the step, as `ReqRuns` states it on the C path
(`LeanExe/Native/Proof/Req.lean`).  A step takes the words of a state and the value that the last
request read and returns the words of the next state and a request, all of type `i64`.  `main`
keeps these words in its outgoing area, slot `i` for word `i`, so `step_call` states the call from
a state whose outgoing area holds the state's words and the value, `WordsAt`, and gives the
return with the outgoing area holding the words of the step's result.  It quantifies over every
Talos store with a heap that `Heap.At` relates to it and a memory cap that the compiler's theorem
admits, since the relation of the simulation holds no store; the store after the call satisfies
the same conditions, so a loop's invariant can carry them from one call to the next.
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

/-- The call of the step `k` of the generator's program, which the compiler's theorem `himpl`
states without a trap: from the step's entry, with bit 0 of LR set, the stack that `StackOk`
states for `stackBound m k` bytes, and the words of the state `s` and the value `v` in the
outgoing area, the model returns to LR with bit 0 clear, with SP, LR, the device trace, and the
read count as they were, every byte from the end of the outgoing area's `s0.length + 1` slots up
unchanged, and the words of the step's result in the outgoing area.  The store after Talos's call
again has a heap at it and the same memory caps. -/
theorem step_call {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {base limit dev : UInt32} {is : List Instr} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hcap : st.memoryCap m 0 ≤ 65535)
    (s : G) (v : UInt64) (ms : State) (hpc : ms.pc = after base (mainSize s0))
    (hlr : ms.lr % 2 = 1) (hstk : StackOk P limit (s0.length + 1) (stackBound m k) ms)
    (hargs : WordsAt ms (words s ++ [v])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.lr &&& 0xFFFFFFFE ∧ ms'.sp = ms.sp ∧
      ms'.lr = ms.lr ∧ ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧
      (∀ a : UInt32, ms.sp.toNat + 8 * (s0.length + 1) ≤ a.toNat → ms'.mem a = ms.mem a) ∧
      WordsAt ms' (words (tick s v).1 ++ [(tick s v).2]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ st'.memoryCaps = st.memoryCaps := by
  obtain ⟨f, S, need, hk, hSl, hps, hrs, hneedk, hsim⟩ :=
    step_sim (P := P) (σ := σ) hm hg hcode hev hcov
  have hl1 : (words s ++ [v]).length = s0.length + 1 := by simp [hlen]
  -- the arguments and Talos's call
  have hb : Represent.borrowed heap st ((words s ++ [v]).map Value.i64) (s, v) := by
    show _ = Scalar.values s ++ Scalar.values v
    rw [hwords]
    simp [Scalar.values]
  obtain ⟨N, hN⟩ := himpl {} st heap ((words s ++ [v]).map Value.i64) (s, v) hat (hPre _ _ _) hb
    Separate.nil hcap
  rcases hN N (Nat.le_refl _) with ⟨vals, final, hrun, heap', hat', hown, hcaps, -, -⟩ | habs
  swap
  · exact habs.elim
  have hvals : vals.reverse = (words (tick s v).1 ++ [(tick s v).2]).map Value.i64 := by
    have : vals.reverse = Scalar.values (tick s v).1 ++ Scalar.values (tick s v).2 := hown
    rw [this, hwords]
    simp [Scalar.values]
  -- the simulation of the call
  generalize hvs : ((words s ++ [v]).map Value.i64).reverse = vs at hrun
  have hvsl : vs.length = s0.length + 1 := by rw [← hvs]; simp [hlen]
  have hcr : CallResult P σ code f.params f.results vs (Wasm.run N m k st vs) ms := by
    refine hsim N st vs ms (by rw [hps, List.length_replicate]; omega) ?_ hpc hlr
      (by rw [hSl, hps, hrs, List.length_replicate, Nat.max_self, hneedk]; exact hstk) ?_
    · have h1 := (typed_i64 (words s ++ [v])).reverse
      rw [List.reverse_replicate, hl1] at h1
      rw [hps, List.length_replicate, List.reverse_replicate, ← hvs,
        List.take_of_length_le (by simp [hlen])]
      exact h1
    · rw [hps, List.length_replicate, ← hvs, List.take_of_length_le (by simp [hlen])]
      intro i w hw
      rw [List.reverse_reverse, List.getElem?_map] at hw
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hw
      obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hx
      exact hargs i hi'
  rw [hrun] at hcr
  obtain ⟨ms', hr, hpc', hsp', hlr', htr', hrd', hmem', hlen', -, hargs', -⟩ := hcr
  have hvl : vals.length = s0.length + 1 := by
    have := congrArg List.length hvals
    simp [hlen] at this
    exact this
  rw [hrs, List.length_replicate, List.take_of_length_le (by omega)] at hargs'
  rw [hps, hrs, List.length_replicate, Nat.max_self] at hmem'
  refine ⟨ms', hr, hpc', hsp', hlr', htr', hrd', hmem', fun i hi => ?_, final, heap', hat', hcaps⟩
  apply hargs' i
  rw [hvals, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

end LeanExe.M7
