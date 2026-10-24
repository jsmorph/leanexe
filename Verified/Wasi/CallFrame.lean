import Verified.Wasi.CallArguments
import Verified.Wasi.CallAfter
import Verified.ArgPot

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

namespace ArgumentsAfter

variable {World : Type} {S : List Sig} {context params : List Ty}
  {funs : Funs S} {flags : Flags S} {bounds : Bounds S} {fits : Fits S}
  {modes : Nat → Mode} {args : (i : Fin params.length) → Expr S context (params.get i)}
  {env : Env context} {slots : List Slot} {all kept : Nat → Bool} {base : Nat}
  {heap argumentHeap : Heap} {initial arguments : Store World} {locals argumentLocals : Locals}
  {words : List Value} {fresh : List (Nat × Nat)}

theorem ofValues {values : List Value}
    (after : ArgumentsAfter funs flags bounds fits modes args env slots all kept base
      heap initial { locals with values } argumentHeap arguments argumentLocals words fresh) :
    ArgumentsAfter funs flags bounds fits modes args env slots all kept base
      heap initial locals argumentHeap arguments argumentLocals words fresh :=
  ⟨after.step, after.frame.values, after.holds, after.rep, after.separate,
    after.movesApart, after.borrowedApart, after.top⟩

theorem pool_input {pool : Bytes.LiteralPool} {signature : EffectSig}
    {args : (i : Fin signature.params.length) → Expr S context (signature.params.get i)}
    (after : ArgumentsAfter funs flags bounds fits signature.mode args env slots all kept base
      heap initial locals argumentHeap arguments argumentLocals words fresh)
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (safe : pool.Safe env slots all heap (PureTransport.erase initial) locals) :
    @Bytes.LiteralPool.Input (Env signature.params)
      (Env.represent signature.params signature.modes) pool argumentHeap
      (PureTransport.erase arguments) words (Env.ofFn fun i => (args i).denote funs env) := by
  obtain ⟨static, apartFresh⟩ := safe.static.step after.step (fun _ _ => trivial)
  refine ⟨static, fun region member => after.movesApart region (apartFresh region member) ?_⟩
  exact (safe.apart region member).mono (fun k moved _ => by
    obtain ⟨i, selected⟩ := argsAny_true.mp moved
    simp only [Bool.and_eq_true] at selected
    exact ⟨uses i k selected.1.2, rfl⟩)

theorem scratch
    (after : ArgumentsAfter funs flags bounds fits modes args env slots all kept base
      heap initial locals argumentHeap arguments argumentLocals words fresh)
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (apart : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch) :
    ∀ region ∈ Env.reads (PureTransport.erase arguments) modes words
      (Env.ofFn fun i => (args i).denote funs env), regionsDisjoint ABI.scratch region := by
  apply after.borrowedApart ABI.scratch
  exact apart.mono (fun k borrowed => by
    obtain ⟨i, selected⟩ := argsAny_true.mp borrowed
    simp only [Bool.and_eq_true] at selected
    exact uses i k selected.2)

theorem call {signature : EffectSig} {finalHeap : Heap} {final : Store World}
    {args : (i : Fin signature.params.length) → Expr S context (signature.params.get i)}
    {value : signature.result.denote} {resultWords : List Value}
    (after : ArgumentsAfter funs flags bounds fits signature.mode args env slots all kept base
      heap initial locals argumentHeap arguments argumentLocals words fresh)
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (keptSelected : ∀ i, kept i = true → all i = true)
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch)
    (callStep : Step argumentHeap (PureTransport.erase arguments)
      (fun region => Apart (PureTransport.erase arguments)
          (Env.moves (PureTransport.erase arguments) signature.mode words
            (Env.ofFn fun i => (args i).denote funs env)) region ∧
        regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final)
      (signature.result.fresh (PureTransport.erase final) resultWords value))
    (rep : signature.result.Rep finalHeap (PureTransport.erase final) resultWords value) :
    After env slots all kept base heap initial locals signature.result value
      finalHeap final argumentLocals resultWords := by
  apply call_after vars apart after.step after.frame after.holds keptSelected
    (fun region freshApart keptRegion => after.movesApart region freshApart
      (keptRegion.mono (fun k moved _ => by
        obtain ⟨i, selected⟩ := argsAny_true.mp moved
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at selected
        exact ⟨uses i k selected.1.2, selected.2⟩)))
    (args_moves_apart_kept signature.mode args uses keptSelected vars
      after.step after.frame after.movesApart) callStep rep

end ArgumentsAfter
end Verified.Wasi
