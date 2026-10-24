import Verified.Wasi.EffectSpec
import Verified.Wasi.ScratchContext

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem call_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {all kept : Nat → Bool} {base : Nat}
    {heap argumentHeap finalHeap : Heap} {initial arguments final : Store World}
    {locals argumentLocals : Locals} {signature : EffectSig} {args : Env signature.params}
    {params words : List Value} {fresh : List (Nat × Nat)} {value : signature.result.denote}
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots all (PureTransport.erase initial) locals ABI.scratch)
    (argumentStep : Step heap (PureTransport.erase initial) (fun _ => True)
      argumentHeap (PureTransport.erase arguments) fresh)
    (frame : Frame base locals argumentLocals)
    (argumentVars : Holds env slots all base argumentHeap (PureTransport.erase arguments)
      argumentLocals)
    (keptSelected : ∀ i, kept i = true → all i = true)
    (movesApart : ∀ region, (∀ block ∈ fresh, regionsDisjoint region block) →
      Holds.KeepDying env slots all kept (PureTransport.erase initial) locals region →
      Apart (PureTransport.erase arguments)
        (Env.moves (PureTransport.erase arguments) signature.mode params args) region)
    (keptApart : ∀ type (sourceVar : Var context type), kept sourceVar.index = true →
      ∀ values, LocalsHold argumentLocals (slots.getD sourceVar.index default).loc type.types
        values → values.length = type.width →
      ∀ region ∈ type.regions (slots.getD sourceVar.index default).mode
        (PureTransport.erase arguments) values (env.get sourceVar),
      Apart (PureTransport.erase arguments)
        (Env.moves (PureTransport.erase arguments) signature.mode params args) region)
    (callStep : Step argumentHeap (PureTransport.erase arguments)
      (fun region => Apart (PureTransport.erase arguments)
          (Env.moves (PureTransport.erase arguments) signature.mode params args) region ∧
        regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final)
      (signature.result.fresh (PureTransport.erase final) words value))
    (rep : signature.result.Rep finalHeap (PureTransport.erase final) words value) :
    After env slots all kept base heap initial locals signature.result value
      finalHeap final argumentLocals words := by
  have keptVars := argumentVars.live_mono keptSelected
  have keptScratch : Holds.ApartFrom env slots kept (PureTransport.erase arguments)
      argumentLocals ABI.scratch :=
    Holds.ApartFrom.transfer vars (scratch.mono keptSelected) argumentStep frame keptSelected
      (fun _ _ _ _ _ _ _ _ => trivial)
  have keep : ∀ type (sourceVar : Var context type), kept sourceVar.index = true →
      ∀ values, LocalsHold argumentLocals (slots.getD sourceVar.index default).loc type.types
        values → values.length = type.width →
      ∀ region ∈ type.regions (slots.getD sourceVar.index default).mode
          (PureTransport.erase arguments) values (env.get sourceVar),
      Apart (PureTransport.erase arguments)
          (Env.moves (PureTransport.erase arguments) signature.mode params args) region ∧
        regionsDisjoint region ABI.scratch := by
    intro type sourceVar live values held width region member
    exact ⟨keptApart type sourceVar live values held width region member,
      regionsDisjoint_symm (keptScratch type sourceVar live values held width region member)⟩
  refine ⟨argumentStep.trans callStep (fun region keptRegion =>
      ⟨trivial, fun separated => ⟨movesApart region separated keptRegion.1, keptRegion.2⟩⟩),
    frame, keptVars.step callStep keep, rep, ?_⟩
  cases signature with
  | mk name types modes result =>
      cases result with
      | unit => trivial
      | value type =>
          intro other sourceVar live _ values held width resultRegion resultMember region member
          obtain ⟨same, freshApart⟩ := keptVars.regions_after callStep live held width
            (keep other sourceVar live values held width)
          rw [same] at member
          exact regionsDisjoint_symm (freshApart region member resultRegion resultMember)

end Verified.Wasi
