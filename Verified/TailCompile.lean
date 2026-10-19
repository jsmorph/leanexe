import Verified.TailSource

namespace Verified

open Wasm

def TailFunc.depth (func : TailFunc S) : Bool := func.body.depthCalls

def TailFunc.aborts (func : TailFunc S) : Bool :=
  func.body.aborts || !func.result.scalar || (paramModes func.params func.modes).any (· == .owned)

def TailFunc.sig (func : TailFunc S) : Sig :=
  ⟨func.params, func.result, func.aborts, func.modes, func.depth⟩

def tailSig (params : List Ty) (result : Ty) (modes : List Mode) : Sig :=
  ⟨params, result, true, modes, false⟩

def TailBody.width (targetModes : List Mode) :
    {Γ : List Ty} → TailBody S params result Γ → Nat
  | _, .ret value => max value.width (copyWidth result)
  | _, .next args =>
    argsMax fun i =>
      if paramMode params targetModes i = .owned then copyWidth (params.get i) else (args i).width
  | _, .ite cond yes no => max cond.width (max (yes.width targetModes) (no.width targetModes))
  | _, .letE (t := t) value body => t.width + max value.width (body.width targetModes)
  | _, .letPair (s := s) (t := t) value body =>
    s.width + t.width + max value.width (body.width targetModes)

def storeParamsCode (h base : Nat) : List Ty → Program
  | [] => []
  | t :: ts => storeParamsCode h (base + t.width) ts ++ storeCode h base t.types

def TailBody.code (targetModes : List Mode) (h p0 resultBase : Nat) :
    {Γ : List Ty} → TailBody S params result Γ → List Slot → Nat → Nat → Nat → Program
  | _, .ret value, slots, base, exitLabel, _ =>
    value.code h slots base (fun _ => false) ++
      coerceCode h result (value.mode (slots.map Slot.mode)) .owned base ++
      storeCode h resultBase result.types ++ [.br exitLabel]
  | Γ, .next args, slots, base, _, nextLabel =>
    let g := tailSig params result targetModes
    let all := fun i => argsAny fun j => (args j).usesFast i
    let kept := fun i =>
      all i && !(argsAny fun j => callMoves slots (fun _ => false) (g := g) args j &&
        (args j).usesFast i)
    argsCode (fun i =>
      if (params.get i).scalar then (args i).code h slots base all
      else if paramMode params targetModes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots) ++
      releaseWhere Γ slots kept ++ storeParamsCode h p0 params ++ [.br nextLabel]
  | Γ, .ite cond yes no, slots, base, exitLabel, nextLabel =>
    let mid := fun i => yes.usesFast i || no.usesFast i
    cond.code h slots base mid ++
      [.eqzI64, .iff 0 0
        (releaseWhere Γ slots (fun i => mid i && !no.usesFast i) ++
          no.code targetModes h p0 resultBase slots base (exitLabel + 1) (nextLabel + 1))
        (releaseWhere Γ slots (fun i => mid i && !yes.usesFast i) ++
          yes.code targetModes h p0 resultBase slots base (exitLabel + 1) (nextLabel + 1)) [] []]
  | _, .letE (t := t) value body, slots, base, exitLabel, nextLabel =>
    let mode := value.mode (slots.map Slot.mode)
    value.code h slots (base + t.width) (fun i => body.usesFast (i + 1)) ++
      storeCode h base t.types ++
      (if mode = .owned ∧ body.usesFast 0 = false then releaseCode t base else []) ++
      body.code targetModes h p0 resultBase (⟨base, mode⟩ :: slots) (base + t.width)
        exitLabel nextLabel
  | _, .letPair (s := s) (t := t) value body, slots, base, exitLabel, nextLabel =>
    let mode := value.mode (slots.map Slot.mode)
    value.code h slots (base + s.width + t.width) (fun i => body.usesFast (i + 2)) ++
      storeCode h (base + s.width) t.types ++ storeCode h base s.types ++
      (if mode = .owned ∧ body.usesFast 1 = false then releaseCode s base else []) ++
      (if mode = .owned ∧ body.usesFast 0 = false then releaseCode t (base + s.width) else []) ++
      body.code targetModes h p0 resultBase (⟨base + s.width, mode⟩ :: ⟨base, mode⟩ :: slots)
        (base + s.width + t.width) exitLabel nextLabel

def TailFunc.positions (func : TailFunc S) : Nat :=
  (if func.depth then 1 else 0) + 2 * widthSum func.params + func.result.width +
    func.body.width func.modes

def TailFunc.function (func : TailFunc S) (typeIdx : Nat) : Wasm.Function :=
  let p0 := if func.depth then 1 else 0
  let stateBase := p0 + widthSum func.params
  let slots := paramSlots func.params func.modes stateBase
  let h := func.positions
  let resultBase := stateBase + widthSum func.params
  { params := codeParams func.params func.depth
    locals := List.replicate
      (widthSum func.params + func.result.width + func.body.width func.modes) .i64 ++
      List.replicate h .f64
    body := (if func.depth then guardCode else []) ++
      paramCopyCode h p0 (func.params.flatMap Ty.types) ++
      loadCode h p0 (func.params.flatMap Ty.types) ++ storeParamsCode h stateBase func.params ++
      [.block 0 0 [.loop 0 0
        (releaseWhere func.params slots (fun i => !func.body.usesFast i) ++
          func.body.code func.modes h stateBase resultBase slots
            (resultBase + func.result.width) 1 0)
        [] []] [] []] ++ loadCode h resultBase func.result.types
    results := func.result.types
    typeIdx := some typeIdx }

end Verified
