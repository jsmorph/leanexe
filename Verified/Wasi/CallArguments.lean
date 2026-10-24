import Verified.ArgsCorrect
import Verified.ArgumentMoves
import Verified.Wasi.Code
import Verified.Wasi.PurePrefix

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem EffectSig.callMoves_moved {S : List Sig} {context : List Ty}
    (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr S context (signature.params.get i))
    (variableArgs : ∀ i : Fin signature.params.length,
      signature.mode i = .owned → ∃ x, args i = .var x) :
    ∀ index, (argsAny fun j => signature.callMoves slots live args j &&
        (args j).uses index) = true →
      ∃ j x, args j = .var x ∧ x.index = index ∧ signature.mode j = .owned ∧
        (slots.getD index default).mode = .owned ∧ live index = false ∧
        ∀ other, other ≠ j → (signature.params.get other).scalar = false →
          (args other).uses index = false :=
  arguments_moved signature.mode slots live args (signature.callMoves slots live args)
    (fun _ => rfl) variableArgs

theorem relocate_argsCode {n : Nat} (code : Fin n → Program) :
    Relocation.program (argsCode code) = argsCode (fun i => Relocation.program (code i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [argsCode, Relocation.program_append, ih]

def argumentCost {S : List Sig} {context params : List Ty}
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (modes : Nat → Mode) (args : (i : Fin params.length) → Expr S context (params.get i))
    (env : Env context) (slots : List Slot) (all kept : Nat → Bool) : Nat :=
  argsSum (argCost funs flags bounds (slots.map Slot.mode) [] all kept modes args env)

structure ArgumentsAfter {World : Type} {S : List Sig} {context params : List Ty}
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S)
    (modes : Nat → Mode) (args : (i : Fin params.length) → Expr S context (params.get i))
    (env : Env context) (slots : List Slot) (all kept : Nat → Bool) (base : Nat)
    (heap : Heap) (initial : Store World) (locals : Locals)
    (finalHeap : Heap) (final : Store World) (finalLocals : Locals) (words : List Value)
    (fresh : List (Nat × Nat)) : Prop where
  step : Step heap (PureTransport.erase initial) (fun _ => True)
    finalHeap (PureTransport.erase final) fresh
  frame : Frame base locals finalLocals
  holds : Holds env slots all base finalHeap (PureTransport.erase final) finalLocals
  rep : Env.Rep modes finalHeap (PureTransport.erase final) words
    (Env.ofFn fun i => (args i).denote funs env)
  separate : Separate (PureTransport.erase final)
    (Env.moves (PureTransport.erase final) modes words
      (Env.ofFn fun i => (args i).denote funs env))
    (Env.reads (PureTransport.erase final) modes words
      (Env.ofFn fun i => (args i).denote funs env))
  movesApart : ∀ region, (∀ block ∈ fresh, regionsDisjoint region block) →
    Holds.KeepDying env slots
      (fun k => argsAny fun i => modes i == .owned && (args i).uses k && !kept k)
      (fun _ => false) (PureTransport.erase initial) locals region →
    Apart (PureTransport.erase final)
      (Env.moves (PureTransport.erase final) modes words
        (Env.ofFn fun i => (args i).denote funs env)) region
  borrowedApart : ∀ region, Holds.ApartFrom env slots
      (fun k => argsAny fun i => modes i == .borrowed && !(params.get i).scalar &&
        (args i).uses k) (PureTransport.erase initial) locals region →
    ∀ other ∈ Env.reads (PureTransport.erase final) modes words
      (Env.ofFn fun i => (args i).denote funs env), regionsDisjoint region other
  top : argsAll (fun i => (args i).fits funs fits env) = true →
    finalHeap.top.toNat ≤ heap.top.toNat + argumentCost funs flags bounds modes args env slots all kept

theorem wp_arguments {World : Type} {S : List Sig} {context params : List Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {modes : Nat → Mode}
    {args : (i : Fin params.length) → Expr S context (params.get i)}
    {env : Env context} {slots : List Slot} {all kept : Nat → Bool} {pv : List Value}
    {heap : Heap} {initial : Store World} {locals : Locals} {h base : Nat}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : ∀ i env slots paid live,
      CodeSpec (pool := pool) source funs flags bounds fits sourceHost pv (args i) env slots paid live)
    (uses : ∀ i k, (args i).uses k = true → all k = true)
    (keptSelected : ∀ k, kept k = true → all k = true)
    (ownedHeap : ∀ i : Fin params.length, modes i = .owned → (params.get i).scalar = false)
    (places : ∀ i, (params.get i).scalar = false → modes i = .borrowed →
      (args i).isPlace = true)
    (owned : ∀ i : Fin params.length, modes i = .owned →
      ∃ x : Var context (params.get i), args i = .var x ∧
        (kept x.index = false → (slots.getD x.index default).mode = .owned ∧
          ∀ j : Fin params.length, j ≠ i → (params.get j).scalar = false →
            (args j).uses x.index = false))
    (placeArgs : ∀ i, (args i).placeArgs = true)
    (positions : locals.positions = h) (parameters : locals.params = pv)
    (vars : Holds env slots all base heap (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots all heap (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : ∀ i : Fin params.length,
      base + (if modes i = .owned then copyWidth (params.get i) else (args i).width) ≤ h)
    (form : Encoding.ProgramForm (argsCode (fun i =>
      if (params.get i).scalar then (args i).code (pool := pool) h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots)))
    (closed : Relocation.programClosed source.funcs.length (argsCode (fun i =>
      if (params.get i).scalar then (args i).code (pool := pool) h slots base all
      else if modes i = .owned then (args i).ownedCode h slots base kept
      else (args i).placeCode h slots)) = true)
    (resource : (!(argsAll fun i => (args i).fits funs fits env) ||
        !decide (heap.Within (PureTransport.erase initial) source
          (argumentCost funs flags bounds modes args env slots all kept))) = true →
      ∀ final : Store World, final.host = initial.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap finalStore finalLocals words fresh,
      ArgumentsAfter funs flags bounds fits modes args env slots all kept base
        heap initial locals finalHeap finalStore finalLocals words fresh →
      finalStore.host = initial.host →
      wp target rest Q finalStore { finalLocals with values := words.reverse ++ locals.values }
        targetHost) :
    wp target (argsCode (fun i => Relocation.program (
        if (params.get i).scalar then (args i).code (pool := pool) h slots base all
        else if modes i = .owned then (args i).ownedCode h slots base kept
        else (args i).placeCode h slots)) ++ rest) Q initial locals targetHost := by
  let failure := !(argsAll fun i => (args i).fits funs fits env) ||
    !decide (heap.Within (PureTransport.erase initial) source
      (argumentCost funs flags bounds modes args env slots all kept))
  let P : Assertion Unit := fun continuation =>
    match continuation with
    | .Fallthrough finalStore resultLocals =>
        ∃ finalHeap finalLocals words fresh,
          ArgumentsAfter funs flags bounds fits modes args env slots all kept base heap
            initial locals finalHeap (PureTransport.restore initial.host finalStore)
            finalLocals words fresh ∧
          resultLocals = { finalLocals with values := words.reverse ++ locals.values }
    | .Trap _ message => failure = true ∧ message = "unreachable"
    | _ => False
  have trap : TrapOK failure P := by
    cases failed : failure with
    | false => trivial
    | true => exact fun _ => ⟨failed, rfl⟩
  have pureCode := args_spec (pool := pool) (funs := funs) (flags := flags)
    (bounds := bounds) (fits := fits) (host := sourceHost) (pv := pv)
    (all := all) (kept := kept) runtime (paid := [])
    (d := !(argsAll fun i => (args i).fits funs fits env)) (a := true)
    modes args spec uses keptSelected ownedHeap
    places owned placeArgs
    (fun i failed => by
      simp only [Bool.not_eq_true'] at failed ⊢
      exact argsAll_false (fun j => (args j).fits funs fits env) i failed)
    (fun _ _ => rfl) heap (PureTransport.erase initial) locals positions parameters vars at_
    safe cap low room [] P (by change TrapOK failure P; exact trap)
    (fun finalHeap finalStore finalLocals words fresh step frame holds rep separate
        movesApart borrowedApart top _ => by
      simp only [wp_nil, P]
      exact ⟨finalHeap, finalLocals, words, fresh,
        ⟨by simpa only [PureTransport.erase_restore] using step, frame,
          by simpa only [PureTransport.erase_restore] using holds,
          by simpa only [PureTransport.erase_restore] using rep,
          by simpa only [PureTransport.erase_restore] using separate,
          by simpa only [PureTransport.erase_restore] using movesApart,
          by simpa only [PureTransport.erase_restore] using borrowedApart,
          fun fitsAll => top (by simp only [Bool.not_eq_false']; exact fitsAll)⟩, rfl⟩)
  have transported := PureTransport.wp_prefix layout profile form closed initial.host
    (by simpa only [List.append_nil] using pureCode)
    (rest := rest) (Q := Q) (targetHost := targetHost) (fun continuation post => by
      cases continuation with
      | Fallthrough finalStore resultLocals =>
          obtain ⟨finalHeap, finalLocals, words, fresh, after, rfl⟩ := post
          exact next finalHeap _ finalLocals words fresh after rfl
      | Trap finalStore message =>
          obtain ⟨failed, rfl⟩ := post
          exact resource failed _ rfl
      | _ => exact False.elim post)
  simpa only [PureTransport.restore_erase, relocate_argsCode] using transported

end Verified.Wasi
