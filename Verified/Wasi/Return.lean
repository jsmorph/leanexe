import Verified.Wasi.After
import Verified.Wasi.Code
import Verified.Wasi.PurePrefix
import Verified.OwnedExpr

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

def returnCost {S : List Sig} {context : List Ty} {type : Ty}
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S)
    (value : Expr S context type) (env : Env context) (slots : List Slot)
    (paid : List Bool) (live : Nat → Bool) (store : Store Unit) (locals : Locals) : Nat :=
  dyingPot store locals env slots paid (fun i => live i || value.uses i) live +
    value.allocs funs flags bounds (slots.map Slot.mode) paid live env +
    coerceCost type (value.mode (slots.map Slot.mode)) .owned (value.denote funs env)

theorem wp_return {World : Type} {S : List Sig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {value : Expr S context type} {env : Env context}
    {slots : List Slot} {paid : List Bool} {live : Nat → Bool} {params : List Value}
    {heap : Heap} {initial : Store World} {locals : Locals} {h base : Nat}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params value env slots paid live pool)
    (form : Encoding.ProgramForm (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (value.code (pool := pool) h slots base live ++
        coerceCode h type (value.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || value.uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || value.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max value.width (copyWidth type) ≤ h)
    (place : value.placeArgs = true)
    (resource : (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (returnCost funs flags bounds value env slots paid live
            (PureTransport.erase initial) locals))) = true →
      ∀ final : Store World, final.host = initial.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap finalStore finalLocals words,
      After env slots (fun i => live i || value.uses i) live base heap initial locals
        (.value type) (value.denote funs env) finalHeap finalStore finalLocals words →
      finalStore.host = initial.host →
      (value.fits funs fits env = true → finalHeap.top.toNat ≤ heap.top.toNat +
        returnCost funs flags bounds value env slots paid live (PureTransport.erase initial)
          locals) →
      wp target rest Q finalStore { finalLocals with values := words.reverse ++ locals.values }
        targetHost) :
    wp target (Relocation.program (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base) ++ rest)
      Q initial locals targetHost := by
  let P : Assertion Unit := fun continuation =>
    match continuation with
    | .Fallthrough finalStore resultLocals =>
        ∃ finalHeap finalLocals words,
          Verified.After env slots (fun i => live i || value.uses i) live base heap
            (PureTransport.erase initial) locals type .owned (value.denote funs env)
            finalHeap finalStore finalLocals words ∧
          resultLocals = { finalLocals with values := words.reverse ++ locals.values } ∧
          (value.fits funs fits env = true → finalHeap.top.toNat ≤ heap.top.toNat +
            returnCost funs flags bounds value env slots paid live
              (PureTransport.erase initial) locals)
    | .Trap _ message => (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (returnCost funs flags bounds value env slots paid live
            (PureTransport.erase initial) locals))) = true ∧ message = "unreachable"
    | _ => False
  have pureCode : wp source (value.code (pool := pool) h slots base live ++
      coerceCode h type (value.mode (slots.map Slot.mode)) .owned base) P
      (PureTransport.erase initial) locals sourceHost := by
    have trap : TrapOK (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (dyingPot (PureTransport.erase initial) locals env slots paid
              (fun i => live i || value.uses i) live +
            value.allocs funs flags bounds (slots.map Slot.mode) paid live env +
            coerceCost type (value.mode (slots.map Slot.mode)) .owned
              (value.denote funs env)))) P := by
      change TrapOK (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (returnCost funs flags bounds value env slots paid live
            (PureTransport.erase initial) locals))) P
      cases failure : (!(value.fits funs fits env) || !decide
        (heap.Within (PureTransport.erase initial) source
          (returnCost funs flags bounds value env slots paid live
            (PureTransport.erase initial) locals))) with
      | false => trivial
      | true => exact fun _ => ⟨failure, rfl⟩
    have execution := spec.owned runtime positions parameters vars at_ safe cap low room place
      (rest := []) trap (fun finalHeap finalStore finalLocals words after top => by
        simp only [wp_nil, P]
        exact ⟨finalHeap, finalLocals, words, after, rfl,
          by simpa only [returnCost, Nat.add_assoc] using top⟩)
    simpa only [List.append_nil] using execution
  have transported := PureTransport.wp_prefix layout profile form closed initial.host pureCode
    (rest := rest) (Q := Q) (targetHost := targetHost) (fun continuation post => by
      cases continuation with
      | Fallthrough finalStore resultLocals =>
          obtain ⟨finalHeap, finalLocals, words, after, rfl, top⟩ := post
          change wp target rest Q (PureTransport.restore initial.host finalStore)
            { finalLocals with values := words.reverse ++ locals.values } targetHost
          apply next finalHeap _ finalLocals words
          · apply After.ofPure
            simpa only [PureTransport.erase_restore] using after
          · rfl
          · exact top
      | Trap finalStore message =>
          obtain ⟨failure, rfl⟩ := post
          exact resource failure _ rfl
      | _ => exact False.elim post)
  simpa only [PureTransport.restore_erase] using transported

end Verified.Wasi
