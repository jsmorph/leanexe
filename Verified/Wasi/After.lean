import Verified.Wasi.EffectAnalysis
import Verified.Wasi.ABI
import Verified.Wasi.PureTransport
import Verified.After

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

def ResultTy.Rep (result : ResultTy) (heap : Heap) (store : Store Unit)
    (words : List Value) (value : result.denote) : Prop :=
  match result, value with
  | .unit, _ => words = []
  | .value type, value => type.Rep .owned heap store words value

def ResultTy.fresh (result : ResultTy) (store : Store Unit)
    (words : List Value) (value : result.denote) : List (Nat × Nat) :=
  match result, value with
  | .unit, _ => []
  | .value type, value => Mode.owned.fresh store type words value

def ResultTy.Apart (result : ResultTy) {context : List Ty} (env : Env context)
    (slots : List Slot) (live : Nat → Bool) (store : Store Unit) (locals : Locals)
    (words : List Value) (value : result.denote) : Prop :=
  match result, value with
  | .unit, _ => True
  | .value type, value => Holds.Apart env slots live store locals type .owned words value

structure After {World : Type} {context : List Ty}
    (env : Env context) (slots : List Slot) (liveIn live : Nat → Bool) (base : Nat)
    (heap : Heap) (store : Store World) (locals : Locals) (result : ResultTy)
    (value : result.denote) (finalHeap : Heap) (finalStore : Store World)
    (finalLocals : Locals) (words : List Value) : Prop where
  step : Step heap (PureTransport.erase store)
    (fun region => Holds.KeepDying env slots liveIn live (PureTransport.erase store) locals region ∧
      regionsDisjoint region ABI.scratch)
    finalHeap (PureTransport.erase finalStore)
    (result.fresh (PureTransport.erase finalStore) words value)
  frame : Frame base locals finalLocals
  holds : Holds env slots live base finalHeap (PureTransport.erase finalStore) finalLocals
  rep : result.Rep finalHeap (PureTransport.erase finalStore) words value
  apart : result.Apart env slots live (PureTransport.erase finalStore) finalLocals words value

theorem After.ofPure {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat}
    {heap finalHeap : Heap} {store finalStore : Store World} {locals finalLocals : Locals}
    {type : Ty} {value : type.denote} {words : List Value}
    (h : Verified.After env slots liveIn live base heap (PureTransport.erase store) locals
      type .owned value finalHeap (PureTransport.erase finalStore) finalLocals words) :
    After env slots liveIn live base heap store locals (.value type) value
      finalHeap finalStore finalLocals words :=
  ⟨h.step.mono (fun _ hKeep => hKeep.1) (fun _ hMember => hMember),
    h.frame, h.holds, h.rep, h.apart⟩

theorem After.unit {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {live : Nat → Bool} {base : Nat} {heap : Heap}
    {store : Store World} {locals : Locals}
    (hHeap : heap.At (PureTransport.erase store))
    (hVars : Holds env slots live base heap (PureTransport.erase store) locals) :
    After env slots live live base heap store locals .unit () heap store locals [] :=
  ⟨Step.refl hHeap _, Frame.refl base locals, hVars, rfl, trivial⟩

end Verified.Wasi
