import Verified.Wasi.FunctionRun
import Verified.Wasi.LoopAfter
import Verified.Wasi.CommandValue

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_store_owned_result {World : Type}
    {context : List Ty} {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool}
    {base h : Nat} {result : ResultTy} {value : result.denote} {words : List Value}
    {target : Module} {targetHost : HostEnv World}
    {initial final : Store World} {heap finalHeap : Heap} {locals finalLocals : Locals}
    {P : Assertion World}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (selected : ∀ i, live i = true → liveIn i = true)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + result.width ≤ h)
    (after : After env slots liveIn live (base + result.width) heap initial locals result value
      finalHeap final finalLocals words)
    (next : ∀ stored : Locals,
      After env slots liveIn live base heap initial locals result value
        finalHeap final stored words →
      LocalsHold stored base result.types words → P (.Fallthrough final stored)) :
    wp target (storeCode h base result.types) P final
      { finalLocals with values := words.reverse ++ locals.values } targetHost := by
  have reduced := after.lower vars selected (Nat.le_add_right base result.width)
  have stored : wp target (storeCode h base result.types ++ []) P final
      { finalLocals with values := words.reverse ++ locals.values } targetHost := by
    refine wp_storeCode words h base result.types finalLocals locals.values
      (after.rep.length.trans result.types_length.symm)
      (after.frame.positions.trans positions)
      (by rw [after.frame.params]; exact low)
      (by rw [after.frame.positions, positions, result.types_length]; exact room) ?_
    intro stored frame held _
    rw [wp_nil]
    have frame' : Frame base finalLocals { stored with values := locals.values } :=
      ⟨frame.params, frame.length, frame.below, frame.below32⟩
    exact next _ (reduced.reframe frame') held
  simpa only [List.append_nil] using stored

end Verified.Wasi
