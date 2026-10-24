import Verified.Wasi.PurePrefix
import Verified.Heap

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopRelease {World : Type} {source target : Wasm.Module}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv World} {context : List Ty}
    {env : Env context} {slots : List Slot} {type : Ty} {state : type.denote}
    {stateSlot scratch : Nat} {releaseIn bodyIn : Nat → Bool} {used : Bool}
    {heap : Heap} {initial : Store World} {locals : Locals} {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (form : Encoding.ProgramForm (releaseCode type stateSlot))
    (closed : Relocation.programClosed source.funcs.length (releaseCode type stateSlot) = true)
    (vars : Holds (.cons state env) (⟨stateSlot, .owned⟩ :: slots) releaseIn scratch heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (head : releaseIn 0 = true) (bodyHead : bodyIn 0 = used)
    (selected : ∀ i, bodyIn i = true → releaseIn i = true)
    (next : ∀ finalHeap final,
      Evolves (.cons state env) (⟨stateSlot, .owned⟩ :: slots) releaseIn bodyIn scratch heap
        (PureTransport.erase initial) locals finalHeap (PureTransport.erase final) locals →
      finalHeap.top = heap.top → final.host = initial.host → wp target rest Q final locals targetHost) :
    wp target ((if used = false then Relocation.program (releaseCode type stateSlot) else []) ++ rest)
      Q initial locals targetHost := by
  let indices : List Nat := if used = false then [0] else []
  let code := indices.flatMap (releaseVar (type :: context) (⟨stateSlot, .owned⟩ :: slots))
  have codeEq : code = if used = false then releaseCode type stateSlot else [] := by
    cases used <;> simp [code, indices, releaseVar]
  have codeForm : Encoding.ProgramForm code := by
    rw [codeEq]
    cases used with
    | false => exact form
    | true => exact .nil
  have codeClosed : Relocation.programClosed source.funcs.length code = true := by
    rw [codeEq]
    cases used with
    | false => exact closed
    | true => rfl
  let P : Assertion Unit := fun continuation => match continuation with
    | .Fallthrough final after => ∃ finalHeap,
        Evolves (.cons state env) (⟨stateSlot, .owned⟩ :: slots) releaseIn bodyIn scratch heap
          (PureTransport.erase initial) locals finalHeap final locals ∧
          after = locals ∧ finalHeap.top = heap.top
    | _ => False
  have execution : wp source code P (PureTransport.erase initial) locals sourceHost := by
    have pureCode := wp_releaseVars (host := sourceHost) runtime indices
      (by cases used <;> simp [indices]) vars at_
      (fun i member => by
        cases used with
        | false =>
            have equal : i = 0 := by simpa [indices] using member
            simpa only [equal] using head
        | true => simp [indices] at member)
      (rest := []) (Q := P) (fun finalHeap final evolution top => by
        have narrowed := evolution.mono (live' := bodyIn) (fun i isLive => by
          cases truth : used with
          | false =>
              have nonzero : i ≠ 0 := by
                intro equal
                subst i
                rw [bodyHead, truth] at isLive
                exact nomatch isLive
              simp [indices, truth, selected i isLive, nonzero]
          | true => simpa only [indices, truth, Bool.true_eq_false, ite_false,
              List.contains_nil, Bool.not_false, Bool.and_true] using selected i isLive)
        rw [wp_nil]
        exact ⟨finalHeap, narrowed, rfl, top⟩)
    simpa only [code, List.append_nil] using pureCode
  have transported := PureTransport.wp_prefix layout profile codeForm codeClosed initial.host execution
    (rest := rest) (Q := Q) (targetHost := targetHost) (fun continuation post => by
      cases continuation with
      | Fallthrough final after =>
          obtain ⟨finalHeap, evolution, rfl, top⟩ := post
          apply next finalHeap (PureTransport.restore initial.host final)
          · simpa only [PureTransport.erase_restore] using evolution
          · exact top
          · rfl
      | _ => exact False.elim post)
  cases used <;>
    simpa only [codeEq, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      Relocation.program, PureTransport.restore_erase] using transported

end Verified.Wasi
