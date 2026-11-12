import Verified.Wasi.ReadAllCommand
import Verified.Wasi.SysForm

/-! The result of a `sys` command: the words that represent a result of each form, the blocks that
the result owns, and the state after the command from the heap step of its code. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wordsElem_values : ∀ (count : Nat) (words : List UInt64), words.length = count + 1 →
    (wordsElem count).values (wordsValue count words) = words.map .i64
  | 0, [_], _ => rfl
  | count + 1, word :: words, length => by
    simp only [wordsElem, wordsValue, Elem.values, List.headD_cons, List.tail_cons, List.map_cons]
    rw [wordsElem_values count words (by simpa using length)]
    rfl
  | 0, [], length | 0, _ :: _ :: _, length | _ + 1, [], length => by simp at length

theorem wordsBytes_rep {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (rep : Bytes.Rep heap store root length bytes) :
    ∀ (count : Nat) (words : List UInt64), words.length = count →
      (wordsBytesTy count).Rep .owned heap store (words.map .i64 ++ [.i64 root, .i64 length])
        (wordsBytesValue count words bytes)
  | 0, [], _ => ⟨root, length, rfl, rep⟩
  | count + 1, word :: words, h => by
    refine ⟨[.i64 word], words.map .i64 ++ [.i64 root, .i64 length], rfl, rfl,
      wordsBytes_rep rep count words (by simpa using h), ?_⟩
    intro _ block member
    exact nomatch member
  | 0, _ :: _, h | _ + 1, [], h => by simp at h

theorem wordsBytes_blocks (store : Store Unit) (root length : UInt64) (bytes : LeanExe.Bytes) :
    ∀ (count : Nat) (words : List UInt64), words.length = count →
      (wordsBytesTy count).blocks store (words.map .i64 ++ [.i64 root, .i64 length])
        (wordsBytesValue count words bytes) = Bytes.regions store root
  | 0, [], _ => Bytes.roots_regions store root length
  | count + 1, word :: words, h => by
    simp only [wordsBytesTy, Ty.blocks, List.map_cons, List.cons_append, Ty.width,
      Elem.width_word, List.drop_succ_cons, List.drop_zero, List.nil_append]
    exact wordsBytes_blocks store root length bytes count words (by simpa using h)
  | 0, _ :: _, h | _ + 1, [], h => by simp at h

/-- The state after a `sys` command whose code leaves the words of `value`, from the step of its
code, which keeps every region apart from the scratch area, and the representation of the result:
argument variables that die are words, which own no blocks. -/
theorem sys_after {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap finalHeap : Heap}
    {initial final : Store World} {locals finalLocals : Locals} {type : Ty} {value : type.denote}
    {words : List Value} {fresh : List (Nat × Nat)}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (selected : ∀ i, live i = true → liveIn i = true)
    (step : Step heap (PureTransport.erase initial) (fun region => regionsDisjoint region ABI.scratch)
      finalHeap (PureTransport.erase final) fresh)
    (frame : Frame base locals finalLocals)
    (rep : type.Rep .owned finalHeap (PureTransport.erase final) words value)
    (blocks : type.blocks (PureTransport.erase final) words value = fresh) :
    After env slots liveIn live base heap initial locals (.value type) value finalHeap final
      finalLocals words := by
  have vars' := vars.live_mono selected
  have apart' := apart.mono selected
  refine ⟨?_, frame, vars'.step_scratch apart' step frame, rep, ?_⟩
  · change Step heap _ _ finalHeap _ (type.blocks (PureTransport.erase final) words value)
    rw [blocks]
    exact step.mono (fun _ kept => kept.2) (fun _ member => member)
  · intro other x hLive _ otherWords held width resultRegion hResult region member
    have heldBefore := (vars'.hold_agree frame hLive width).mp held
    obtain ⟨same, freshApart⟩ := vars'.regions_after step hLive heldBefore width
      (fun block hBlock =>
        regionsDisjoint_symm (apart' other x hLive otherWords heldBefore width block hBlock))
    rw [same] at member
    have hResult' : resultRegion ∈ fresh := by
      rw [← blocks]
      exact hResult
    exact regionsDisjoint_symm (freshApart region member resultRegion hResult')

end Verified.Wasi
