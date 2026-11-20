import Verified.Shim.Trace

/-!
The descriptors that the shim's layer events name.  The shim holds open the numbers of
`openNumbers I events`, which it reads from the layer events before each call, and refuses every
other number as a directory or file descriptor.  `NamesHeld I events ls` states that the layer
events `ls`, made after `events`, name only those numbers or a standard stream: the descriptor of
each `read` and `write` is 0, 1, or 2 or a number that the shim holds open after the events before
it, and the descriptor of each `close` and `statx` and the directory of each `openat2` is such a
number.
`footprint_namesHeld` proves it of every run that `Footprint` describes, for every command and
every reply sequence, so the shim never names a descriptor above 2 that neither the launcher
granted as 3 nor an `openat2` returned.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

/-- The layer events `ls`, made after `events`, name only standard streams and the numbers that
the shim holds open: the descriptor of each `read` and `write` is 0, 1, or 2 or a number of
`openNumbers I` after the events before it, and the descriptor of each `close` and `statx` and the
directory of each `openat2` is a number of `openNumbers I` after the events before it. -/
def NamesHeld (I : Launch) (events ls : List Linux.Event) : Prop :=
  ∀ pre x post, ls = pre ++ x :: post →
    (x.call ∈ [Linux.readCall, Linux.writeCall] →
      Linux.arg x.args 0 ∈ ([0, 1, 2] : List UInt64) ∨
        Linux.arg x.args 0 ∈ openNumbers I (events ++ pre)) ∧
    (x.call ∈ [Linux.openat2Call, Linux.closeCall, Linux.statxCall] →
      Linux.arg x.args 0 ∈ openNumbers I (events ++ pre))

theorem openAfter_append (opened : List UInt64) :
    ∀ l m : List Linux.Event,
      Linux.openAfter opened (l ++ m) = Linux.openAfter (Linux.openAfter opened l) m := by
  intro l
  induction l generalizing opened with
  | nil => intro m; rfl
  | cons e l ih =>
    intro m
    simp only [List.cons_append, Linux.openAfter]
    split
    · exact ih _ m
    · split
      · exact ih _ m
      · exact ih _ m

theorem eagain_large : ¬(0 - 11 : UInt64).toNat < 2 ^ 31 := by decide

theorem openat2_ne_close : Linux.openat2Call ≠ Linux.closeCall := by decide

/-- An `openat2` whose result is not a descriptor below `2^31` keeps the layer's open
descriptors. -/
theorem openAfter_unopened {opened : List UInt64} {e : Linux.Event}
    (call : e.call = Linux.openat2Call) (large : ¬e.ret.toNat < 2 ^ 31) (l : List Linux.Event) :
    Linux.openAfter opened (e :: l) = Linux.openAfter opened l := by
  simp only [Linux.openAfter, call, large, and_false, ↓reduceIte, openat2_ne_close]

/-- The calls of `path_open` before its last `openat2` failed with `EAGAIN`, which opens nothing,
and each names the directory. -/
theorem openCalls_split {L : ShimLayout} {dir : UInt64} {path how : List UInt8}
    {reply : Transfer (List Bytes)} (opened : List UInt64) :
    ∀ {calls : Nat} {l : List Linux.Event}, OpenCalls L dir path how calls l reply →
      ∀ pre x post, l = pre ++ x :: post →
        Linux.openAfter opened pre = opened ∧ x.call = Linux.openat2Call ∧ Linux.arg x.args 0 = dir
  | _, [], h => h.elim
  | _, e :: l, ⟨ret, event, rest⟩ => by
    subst event
    intro pre x post same
    cases pre with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj same
      exact ⟨rfl, rfl, rfl⟩
    | cons first pre =>
      obtain ⟨rfl, tail⟩ := List.cons.inj same
      split at rest
      · rename_i again
        obtain ⟨keep, call, named⟩ := openCalls_split opened rest pre x post tail
        refine ⟨?_, call, named⟩
        rw [openAfter_unopened rfl (by rw [again.1]; exact eagain_large)]
        exact keep
      · obtain ⟨rfl, -⟩ := rest
        cases pre <;> simp at tail

/-- A `path_open` that passes `openCheck` names a directory that `opened` holds. -/
theorem openCheck_held {opened : List UInt64} {dir oflags fdflags : UInt64} {path : Bytes}
    (h : openCheck opened dir oflags path fdflags = 0) : dir ∈ opened := by
  by_contra outside
  unfold openCheck at h
  split_ifs at h
  all_goals exact absurd h (by decide)

/-- The single layer event of an image. -/
theorem single_split {y x : Linux.Event} {pre post : List Linux.Event}
    (h : [y] = pre ++ x :: post) : pre = [] ∧ x = y := by
  cases pre with
  | nil =>
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact ⟨rfl, rfl⟩
  | cons first pre => cases pre <;> simp at h

theorem empty_split {x : Linux.Event} {pre post : List Linux.Event} :
    ([] : List Linux.Event) ≠ pre ++ x :: post := by
  cases pre <;> simp

/-- An event of a call other than `read`, `write`, `openat2`, `close`, and `statx` names no
descriptor. -/
theorem names_other {I : Launch} {events pre : List Linux.Event} {x : Linux.Event}
    (other : x.call ∈ [Linux.clockGettimeCall, Linux.getrandomCall]) :
    (x.call ∈ [Linux.readCall, Linux.writeCall] →
      Linux.arg x.args 0 ∈ ([0, 1, 2] : List UInt64) ∨
        Linux.arg x.args 0 ∈ openNumbers I (events ++ pre)) ∧
    (x.call ∈ [Linux.openat2Call, Linux.closeCall, Linux.statxCall] →
      Linux.arg x.args 0 ∈ openNumbers I (events ++ pre)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at other
  rcases other with same | same <;> rw [same] <;>
    exact ⟨fun inside => absurd inside (by decide), fun inside => absurd inside (by decide)⟩

/-- The layer events of an image name only standard streams and the numbers that the shim holds
open. -/
theorem image_namesHeld {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Wasi.Event} {l : List Linux.Event} (image : Image F L I events e l) :
    NamesHeld I events l := by
  intro pre x post same
  cases e with
  | read count reply =>
    obtain ⟨y, a, rfl, call, args, _⟩ := image
    obtain ⟨rfl, rfl⟩ := single_split same
    refine ⟨fun _ => .inl ?_, fun inside => ?_⟩
    · rw [args]
      simp [Linux.arg]
    · rw [call] at inside
      exact absurd inside (by decide)
  | write output bytes reply =>
    obtain ⟨y, a, rfl, call, args, _⟩ := image
    obtain ⟨rfl, rfl⟩ := single_split same
    refine ⟨fun _ => .inl ?_, fun inside => ?_⟩
    · rw [args]
      cases output <;> simp [Linux.arg, Output.fd]
    · rw [call] at inside
      exact absurd inside (by decide)
  | exit code =>
    cases image
    exact absurd same empty_split
  | exitTrap code message =>
    cases image
    exact absurd same empty_split
  | sys call args reply =>
    obtain ⟨_, image⟩ := image
    have member := sysImage_mem image
    simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · rw [sysImage_clock] at image
      unfold ClockImage at image
      split at image
      · split at image
        · obtain ⟨_, _, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          exact names_other (by simp)
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_random] at image
      unfold RandomImage at image
      split at image
      · obtain ⟨_, image⟩ := image
        exact names_other (by simp [randomCalls_calls image x (by rw [same]; simp)])
      · exact image.elim
    · rw [sysImage_argsSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      exact absurd same empty_split
    · rw [sysImage_args] at image
      obtain ⟨_, rfl, _⟩ := image
      exact absurd same empty_split
    · rw [sysImage_environSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      exact absurd same empty_split
    · rw [sysImage_environ] at image
      obtain ⟨_, rfl, _⟩ := image
      exact absurd same empty_split
    · rw [sysImage_open] at image
      unfold OpenImage at image
      split at image
      · split at image
        · obtain ⟨keep, call, named⟩ := openCalls_split
            (Linux.openAfter (if I.preopen then [3] else []) events) image pre x post same
          have held : Linux.arg x.args 0 ∈ openNumbers I (events ++ pre) := by
            rw [openNumbers, openAfter_append, keep, ← openNumbers, named]
            exact openCheck_held (by assumption)
          refine ⟨fun inside => ?_, fun _ => held⟩
          rw [call] at inside
          exact absurd inside (by decide)
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_close] at image
      unfold CloseImage at image
      split at image
      · split at image
        · obtain ⟨_, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          refine ⟨fun inside => absurd
            (show Linux.closeCall ∈ [Linux.readCall, Linux.writeCall] from inside) (by decide),
            fun _ => ?_⟩
          simp only [Linux.arg, List.getD_cons_zero, List.append_nil]
          assumption
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_read] at image
      unfold HandleReadImage at image
      split at image
      · split at image
        · obtain ⟨_, _, _, _, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          refine ⟨fun _ => .inr ?_, fun inside => absurd
            (show Linux.readCall ∈ [Linux.openat2Call, Linux.closeCall, Linux.statxCall] from
              inside)
            (by decide)⟩
          simp only [Linux.arg, List.getD_cons_zero, List.append_nil]
          assumption
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_write] at image
      unfold HandleWriteImage at image
      split at image
      · split at image
        · obtain ⟨_, _, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          refine ⟨fun _ => .inr ?_, fun inside => absurd
            (show Linux.writeCall ∈ [Linux.openat2Call, Linux.closeCall, Linux.statxCall] from
              inside)
            (by decide)⟩
          simp only [Linux.arg, List.getD_cons_zero, List.append_nil]
          assumption
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_prestat] at image
      unfold PrestatImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_dirName] at image
      unfold DirNameImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        exact absurd same empty_split
      · exact image.elim
    · rw [sysImage_filestat] at image
      unfold FilestatImage at image
      split at image
      · split at image
        · obtain ⟨_, _, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          refine ⟨fun inside => absurd
            (show Linux.statxCall ∈ [Linux.readCall, Linux.writeCall] from inside) (by decide),
            fun _ => ?_⟩
          simp only [Linux.arg, List.getD_cons_zero, List.append_nil]
          assumption
        · obtain ⟨rfl, _⟩ := image
          exact absurd same empty_split
      · exact image.elim

/-- The layer events of images of a WASI trace name only standard streams and the numbers that the
shim holds open. -/
theorem images_namesHeld {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {trace : List Wasi.Event} {ls : List Linux.Event} (h : Images F L I events trace ls) :
    NamesHeld I events ls := by
  induction h with
  | nil =>
    intro pre x post same
    exact absurd same empty_split
  | @cons events e l es ls image _ ih =>
    intro pre x post same
    rcases List.append_eq_append_iff.mp same with ⟨rest, rfl, tail⟩ | ⟨middle, head, tail⟩
    · have found := ih rest x post tail
      simpa only [List.append_assoc] using found
    · cases middle with
      | nil =>
        simp only [List.append_nil] at head
        subst head
        simp only [List.nil_append] at tail
        have found := ih [] x post tail.symm
        simpa only [List.append_nil] using found
      | cons y middle =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj tail
        exact image_namesHeld image pre x middle head

/-- Every run that `Footprint` describes, with the layer events `ls` after the initial ones, names
only standard streams and the numbers that the shim holds open, for every command and every reply
sequence. -/
theorem footprint_namesHeld {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {action : Action Unit} {initial : Observed LinuxWorld}
    {aborts : Bool} {final : Store (Observed LinuxWorld)} {message : String}
    (footprint : Footprint F L I replies action initial aborts (.Trap final message))
    {ls : List Linux.Event} (grown : final.host.world.events = initial.world.events ++ ls) :
    NamesHeld I initial.world.events ls := by
  obtain ⟨trace, ls', grown', images, _⟩ := footprint
  have same : ls' = ls := List.append_cancel_left (grown'.symm.trans grown)
  subst same
  exact images_namesHeld images

end Verified.Shim
