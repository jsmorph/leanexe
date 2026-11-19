import Verified.Shim.Host

/-!
The images of a WASI trace under the shim's host as lists of layer events.  `images_split` splits
the images of a trace that is the concatenation of two traces into the images of each, the second
after the events of the first, and `images_mem` finds the image of each event of a trace among the
images of the trace.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi

theorem images_split {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {events : List Linux.Event} {first rest : List Wasi.Event} {ls : List Linux.Event},
      Images F L I events (first ++ rest) ls →
        ∃ l l', ls = l ++ l' ∧ Images F L I events first l ∧ Images F L I (events ++ l) rest l'
  | _, [], _, ls, h => ⟨[], ls, rfl, .nil, by simpa using h⟩
  | _, _ :: _, _, _, h => by
    rw [List.cons_append] at h
    cases h with
    | cons image tail =>
      obtain ⟨l, l', rfl, first, rest⟩ := images_split tail
      exact ⟨_ ++ l, l', by rw [List.append_assoc], .cons image first,
        by rwa [← List.append_assoc]⟩

/-- The image of each event of a trace lies among the images of the trace. -/
theorem images_mem {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {events : List Linux.Event} {T : List Event} {ls : List Linux.Event},
      Images F L I events T ls → ∀ e ∈ T,
        ∃ before l, Image F L I before e l ∧ ∀ x ∈ l, x ∈ ls
  | _, _, _, .nil, _, member => nomatch member
  | _, _, _, .cons image rest, e, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, _, image, fun x m => List.mem_append_left _ m⟩
    · obtain ⟨before, l, found, sub⟩ := images_mem rest e member
      exact ⟨before, l, found, fun x m => List.mem_append_right _ (sub x m)⟩

end Verified.Shim
