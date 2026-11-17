import Verified.Shim.Trace
import Verified.Wasi.Handles

/-!
The bracket corollary of the footprint theorem.  For a command that passes the handle check, every
run that `Footprint` describes keeps the discipline of `withOpen` (`bracketRuns_command`), and
when the kernel returns from `openat2` only descriptors that are not open, step 5's `FreshOpens`
from the open descriptors 0 to 3, the layer events name only open descriptors (`NamesOpen`): the
descriptor of each `read`, `write`, and `close` and the directory of each `openat2` is 0, 1, 2, 3,
or a descriptor that an earlier `openat2` returned and no `close` has released, and no `close`
closes 0 to 3.  The proof carries `WellBracketed.descriptors` from the WASI trace to its images:
the layer's open descriptors after the images of a prefix are the WASI trace's
(`image_openAfter`), and the layer's `FreshOpens` gives the WASI trace's (`images_fresh`).
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

/-- The layer events `ls` name only open descriptors: the descriptor of each `read`, `write`, and
`close` and the directory of each `openat2` is open after the events before it, from the open
descriptors 0 to 3, and no `close` closes 0 to 3. -/
def NamesOpen (ls : List Linux.Event) : Prop :=
  ∀ pre x post, ls = pre ++ x :: post →
    (x.call ∈ [Linux.readCall, Linux.writeCall, Linux.openat2Call, Linux.closeCall] →
      Linux.arg x.args 0 ∈ Linux.openAfter [0, 1, 2, 3] pre) ∧
    (x.call = Linux.closeCall → Linux.arg x.args 0 ∉ [0, 1, 2, 3])

/-- The runs of a command whose `main` passes the handle check keep the discipline of `withOpen`,
its exit included. -/
theorem bracketRuns_command {pureSigs : List Sig} {effectSigs : List EffectSig}
    (pureFuns : Funs pureSigs) (program : EffectProg pureSigs effectSigs)
    (helpers : List (List Bool)) (checked : program.HandleCheck helpers)
    (main : EffectMain effectSigs) (args : Env main.signature.params)
    (unmarked : (main.callee.marks helpers).all (· == false) = true) (native : Action UInt64)
    (related : Action.Rel (fun native flat : UInt64 => flat = native) native
      ((program.funs pureFuns).get main.callee args)) :
    (Action.bind native fun status => Action.exit (α := Unit) status).BracketRuns := by
  have handles := program.handlesSafe pureFuns helpers checked main.callee args []
    (EnvMarked.unmarked unmarked)
  exact Action.BracketRuns.of_rel (main.related_action pureFuns program args native related)
    (Action.Handles.bracketRuns (Action.Handles.bind_iff.mpr (handles.mono fun _ _ _ => trivial)))

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

theorem freshOpens_append {opened : List UInt64} {l m : List Linux.Event}
    (h : Linux.FreshOpens opened (l ++ m)) :
    Linux.FreshOpens opened l ∧ Linux.FreshOpens (Linux.openAfter opened l) m := by
  constructor
  · intro pre e post same opens
    exact h pre e (post ++ m) (by rw [same]; simp) opens
  · intro pre e post same opens
    have fresh := h (l ++ pre) e post (by rw [same]; simp) opens
    rwa [openAfter_append] at fresh

theorem descriptor_small {fd : UInt64} (small : fd.toNat < 2 ^ 32) : Linux.descriptor fd = fd := by
  apply UInt64.toNat_inj.mp
  rw [Linux.descriptor, UInt64.toNat_and,
    show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt small]

/-- A descriptor that `openReply` returns. -/
theorem openReply_descriptor {ret : UInt64} {outputs : List Bytes}
    (h : openReply ret = .returned 0 outputs) :
    ret.toNat < 2 ^ 31 ∧ openedDescriptor outputs = ret := by
  unfold openReply at h
  by_cases small : ret.toNat < 2 ^ 31
  · simp only [small, ↓reduceIte] at h
    obtain ⟨_, rfl⟩ := Transfer.returned.inj h
    refine ⟨small, ?_⟩
    simp only [openedDescriptor, Reply.word, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    rw [littleEndian_leBytes (by omega) (by omega)]
    exact UInt64.ofNat_toNat
  · simp only [small, ↓reduceIte] at h
    by_cases error : Linux.isError ret = true
    · simp only [error, ↓reduceIte] at h
      exact absurd (Transfer.returned.inj h).1 (errnoOf_valid _).2
    · simp only [error, Bool.false_eq_true, ↓reduceIte] at h
      cases h

theorem eagain_large : ¬(0 - 11 : UInt64).toNat < 2 ^ 31 := by decide

theorem openat2_opens : Linux.openat2Call.opens = true := rfl

theorem openat2_ne_close : Linux.openat2Call ≠ Linux.closeCall := by decide

/-- An `openat2` whose result is not a descriptor below `2^31` keeps the open descriptors. -/
theorem openAfter_unopened {opened : List UInt64} {e : Linux.Event}
    (call : e.call = Linux.openat2Call) (large : ¬e.ret.toNat < 2 ^ 31) (l : List Linux.Event) :
    Linux.openAfter opened (e :: l) = Linux.openAfter opened l := by
  simp only [Linux.openAfter, call, large, and_false, ↓reduceIte, openat2_ne_close]

/-- Events that neither open nor close keep the open descriptors. -/
theorem openAfter_none {opened : List UInt64} :
    ∀ {l : List Linux.Event}, (∀ x ∈ l, x.call.opens = false ∧ x.call ≠ Linux.closeCall) →
      Linux.openAfter opened l = opened
  | [], _ => rfl
  | x :: l, quiet => by
    have head := quiet x List.mem_cons_self
    simp only [Linux.openAfter, head.1, Bool.false_eq_true, false_and, ↓reduceIte, head.2]
    exact openAfter_none fun y member => quiet y (List.mem_cons_of_mem _ member)

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

/-- The `openat2` calls of `path_open` open what `openReply` returns, and nothing else. -/
theorem openCalls_openAfter {L : ShimLayout} {dir : UInt64} {path how : List UInt8}
    {reply : Transfer (List Bytes)} (opened : List UInt64) :
    ∀ {calls : Nat} {l : List Linux.Event}, OpenCalls L dir path how calls l reply →
      Linux.openAfter opened l = match reply with
        | .returned errno outputs => if errno = 0 then openedDescriptor outputs :: opened
          else opened
        | .trapped _ _ => opened
  | _, [], h => h.elim
  | _, _ :: _, ⟨ret, event, rest⟩ => by
    subst event
    split at rest
    · rename_i again
      rw [openAfter_unopened rfl (by rw [again.1]; exact eagain_large)]
      exact openCalls_openAfter opened rest
    · obtain ⟨rfl, rfl⟩ := rest
      by_cases small : ret.toNat < 2 ^ 31
      · have success : openReply ret = .returned 0 [leBytes 4 ret.toNat] := by
          simp only [openReply, small, ↓reduceIte]
        rw [success]
        show _ = openedDescriptor [leBytes 4 ret.toNat] :: opened
        rw [(openReply_descriptor success).2]
        simp only [Linux.openAfter, openat2_opens, small, and_self, ↓reduceIte]
      · rw [openAfter_unopened rfl small]
        unfold openReply
        simp only [small, ↓reduceIte]
        by_cases error : Linux.isError ret = true
        · simp only [error, ↓reduceIte]
          show opened = if errnoOf (0 - ret) = 0 then _ else opened
          rw [ite_eq_right (errnoOf_valid _).2]
        · simp only [error, Bool.false_eq_true, ↓reduceIte]
          rfl

theorem openCalls_fresh {L : ShimLayout} {dir : UInt64} {path how : List UInt8}
    {outputs : List Bytes} {opened : List UInt64} :
    ∀ {calls : Nat} {l : List Linux.Event}, OpenCalls L dir path how calls l (.returned 0 outputs) →
      Linux.FreshOpens opened l → openedDescriptor outputs ∉ opened
  | _, [], h => h.elim
  | _, e :: l, ⟨ret, event, rest⟩ => by
    subst event
    intro fresh
    split at rest
    · rename_i again
      have split := freshOpens_append (l := [_]) (m := l) fresh
      rw [openAfter_unopened rfl (by rw [again.1]; exact eagain_large)] at split
      exact openCalls_fresh rest split.2
    · obtain ⟨rfl, same⟩ := rest
      obtain ⟨small, rfl⟩ := openReply_descriptor same.symm
      have fresh := fresh [] _ [] rfl rfl
      rcases fresh with error | ⟨_, outside⟩
      · simp only [Linux.isError, decide_eq_true_eq] at error
        omega
      · exact outside

/-- The layer's open descriptors after an image of a WASI event are the WASI trace's after the
event. -/
theorem image_openAfter {F : OpenFlags} {L : ShimLayout} {I : Launch} {e : Wasi.Event}
    {l : List Linux.Event} (image : Image F L I e l) (opened : List UInt64) :
    Linux.openAfter opened l = openStep opened e := by
  cases e with
  | read count reply =>
    obtain ⟨x, a, rfl, call, _⟩ := image
    simp [Linux.openAfter, openStep, call, Linux.readCall, Linux.closeCall]
  | write output bytes reply =>
    obtain ⟨x, a, rfl, call, _⟩ := image
    simp [Linux.openAfter, openStep, call, Linux.writeCall, Linux.closeCall]
  | exit code =>
    cases image
    rfl
  | exitTrap code message =>
    cases image
    rfl
  | sys call args reply =>
    obtain ⟨accepted, image⟩ := image
    have member := sysImage_mem image
    simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
    have plain : call.name ≠ "path_open" → call.name ≠ "fd_close" →
        (∀ x ∈ l, x.call.opens = false ∧ x.call ≠ Linux.closeCall) →
        Linux.openAfter opened l = openStep opened (.sys call args reply) := by
      intro notOpen notClose none
      rw [openAfter_none none]
      simp [openStep, notOpen, notClose]
    have quiet : ∀ x : Linux.Event, x.call ∈ [Linux.clockGettimeCall, Linux.getrandomCall,
        Linux.readCall, Linux.writeCall] → x.call.opens = false ∧ x.call ≠ Linux.closeCall := by
      intro x listed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same <;> rw [same] <;> decide
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine plain (by decide) (by decide) fun x member => quiet x ?_
      rw [sysImage_clock] at image
      unfold ClockImage at image
      split at image
      · split at image
        · obtain ⟨_, _, rfl, _⟩ := image
          obtain rfl := List.mem_singleton.mp member
          simp
        · obtain ⟨rfl, _⟩ := image
          cases member
      · exact image.elim
    · refine plain (by decide) (by decide) fun x member => quiet x ?_
      rw [sysImage_random] at image
      unfold RandomImage at image
      split at image
      · obtain ⟨_, image⟩ := image
        simp [randomCalls_calls image x member]
      · exact image.elim
    · rw [sysImage_argsSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      exact plain (by decide) (by decide) fun _ member => nomatch member
    · rw [sysImage_args] at image
      obtain ⟨_, rfl, _⟩ := image
      exact plain (by decide) (by decide) fun _ member => nomatch member
    · rw [sysImage_environSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      exact plain (by decide) (by decide) fun _ member => nomatch member
    · rw [sysImage_environ] at image
      obtain ⟨_, rfl, _⟩ := image
      exact plain (by decide) (by decide) fun _ member => nomatch member
    · rw [sysImage_open] at image
      unfold OpenImage at image
      split at image
      · split at image
        · rw [openCalls_openAfter opened image]
          cases reply <;> simp (config := { decide := true }) only [openStep, ↓reduceIte]
        · rename_i failed
          obtain ⟨rfl, rfl⟩ := image
          simp (config := { decide := true }) [Linux.openAfter, openStep, failed]
      · exact image.elim
    · rw [sysImage_close] at image
      unfold CloseImage at image
      split at image
      · rename_i fd
        obtain ⟨ret, rfl, rfl⟩ := image
        have small : fd.toNat < 2 ^ 32 := by
          by_contra big
          have refused : ((61 : UInt64) = 0) = False := eq_false (by decide)
          simp only [Call.reject, Call.fdClose, rejectArgs, Param.takesArg, ↓reduceIte,
            Param.reject, Arg.value, big, refused] at accepted
        simp only [Linux.openAfter, Linux.closeCall, Bool.false_eq_true, false_and, ↓reduceIte,
          Linux.arg, List.getD_cons_zero, descriptor_small small]
        simp (config := { decide := true }) only [openStep, ↓reduceIte,
          List.head?_cons, Option.map_some, Option.getD_some, Arg.value]
        apply List.filter_congr
        intro y _
        by_cases same : y = fd <;> simp [same]
      · exact image.elim
    · refine plain (by decide) (by decide) fun x member => quiet x ?_
      rw [sysImage_read] at image
      unfold HandleReadImage at image
      split at image
      · obtain ⟨_, _, _, _, rfl, _⟩ := image
        obtain rfl := List.mem_singleton.mp member
        simp
      · exact image.elim
    · refine plain (by decide) (by decide) fun x member => quiet x ?_
      rw [sysImage_write] at image
      unfold HandleWriteImage at image
      split at image
      · obtain ⟨_, _, rfl, _⟩ := image
        obtain rfl := List.mem_singleton.mp member
        simp
      · exact image.elim
    · rw [sysImage_prestat] at image
      unfold PrestatImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        exact plain (by decide) (by decide) fun _ member => nomatch member
      · exact image.elim
    · rw [sysImage_dirName] at image
      unfold DirNameImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        exact plain (by decide) (by decide) fun _ member => nomatch member
      · exact image.elim

/-- An image's `openat2` returns a descriptor that the WASI trace does not hold open when the
layer's `FreshOpens` holds. -/
theorem image_fresh {F : OpenFlags} {L : ShimLayout} {I : Launch} {e : Wasi.Event}
    {l : List Linux.Event} (image : Image F L I e l) {opened : List UInt64}
    (fresh : Linux.FreshOpens opened l) :
    ∀ call args outputs, e = .sys call args (.returned 0 outputs) → call.name = "path_open" →
      openedDescriptor outputs ∉ opened := by
  intro call args outputs same named
  subst same
  obtain ⟨_, image⟩ := image
  have member := sysImage_mem image
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd named (by decide) | skip
  rw [sysImage_open] at image
  unfold OpenImage at image
  split at image
  · split at image
    · exact openCalls_fresh image fresh
    · rename_i failed
      obtain ⟨_, same⟩ := image
      exact absurd (Transfer.returned.inj same).1.symm failed
  · exact image.elim

theorem images_fresh {F : OpenFlags} {L : ShimLayout} {I : Launch} {trace : List Wasi.Event}
    {ls : List Linux.Event} (h : Images F L I trace ls) :
    ∀ {opened : List UInt64}, Linux.FreshOpens opened ls → FreshOpens opened trace := by
  induction h with
  | nil => intros; trivial
  | cons image _ ih =>
    intro opened fresh
    have split := freshOpens_append fresh
    refine ⟨image_fresh image split.1, ?_⟩
    rw [← image_openAfter image]
    exact ih split.2

theorem freshOpens_prefix {opened : List UInt64} :
    ∀ {first rest : List Wasi.Event}, FreshOpens opened (first ++ rest) → FreshOpens opened first
  | [], _, _ => trivial
  | _ :: _, _, ⟨head, tail⟩ => ⟨head, freshOpens_prefix (opened := _) tail⟩

theorem wellBracketed_prefix {stack stack' : List UInt64} {first rest : List Wasi.Event}
    (h : WellBracketed stack (first ++ rest) stack') : ∃ middle, WellBracketed stack first middle := by
  unfold WellBracketed at h ⊢
  rw [bracketRun_append] at h
  cases same : bracketRun stack first with
  | none => rw [same] at h; cases h
  | some middle => exact ⟨middle, rfl⟩

/-- The single layer event of an image. -/
theorem single_split {y x : Linux.Event} {pre post : List Linux.Event}
    (h : [y] = pre ++ x :: post) : pre = [] ∧ x = y := by
  cases pre with
  | nil =>
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact ⟨rfl, rfl⟩
  | cons first pre => cases pre <;> simp at h

/-- The descriptors that an image's events name are open when the WASI event uses only open
descriptors and 0 to 3 are open. -/
theorem image_names {F : OpenFlags} {L : ShimLayout} {I : Launch} {e : Wasi.Event}
    {l : List Linux.Event} (image : Image F L I e l) {opened : List UInt64}
    (uses : UsesOpen opened e) (standard : ∀ d ∈ ([0, 1, 2, 3] : List UInt64), d ∈ opened) :
    ∀ pre x post, l = pre ++ x :: post →
      (x.call ∈ [Linux.readCall, Linux.writeCall, Linux.openat2Call, Linux.closeCall] →
        Linux.arg x.args 0 ∈ Linux.openAfter opened pre) ∧
      (x.call = Linux.closeCall → Linux.arg x.args 0 ∉ [0, 1, 2, 3]) := by
  have outside : ∀ x : Linux.Event, x.call ∈ [Linux.clockGettimeCall, Linux.getrandomCall] →
      (x.call ∈ [Linux.readCall, Linux.writeCall, Linux.openat2Call, Linux.closeCall] →
        Linux.arg x.args 0 ∈ Linux.openAfter opened []) ∧
      (x.call = Linux.closeCall → Linux.arg x.args 0 ∉ [0, 1, 2, 3]) := by
    intro x listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with same | same <;> rw [same] <;>
      exact ⟨fun inside => absurd inside (by decide), fun close => absurd close (by decide)⟩
  intro pre x post same
  cases e with
  | read count reply =>
    obtain ⟨y, a, rfl, call, args, _⟩ := image
    obtain ⟨rfl, rfl⟩ := single_split same
    refine ⟨fun _ => ?_, fun close => absurd (call.symm.trans close) (by decide)⟩
    rw [args]
    exact standard 0 (by simp)
  | write output bytes reply =>
    obtain ⟨y, a, rfl, call, args, _⟩ := image
    obtain ⟨rfl, rfl⟩ := single_split same
    refine ⟨fun _ => ?_, fun close => absurd (call.symm.trans close) (by decide)⟩
    rw [args]
    cases output
    · exact standard 1 (by simp)
    · exact standard 2 (by simp)
  | exit code =>
    cases image
    cases pre <;> simp at same
  | exitTrap code message =>
    cases image
    cases pre <;> simp at same
  | sys call args reply =>
    obtain ⟨_, image⟩ := image
    obtain ⟨table, handles, closing⟩ := uses
    have member := sysImage_mem image
    simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [sysImage_clock] at image
      unfold ClockImage at image
      split at image
      · split at image
        · obtain ⟨_, _, rfl, _⟩ := image
          obtain ⟨rfl, rfl⟩ := single_split same
          exact outside _ (by simp)
        · obtain ⟨rfl, _⟩ := image
          cases pre <;> simp at same
      · exact image.elim
    · rw [sysImage_random] at image
      unfold RandomImage at image
      split at image
      · obtain ⟨_, image⟩ := image
        have call := randomCalls_calls image x (by rw [same]; simp)
        refine ⟨fun listed => ?_, fun close => absurd (call.symm.trans close) (by decide)⟩
        rw [call] at listed
        exact absurd listed (by decide)
      · exact image.elim
    · rw [sysImage_argsSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      cases pre <;> simp at same
    · rw [sysImage_args] at image
      obtain ⟨_, rfl, _⟩ := image
      cases pre <;> simp at same
    · rw [sysImage_environSizes] at image
      obtain ⟨_, rfl, _⟩ := image
      cases pre <;> simp at same
    · rw [sysImage_environ] at image
      obtain ⟨_, rfl, _⟩ := image
      cases pre <;> simp at same
    · rw [sysImage_open] at image
      unfold OpenImage at image
      split at image
      · split at image
        · obtain ⟨keep, call, named⟩ := openCalls_split opened image pre x post same
          refine ⟨fun _ => ?_, fun close => absurd (call.symm.trans close) (by decide)⟩
          rw [keep, named]
          refine (handles _ ?_).1
          simp [handleArgs, Param.handleWords, Call.pathOpen, Arg.value]
        · obtain ⟨rfl, _⟩ := image
          cases pre <;> simp at same
      · exact image.elim
    · rw [sysImage_close] at image
      unfold CloseImage at image
      split at image
      · obtain ⟨_, rfl, _⟩ := image
        obtain ⟨rfl, rfl⟩ := single_split same
        obtain ⟨fd', named, open', notStandard⟩ := closing rfl
        cases named
        exact ⟨fun _ => open', fun _ => notStandard⟩
      · exact image.elim
    · rw [sysImage_read] at image
      unfold HandleReadImage at image
      split at image
      · obtain ⟨_, _, _, _, rfl, _⟩ := image
        obtain ⟨rfl, rfl⟩ := single_split same
        refine ⟨fun _ => (handles _ ?_).1, fun close =>
          absurd (show Linux.readCall = Linux.closeCall from close) (by decide)⟩
        simp [handleArgs, Param.handleWords, Call.fdRead, Arg.value, Linux.arg]
      · exact image.elim
    · rw [sysImage_write] at image
      unfold HandleWriteImage at image
      split at image
      · obtain ⟨_, _, rfl, _⟩ := image
        obtain ⟨rfl, rfl⟩ := single_split same
        refine ⟨fun _ => (handles _ ?_).1, fun close =>
          absurd (show Linux.writeCall = Linux.closeCall from close) (by decide)⟩
        simp [handleArgs, Param.handleWords, Call.fdWrite, Arg.value, Linux.arg]
      · exact image.elim
    · rw [sysImage_prestat] at image
      unfold PrestatImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        cases pre <;> simp at same
      · exact image.elim
    · rw [sysImage_dirName] at image
      unfold DirNameImage at image
      split at image
      · obtain ⟨rfl, _⟩ := image
        cases pre <;> simp at same
      · exact image.elim

theorem images_names {F : OpenFlags} {L : ShimLayout} {I : Launch} {trace : List Wasi.Event}
    {ls : List Linux.Event} (h : Images F L I trace ls) :
    ∀ {opened : List UInt64}, (∀ first e rest, trace = first ++ e :: rest →
        UsesOpen (openAfter opened first) e ∧
          ∀ d ∈ ([0, 1, 2, 3] : List UInt64), d ∈ openAfter opened first) →
      ∀ pre x post, ls = pre ++ x :: post →
        (x.call ∈ [Linux.readCall, Linux.writeCall, Linux.openat2Call, Linux.closeCall] →
          Linux.arg x.args 0 ∈ Linux.openAfter opened pre) ∧
        (x.call = Linux.closeCall → Linux.arg x.args 0 ∉ [0, 1, 2, 3]) := by
  induction h with
  | nil =>
    intro opened _ pre x post same
    cases pre <;> simp at same
  | @cons e l es ls image _ ih =>
    intro opened uses pre x post same
    have later : ∀ first e' rest, es = first ++ e' :: rest →
        UsesOpen (openAfter (openStep opened e) first) e' ∧
          ∀ d ∈ ([0, 1, 2, 3] : List UInt64), d ∈ openAfter (openStep opened e) first :=
      fun first e' rest split => uses (e :: first) e' rest (by rw [split]; rfl)
    rcases List.append_eq_append_iff.mp same with ⟨rest, rfl, tail⟩ | ⟨middle, head, tail⟩
    · have found := ih later rest x post tail
      rw [openAfter_append, image_openAfter image]
      exact found
    · cases middle with
      | nil =>
        simp only [List.append_nil] at head
        subst head
        simp only [List.nil_append] at tail
        have found := ih later [] x post tail.symm
        rw [image_openAfter image]
        exact found
      | cons y middle =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj tail
        have first := uses [] e es rfl
        exact image_names image first.1 first.2 pre x middle head

/-- The bracket corollary: for a command whose runs keep the discipline of `withOpen`, every run
that `Footprint` describes, with the layer events `ls` after the initial ones, names only open
descriptors when the kernel's `openat2` returns only descriptors that are not open, from the open
descriptors 0 to 3. -/
theorem footprint_namesOpen {F : OpenFlags} {L : ShimLayout} {I : Launch}
    {replies : Linux.Replies} {native : Action UInt64}
    (bracketed : (Action.bind native fun status => Action.exit (α := Unit) status).BracketRuns)
    {initial : Observed LinuxWorld} {aborts : Bool} {final : Store (Observed LinuxWorld)}
    {message : String}
    (footprint : Footprint F L I replies (Action.bind native fun status => Action.exit status)
      initial aborts (.Trap final message))
    {ls : List Linux.Event} (grown : final.host.world.events = initial.world.events ++ ls)
    (fresh : Linux.FreshOpens [0, 1, 2, 3] ls) : NamesOpen ls := by
  obtain ⟨trace, ls', grown', images, _, _, _, runs⟩ := footprint
  have same : ls' = ls := List.append_cancel_left (grown'.symm.trans grown)
  subst same
  have bracketedTrace : ∃ stack, WellBracketed [] trace stack := by
    rcases runs with ⟨_, _, run⟩ | ⟨_, run⟩ | ⟨_, run⟩ | ⟨_, _, residual, run⟩
    · obtain ⟨stack, bracket, _⟩ := bracketed.1 _ _ _ _ _ run
      exact ⟨stack, bracket⟩
    · obtain ⟨stack, bracket, _⟩ := bracketed.1 _ _ _ _ _ run
      exact ⟨stack, bracket⟩
    · obtain ⟨stack, bracket, _⟩ := bracketed.1 _ _ _ _ _ run
      exact ⟨stack, bracket⟩
    · exact bracketed.2 _ _ _ _ _ run
  obtain ⟨stack, bracket⟩ := bracketedTrace
  have wasiFresh : FreshOpens initialDescriptors trace := images_fresh images fresh
  have uses := (bracket.descriptors wasiFresh).1
  intro pre x post split
  refine images_names images (fun first e rest split' => ⟨uses first e rest split', ?_⟩)
    pre x post split
  intro d listed
  rw [split'] at bracket wasiFresh
  obtain ⟨middle, prefixBracket⟩ := wellBracketed_prefix bracket
  have prefixOpen := (prefixBracket.descriptors (freshOpens_prefix wasiFresh)).2
  exact (prefixOpen.2.2 d).mpr (Or.inr listed)

end Verified.Shim
