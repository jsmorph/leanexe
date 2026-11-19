import Demos.ManifestCheck.NativeSpec
import Demos.ManifestCheck.CommandProof
import Demos.ManifestCheck.Budget
import Verified.Shim.Images
import Verified.Shim.Args

/-! The manifest checker's specification at the Linux call layer from its specification at WASI.
Each WASI event of the command has, under `linuxHost` with the results of `InRange`, one image:
`path_open` the `openat2` calls of `Opening` (`open_native`), `fd_filestat_get` one `statx`
(`stat_native`), `fd_read` on a handle one `read` (`read_native`), `fd_close` one `close`
(`close_native`), and a write to standard output one `write` of descriptor 1 (`write_native`).
The calls on a descriptor make their `read`, `statx`, and `close` because the descriptor that the
`openat2` of the bracket returned stays among the numbers that the shim holds until its `close`
(`Opening.held`, `held_quiet`).  The translations of the WASI predicates follow their
constructors, and `run_native` and `handled_native` translate `Run` and `Handled`.

Under a host that rejects only exit statuses of 126 or more, a run of `main` and its exit that
traps has a trapped call among its events (`exec_trapped_call`, from `TrapsInCall` of each part of
`main`), and no call of the command whose image has results in Linux's range traps
(`image_untrapped`).  `linux_exec_meets` combines these with `exec_main`: every run under
`linuxHost` from a launch whose arguments have no zero byte and fit `argsLimit`, and whose layer
events have results in Linux's range (`InRange`) and `read` outputs as long as the counts that they
ask for (`Sized`), ends at an accepted exit whose status and layer events meet `NMeets`. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## The images of the calls -/

theorem openHow_readOnly (F : OpenFlags) {rights : UInt64}
    (hr : rights = manifestRights ∨ rights = fileRights) :
    openHowBytes F 1 0 rights 0 = readOnlyHow := by
  rcases hr with rfl | rfl <;>
    simp [openHowBytes, openFlagsWord, manifestRights, fileRights, readOnlyHow] <;> decide

theorem openReply_ranged {ret : UInt64} (range : Linux.isError ret = true ∨ ret.toNat < 1024) :
    (ret.toNat < 1024 ∧ openReply ret = .returned 0 [leBytes 4 ret.toNat]) ∨
      (Linux.isError ret = true ∧ ¬ ret.toNat < 1024 ∧
        openReply ret = .returned (errnoOf (0 - ret)) [zeros 4]) := by
  unfold openReply
  by_cases low : ret.toNat < descriptorLimit
  · exact .inl ⟨low, by rw [ite_eq_left low]⟩
  · have error : Linux.isError ret = true := by
      rcases range with h | h
      · exact h
      · exact absurd h low
    exact .inr ⟨error, low, by rw [ite_eq_right low, ite_eq_left error]⟩

theorem openedDescriptor_leBytes {ret : UInt64} (low : ret.toNat < 1024) :
    openedDescriptor [leBytes 4 ret.toNat] = ret := by
  unfold openedDescriptor
  simp only [Reply.word, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
  rw [littleEndian_leBytes (by decide) (by omega), UInt64.ofNat_toNat]

/-- The `openat2` calls of `OpenCalls` for the path `name` and the record `readOnlyHow` under
directory 3, whose results lie in Linux's range, are those of `Opening`, and the reply is
returned with the errno and the descriptor that `Opening` names. -/
theorem openCalls_native {L : ShimLayout} {name : List UInt8} :
    ∀ {calls : Nat} {l : List Linux.Event} {reply : Transfer (List Bytes)}, calls ≤ 3 →
      OpenCalls L 3 name readOnlyHow calls l reply → InRange l →
      ∃ errno outputs, reply = .returned errno outputs ∧
        ∃ retries last, l = retries ++ [last] ∧ retries.length + calls ≤ 3 ∧
          (∀ e ∈ l, OpensBeneath name e) ∧ (∀ e ∈ retries, e.ret = 0 - 11) ∧
          ((last.ret.toNat < 1024 ∧ errno = 0 ∧ openedDescriptor outputs = last.ret) ∨
            (Linux.isError last.ret = true ∧ errno = errnoOf (0 - last.ret)))
  | _, [], _, _, h, _ => h.elim
  | calls, e :: l, reply, bound, ⟨ret, event, rest⟩, range => by
    subst event
    have opens : OpensBeneath name ⟨Linux.openat2Call, [3, L.path, L.openHow, 24],
        [name ++ [0], readOnlyHow], [], ret, []⟩ := ⟨rfl, rfl, rfl⟩
    split at rest
    · rename_i again
      obtain ⟨errno, outputs, rfl, retries, last, rfl, count, all, eagain, ending⟩ :=
        openCalls_native (by omega) rest (fun x m => range x (List.mem_cons_of_mem _ m))
      refine ⟨errno, outputs, rfl, _ :: retries, last, rfl, by simp; omega, fun x m => ?_,
        fun x m => ?_, ending⟩
      · rcases List.mem_cons.mp m with rfl | m
        · exact opens
        · exact all x m
      · rcases List.mem_cons.mp m with rfl | m
        · exact again.1
        · exact eagain x m
    · obtain ⟨rfl, rfl⟩ := rest
      have inRange := (range _ (List.mem_singleton_self _)).2.1 rfl
      have all : ∀ x ∈ [(⟨Linux.openat2Call, [3, L.path, L.openHow, 24],
          [name ++ [0], readOnlyHow], [], ret, []⟩ : Linux.Event)], OpensBeneath name x := by
        intro x m
        rw [List.mem_singleton.mp m]
        exact opens
      have none : ∀ x ∈ ([] : List Linux.Event), x.ret = 0 - 11 := fun x m => nomatch m
      have count : ([] : List Linux.Event).length + calls ≤ 3 := by simp; omega
      rcases openReply_ranged inRange with ⟨low, same⟩ | ⟨error, _, same⟩
      · refine ⟨_, _, same, [], _, rfl, count, all, none, ?_⟩
        exact .inl ⟨low, rfl, openedDescriptor_leBytes low⟩
      · refine ⟨_, _, same, [], _, rfl, count, all, none, ?_⟩
        exact .inr ⟨error, rfl⟩

/-- The image of the command's `path_open` of `name` under directory 3, read-only, with results in
Linux's range: a reply returned with an errno and the descriptor of `Opening`. -/
theorem open_native {F : OpenFlags} {L : ShimLayout} {opened : List UInt64} {rights : UInt64}
    {name : List UInt8} {reply : Transfer (List Bytes)} {l : List Linux.Event}
    (hr : rights = manifestRights ∨ rights = fileRights)
    (image : OpenImage F L opened (openArgs rights name) reply l) (range : InRange l) :
    ∃ errno outputs, reply = .returned errno outputs ∧
      Opening name l errno (openedDescriptor outputs) := by
  simp only [OpenImage, openArgs] at image
  have path : (bytesOf name).data.data.toList = name := by simp [bytesOf]
  rw [path, openHow_readOnly F hr] at image
  by_cases checked : openCheck opened 3 0 (bytesOf name) 0 = 0
  · rw [ite_eq_left checked] at image
    obtain ⟨errno, outputs, same, retries, last, split, count, all, eagain, ending⟩ :=
      openCalls_native (by omega) image range
    exact ⟨errno, outputs, same, .inr ⟨retries, last, split, by omega, all, eagain, ending⟩⟩
  · rw [ite_eq_right checked] at image
    obtain ⟨empty, same⟩ := image
    exact ⟨_, _, same, .inl ⟨empty, checked⟩⟩

/-- An event of a call that opens no descriptor and is no `close` keeps the numbers that the shim
holds. -/
theorem held_quiet (I : Launch) (events : List Linux.Event) :
    ∀ {l : List Linux.Event}, (∀ x ∈ l, x.call = Linux.readCall ∨ x.call = Linux.statxCall ∨
        (x.call = Linux.openat2Call ∧ ¬ x.ret.toNat < 2 ^ 31)) →
      openNumbers I (events ++ l) = openNumbers I events
  | [], _ => by rw [List.append_nil]
  | x :: l, quiet => by
    have first := openNumbers_append_quiet I events (e := x) (by
        rcases quiet x (List.mem_cons_self ..) with h | h | ⟨_, h⟩
        · simp [h, Linux.readCall]
        · simp [h, Linux.statxCall]
        · exact fun both => h both.2)
      (by
        rcases quiet x (List.mem_cons_self ..) with h | h | ⟨h, _⟩ <;>
          simp [h, Linux.readCall, Linux.statxCall, Linux.openat2Call, Linux.closeCall])
    rw [show events ++ x :: l = (events ++ [x]) ++ l by simp,
      held_quiet I (events ++ [x]) (fun y m => quiet y (List.mem_cons_of_mem _ m)), first.1]

/-- An opening that gives errno 0 leaves its descriptor, below 1,024, among the numbers that the
shim holds. -/
theorem Opening.held {name : List UInt8} {l : List Linux.Event} {fd : UInt64}
    (h : Opening name l 0 fd) (I : Launch) (events : List Linux.Event) :
    fd.toNat < 1024 ∧ fd ∈ openNumbers I (events ++ l) := by
  rcases h with ⟨-, nonzero⟩ | ⟨retries, last, rfl, -, all, eagain, ending⟩
  · exact absurd rfl nonzero
  rcases ending with ⟨low, -, rfl⟩ | ⟨-, zero⟩
  · refine ⟨low, ?_⟩
    have quiet := held_quiet I events (l := retries) (fun x m => .inr (.inr
      ⟨(all x (List.mem_append_left _ m)).1, by rw [eagain x m]; decide⟩))
    have lastOpens := (all last (List.mem_append_right _ (List.mem_singleton_self _))).1
    have added := (openNumbers_append_open I (events ++ retries) (e := last)
      (by rw [lastOpens]; rfl) (by unfold descriptorLimit; exact low)).1 last.ret
    rw [← List.append_assoc]
    exact added.mpr (.inl rfl)
  · exact absurd zero.symm (errnoOf_valid _).2



/-- Under the results of `InRange`, the reply of a `statx` record with result 0 is the first
timestamp that overflows, if one does. -/
theorem filestatReply_found {output : List UInt8}
    (valid : ∀ o ∈ stampOffsets output, stampValid output o = true) :
    ((stampOffsets output).find?
        fun o => !stampValid output o || decide (2 ^ 64 ≤ stampTime output o)) = none ↔
      ¬ Overflows output := by
  rw [List.find?_eq_none]
  constructor
  · rintro miss ⟨o, member, beyond⟩
    have := miss o member
    simp only [valid o member, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this beyond
  · intro fits o member
    simp only [valid o member, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    exact fun beyond => fits ⟨o, member, beyond⟩

theorem filestatReply_over {output : List UInt8}
    (valid : ∀ o ∈ stampOffsets output, stampValid output o = true)
    (beyond : Overflows output) : filestatReply 0 output = .returned 61 [zeros 64] := by
  unfold filestatReply
  rw [ite_eq_left rfl]
  cases found : (stampOffsets output).find?
      fun o => !stampValid output o || decide (2 ^ 64 ≤ stampTime output o) with
  | some o =>
    have member := List.mem_of_find?_eq_some found
    simp only [valid o member, ↓reduceIte]
  | none => exact absurd beyond ((filestatReply_found valid).mp found)

theorem filestatReply_fits {output : List UInt8}
    (valid : ∀ o ∈ stampOffsets output, stampValid output o = true)
    (fits : ¬ Overflows output) :
    filestatReply 0 output = .returned 0 [filestatBytes output] := by
  unfold filestatReply
  rw [ite_eq_left rfl, (filestatReply_found valid).mpr fits]

/-- The image of the command's `fd_filestat_get` of a descriptor that the shim holds, with a result
in Linux's range: one `statx` of `StatOf`, whose reply is an errno for an error number, 61 for a
timestamp of `2^64` nanoseconds or more, and the record of `filestatBytes` otherwise. -/
theorem stat_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {fd : UInt64} {reply : Transfer (List Bytes)} {l : List Linux.Event}
    (held : fd ∈ openNumbers I events)
    (image : SysImage F L I events Call.fdFilestatGet [.word fd] reply l) (range : InRange l) :
    ∃ e, l = [e] ∧ StatOf fd e ∧
      ((Linux.isError e.ret = true ∧ reply = .returned (errnoOf (0 - e.ret)) [zeros 64]) ∨
        (e.ret = 0 ∧ Overflows e.output ∧ reply = .returned 61 [zeros 64]) ∨
        (e.ret = 0 ∧ ¬ Overflows e.output ∧ reply = .returned 0 [filestatBytes e.output])) := by
  rw [sysImage_filestat] at image
  simp only [FilestatImage, held, ↓reduceIte] at image
  obtain ⟨ret, output, rfl, rfl⟩ := image
  refine ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rcases (range _ (List.mem_singleton_self _)).2.2.2 rfl with error | ⟨zero, valid⟩
  · refine .inl ⟨error, ?_⟩
    have nonzero : ret ≠ 0 := by
      rintro rfl
      simp [Linux.isError] at error
    simp [filestatReply, nonzero, error]
  · dsimp only at zero valid ⊢
    subst zero
    rcases Classical.em (Overflows output) with beyond | fits
    · exact .inr (.inl ⟨rfl, beyond, filestatReply_over valid beyond⟩)
    · exact .inr (.inr ⟨rfl, fits, filestatReply_fits valid fits⟩)

/-- The image of an `fd_read` on a descriptor that the shim holds, with a result in Linux's range:
one `read` of `ReadOf`, whose reply is the errno of an error number or, with errno 0, the bytes
that it returned. -/
theorem read_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {fd length : UInt64} {reply : Transfer (List Bytes)} {l : List Linux.Event}
    (held : fd ∈ openNumbers I events) (small : length.toNat < 2 ^ 32)
    (image : SysImage F L I events Call.fdRead [.word fd, .space length] reply l)
    (range : InRange l) :
    ∃ e, l = [e] ∧ ReadOf fd length e ∧
      ((Linux.isError e.ret = true ∧ ∃ outputs, reply = .returned (errnoOf (0 - e.ret)) outputs) ∨
        (Linux.isError e.ret = false ∧ e.ret.toNat ≤ length.toNat ∧ ∃ outputs,
          reply = .returned 0 outputs ∧ returned length outputs = e.readBytes fd)) := by
  rw [sysImage_read] at image
  simp only [HandleReadImage, held, ↓reduceIte] at image
  obtain ⟨a, prior, ret, output, rfl, rfl⟩ := image
  have read : ReadOf fd length ⟨Linux.readCall, [fd, a, length], [], prior, ret, output⟩ :=
    ⟨rfl, rfl, rfl⟩
  refine ⟨_, rfl, read, ?_⟩
  rcases (range _ (List.mem_singleton_self _)).1 (.inl rfl) with error | within
  · refine .inl ⟨error, ?_⟩
    have big : ¬ ret.toNat ≤ length.toNat := by
      intro low
      simp only [Linux.isError, decide_eq_true_eq] at error
      omega
    exact ⟨_, by rw [handleReadReply, ite_eq_right big, ite_eq_left error]⟩
  · change ret.toNat ≤ length.toNat at within
    have notError : Linux.isError ret = false := by
      simp only [Linux.isError, decide_eq_false_iff_not, not_lt]
      omega
    refine .inr ⟨notError, within, _, by rw [handleReadReply, ite_eq_left within], ?_⟩
    have word : (⟨0, [bytesOfList output, leBytes 4 ret.toNat]⟩ : Reply).word 1 = ret := by
      simp only [Reply.word, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rw [littleEndian_leBytes (by decide) (by omega), UInt64.ofNat_toNat]
    have least : Min.min ret length = ret := by
      rw [UInt64.min_def, ite_eq_left (UInt64.le_iff_toNat_le.mpr within)]
    rw [returned_eq, word, least]
    simp [Linux.Event.readBytes, Linux.arg, within, bytesOfList]

/-- The image of an `fd_close` of a descriptor that the shim holds, with a result in Linux's range:
one `close` of `CloseOf`, whose reply is the errno of `closeErrno`. -/
theorem close_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {fd : UInt64} {reply : Transfer (List Bytes)} {l : List Linux.Event}
    (held : fd ∈ openNumbers I events)
    (image : SysImage F L I events Call.fdClose [.word fd] reply l) (range : InRange l) :
    ∃ e, l = [e] ∧ CloseOf fd e ∧ reply = .returned (closeErrno e.ret) [] := by
  rw [sysImage_close] at image
  simp only [CloseImage, held, ↓reduceIte] at image
  obtain ⟨ret, rfl, rfl⟩ := image
  refine ⟨_, rfl, ⟨rfl, rfl⟩, ?_⟩
  rcases (range _ (List.mem_singleton_self _)).2.2.1 rfl with zero | error
  · dsimp only at zero
    simp [closeReply, closeErrno, zero]
  · dsimp only at error
    have nonzero : ret ≠ 0 := by
      rintro rfl
      exact absurd error (by decide)
    simp [closeReply, closeErrno, nonzero, error]

/-- The image of a write to standard output, with a result in Linux's range: one `write` of
descriptor 1, which offered the write's bytes and took the bytes that the write took, whose reply
is the errno of an error number or, with errno 0, the count that it returned. -/
theorem write_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {offered : Bytes} {reply : Transfer UInt64} {l : List Linux.Event}
    (image : Image F L I events (.write .stdout offered reply) l) (range : InRange l) :
    ∃ e, l = [e] ∧ e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1 ∧
      e.inputs.headD [] = offered.data.data.toList ∧
      Linux.writeData 1 l = (Event.write .stdout offered reply).stdoutTaken ∧
      ((Linux.isError e.ret = true ∧ reply = .returned (errnoOf (0 - e.ret)) 0) ∨
        (Linux.isError e.ret = false ∧ ∃ count, reply = .returned 0 count)) := by
  obtain ⟨e, a, rfl, call, args, inputs, -, small, rfl⟩ := image
  have wide : (UInt64.ofNat offered.data.size).toNat = offered.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have count : Linux.arg e.args 2 = UInt64.ofNat offered.data.size := by simp [args, Linux.arg]
  refine ⟨e, rfl, call, by simp [args, Linux.arg, Output.fd], by simp [inputs], ?_, ?_⟩
  · unfold writeReply
    split
    · rename_i within
      rw [wide] at within
      simp [Linux.writeData, Linux.Event.writeBytes, Event.stdoutTaken, call, args, inputs,
        Linux.arg, Output.fd, wide, within]
    · rename_i notWithin
      rw [wide] at notWithin
      split
      · simp [Linux.writeData, Linux.Event.writeBytes, Event.stdoutTaken, call, args, Linux.arg,
          Output.fd, wide, notWithin]
      · simp [Linux.writeData, Linux.Event.writeBytes, Event.stdoutTaken, call, args, Linux.arg,
          Output.fd, wide, notWithin]
  · rcases (range _ (List.mem_singleton_self _)).1 (.inr call) with error | within
    · have big : ¬ e.ret.toNat ≤ (UInt64.ofNat offered.data.size).toNat := by
        rw [wide]
        intro low
        simp only [Linux.isError, decide_eq_true_eq] at error
        omega
      exact .inl ⟨error, by rw [writeReply, ite_eq_right big, ite_eq_left error]⟩
    · rw [count, wide] at within
      have notError : Linux.isError e.ret = false := by
        simp only [Linux.isError, decide_eq_false_iff_not, not_lt]
        omega
      rw [← wide] at within
      exact .inr ⟨notError, _, by rw [writeReply, ite_eq_left within]⟩



/-! ## The manifest -/

/-- Each `read` of `ls` holds the whole buffer of its count in its output. -/
def Sized (ls : List Linux.Event) : Prop :=
  ∀ e ∈ ls, e.call = Linux.readCall → e.output.length = (Linux.arg e.args 2).toNat

theorem Carried.sized {R : Linux.Replies} : ∀ {k : Nat} {ls : List Linux.Event},
    Carried R k ls → Sized ls
  | _, [], _ => fun _ m => nomatch m
  | _, e :: ls, ⟨carries, rest⟩ => by
    intro x m call
    rcases List.mem_cons.mp m with rfl | m
    · rw [carries.2, call]
      simp [Linux.outputRegions, Linux.readCall, Linux.Param.words]
    · exact Carried.sized rest x m call

theorem InRange.left {a b : List Linux.Event} (h : InRange (a ++ b)) : InRange a :=
  fun e m => h e (List.mem_append_left _ m)

theorem InRange.right {a b : List Linux.Event} (h : InRange (a ++ b)) : InRange b :=
  fun e m => h e (List.mem_append_right _ m)

theorem Sized.left {a b : List Linux.Event} (h : Sized (a ++ b)) : Sized a :=
  fun e m => h e (List.mem_append_left _ m)

theorem Sized.right {a b : List Linux.Event} (h : Sized (a ++ b)) : Sized b :=
  fun e m => h e (List.mem_append_right _ m)

theorem images_cons {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Event} {es : List Event} {ls : List Linux.Event}
    (h : Images F L I events (e :: es) ls) :
    ∃ l rest, ls = l ++ rest ∧ Image F L I events e l ∧ Images F L I (events ++ l) es rest := by
  cases h with
  | cons image rest => exact ⟨_, _, rfl, image, rest⟩

theorem images_single {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Event} {ls : List Linux.Event} (h : Images F L I events [e] ls) :
    Image F L I events e ls := by
  obtain ⟨l, rest, rfl, image, more⟩ := images_cons h
  cases more
  simpa using image

theorem images_nil {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {ls : List Linux.Event} (h : Images F L I events [] ls) : ls = [] := by
  cases h
  rfl

/-- A `read` whose result is at most its count and whose output holds its count of bytes returned
no byte exactly when its result is 0. -/
theorem readBytes_nil {e : Linux.Event} {fd n : UInt64} (read : ReadOf fd n e)
    (sized : e.output.length = n.toNat) (within : e.ret.toNat ≤ n.toNat) :
    e.readBytes fd = [] ↔ e.ret = 0 := by
  obtain ⟨call, arg0, arg2⟩ := read
  have bytes : e.readBytes fd = e.output.take e.ret.toNat := by
    simp [Linux.Event.readBytes, call, arg0, arg2, within]
  rw [bytes, List.take_eq_nil_iff, ← UInt64.toNat_inj, UInt64.toNat_zero]
  constructor
  · rintro (zero | empty)
    · exact zero
    · rw [empty, List.length_nil] at sized
      omega
  · exact .inl

/-- The image of a read of the command with errno 0 returned a result in Linux's range below its
count, and the read's bytes; with an errno other than 0, it returned an error number. -/
theorem read_cases {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {fd length errno : UInt64} {outputs : List Bytes} {l : List Linux.Event}
    (held : fd ∈ openNumbers I events)
    (image : Image F L I events (readEvent fd length errno outputs) l) (range : InRange l)
    (sized : Sized l) :
    ∃ e, l = [e] ∧ ReadOf fd length e ∧
      ((errno ≠ 0 ∧ Linux.isError e.ret = true ∧ errno = errnoOf (0 - e.ret)) ∨
        (errno = 0 ∧ Linux.isError e.ret = false ∧
          returned length outputs = e.readBytes fd ∧ (e.readBytes fd = [] ↔ e.ret = 0))) := by
  obtain ⟨reject, sys⟩ := image
  obtain ⟨e, rfl, read, ending⟩ := read_native held (read_small reject) sys range
  refine ⟨e, rfl, read, ?_⟩
  rcases ending with ⟨error, outputs', same⟩ | ⟨notError, within, outputs', same, bytes⟩
  · obtain ⟨rfl, -⟩ := Transfer.returned.inj same
    exact .inl ⟨(errnoOf_valid _).2, error, rfl⟩
  · obtain ⟨rfl, rfl⟩ := Transfer.returned.inj same
    have size := sized e (List.mem_singleton_self _) read.1
    rw [read.2.2] at size
    exact .inr ⟨rfl, notError, bytes, readBytes_nil read size within⟩

/-- `ManifestReads` at WASI gives `NManifestReads` of the images, which are reads of the
descriptor. -/
theorem manifestReads_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {fd : UInt64}
    {size : Nat} :
    ∀ {held : List UInt8} {events : List Event} {bytes : List UInt8} {status : UInt64}
      {before ls : List Linux.Event},
      ManifestReads fd size held events bytes status → Images F L I before events ls →
      InRange ls → Sized ls → fd ∈ openNumbers I before →
      NManifestReads fd size held ls bytes status ∧
        ∀ x ∈ ls, x.call = Linux.readCall ∧ Linux.arg x.args 0 = fd
  | _, _, _, _, _, _, .full filled, images, _, _, _ => by
    rw [images_nil images]
    exact ⟨.full filled, fun _ m => nomatch m⟩
  | _, _, _, _, _, _, .short left empty, images, range, sized, held => by
    obtain ⟨e, rfl, read, ending⟩ := read_cases held (images_single images) range sized
    rcases ending with ⟨nonzero, -⟩ | ⟨-, -, bytes, zero⟩
    · exact absurd rfl nonzero
    · rw [bytes] at empty
      refine ⟨.short left read (zero.mp empty), fun x m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
  | _, _, _, _, _, _, .failed left nonzero, images, range, sized, held => by
    obtain ⟨e, rfl, read, ending⟩ := read_cases held (images_single images) range sized
    rcases ending with ⟨-, error, rfl⟩ | ⟨zero, -⟩
    · refine ⟨.failed left read error, fun x m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
    · exact absurd zero nonzero
  | _, _, _, _, before, _, .more left nonempty rest, images, range, sized, held => by
    obtain ⟨l, others, rfl, image, more⟩ := images_cons images
    obtain ⟨e, rfl, read, ending⟩ := read_cases held image range.left sized.left
    rcases ending with ⟨nonzero, -⟩ | ⟨-, -, bytes, zero⟩
    · exact absurd rfl nonzero
    have keep : fd ∈ openNumbers I (before ++ [e]) := by
      rw [held_quiet I before (l := [e])
        (fun x m => by rw [List.mem_singleton.mp m]; exact .inl read.1)]
      exact held
    rw [bytes] at rest nonempty
    obtain ⟨tail, calls⟩ := manifestReads_native rest more range.right sized.right keep
    have positive : 0 < e.ret.toNat := by
      have := mt zero.mpr nonempty
      rw [← UInt64.toNat_inj, UInt64.toNat_zero] at this
      omega
    refine ⟨.more left read positive tail, fun x m => ?_⟩
    rcases List.mem_append.mp m with m | m
    · rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
    · exact calls x m


theorem leValue_lt : ∀ l : List UInt8, Linux.leValue l < 256 ^ l.length
  | [] => by simp [Linux.leValue]
  | b :: bs => by
    have rest := leValue_lt bs
    have byte := b.toNat_lt
    simp only [Linux.leValue, List.length_cons, Nat.pow_succ]
    omega

theorem fieldAt_lt (output : List UInt8) (offset width : Nat) :
    fieldAt output offset width < 256 ^ width :=
  Nat.lt_of_lt_of_le (leValue_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem statxSize_lt (output : List UInt8) : statxSize output < UInt64.size :=
  Nat.lt_of_lt_of_le (fieldAt_lt output 40 8) (by decide)

/-- The size that a `filestat` record of `filestatBytes` reports is `stx_size`. -/
theorem statSize_filestat (output : List UInt8) :
    statSize [filestatBytes output] = UInt64.ofNat (statxSize output) := by
  have small : statxSize output < 2 ^ (8 * 8) := fieldAt_lt output 40 8
  have bytes : (⟨(filestatBytes output).data.extract 32 40⟩ : Bytes) =
      leBytes 8 (statxSize output) := by
    simp only [filestatBytes, leBytes, bytesOfList, statxSize, ByteArray.extract,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
  unfold statSize
  simp only [Reply.field, Reply.bytes, List.getElem?_cons_zero, Option.getD_some]
  rw [bytes, littleEndian_leBytes (by decide) small]

/-- The image of the command's `fd_filestat_get` of a descriptor that the shim holds: one `statx` of
`StatOf`, with the errno and the size of the WASI reply. -/
theorem stat_cases {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {fd errno : UInt64} {outputs : List Bytes} {l : List Linux.Event}
    (held : fd ∈ openNumbers I events)
    (image : Image F L I events (statEvent fd errno outputs) l) (range : InRange l) :
    ∃ e, l = [e] ∧ StatOf fd e ∧
      ((Linux.isError e.ret = true ∧ errno = errnoOf (0 - e.ret)) ∨
        (e.ret = 0 ∧ Overflows e.output ∧ errno = 61) ∨
        (e.ret = 0 ∧ ¬ Overflows e.output ∧ errno = 0 ∧
          statSize outputs = UInt64.ofNat (statxSize e.output))) := by
  obtain ⟨-, sys⟩ := image
  obtain ⟨e, rfl, stat, ending⟩ := stat_native held sys range
  refine ⟨e, rfl, stat, ?_⟩
  rcases ending with ⟨error, same⟩ | ⟨zero, beyond, same⟩ | ⟨zero, fits, same⟩
  · exact .inl ⟨error, (Transfer.returned.inj same).1⟩
  · exact .inr (.inl ⟨zero, beyond, (Transfer.returned.inj same).1⟩)
  · obtain ⟨rfl, rfl⟩ := Transfer.returned.inj same
    exact .inr (.inr ⟨zero, fits, rfl, statSize_filestat _⟩)

/-- The calls of the reading of a manifest: reads and the `statx` of its descriptor. -/
def OnFd (fd : UInt64) (x : Linux.Event) : Prop :=
  (x.call = Linux.readCall ∨ x.call = Linux.statxCall) ∧ Linux.arg x.args 0 = fd

theorem OnFd.quiet {fd : UInt64} {x : Linux.Event} (h : OnFd fd x) :
    x.call = Linux.readCall ∨ x.call = Linux.statxCall ∨
      (x.call = Linux.openat2Call ∧ ¬ x.ret.toNat < 2 ^ 31) := by
  rcases h.1 with h | h
  · exact .inl h
  · exact .inr (.inl h)

/-- `ManifestBody` at WASI gives `NManifestBody` of the images, which are calls on the
descriptor. -/
theorem manifestBody_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {fd : UInt64}
    {events : List Event} {status : UInt64} {bytes : List UInt8} {before ls : List Linux.Event}
    (body : ManifestBody fd events status bytes) (images : Images F L I before events ls)
    (range : InRange ls) (sized : Sized ls) (held : fd ∈ openNumbers I before) :
    NManifestBody fd ls status bytes ∧ ∀ x ∈ ls, OnFd fd x := by
  have statOn : ∀ e, StatOf fd e → ∀ x ∈ [e], OnFd fd x := fun e stat x m => by
    rw [List.mem_singleton.mp m]
    exact ⟨.inr stat.1, stat.2.1⟩
  cases body with
  | statFailed nonzero =>
    obtain ⟨e, rfl, stat, ending⟩ := stat_cases held (images_single images) range
    refine ⟨?_, statOn e stat⟩
    rcases ending with ⟨error, rfl⟩ | ⟨zero, beyond, rfl⟩ | ⟨-, -, rfl, -⟩
    · exact .statFailed stat error
    · exact .overflow stat zero beyond
    · exact absurd rfl nonzero
  | tooLarge large =>
    obtain ⟨e, rfl, stat, ending⟩ := stat_cases held (images_single images) range
    refine ⟨?_, statOn e stat⟩
    rcases ending with ⟨error, same⟩ | ⟨-, -, same⟩ | ⟨zero, fits, -, size⟩
    · exact absurd same.symm (errnoOf_valid _).2
    · exact absurd same (by decide)
    · rw [size, UInt64.toNat_ofNat_of_lt' (statxSize_lt _)] at large
      exact .tooLarge stat zero fits large
  | stopped small reads nonzero =>
    obtain ⟨l, rest, rfl, image, more⟩ := images_cons images
    obtain ⟨e, rfl, stat, ending⟩ := stat_cases held image range.left
    rcases ending with ⟨error, same⟩ | ⟨-, -, same⟩ | ⟨zero, fits, -, size⟩
    · exact absurd same.symm (errnoOf_valid _).2
    · exact absurd same (by decide)
    have keep : fd ∈ openNumbers I (before ++ [e]) := by
      rw [held_quiet I _ (l := [e]) (fun x m => (statOn e stat x m).quiet)]
      exact held
    rw [size, UInt64.toNat_ofNat_of_lt' (statxSize_lt _)] at small reads
    obtain ⟨tail, calls⟩ := manifestReads_native reads more range.right sized.right keep
    refine ⟨.stopped stat zero fits small tail nonzero, fun x m => ?_⟩
    rcases List.mem_append.mp m with m | m
    · exact statOn e stat x m
    · exact ⟨.inl (calls x m).1, (calls x m).2⟩
  | probed small reads =>
    obtain ⟨l, rest, rfl, image, more⟩ := images_cons images
    obtain ⟨e, rfl, stat, ending⟩ := stat_cases held image range.left
    rcases ending with ⟨error, same⟩ | ⟨-, -, same⟩ | ⟨zero, fits, -, size⟩
    · exact absurd same.symm (errnoOf_valid _).2
    · exact absurd same (by decide)
    have keep : fd ∈ openNumbers I (before ++ [e]) := by
      rw [held_quiet I _ (l := [e]) (fun x m => (statOn e stat x m).quiet)]
      exact held
    rw [size, UInt64.toNat_ofNat_of_lt' (statxSize_lt _)] at small reads
    obtain ⟨readsLs, probeLs, rfl, readImages, probeImages⟩ := images_split more
    have rangeRest := range.right
    have sizedRest := sized.right
    obtain ⟨tail, calls⟩ := manifestReads_native reads readImages rangeRest.left sizedRest.left
      keep
    have keep' : fd ∈ openNumbers I (before ++ [e] ++ readsLs) := by
      rw [held_quiet I _ (l := readsLs) (fun x m => .inl (calls x m).1)]
      exact keep
    obtain ⟨p, rfl, probe, probeEnding⟩ := read_cases keep' (images_single probeImages)
      rangeRest.right sizedRest.right
    have shown := NManifestBody.probed stat zero fits small tail probe
    refine ⟨?_, fun x m => ?_⟩
    · rw [show [e] ++ (readsLs ++ [p]) = e :: readsLs ++ [p] by simp]
      convert shown using 1
      rcases probeEnding with ⟨nonzero, error, rfl⟩ | ⟨rfl, notError, bytes, zeroP⟩
      · rw [ite_eq_left nonzero, ite_eq_left error]
      · rw [bytes]
        by_cases zr : p.ret = 0
        · have empty : p.readBytes fd = [] := zeroP.mpr zr
          rw [zr] at notError
          simp [empty, zr, notError]
        · have full : p.readBytes fd ≠ [] := fun h => zr (zeroP.mp h)
          simp [full, zr, notError]
    · simp only [List.mem_append, List.mem_singleton] at m
      rcases m with rfl | m | rfl
      · exact statOn _ stat _ (List.mem_singleton_self _)
      · exact ⟨.inl (calls x m).1, (calls x m).2⟩
      · exact ⟨.inl probe.1, probe.2.1⟩


/-! ## The checks -/

/-- `FileReads` at WASI gives `NFileReads` of the images, which are reads of the descriptor. -/
theorem fileReads_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {fd : UInt64} :
    ∀ {r : Nat} {done : List UInt8} {events : List Event} {bytes : List UInt8} {ending : Ending}
      {before ls : List Linux.Event},
      FileReads fd r done events bytes ending → Images F L I before events ls →
      InRange ls → Sized ls → fd ∈ openNumbers I before →
      NFileReads fd r done ls bytes ending ∧
        ∀ x ∈ ls, x.call = Linux.readCall ∧ Linux.arg x.args 0 = fd
  | _, _, _, _, _, _, _, .cut, images, _, _, _ => by
    rw [images_nil images]
    exact ⟨.cut, fun _ m => nomatch m⟩
  | _, _, _, _, _, _, _, .eof empty, images, range, sized, held => by
    obtain ⟨e, rfl, read, ending⟩ := read_cases held (images_single images) range sized
    rcases ending with ⟨nonzero, -⟩ | ⟨-, -, bytes, zero⟩
    · exact absurd rfl nonzero
    · rw [bytes] at empty
      refine ⟨.eof read (zero.mp empty), fun x m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
  | _, _, _, _, _, _, _, .failed nonzero, images, range, sized, held => by
    obtain ⟨e, rfl, read, ending⟩ := read_cases held (images_single images) range sized
    rcases ending with ⟨-, error, rfl⟩ | ⟨zero, -⟩
    · refine ⟨.failed read error, fun x m => ?_⟩
      rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
    · exact absurd zero nonzero
  | _, _, _, _, _, before, _, .more nonempty rest, images, range, sized, held => by
    obtain ⟨l, others, rfl, image, more⟩ := images_cons images
    obtain ⟨e, rfl, read, ending⟩ := read_cases held image range.left sized.left
    rcases ending with ⟨nonzero, -⟩ | ⟨-, -, bytes, zero⟩
    · exact absurd rfl nonzero
    have keep : fd ∈ openNumbers I (before ++ [e]) := by
      rw [held_quiet I before (l := [e])
        (fun x m => by rw [List.mem_singleton.mp m]; exact .inl read.1)]
      exact held
    rw [bytes] at rest nonempty ⊢
    obtain ⟨tail, calls⟩ := fileReads_native rest more range.right sized.right keep
    have positive : 0 < e.ret.toNat := by
      have := mt zero.mpr nonempty
      rw [← UInt64.toNat_inj, UInt64.toNat_zero] at this
      omega
    refine ⟨.more read positive tail, fun x m => ?_⟩
    rcases List.mem_append.mp m with m | m
    · rw [List.mem_singleton.mp m]
      exact ⟨read.1, read.2.1⟩
    · exact calls x m


/-! ## The brackets -/

/-- The image of the command's `path_open` that returned `errno` and `outputs` is an opening of
`Opening`. -/
theorem open_cases {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {rights : UInt64} {name : List UInt8} {errno : UInt64} {outputs : List Bytes}
    {l : List Linux.Event} (hr : rights = manifestRights ∨ rights = fileRights)
    (image : Image F L I before (.sys .pathOpen (openArgs rights name) (.returned errno outputs)) l)
    (range : InRange l) : Opening name l errno (openedDescriptor outputs) := by
  obtain ⟨-, sys⟩ := image
  rw [sysImage_open] at sys
  obtain ⟨errno', outputs', same, opening⟩ := open_native hr sys range
  obtain ⟨rfl, rfl⟩ := Transfer.returned.inj same
  exact opening

/-- An opening that gives an errno other than 0 is one for every descriptor. -/
theorem Opening.refuse {name : List UInt8} {l : List Linux.Event} {errno fd : UInt64}
    (h : Opening name l errno fd) (nonzero : errno ≠ 0) (fd' : UInt64) :
    Opening name l errno fd' := by
  rcases h with ⟨empty, -⟩ | ⟨retries, last, split, count, all, eagain, ending⟩
  · exact .inl ⟨empty, nonzero⟩
  · refine .inr ⟨retries, last, split, count, all, eagain, ?_⟩
    rcases ending with ⟨-, zero, -⟩ | ending
    · exact absurd zero nonzero
    · exact .inr ending

/-- The events of an opening are `openat2` calls. -/
theorem Opening.calls {name : List UInt8} {l : List Linux.Event} {errno fd : UInt64}
    (h : Opening name l errno fd) : ∀ x ∈ l, OpensBeneath name x := by
  rcases h with ⟨rfl, -⟩ | ⟨retries, last, rfl, -, all, -, -⟩
  · exact fun _ m => nomatch m
  · exact all

/-- The image of the command's `fd_close` of a descriptor that the shim holds that returned
`errno` is one `close` whose `closeErrno` is `errno`. -/
theorem close_cases {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {fd errno : UInt64} {outs : List Bytes} {l : List Linux.Event}
    (held : fd ∈ openNumbers I before)
    (image : Image F L I before (.sys .fdClose [.word fd] (.returned errno outs)) l)
    (range : InRange l) : ∃ c, l = [c] ∧ CloseOf fd c ∧ errno = closeErrno c.ret := by
  obtain ⟨-, sys⟩ := image
  obtain ⟨c, rfl, close, reply⟩ := close_native held sys range
  exact ⟨c, rfl, close, (Transfer.returned.inj reply).1⟩

theorem closeErrno_zero (ret : UInt64) : closeErrno ret = 0 ↔ ret = 0 := by
  unfold closeErrno
  split
  · simp_all
  · rename_i nonzero
    exact ⟨fun h => absurd h (errnoOf_valid _).2, fun h => absurd h nonzero⟩

/-- `FileCheck` at WASI gives `NFileCheck` of the images. -/
theorem fileCheck_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {name line : List UInt8}
    {events : List Event} {ok : Bool} {before ls : List Linux.Event}
    (check : FileCheck name line events ok) (images : Images F L I before events ls)
    (range : InRange ls) (sized : Sized ls) : NFileCheck name line ls ok := by
  cases check with
  | refused nonzero =>
    have opening := open_cases (.inr rfl) (images_single images) range
    exact .refused (opening.refuse nonzero 0) nonzero
  | @opened outputs events bytes ending closeErrno committed ok reads verdict =>
    obtain ⟨lo, rest, rfl, openImage, restImages⟩ := images_cons images
    have opening := open_cases (.inr rfl) openImage range.left
    obtain ⟨-, held⟩ := opening.held I before
    obtain ⟨lr, lc, rfl, readImages, closeImages⟩ := images_split restImages
    have rangeRest := range.right
    have sizedRest := sized.right
    obtain ⟨reading, calls⟩ := fileReads_native reads readImages rangeRest.left sizedRest.left held
    have held' : openedDescriptor outputs ∈ openNumbers I (before ++ lo ++ lr) := by
      rw [held_quiet I _ (l := lr) (fun x m => .inl (calls x m).1)]
      exact held
    obtain ⟨c, rfl, close, errno⟩ := close_cases held' (images_single closeImages)
      rangeRest.right
    rw [← List.append_assoc]
    refine .opened opening reading close ?_
    rw [verdict, errno, closeErrno_zero]

/-- `ManifestRun` at WASI gives `NManifestRun` of the images. -/
theorem manifestRun_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {name : List UInt8}
    {events : List Event} {status : UInt64} {bytes : List UInt8} {before ls : List Linux.Event}
    (run : ManifestRun name events status bytes) (images : Images F L I before events ls)
    (range : InRange ls) (sized : Sized ls) : NManifestRun name ls status bytes := by
  cases run with
  | refused nonzero =>
    have opening := open_cases (.inl rfl) (images_single images) range
    exact .refused (opening.refuse nonzero 0) nonzero
  | @opened outputs body status closeErrno bytes committed reading =>
    obtain ⟨lo, rest, rfl, openImage, restImages⟩ := images_cons images
    have opening := open_cases (.inl rfl) openImage range.left
    obtain ⟨-, held⟩ := opening.held I before
    obtain ⟨lb, lc, rfl, bodyImages, closeImages⟩ := images_split restImages
    have rangeRest := range.right
    have sizedRest := sized.right
    obtain ⟨shown, calls⟩ := manifestBody_native reading bodyImages rangeRest.left sizedRest.left
      held
    have held' : openedDescriptor outputs ∈ openNumbers I (before ++ lo ++ lb) := by
      rw [held_quiet I _ (l := lb) (fun x m => (calls x m).quiet)]
      exact held
    obtain ⟨c, rfl, close, errno⟩ := close_cases held' (images_single closeImages)
      rangeRest.right
    rw [errno, ← List.append_assoc]
    exact .opened opening shown close


/-! ## The writes -/

/-- The write to standard output `w` and its image `e`: one `write` of descriptor 1 that offered
the write's bytes and took the bytes that the write took, which returned an error number exactly
when the write returned an errno other than 0, with that errno. -/
def WritePair (w : Event) (e : Linux.Event) : Prop :=
  ∃ offered errno count, w = .write .stdout offered (.returned errno count) ∧
    e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1 ∧
    e.inputs.headD [] = offered.data.data.toList ∧ e.writeBytes 1 = w.stdoutTaken ∧
    (errno = 0 → Linux.isError e.ret = false) ∧
    (errno ≠ 0 → Linux.isError e.ret = true ∧ errno = errnoOf (0 - e.ret))

/-- The writes `ws` and their images `ls`, pairwise. -/
inductive WritePairs : List Event → List Linux.Event → Prop
  | nil : WritePairs [] []
  | cons {w : Event} {e : Linux.Event} {ws : List Event} {ls : List Linux.Event}
      (pair : WritePair w e) (rest : WritePairs ws ls) : WritePairs (w :: ws) (e :: ls)

/-- The images of writes to standard output that returned are their pairs. -/
theorem writes_pairs {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {before : List Linux.Event} {writes : List Event} {ls : List Linux.Event},
      Images F L I before writes ls → InRange ls →
      (∀ w ∈ writes, ∃ offered errno count, w = .write .stdout offered (.returned errno count)) →
      WritePairs writes ls
  | _, _, _, .nil, _, _ => .nil
  | _, w :: ws, _, .cons image rest, range, shape => by
    obtain ⟨offered, errno, count, rfl⟩ := shape w (List.mem_cons_self ..)
    obtain ⟨e, rfl, call, fd, input, data, ending⟩ := write_native image range.left
    have pair : WritePair (.write .stdout offered (.returned errno count)) e := by
      refine ⟨offered, errno, count, rfl, call, fd, input, by simpa [Linux.writeData] using data,
        fun zero => ?_, fun nonzero => ?_⟩
      · rcases ending with ⟨-, same⟩ | ⟨notError, -⟩
        · exact absurd ((Transfer.returned.inj same).1.symm.trans zero) (errnoOf_valid _).2
        · exact notError
      · rcases ending with ⟨error, same⟩ | ⟨-, count', same⟩
        · exact ⟨error, (Transfer.returned.inj same).1⟩
        · exact absurd (Transfer.returned.inj same).1 nonzero
    exact .cons pair (writes_pairs rest range.right fun x m => shape x (List.mem_cons_of_mem _ m))

theorem WritePairs.length : ∀ {ws : List Event} {ls : List Linux.Event}, WritePairs ws ls →
    ls.length = ws.length
  | _, _, .nil => rfl
  | _, _, .cons _ rest => by simp [rest.length]

theorem WritePairs.data : ∀ {ws : List Event} {ls : List Linux.Event}, WritePairs ws ls →
    Linux.writeData 1 ls = stdoutTaken ws
  | _, _, .nil => rfl
  | _, _, .cons ⟨_, _, _, _, _, _, _, bytes, _⟩ rest => by
    simp only [Linux.writeData, List.flatMap_cons, stdoutTaken_cons] at *
    rw [bytes, ← Linux.writeData, rest.data]

theorem WritePairs.calls : ∀ {ws : List Event} {ls : List Linux.Event}, WritePairs ws ls →
    ∀ e ∈ ls, e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1
  | _, _, .nil => fun _ m => nomatch m
  | _, _, .cons ⟨_, _, _, _, call, fd, _⟩ rest => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · exact ⟨call, fd⟩
    · exact rest.calls e m

theorem WritePairs.ok : ∀ {ws : List Event} {ls : List Linux.Event}, WritePairs ws ls →
    (∀ w ∈ ws, ∃ offered count, w = .write .stdout offered (.returned 0 count)) →
    ∀ e ∈ ls, Linux.isError e.ret = false
  | _, _, .nil, _ => fun _ m => nomatch m
  | _, _, .cons ⟨offered, errno, count, rfl, _, _, _, _, zero, _⟩ rest, every => fun e m => by
    obtain ⟨offered', count', same⟩ := every _ (List.mem_cons_self ..)
    obtain ⟨-, rfl, -⟩ := Event.write.inj same
    rcases List.mem_cons.mp m with rfl | m
    · exact zero (Transfer.returned.inj (by simpa using same)).1
    · exact rest.ok (fun w m' => every w (List.mem_cons_of_mem _ m')) e m

theorem WritePairs.some : ∀ {ws : List Event} {ls : List Linux.Event}, WritePairs ws ls →
    (∀ w ∈ ws, WroteSome w) → ∀ e ∈ ls, e.inputs.headD [] ≠ []
  | _, _, .nil, _ => fun _ m => nomatch m
  | _, _, .cons ⟨offered, errno, count, rfl, _, _, input, _⟩ rest, every => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · obtain ⟨offered', reply, same, size⟩ := every _ (List.mem_cons_self ..)
      obtain ⟨-, rfl, -⟩ := Event.write.inj same
      rw [input]
      intro empty
      apply size
      simpa using congrArg List.length empty
    · exact rest.some (fun w m' => every w (List.mem_cons_of_mem _ m')) e m

theorem WritePairs.append_single : ∀ {ws : List Event} {w : Event} {ls : List Linux.Event},
    WritePairs (ws ++ [w]) ls → ∃ ls' e, ls = ls' ++ [e] ∧ WritePairs ws ls' ∧ WritePair w e
  | [], _, _, .cons pair .nil => ⟨[], _, rfl, .nil, pair⟩
  | _ :: _, _, _, .cons pair rest => by
    obtain ⟨ls', e, rfl, rest', last⟩ := WritePairs.append_single rest
    exact ⟨_ :: ls', e, rfl, .cons pair rest', last⟩

/-- The offers of writes give the offers of their images, indexed. -/
theorem WritePairs.offers {text : List UInt8} :
    ∀ {ws : List Event} {ls : List Linux.Event} {taken : Nat}, WritePairs ws ls →
      Offered text taken ws → ∀ i (h : i < ls.length),
        ls[i].inputs.headD [] = text.drop (taken + (Linux.writeData 1 (ls.take i)).length)
  | _, _, _, .nil, _ => fun _ h => absurd h (Nat.not_lt_zero _)
  | _, _, taken, .cons ⟨offered, errno, count, rfl, _, _, input, bytes, _⟩ rest,
      ⟨⟨offered', reply, same, offers⟩, more⟩ => by
    obtain ⟨-, rfl, -⟩ := Event.write.inj same
    intro i h
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, Linux.writeData, List.flatMap_nil,
        List.length_nil, Nat.add_zero]
      rw [input]
      exact offers
    | succ i =>
      have step := rest.offers more i (by simpa using h)
      simp only [List.getElem_cons_succ, List.take_succ_cons, Linux.writeData, List.flatMap_cons,
        List.length_append] at step ⊢
      rw [step, bytes, Nat.add_assoc]

/-- `LineWrites` at WASI gives `NLineWrites` of the images. -/
theorem lineWrites_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {text : List UInt8}
    {writes : List Event} {ending : WriteEnd} {before ls : List Linux.Event}
    (wrote : LineWrites text writes ending) (images : Images F L I before writes ls)
    (range : InRange ls) : NLineWrites text ls ending := by
  obtain ⟨offered, count, some, final⟩ := wrote
  have shape : ∀ w ∈ writes, ∃ offered errno count,
      w = .write .stdout offered (.returned errno count) := by
    intro w m
    obtain ⟨o, reply, rfl, -⟩ := some w m
    cases ending with
    | all =>
      obtain ⟨o', c, same⟩ := final.1 _ m
      exact ⟨_, _, _, same⟩
    | stalled =>
      obtain ⟨o', c, same⟩ := final.1 _ m
      exact ⟨_, _, _, same⟩
    | failed errno =>
      obtain ⟨-, -, ⟨before, o', c, rfl, every⟩, -⟩ := final
      rcases List.mem_append.mp m with m | m
      · obtain ⟨o'', c', same⟩ := every _ m
        exact ⟨_, _, _, same⟩
      · rw [List.mem_singleton.mp m]
        exact ⟨_, _, _, rfl⟩
  have pairs := writes_pairs images range shape
  have offers := pairs.offers offered
  refine ⟨fun i h => by simpa using offers i h, fun e m => ⟨(pairs.calls e m).1,
    (pairs.calls e m).2, pairs.some some e m⟩, by rw [pairs.length]; exact count, ?_⟩
  rw [pairs.data]
  cases ending with
  | all => exact ⟨pairs.ok final.1, final.2⟩
  | stalled => exact ⟨pairs.ok final.1, by rw [pairs.length]; exact final.2.1, final.2.2⟩
  | failed errno =>
    obtain ⟨nonzero, -, ⟨before, o, c, rfl, every⟩, isPrefix, short⟩ := final
    refine ⟨?_, isPrefix, short⟩
    obtain ⟨ls', e, rfl, beforePairs, ⟨o', errno', c', same, -, -, -, -, -, failed⟩⟩ :=
      pairs.append_single
    obtain ⟨-, -, same⟩ := Event.write.inj same
    obtain ⟨rfl, -⟩ := Transfer.returned.inj same
    obtain ⟨error, rfl⟩ := failed nonzero
    exact ⟨ls', e, rfl, beforePairs.ok every, error, rfl⟩


/-- `Checks` at WASI gives `NChecks` of the images. -/
theorem checks_native {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {lines : List (List UInt8)} {allOk : Bool} {events : List Event} {code : UInt64}
      {before ls : List Linux.Event},
      Checks lines allOk events code → Images F L I before events ls → InRange ls → Sized ls →
      NChecks lines allOk ls code
  | _, _, _, _, _, _, .done, images, _, _ => by
    rw [images_nil images]
    exact .done
  | _, _, _, _, _, _, .line check wrote more, images, range, sized => by
    obtain ⟨lfw, lr, rfl, fwImages, restImages⟩ := images_split images
    obtain ⟨lf, lw, rfl, fileImages, writeImages⟩ := images_split fwImages
    have rangeFW := range.left
    have sizedFW := sized.left
    exact .line (fileCheck_native check fileImages rangeFW.left sizedFW.left)
      (lineWrites_native wrote writeImages rangeFW.right)
      (checks_native more restImages range.right sized.right)
  | _, _, _, _, _, _, .stalled check wrote, images, range, sized => by
    obtain ⟨lf, lw, rfl, fileImages, writeImages⟩ := images_split images
    exact .stalled (fileCheck_native check fileImages range.left sized.left)
      (lineWrites_native wrote writeImages range.right)
  | _, _, _, _, _, _, .failed check wrote, images, range, sized => by
    obtain ⟨lf, lw, rfl, fileImages, writeImages⟩ := images_split images
    exact .failed (fileCheck_native check fileImages range.left sized.left)
      (lineWrites_native wrote writeImages range.right)

/-! ## The run -/

/-- Two strings without zero bytes, each followed by a zero byte, determine each other. -/
theorem split_zero : ∀ {p q r s : List UInt8}, (0 : UInt8) ∉ p → (0 : UInt8) ∉ q →
    p ++ 0 :: r = q ++ 0 :: s → p = q ∧ r = s
  | [], [], _, _, _, _, h => ⟨rfl, (List.cons.inj h).2⟩
  | [], b :: q, _, _, _, hq, h => by
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact absurd (List.mem_cons_self ..) hq
  | b :: p, [], _, _, hp, _, h => by
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact absurd (List.mem_cons_self ..) hp
  | b :: p, c :: q, _, _, hp, hq, h => by
    obtain ⟨rfl, tail⟩ := List.cons.inj h
    obtain ⟨rfl, rfl⟩ := split_zero (fun m => hp (List.mem_cons_of_mem _ m))
      (fun m => hq (List.mem_cons_of_mem _ m)) tail
    exact ⟨rfl, rfl⟩

theorem count_stringsBytes : ∀ {args : List (List UInt8)}, (∀ s ∈ args, (0 : UInt8) ∉ s) →
    (stringsBytes args).count 0 = args.length
  | [], _ => rfl
  | s :: rest, h => by
    have ih := count_stringsBytes (fun t m => h t (List.mem_cons_of_mem _ m))
    simp only [stringsBytes] at ih
    simp only [stringsBytes, List.flatMap_cons, List.count_append, List.length_cons]
    rw [ih, List.count_eq_zero.mpr (h s (List.mem_cons_self ..))]
    simp
    omega

/-- The argument buffer of arguments without zero bytes holds one argument after the program name
exactly when there are two arguments. -/
theorem oneArgument_args {args : List (List UInt8)} (noZero : ∀ s ∈ args, (0 : UInt8) ∉ s)
    (name : List UInt8) :
    OneArgument (stringsBytes args) name ↔ ∃ program, args = [program, name] := by
  constructor
  · intro one
    have two := (oneArgument_shape one).1
    rw [count_stringsBytes noZero] at two
    match args, two with
    | [program, other], _ =>
      obtain ⟨p, same, hp, hn⟩ := one
      simp only [stringsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc, List.singleton_append] at same
      obtain ⟨rfl, rest⟩ := split_zero (noZero program (by simp)) hp same
      have : other ++ [0] = name ++ [0] := rest
      exact ⟨program, by rw [List.append_cancel_right this]⟩
  · rintro ⟨program, rfl⟩
    exact ⟨program, by simp [stringsBytes], noZero program (by simp), noZero name (by simp)⟩

/-- `Run` at WASI under the shim's host gives `NRun` of the images, for arguments without zero
bytes whose strings and eight-byte pointers take at most `argsLimit` bytes. -/
theorem run_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world : LinuxWorld} {a : ArgsResult} {manifest : List UInt8} {events : List Event}
    {code : UInt64} {before ls : List Linux.Event}
    (noZero : ∀ s ∈ I.args, (0 : UInt8) ∉ s)
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (run : Run (linuxHost F L I R) world a manifest events code)
    (images : Images F L I before events ls) (range : InRange ls) (sized : Sized ls) :
    NRun I.args manifest ls code := by
  obtain ⟨pre, rest, middle, rfl, argsRun, -, noArg, oneArg⟩ := run
  obtain ⟨aZero, aBytes, preEmpty⟩ := linux_args (by decide) (by decide) small argsRun
  obtain ⟨lp, lr, rfl, preImages, restImages⟩ := images_split images
  have empty := preEmpty _ _ preImages
  subst empty
  rw [List.nil_append] at range sized ⊢
  have buffer : a.bytes.data.data.toList = stringsBytes I.args := by
    rw [aBytes]
    simp [bytesOfList]
  refine ⟨fun two => ?_, fun program name same => ?_⟩
  · obtain ⟨one, rfl⟩ := noArg aZero (fun name h => by
      rw [buffer, oneArgument_args noZero] at h
      obtain ⟨p, hp⟩ := h
      rw [hp] at two
      exact two rfl)
    exact ⟨one, images_nil restImages⟩
  · have one : OneArgument a.bytes.data.data.toList name := by
      rw [buffer, oneArgument_args noZero]
      exact ⟨program, same⟩
    obtain ⟨opening, post, status, rfl, manifestRun, failed, rejected, accepted⟩ :=
      oneArg aZero name one
    obtain ⟨lo, lq, rfl, openImages, postImages⟩ := images_split restImages
    refine ⟨lo, lq, status, rfl,
      manifestRun_native manifestRun openImages range.left sized.left, fun nonzero => ?_,
      fun zero bad => ?_, fun zero nonempty all => ?_⟩
    · obtain ⟨rfl, rfl⟩ := failed nonzero
      exact ⟨rfl, images_nil postImages⟩
    · obtain ⟨rfl, rfl⟩ := rejected zero bad
      exact ⟨rfl, images_nil postImages⟩
    · exact checks_native (accepted zero nonempty all) postImages range.right sized.right

theorem openArgs_rights {r r' : UInt64} {name name' : List UInt8}
    (h : openArgs r name = openArgs r' name') : r = r' ∧ name = name' := by
  simp only [openArgs, List.cons.injEq, Arg.word.injEq, Arg.bytes.injEq, true_and,
    and_true] at h
  exact ⟨h.2, by simpa [bytesOf] using congrArg (fun b : Bytes => b.data.data.toList) h.1⟩

/-- Every open of a run that meets `Run` and `Confined` names the argument with the rights
`manifestRights`, or with the rights `fileRights` the name of a line of a manifest that has at
least one line and every line in the format. -/
theorem confined_accepted {World : Type} {host : Host World} {world : World} {a : ArgsResult}
    {manifest : List UInt8} {events : List Event} {code : UInt64}
    (run : Run host world a manifest events code)
    (confined : Confined a.bytes.data.data.toList manifest events) :
    ∀ args reply, Event.sys .pathOpen args reply ∈ events → ∃ name,
      (args = openArgs manifestRights name ∧ OneArgument a.bytes.data.data.toList name) ∨
      (args = openArgs fileRights name ∧ lines manifest ≠ [] ∧
        (∀ l ∈ lines manifest, WellFormed l.2) ∧ ∃ l ∈ lines manifest, name = l.2.drop 66) := by
  intro args reply member
  obtain ⟨name, manifestCase | ⟨rfl, l, hl, -, rfl⟩⟩ := confined args reply member
  · exact ⟨name, .inl manifestCase⟩
  refine ⟨_, .inr ⟨rfl, ?_⟩⟩
  obtain ⟨pre, rest, middle, rfl, argsRun, refused, noArg, oneArg⟩ := run
  have inRest : Event.sys .pathOpen (openArgs fileRights (l.2.drop 66)) reply ∈ rest := by
    rcases List.mem_append.mp member with m | m
    · exact absurd m (no_open_of_args (args_events argsRun) _ _)
    · exact m
  have nonempty : rest ≠ [] := fun h => by rw [h] at inRest; cases inRest
  by_cases errno : a.errno = 0
  swap
  · exact absurd (refused errno).2 nonempty
  by_cases two : ∃ name, OneArgument a.bytes.data.data.toList name
  swap
  · exact absurd (noArg errno (fun name h => two ⟨name, h⟩)).2 nonempty
  obtain ⟨name, one⟩ := two
  obtain ⟨opening, post, status, rfl, manifestRun, failed, rejected, accepted⟩ :=
    oneArg errno name one
  rcases List.mem_append.mp inRest with m | m
  · have same := manifestRun.opens _ _ m
    exact absurd (openArgs_rights same).1 (by decide)
  · have postNonempty : post ≠ [] := fun h => by rw [h] at m; cases m
    by_cases zero : status = 0
    swap
    · exact absurd (failed zero).2 postNonempty
    by_cases ok : lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2
    · exact ⟨ok.1, ok.2, l, hl, rfl⟩
    · refine absurd (rejected zero ?_).2 postNonempty
      by_cases emptyLines : lines manifest = []
      · exact .inl emptyLines
      · refine .inr ?_
        by_contra none
        push Not at none
        exact ok ⟨emptyLines, none⟩

theorem isError_eagain : Linux.isError (0 - 11) = true := by decide

/-- The events of a refused opening are `openat2` calls that returned an error number. -/
theorem Opening.refusedCalls {name : List UInt8} {l : List Linux.Event} {errno fd : UInt64}
    (h : Opening name l errno fd) (nonzero : errno ≠ 0) :
    ∀ x ∈ l, x.call = Linux.openat2Call ∧ Linux.isError x.ret = true := by
  rcases h with ⟨rfl, -⟩ | ⟨retries, last, rfl, -, all, eagain, ending⟩
  · exact fun _ m => nomatch m
  intro x m
  refine ⟨(all x m).1, ?_⟩
  rcases List.mem_append.mp m with m | m
  · rw [eagain x m]
    exact isError_eagain
  · rw [List.mem_singleton.mp m]
    rcases ending with ⟨-, zero, -⟩ | ⟨error, -⟩
    · exact absurd zero nonzero
    · exact error

theorem NHandled.refusedAll : ∀ {l rest : List Linux.Event},
    (∀ x ∈ l, x.call = Linux.openat2Call ∧ Linux.isError x.ret = true) → NHandled rest →
      NHandled (l ++ rest)
  | [], _, _, tail => tail
  | x :: l, _, fails, tail => by
    obtain ⟨call, error⟩ := fails x (List.mem_cons_self ..)
    exact .refused call error
      (NHandled.refusedAll (fun y m => fails y (List.mem_cons_of_mem _ m)) tail)

/-- The images of calls on a descriptor that the shim holds are `read` and `statx` calls of that
descriptor. -/
theorem onDescriptor_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {fd : UInt64} :
    ∀ {inner : List Event} {before ls : List Linux.Event},
      (∀ e ∈ inner, OnDescriptor fd e) → Images F L I before inner ls → InRange ls →
      fd ∈ openNumbers I before → ∀ x ∈ ls, OnFd fd x
  | [], _, _, _, images, _, _ => by
    rw [images_nil images]
    exact fun _ m => nomatch m
  | e :: inner, before, _, calls, images, range, held => by
    obtain ⟨l, others, rfl, image, rest⟩ := images_cons images
    have first : ∀ x ∈ l, OnFd fd x := by
      rcases calls e (List.mem_cons_self ..) with ⟨length, reply, rfl⟩ | ⟨reply, rfl⟩
      · obtain ⟨reject, sys⟩ := image
        obtain ⟨x, rfl, read, -⟩ := read_native held (read_small reject) sys range.left
        intro y m
        rw [List.mem_singleton.mp m]
        exact ⟨.inl read.1, read.2.1⟩
      · obtain ⟨-, sys⟩ := image
        obtain ⟨x, rfl, stat, -⟩ := stat_native held sys range.left
        intro y m
        rw [List.mem_singleton.mp m]
        exact ⟨.inr stat.1, stat.2.1⟩
    have keep : fd ∈ openNumbers I (before ++ l) := by
      rw [held_quiet I before (fun x m => (first x m).quiet)]
      exact held
    have more := onDescriptor_native (fun x m => calls x (List.mem_cons_of_mem _ m)) rest
      range.right keep
    intro x m
    rcases List.mem_append.mp m with m | m
    · exact first x m
    · exact more x m

/-- `Handled` at WASI gives `NHandled` of the images, and every `openat2` among them opens a name
that the WASI open of its image names, beneath descriptor 3. -/
theorem handled_native {F : OpenFlags} {L : ShimLayout} {I : Launch} {P : List UInt8 → Prop} :
    ∀ {events : List Event} {before ls : List Linux.Event},
      Handled events → Images F L I before events ls → InRange ls →
      (∀ args reply, Event.sys .pathOpen args reply ∈ events → ∃ name,
        (args = openArgs manifestRights name ∨ args = openArgs fileRights name) ∧ P name) →
      NHandled ls ∧ ∀ x ∈ ls, x.call = Linux.openat2Call → ∃ name, OpensBeneath name x ∧ P name
  | _, _, _, .nil, images, _, _ => by
    rw [images_nil images]
    exact ⟨.nil, fun _ m => nomatch m⟩
  | _, before, _, @Handled.write offered reply rest tail, images, range, names => by
    obtain ⟨l, others, rfl, image, more⟩ := images_cons images
    obtain ⟨e, rfl, call, fd, -⟩ := write_native image range.left
    obtain ⟨handled, opens⟩ := handled_native tail more range.right
      (fun args reply m => names args reply (List.mem_cons_of_mem _ m))
    refine ⟨.write call fd handled, fun x m c => ?_⟩
    rcases List.mem_append.mp m with m | m
    · rw [List.mem_singleton.mp m, call] at c
      exact absurd c (by decide)
    · exact opens x m c
  | _, before, _, @Handled.argsCall call args reply rest named tail, images, range, names => by
    obtain ⟨l, others, rfl, image, more⟩ := images_cons images
    obtain ⟨-, sys⟩ := image
    have empty : l = [] := by
      rcases named with rfl | rfl
      · rw [sysImage_argsSizes] at sys
        exact sys.2.1
      · rw [sysImage_args] at sys
        exact sys.2.1
    subst empty
    rw [List.nil_append] at range ⊢
    rw [List.append_nil] at more
    exact handled_native tail more range
      (fun args reply m => names args reply (List.mem_cons_of_mem _ m))
  | _, before, _, @Handled.refused args errno outputs rest nonzero tail, images, range, names => by
    obtain ⟨l, others, rfl, image, more⟩ := images_cons images
    obtain ⟨name, hr, pname⟩ := names _ _ (List.mem_cons_self ..)
    have opening : Opening name l errno (openedDescriptor outputs) := by
      rcases hr with rfl | rfl
      · exact open_cases (.inl rfl) image range.left
      · exact open_cases (.inr rfl) image range.left
    obtain ⟨handled, opens⟩ := handled_native tail more range.right
      (fun args reply m => names args reply (List.mem_cons_of_mem _ m))
    refine ⟨NHandled.refusedAll (opening.refusedCalls nonzero) handled, fun x m c => ?_⟩
    rcases List.mem_append.mp m with m | m
    · exact ⟨name, opening.calls x m, pname⟩
    · exact opens x m c
  | _, before, _, @Handled.bracket args outputs inner closed rest calls tail, images, range,
      names => by
    obtain ⟨lo, others, rfl, image, more⟩ := images_cons images
    obtain ⟨name, hr, pname⟩ := names _ _ (List.mem_cons_self ..)
    have opening : Opening name lo 0 (openedDescriptor outputs) := by
      rcases hr with rfl | rfl
      · exact open_cases (.inl rfl) image range.left
      · exact open_cases (.inr rfl) image range.left
    obtain ⟨-, held⟩ := opening.held I before
    obtain ⟨li, lc, rfl, innerImages, closeImages⟩ := images_split more
    obtain ⟨lcl, lrest, rfl, closeImage, restImages⟩ := images_cons closeImages
    have rangeRest := range.right
    have rangeTail := rangeRest.right
    have onFd := onDescriptor_native calls innerImages rangeRest.left held
    have held' : openedDescriptor outputs ∈ openNumbers I (before ++ lo ++ li) := by
      rw [held_quiet I _ (l := li) (fun x m => (onFd x m).quiet)]
      exact held
    obtain ⟨-, sys⟩ := closeImage
    obtain ⟨c, rfl, close, -⟩ := close_native held' sys rangeTail.left
    obtain ⟨handled, opens⟩ := handled_native tail restImages rangeTail.right
      (fun args reply m => names args reply
        (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ m))))
    rcases opening with ⟨-, nonzero⟩ | ⟨retries, last, rfl, -, all, eagain, ending⟩
    · exact absurd rfl nonzero
    rcases ending with ⟨low, -, same⟩ | ⟨-, zero⟩
    swap
    · exact absurd zero.symm (errnoOf_valid _).2
    have refused : ∀ x ∈ retries, x.call = Linux.openat2Call ∧ Linux.isError x.ret = true :=
      fun x m => ⟨(all x (List.mem_append_left _ m)).1, by rw [eagain x m]; exact isError_eagain⟩
    have lastCall := (all last (List.mem_append_right _ (List.mem_singleton_self _))).1
    have shape : retries ++ [last] ++ (li ++ ([c] ++ lrest)) =
        retries ++ (last :: (li ++ c :: lrest)) := by simp
    rw [shape]
    refine ⟨NHandled.refusedAll refused (.bracket lastCall low (fun x m => ?_) ?_ handled),
      fun x m cx => ?_⟩
    · rw [← same]
      exact ⟨(onFd x m).1, (onFd x m).2⟩
    · rw [← same]
      exact close
    · simp only [List.mem_append, List.mem_cons] at m
      rcases m with m | rfl | m | rfl | m
      · exact ⟨name, all x (List.mem_append_left _ m), pname⟩
      · exact ⟨name, all x (List.mem_append_right _ (List.mem_singleton_self _)), pname⟩
      · rcases (onFd x m).1 with h | h <;> rw [h] at cx <;> exact absurd cx (by decide)
      · rw [close.1] at cx
        exact absurd cx (by decide)
      · exact opens x m cx

/-! ## Runs that trap -/

/-- A call, read, or write whose reply trapped. -/
def TrappedCall : Event → Prop
  | .sys _ _ (.trapped _ _) => True
  | .read _ (.trapped _ _) => True
  | .write _ _ (.trapped _ _) => True
  | _ => False

/-- Every run of `action` under `host` that traps has a trapped call among its events. -/
def TrapsInCall {World : Type} (host : Host World) {α : Type} (action : Action α) : Prop :=
  ∀ {world : World} {trace : List Event} {message : String} {final : World},
    Exec host action world trace (.trapped message) final → ∃ e ∈ trace, TrappedCall e

section Traps

variable {World : Type} {host : Host World}

theorem TrapsInCall.pure {α : Type} (value : α) : TrapsInCall host (.pure value) := by
  intro world trace message final run
  cases run

theorem TrapsInCall.sys {α : Type} {call : Call} {args : List Arg} {next : Reply → Action α}
    (h : ∀ reply, TrapsInCall host (next reply)) : TrapsInCall host (.sys call args next) := by
  intro world trace message final run
  cases run with
  | sys_reject _ rest => exact h _ rest
  | sys_return _ _ rest =>
    obtain ⟨e, m, t⟩ := h _ rest
    exact ⟨e, List.mem_cons_of_mem _ m, t⟩
  | sys_trap => exact ⟨_, List.mem_singleton_self _, trivial⟩

theorem TrapsInCall.write {α : Type} {output : Output} {bytes : Bytes}
    {next : WriteResult → Action α}
    (h : ∀ errno committed, errno.toNat ≤ 76 →
      TrapsInCall host (next (writeResult errno committed))) :
    TrapsInCall host (.write output bytes next) := by
  intro world trace message final run
  cases run with
  | write_return reply rest =>
    obtain ⟨e, m, t⟩ := h _ _ (host.write_bound reply).2 rest
    exact ⟨e, List.mem_cons_of_mem _ m, t⟩
  | write_trap => exact ⟨_, List.mem_singleton_self _, trivial⟩

theorem TrapsInCall.exit {α : Type}
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat) {code : UInt64} (low : code.toNat < 126) :
    TrapsInCall host (Action.exit (α := α) code) := by
  intro world trace message final run
  cases run with
  | exitTrap rejected =>
    have high := accepts rejected
    rw [exitStatus_of_lt (by omega)] at high
    omega

theorem TrapsInCall.bind {α β : Type} {first : Action α} {next : α → Action β}
    (hf : TrapsInCall host first) (hn : ∀ v, TrapsInCall host (next v)) :
    TrapsInCall host (Action.bind first next) := by
  intro world trace message final run
  obtain ⟨after, pre, middle, rest, firstRun, cont, rfl⟩ := Exec.unbind first run
  cases middle with
  | returned v =>
    obtain ⟨e, m, t⟩ := hn v cont
    exact ⟨e, List.mem_append_right _ m, t⟩
  | exited c =>
    obtain ⟨-, same, -⟩ := cont
    cases same
  | trapped m =>
    obtain ⟨rfl, -, -⟩ := cont
    obtain ⟨e, mem, t⟩ := hf firstRun
    exact ⟨e, List.mem_append_left _ mem, t⟩

theorem TrapsInCall.loopExec {σ α : Type} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α}
    (hs : ∀ i s, TrapsInCall host (step i s)) (hn : ∀ s, TrapsInCall host (next s)) :
    ∀ (remaining index : Nat) (state : σ) {world : World} {trace : List Event} {message : String}
      {final : World},
      LoopExec host remaining index state test step next world trace (.trapped message) final →
      ∃ e ∈ trace, TrappedCall e
  | 0, _, _, _, _, _, _, run => by
    cases run with
    | zero rest => exact hn _ rest
  | r + 1, index, state, _, _, _, _, run => by
    cases run with
    | stop _ rest => exact hn _ rest
    | next _ _ restRun =>
      obtain ⟨e, m, t⟩ := TrapsInCall.loopExec hs hn r _ _ restRun
      exact ⟨e, List.mem_append_right _ m, t⟩
    | trap _ stepRun => exact hs _ _ stepRun

theorem TrapsInCall.loop {σ α : Type} {count : UInt64} {init : σ} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {next : σ → Action α}
    (hs : ∀ i s, TrapsInCall host (step i s)) (hn : ∀ s, TrapsInCall host (next s)) :
    TrapsInCall host (.loop count init test step next) := by
  intro world trace message final run
  cases run with
  | loop inner => exact TrapsInCall.loopExec hs hn _ _ _ inner

theorem args_traps : TrapsInCall host args := by
  unfold args
  refine TrapsInCall.sys fun sizes => ?_
  split
  · exact TrapsInCall.pure _
  split
  · exact TrapsInCall.pure _
  refine TrapsInCall.sys fun got => ?_
  split <;> exact TrapsInCall.pure _

theorem withOpen_traps {α : Type} {dir : Handle} {dirflags : UInt64} {path : Bytes}
    {oflags rights inheriting fdflags : UInt64} {onError : UInt64 → Action α}
    {body : Handle → Action α} (he : ∀ errno, TrapsInCall host (onError errno))
    (hb : ∀ h, TrapsInCall host (body h)) :
    TrapsInCall host
      (withOpen dir dirflags path oflags rights inheriting fdflags onError body) := by
  unfold withOpen
  refine TrapsInCall.sys fun opened => ?_
  split
  · exact TrapsInCall.bind (he _) fun _ => TrapsInCall.pure _
  · exact TrapsInCall.bind (hb _) fun _ => TrapsInCall.sys fun _ => TrapsInCall.pure _

theorem readManifest_traps (file : Handle) (buffer : Bytes) :
    TrapsInCall host (readManifest file buffer) := by
  unfold readManifest readBytes
  refine TrapsInCall.bind (TrapsInCall.sys fun _ => TrapsInCall.pure _) fun stat => ?_
  split
  · exact TrapsInCall.pure _
  split
  · exact TrapsInCall.pure _
  refine TrapsInCall.bind
    (TrapsInCall.loop (fun index state => ?_) fun _ => TrapsInCall.pure _) fun s => ?_
  · refine TrapsInCall.bind (TrapsInCall.sys fun _ => TrapsInCall.pure _) fun got => ?_
    split
    · exact TrapsInCall.pure _
    split <;> exact TrapsInCall.pure _
  · split
    · exact TrapsInCall.pure _
    refine TrapsInCall.bind (TrapsInCall.sys fun _ => TrapsInCall.pure _) fun probe => ?_
    split
    · exact TrapsInCall.pure _
    split <;> exact TrapsInCall.pure _

theorem hashFile_traps (file : Handle) (buffer : Bytes) :
    TrapsInCall host (hashFile file buffer) := by
  unfold hashFile
  refine TrapsInCall.bind
    (TrapsInCall.loop (fun index state => ?_) fun _ => TrapsInCall.pure _)
    fun _ => TrapsInCall.pure _
  refine TrapsInCall.bind (TrapsInCall.sys fun _ => TrapsInCall.pure _) fun got => ?_
  split
  · exact TrapsInCall.pure _
  split
  · exact TrapsInCall.pure _
  split <;> exact TrapsInCall.pure _

theorem writeAll_traps
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat) (buffer : Bytes) (start count : UInt64) :
    TrapsInCall host (writeAll buffer start count) := by
  unfold writeAll
  refine TrapsInCall.loop (fun _ written => ?_) fun _ => TrapsInCall.pure _
  refine TrapsInCall.write fun errno committed valid => ?_
  simp only [Action.bind]
  split
  · exact TrapsInCall.exit accepts (by simp only [writeResult]; omega)
  · exact TrapsInCall.pure _

theorem checkLines_traps
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat) (m : Bytes) (entries : Array UInt64) (buffer : Bytes) :
    TrapsInCall host (checkLines m entries buffer) := by
  unfold checkLines
  refine TrapsInCall.bind (TrapsInCall.loop (fun j s => ?_) fun _ => TrapsInCall.pure _) fun s => ?_
  · dsimp only
    exact TrapsInCall.bind
      (withOpen_traps (fun _ => TrapsInCall.pure _) fun file => hashFile_traps file _)
      fun checked =>
      TrapsInCall.bind (writeAll_traps accepts _ _ _) fun _ => TrapsInCall.pure _
  · split <;> exact TrapsInCall.pure _

theorem main_traps
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat) : TrapsInCall host main := by
  unfold main
  refine TrapsInCall.bind args_traps fun arguments => ?_
  split
  · exact TrapsInCall.pure _
  dsimp only
  split
  · exact TrapsInCall.pure _
  refine TrapsInCall.bind
    (withOpen_traps (fun _ => TrapsInCall.pure _) fun file => readManifest_traps file _)
    fun got => ?_
  split
  · exact TrapsInCall.pure _
  split
  · exact TrapsInCall.pure _
  split
  · exact TrapsInCall.pure _
  · exact checkLines_traps accepts _ _ _

/-- A run of `main` and its exit that traps, under a host that rejects only exit statuses of 126
or more, has a trapped call among its events. -/
theorem exec_trapped_call
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat)
    {world final : World} {trace : List Event} {message : String}
    (execution : Exec host (main.bind fun status => Action.exit (α := Unit) status) world trace
      (.trapped message) final) : ∃ e ∈ trace, TrappedCall e := by
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  cases middle with
  | returned status =>
    have low := ((main_runs mainRun).1 status rfl).1
    change Exec host (Action.exit status) after rest (.trapped message) final at cont
    obtain ⟨e, m, t⟩ := TrapsInCall.exit accepts (by omega) cont
    exact ⟨e, List.mem_append_right _ m, t⟩
  | exited c =>
    obtain ⟨-, same, -⟩ := cont
    cases same
  | trapped m =>
    obtain ⟨rfl, -, -⟩ := cont
    obtain ⟨e, mem, t⟩ := main_traps accepts mainRun
    exact ⟨e, List.mem_append_left _ mem, t⟩

end Traps

/-- The calls that the command's events can make: writes to standard output, `args_sizes_get`,
`args_get`, `path_open`, `fd_close`, `fd_read`, `fd_filestat_get`, and a rejected exit. -/
def CommandEvent : Event → Prop
  | .write output _ _ => output = .stdout
  | .sys call _ _ => call = .argsSizesGet ∨ call = .argsGet ∨ call = .pathOpen ∨
      call = .fdClose ∨ call = .fdRead ∨ call = .fdFilestatGet
  | .exitTrap _ _ => True
  | _ => False

theorem Handled.commands : ∀ {events : List Event}, Handled events → ∀ e ∈ events, CommandEvent e
  | _, .nil => fun _ m => nomatch m
  | _, .write tail => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · rfl
    · exact tail.commands e m
  | _, .argsCall named tail => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · rcases named with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
    · exact tail.commands e m
  | _, .refused _ tail => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · exact .inr (.inr (.inl rfl))
    · exact tail.commands e m
  | _, .bracket calls tail => fun e m => by
    rcases List.mem_cons.mp m with rfl | m
    · exact .inr (.inr (.inl rfl))
    rcases List.mem_append.mp m with m | m
    · rcases calls e m with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inr (.inr (.inr (.inr (.inr rfl))))
    rcases List.mem_cons.mp m with rfl | m
    · exact .inr (.inr (.inr (.inl rfl)))
    · exact tail.commands e m

theorem Unfinished.commands {events : List Event} (h : Unfinished events) :
    ∀ e ∈ events, CommandEvent e := by
  cases h with
  | empty => exact fun _ m => nomatch m
  | opened calls =>
    intro e m
    rcases List.mem_cons.mp m with rfl | m
    · exact .inr (.inr (.inl rfl))
    · rcases calls e m with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inr (.inr (.inr (.inr (.inr rfl))))
  | openTrapped =>
    intro e m
    rw [List.mem_singleton.mp m]
    exact .inr (.inr (.inl rfl))
  | exitRejected =>
    intro e m
    rw [List.mem_singleton.mp m]
    trivial

/-- The `openat2` calls of `OpenCalls` whose results lie in Linux's range give a returned reply. -/
theorem openCalls_returned {L : ShimLayout} {dir : UInt64} {path how : List UInt8} :
    ∀ {calls : Nat} {l : List Linux.Event} {message : String} {outputs : List Bytes},
      OpenCalls L dir path how calls l (.trapped message outputs) → InRange l → False
  | _, [], _, _, h, _ => h.elim
  | _, e :: l, _, _, ⟨ret, event, rest⟩, range => by
    subst event
    split at rest
    · exact openCalls_returned rest (fun x m => range x (List.mem_cons_of_mem _ m))
    · obtain ⟨rfl, same⟩ := rest
      rcases openReply_ranged ((range _ (List.mem_singleton_self _)).2.1 rfl) with
        ⟨_, reply⟩ | ⟨_, _, reply⟩ <;> rw [reply] at same <;> cases same

/-- No call of the command's events has an image with results in Linux's range whose reply
trapped. -/
theorem image_untrapped {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Event} {l : List Linux.Event} (image : Image F L I events e l) (trapped : TrappedCall e)
    (command : CommandEvent e) (range : InRange l) (fit : stringsFit I.args = true) : False := by
  cases e with
  | write output bytes reply =>
    cases reply with
    | returned => exact trapped
    | trapped message committed =>
      obtain rfl : output = .stdout := command
      obtain ⟨x, rfl, -, -, -, -, ending⟩ := write_native image range
      rcases ending with ⟨-, same⟩ | ⟨-, _, same⟩ <;> cases same
  | sys call args reply =>
    cases reply with
    | returned => exact trapped
    | trapped message committed =>
      obtain ⟨-, sys⟩ := image
      rcases command with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [sysImage_argsSizes] at sys
        obtain ⟨-, -, same⟩ := sys
        unfold sizesReply at same
        split at same <;> cases same
      · rw [sysImage_args] at sys
        obtain ⟨-, -, same⟩ := sys
        unfold stringsReply at same
        rw [ite_eq_left fit] at same
        cases same
      · rw [sysImage_open] at sys
        unfold OpenImage at sys
        split at sys
        · split at sys
          · exact openCalls_returned sys range
          · cases sys.2
        · exact sys
      · rw [sysImage_close] at sys
        unfold CloseImage at sys
        split at sys
        · split at sys
          · obtain ⟨ret, rfl, same⟩ := sys
            unfold closeReply at same
            rcases (range _ (List.mem_singleton_self _)).2.2.1 rfl with zero | error
            · dsimp only at zero
              rw [ite_eq_left zero] at same
              cases same
            · dsimp only at error
              have nonzero : ret ≠ 0 := by
                rintro rfl
                simp [Linux.isError] at error
              rw [ite_eq_right nonzero, ite_eq_left error] at same
              cases same
          · cases sys.2
        · exact sys
      · rw [sysImage_read] at sys
        unfold HandleReadImage at sys
        split at sys
        · rename_i fd capacity
          split at sys
          · rename_i held
            obtain ⟨a, prior, ret, output, rfl, same⟩ := sys
            rcases (range _ (List.mem_singleton_self _)).1 (.inl rfl) with error | within
            · dsimp only at error
              revert same
              unfold handleReadReply
              simp only [error, ↓reduceIte]
              split <;> exact fun same => by cases same
            · change ret.toNat ≤ capacity.toNat at within
              unfold handleReadReply at same
              rw [ite_eq_left within] at same
              cases same
          · cases sys.2
        · exact sys
      · rw [sysImage_filestat] at sys
        unfold FilestatImage at sys
        split at sys
        · split at sys
          · rename_i held
            obtain ⟨ret, output, rfl, same⟩ := sys
            rcases (range _ (List.mem_singleton_self _)).2.2.2 rfl with error | ⟨zero, valid⟩
            · dsimp only at error
              have nonzero : ret ≠ 0 := by
                rintro rfl
                simp [Linux.isError] at error
              unfold filestatReply at same
              rw [ite_eq_right nonzero, ite_eq_left error] at same
              cases same
            · dsimp only at zero valid
              subst zero
              rcases Classical.em (Overflows output) with beyond | fits
              · rw [filestatReply_over valid beyond] at same
                cases same
              · rw [filestatReply_fits valid fits] at same
                cases same
          · cases sys.2
        · exact sys
  | read => exact command
  | exit => exact trapped
  | exitTrap => exact trapped

/-- Under the shim's host, every run of `main` and its exit from a launch whose arguments have no
zero byte and whose strings and eight-byte pointers take at most `argsLimit` bytes, whose layer
events, the images of its WASI events, have results in Linux's range, ends at the accepted exit,
and its layer events and status meet `NMeets`. -/
theorem linux_exec_meets {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit} {ls : List Linux.Event}
    (noZero : ∀ s ∈ I.args, (0 : UInt8) ∉ s)
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (execution : Exec (linuxHost F L I R) (main.bind fun status => Action.exit status) world T
      outcome final)
    (images : Images F L I world.events T ls) (range : InRange ls) (sized : Sized ls) :
    ∃ c, outcome = .exited c ∧ NMeets I.args ls c := by
  have fit := stringsFit_of_le (by decide) small
  have accepts : ∀ {world code message final}, (linuxHost F L I R).exitTrap world code message
      final → 126 ≤ code.toNat := fun rejected => rejected.1
  cases outcome with
  | returned v => exact (bind_exit_not_returned execution).elim
  | trapped m =>
    exfalso
    obtain ⟨e, member, trapped⟩ := exec_trapped_call accepts execution
    obtain ⟨-, ⟨closed, rest, split, handled, unfinished⟩, -⟩ := trapped_soFar execution
    have command : CommandEvent e := by
      rw [split] at member
      rcases List.mem_append.mp member with m | m
      · exact handled.commands e m
      · exact unfinished.commands e m
    obtain ⟨_, l, image, sub⟩ := images_mem images e member
    exact image_untrapped image trapped command (fun x m => range x (sub x m)) fit
  | exited c =>
    obtain ⟨events, rfl, -, a, manifest, run, confined, handled⟩ := exec_main execution
    obtain ⟨le, lx, rfl, eventImages, exitImages⟩ := images_split images
    have exitEmpty : lx = [] := by
      obtain ⟨l, rest, rfl, image, more⟩ := images_cons exitImages
      cases more
      rw [List.append_nil]
      exact image
    subst exitEmpty
    rw [List.append_nil] at range sized ⊢
    have nrun := run_native noZero small run eventImages range sized
    have accepted := confined_accepted run confined
    refine ⟨c, rfl, manifest, nrun, ?_⟩
    obtain ⟨pre, rest, middle, -, argsRun, -, -, -⟩ := run
    obtain ⟨-, aBytes, -⟩ := linux_args (by decide) (by decide) small argsRun
    have buffer : a.bytes.data.data.toList = stringsBytes I.args := by
      rw [aBytes]
      simp [bytesOfList]
    obtain ⟨nhandled, opens⟩ := handled_native
      (P := fun name => (∃ program, I.args = [program, name]) ∨
        (lines manifest ≠ [] ∧ (∀ l ∈ lines manifest, WellFormed l.2) ∧
          ∃ l ∈ lines manifest, name = l.2.drop 66)) handled eventImages range
      (fun args reply m => by
        obtain ⟨name, ⟨rfl, one⟩ | ⟨rfl, nonempty, all, l, hl, rfl⟩⟩ := accepted args reply m
        · rw [buffer, oneArgument_args noZero] at one
          exact ⟨name, .inl rfl, .inl one⟩
        · exact ⟨_, .inr rfl, .inr ⟨nonempty, all, l, hl, rfl⟩⟩)
    exact ⟨fun x m c => opens x m c, nhandled⟩

#print axioms run_native
#print axioms handled_native
#print axioms exec_trapped_call
#print axioms linux_exec_meets

end Demos.ManifestCheck
