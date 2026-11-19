import Demos.RandomHistogram.Native
import Verified.Examples.WasiReadAllMessage

/-! The random-residue histogram's corollary at the shim's specification level, over the layer
events of a run under `linuxHost`.

`Full ls` states that every `getrandom` of the layer events `ls` returned the count that it asked
for and that every `write` returned an error number or at most the count of bytes that it offered,
as Linux's `write` does.  `randomData ls` collects the bytes that the `getrandom` events returned,
and `Counts args ls status` states the layer events and the exit status that the request asks of
a run whose `getrandom` calls return every byte, with the arguments `args`.  With N the value that
`parseSpec` reads from the arguments, each followed by a zero byte: when `parseSpec` refuses the
arguments, no layer event precedes `exit_group`, and the status is 2.  Otherwise the events are
calls of `getrandom`, each of at most 4,096 bytes with flags 0, followed by calls of `write` of
descriptor 1, the bytes that `getrandom` returned hold exactly N little-endian words `w`, the counts
of `histogramSpec w` sum to N, and the bytes that the writes took form a prefix of
`renderSpec (histogramSpec w)`, and each write offered the bytes that the writes before it did not
take (`OfferedLayer`).  The status is 0 exactly when that prefix is the whole output.  Either
every write returned at most its count and the status is 0, or 77 after one write for each of the
loop's passes, or the last write returned an error number whose errno is the status.

`linux_exec_counts` proves `Counts` for every `Exec` run of `main` and its exit under the shim's
host, from a launch whose arguments' strings and eight-byte pointers take at most `argsLimit`
bytes, whose layer events, the images of its WASI events, meet `Full`, and such a run ends at the
accepted exit.  A run that traps would have a trapped `args_sizes_get`, `args_get`,
`random_get`, or `fd_write` (`main_trapped`), whose image no event sequence that meets `Full`
gives (`image_untrapped`), and the shim accepts every status of at most 77.

`fullReplies_run` shows that the premises can hold together.  The replies `fullReplies` answer
call 0 with 8 zero bytes and every later call with the size of `oneOutput`, the ten lines of the
counts of one word of residue 0.  Under them, every run of `main` and its exit with the arguments
`oneArgs`, which give N of 1, makes a `getrandom` of 8 bytes and a `write` of `oneOutput`, each
answered in full, ends at the accepted exit with status 0, and has layer events that meet
`Full`. -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The bytes that the `getrandom` events of `ls` returned, in order: for each, the first bytes of
its output region, as many as its result. -/
def randomData (ls : List Linux.Event) : List UInt8 :=
  ls.flatMap fun e => if e.call = Linux.getrandomCall then e.output.take e.ret.toNat else []

/-- Every `getrandom` of `ls` returned the count that it asked for, and every `write` of `ls` an
error number or at most the count of bytes that it offered. -/
def Full (ls : List Linux.Event) : Prop :=
  ∀ e ∈ ls, (e.call = Linux.getrandomCall → e.ret = Linux.arg e.args 1) ∧
    (e.call = Linux.writeCall →
      Linux.isError e.ret = true ∨ e.ret.toNat ≤ (Linux.arg e.args 2).toNat)

/-- A `getrandom` of at most 4,096 bytes with flags 0. -/
def Drawing (e : Linux.Event) : Prop :=
  e.call = Linux.getrandomCall ∧ (Linux.arg e.args 1).toNat ≤ 4096 ∧ Linux.arg e.args 2 = 0

/-- The output that the request asks for from the words of the bytes that the `getrandom` events
of `ls` returned: `renderSpec` of their counts. -/
def askedOutput (ls : List Linux.Event) : List UInt8 :=
  (renderSpec (histogramSpec (words (randomData ls)).toArray)).data.data.toList

/-- `OfferedLayer out taken ls`: the input of each event of `ls` holds the bytes of `out` after the
first `taken` and those that the events before it took as writes of descriptor 1. -/
def OfferedLayer (out : List UInt8) : Nat → List Linux.Event → Prop
  | _, [] => True
  | taken, e :: rest => e.inputs.headD [] = out.drop taken ∧
    OfferedLayer out (taken + (Linux.Event.writeBytes 1 e).length) rest

/-- The event `e` returned at most the count of bytes that it offered. -/
def Took (e : Linux.Event) : Prop := e.ret.toNat ≤ (Linux.arg e.args 2).toNat

/-- The layer events `ls` and the exit status `status` that the request asks of a run whose
`getrandom` calls return every byte, with the arguments `args`, each followed by a zero byte in the
buffer from which `parseSpec` reads N.  When `parseSpec` refuses the arguments, no layer event
precedes `exit_group`, and the status is 2.  Otherwise the events are calls of `getrandom`, each of
at most 4,096 bytes with flags 0, followed by calls of `write` of descriptor 1, the bytes that
`getrandom` returned hold exactly N words `w`, and the counts of `histogramSpec w` sum to N.  Each
write offered the bytes of `renderSpec (histogramSpec w)` that the writes before it did not take,
and the bytes that the writes took form a prefix of that output.  The status is 0 exactly when
they are the whole output.  Either every write returned at most its count and the status is 0, or
77 after one write for each of the loop's passes, or the last write returned an error number whose
errno is the status and every write before it returned at most its count. -/
def Counts (args : List (List UInt8)) (ls : List Linux.Event) (status : UInt64) : Prop :=
  (parseSpec (bytesOfList (stringsBytes args)) = 0 → ls = [] ∧ status = 2) ∧
  (parseSpec (bytesOfList (stringsBytes args)) ≠ 0 →
    (words (randomData ls)).length = (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
    ((histogramSpec (words (randomData ls)).toArray).toList.map UInt64.toNat).sum =
      (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
    Linux.writeData 1 ls <+: askedOutput ls ∧ (status = 0 ↔ Linux.writeData 1 ls = askedOutput ls) ∧
    ∃ draws writes, ls = draws ++ writes ∧ (∀ e ∈ draws, Drawing e) ∧
      (∀ e ∈ writes, e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1) ∧
      OfferedLayer (askedOutput ls) 0 writes ∧
      (((∀ e ∈ writes, Took e) ∧
          (status = 0 ∨ (status = 77 ∧ writes.length = (askedOutput ls).length + 1))) ∨
        (status ≠ 0 ∧ ∃ before e, writes = before ++ [e] ∧ (∀ x ∈ before, Took x) ∧
          Linux.isError e.ret = true ∧ status = errnoOf (0 - e.ret))))

/-! ## Trapped runs of `main` -/

/-- A trapped `args_sizes_get`, `args_get`, or `random_get`, or a trapped write. -/
def TrapEvent : Event → Prop
  | .sys call _ (.trapped _ _) => call = .argsSizesGet ∨ call = .argsGet ∨ call = .randomGet
  | .write _ _ (.trapped _ _) => True
  | _ => False

/-- A trapped run of `args` has a trapped `args_sizes_get` or `args_get`. -/
theorem args_trapped {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {message : String}
    (run : Exec host args world trace (.trapped message) final) : ∃ e ∈ trace, TrapEvent e := by
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap => exact ⟨_, List.mem_singleton_self _, .inl rfl⟩
  | sys_return _ _ next =>
    beta_reduce at next
    split at next
    · cases next
    · split at next
      · cases next
      · cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap => exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), .inr (.inl rfl)⟩
        | sys_return _ _ next =>
          beta_reduce at next
          split at next <;> cases next

/-- A trapped loop of `main` has a trapped `random_get`. -/
theorem loop_trapped {World : Type} {host : Host World} {test : UInt64 → DrawState → Bool}
    {step : UInt64 → DrawState → Action DrawState} (stepped : DrawStep step) :
    ∀ (remaining index : Nat) (state : DrawState) {world trace final} {message : String},
      LoopExec host remaining index state test step .pure world trace (.trapped message) final →
      ∃ e ∈ trace, TrapEvent e
  | 0, _, _, _, _, _, _, run => by
    cases run with
    | zero next => cases next
  | remaining + 1, index, state, _, _, _, _, run => by
    cases run with
    | stop _ next => cases next
    | next _ _ rest =>
      obtain ⟨e, member, trapped⟩ := loop_trapped stepped remaining (index + 1) _ rest
      exact ⟨e, List.mem_append_right _ member, trapped⟩
    | trap _ step =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (randomGet_window_accepted _ _) fits
      | sys_trap => exact ⟨_, List.mem_singleton_self _, .inr (.inr rfl)⟩
      | sys_return _ _ next =>
        beta_reduce at next
        split at next <;> cases next

/-- A trapped run of `main` under a host that accepts every exit status below 126 has a trapped
`args_sizes_get`, `args_get`, `random_get`, or write. -/
theorem main_trapped {World : Type} {host : Host World}
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat)
    {world final : World} {trace : List Event} {message : String}
    (run : Exec host main world trace (.trapped message) final) : ∃ e ∈ trace, TrapEvent e := by
  obtain ⟨after, pre, middle, rest, argsRun, cont, rfl⟩ := Exec.unbind args run
  cases middle with
  | exited c => exact absurd rfl ((args_returned argsRun).1 c)
  | trapped m =>
    obtain ⟨e, member, trapped⟩ := args_trapped argsRun
    exact ⟨e, List.mem_append_left _ member, trapped⟩
  | returned a =>
    have aSize := ((args_returned argsRun).2 a rfl).2
    have parsed : parseN a.bytes = parseSpec a.bytes := parseN_eq a.bytes (by omega)
    change Exec host (if a.errno != 0 then Action.pure a.errno else _) after rest _ final at cont
    split at cont
    · cases cont
    dsimp only at cont
    rw [parsed] at cont
    split at cont
    · cases cont
    generalize parseSpec a.bytes = n at cont
    obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont
    cases loopRun with
    | loop loopRun =>
    cases drawn with
    | exited c => cases cont2.2.1
    | trapped m =>
      obtain ⟨e, member, trapped⟩ := loop_trapped (fun _ _ => rfl) _ _ _ loopRun
      exact ⟨e, List.mem_append_right _ (List.mem_append_left _ member), trapped⟩
    | returned s =>
      change Exec host (if s.2.2.2 != 0 then Action.pure s.2.2.2 else _) loopAfter post _ final
        at cont2
      split at cont2
      · cases cont2
      change Exec host (Action.bind (writeAll (render s.1)) fun written =>
          Action.pure (if written < (render s.1).size then 77 else 0))
        loopAfter post _ final at cont2
      obtain ⟨writeAfter, writes, middle, tail, writeRun, cont3, rfl⟩ := Exec.unbind _ cont2
      cases middle with
      | returned value =>
        change Exec host (Action.pure (if value < (render s.1).size then (77 : UInt64) else 0))
          writeAfter tail _ final at cont3
        generalize (if value < (render s.1).size then (77 : UInt64) else 0) = status at cont3
        cases cont3
      | exited c => cases cont3.2.1
      | trapped m =>
        obtain ⟨rfl, same, -⟩ := cont3
        cases same
        have small := render_size s.1
        obtain ⟨offered, committed, member⟩ :=
          (writeAll_run (by omega) writeRun).trapped_write accepts _ rfl
        exact ⟨_, List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ member)), trivial⟩

/-! ## The images under `Full` -/

theorem Full.sub {ls ls' : List Linux.Event} (full : Full ls) (sub : ∀ x ∈ ls', x ∈ ls) :
    Full ls' := fun e member => full e (sub e member)

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

/-- A `random_get` of `length` bytes whose `getrandom` events return the counts that they ask for
returns errno 0: with no event and no byte when `length` is 0, and otherwise with one event, a
`getrandom` of `length` bytes with flags 0, and the bytes of its output region. -/
theorem random_full {a : UInt64} {length : Nat} {l : List Linux.Event}
    {reply : Transfer (List Bytes)} (calls : RandomCalls a length 0 [] l reply) (full : Full l)
    (small : length < 2 ^ 64) :
    (l = [] ∧ length = 0 ∧ reply = .returned 0 [bytesOfList []]) ∨
      ∃ e, l = [e] ∧ e.call = Linux.getrandomCall ∧ e.ret.toNat = length ∧
        Linux.arg e.args 1 = UInt64.ofNat length ∧ Linux.arg e.args 2 = 0 ∧
        reply = .returned 0 [bytesOfList e.output] := by
  rcases l with _ | ⟨e, rest⟩
  · obtain ⟨done, rfl⟩ := calls
    exact .inl ⟨rfl, done.symm, rfl⟩
  · obtain ⟨_, prior, ret, output, rfl, going⟩ := calls
    have answered := (full _ (List.mem_cons_self ..)).1 rfl
    simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_zero] at answered
    have retNat : ret.toNat = length := by
      rw [answered, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt small
    rw [ite_eq_right (by omega)] at going
    obtain ⟨rfl, rfl⟩ := going
    refine .inr ⟨_, rfl, rfl, retNat, by simp [Linux.arg], rfl, ?_⟩
    simp [randomLast, retNat]

/-- No event sequence that meets `Full` is the image of a trapped `args_sizes_get`, `args_get`,
`random_get`, or write when the arguments fit. -/
theorem image_untrapped {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Event} {l : List Linux.Event} (image : Image F L I events e l) (trapped : TrapEvent e)
    (full : Full l) (fit : stringsFit I.args = true) : False := by
  cases e with
  | sys call args reply =>
    cases reply with
    | returned => exact trapped
    | trapped message committed =>
      obtain ⟨-, image⟩ := image
      rcases trapped with rfl | rfl | rfl
      · rw [sysImage_argsSizes] at image
        obtain ⟨-, -, reply⟩ := image
        unfold sizesReply at reply
        split at reply <;> cases reply
      · rw [sysImage_args] at image
        obtain ⟨-, -, reply⟩ := image
        unfold stringsReply at reply
        rw [ite_eq_left fit] at reply
        cases reply
      · rw [sysImage_random] at image
        unfold RandomImage at image
        split at image
        · rename_i length
          obtain ⟨a, calls⟩ := image
          rcases random_full calls full length.toNat_lt with
            ⟨-, -, reply⟩ | ⟨_, -, -, -, -, -, reply⟩ <;> cases reply
        · exact image
  | write output bytes reply =>
    cases reply with
    | returned => exact trapped
    | trapped message committed =>
      obtain ⟨x, a, rfl, call, args, -, -, small, reply⟩ := image
      have answered := (full x (List.mem_singleton_self _)).2 call
      simp only [args, Linux.arg, List.getD_cons_succ, List.getD_cons_zero] at answered
      unfold writeReply at reply
      split at reply
      · cases reply
      · rename_i notWithin
        split at reply
        · cases reply
        · rename_i notError
          rcases answered with error | within
          · exact notError error
          · exact notWithin within
  | read => exact trapped
  | exit => exact trapped
  | exitTrap => exact trapped

/-! ## Runs that exit -/

theorem stringsFit_of_small {strings : List (List UInt8)}
    (small : stringsSize strings + 8 * strings.length ≤ argsLimit) :
    stringsFit strings = true := by
  unfold stringsFit argsLimit at *
  simp only [decide_eq_true_eq]
  omega

/-- Under the shim's host, an `args_sizes_get` reply for arguments that fit is errno 0 with their
count and size. -/
theorem linux_sizes_fit {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world after : LinuxWorld} {errno : UInt64} {outputs : List LeanExe.Bytes}
    (step : (linuxHost F L I R).sys world Call.argsSizesGet [] (.returned errno outputs) after)
    (fit : stringsFit I.args = true) :
    errno = 0 ∧ outputs = sizesOutputs I.args := by
  obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
  rw [sysImage_argsSizes] at image
  obtain ⟨-, -, reply⟩ := image
  unfold sizesReply at reply
  rw [ite_eq_left fit] at reply
  exact ⟨(Transfer.returned.inj reply).1, (Transfer.returned.inj reply).2⟩

/-- Under the shim's host, a returned `args_get` reply is errno 0 with the arguments, each followed
by a zero byte. -/
theorem linux_strings_any {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world after : LinuxWorld} {errno : UInt64} {got : List LeanExe.Bytes}
    (step : (linuxHost F L I R).sys world Call.argsGet [] (.returned errno got) after) :
    errno = 0 ∧ got = [bytesOfList (stringsBytes I.args)] := by
  obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
  rw [sysImage_args] at image
  obtain ⟨-, -, reply⟩ := image
  unfold stringsReply at reply
  split at reply
  · exact ⟨(Transfer.returned.inj reply).1, (Transfer.returned.inj reply).2⟩
  · cases reply

/-- Under the shim's host, a returned `args` result for arguments whose strings and eight-byte
pointers take at most `argsLimit` bytes holds errno 0 and the arguments, and the images of its
events hold no layer event. -/
theorem linux_args {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {trace : List Event} {a : ArgsResult}
    (run : Exec (linuxHost F L I R) args world trace (.returned a) final)
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit) :
    a.errno = 0 ∧ a.bytes = bytesOfList (stringsBytes I.args) ∧
      ∀ events ls, Images F L I events trace ls → ls = [] := by
  have fit := stringsFit_of_small small
  have reported := reportedSize_le small
  unfold args at run
  obtain ⟨errno, sizes, middle, rest, rfl, reporter, next⟩ := exec_sys_returned run (by decide)
  obtain ⟨rfl, rfl⟩ := linux_sizes_fit reporter fit
  rw [ite_eq_right (by simp [sysReply])] at next
  have below : ¬4294967296 ≤ (sysReply 0 (sizesOutputs I.args)).word 1 +
      4 * (sysReply 0 (sizesOutputs I.args)).word 0 + 3 := by
    rw [UInt64.le_iff_toNat_le]
    simp only [Resource.reportedSize, sysReply, ↓reduceIte] at reported ⊢
    unfold argsLimit at reported
    simp only [UInt64.reduceToNat]
    omega
  rw [ite_eq_right below] at next
  obtain ⟨gotErrno, got, after, last, rfl, getter, next⟩ := exec_sys_returned next (by decide)
  obtain ⟨rfl, rfl⟩ := linux_strings_any getter
  rw [ite_eq_right (by simp [sysReply])] at next
  obtain ⟨rfl, same⟩ := exec_pure next
  cases same
  refine ⟨rfl, rfl, fun events ls images => ?_⟩
  cases images with
  | cons first images =>
    cases images with
    | cons second images =>
      cases images
      obtain ⟨-, first⟩ := first
      rw [sysImage_argsSizes] at first
      obtain ⟨-, rfl, -⟩ := first
      obtain ⟨-, second⟩ := second
      rw [sysImage_args] at second
      obtain ⟨-, rfl, -⟩ := second
      rfl

theorem randomData_append (ls ls' : List Linux.Event) :
    randomData (ls ++ ls') = randomData ls ++ randomData ls' := by
  simp [randomData, List.flatMap_append]

theorem writeData_append (ls ls' : List Linux.Event) :
    Linux.writeData 1 (ls ++ ls') = Linux.writeData 1 ls ++ Linux.writeData 1 ls' := by
  simp [Linux.writeData, List.flatMap_append]

/-- The images of the calls of `Draws` whose `getrandom` events meet `Full`: every call returned
errno 0, the bytes that `getrandom` returned are those that the calls collected, nothing was
written, and every event is a `getrandom` of at most 4,096 bytes with flags 0. -/
theorem draws_full {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {r : UInt64} {draws : List Event} {bytes : List UInt8} {errno : UInt64}
      {events ls : List Linux.Event}, Draws r draws bytes errno →
      Images F L I events draws ls → Full ls →
      errno = 0 ∧ randomData ls = bytes ∧ Linux.writeData 1 ls = [] ∧ ∀ e ∈ ls, Drawing e
  | _, _, _, _, _, _, .done, images, _ => by
    cases images
    exact ⟨rfl, rfl, rfl, fun _ member => nomatch member⟩
  | _, _, _, _, _, _, .failed _ failed, images, full => by
    cases images with
    | cons image rest =>
      cases rest
      obtain ⟨-, image⟩ := image
      rw [sysImage_random] at image
      obtain ⟨a, calls⟩ := image
      rw [List.append_nil] at full
      rcases random_full calls full (UInt64.toNat_lt _) with
        ⟨-, -, reply⟩ | ⟨_, -, -, -, -, -, reply⟩ <;>
        exact absurd (Transfer.returned.inj reply).1 failed
  | r, _, _, _, _, _, .drew nonzero size rest, images, full => by
    cases images with
    | cons image restImages =>
      obtain ⟨-, image⟩ := image
      rw [sysImage_random] at image
      obtain ⟨a, calls⟩ := image
      obtain ⟨errnoZero, restData, restWrites, restDrawing⟩ :=
        draws_full rest restImages (full.sub fun x m => List.mem_append_right _ m)
      rcases random_full calls (full.sub fun x m => List.mem_append_left _ m)
          (UInt64.toNat_lt _) with ⟨-, zero, -⟩ | ⟨e, rfl, call, retNat, asked, flags, reply⟩
      · rw [toNat_eight_min] at zero
        exact absurd (UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)) nonzero
      · have same := (List.cons.inj (Transfer.returned.inj reply).2).1
        subst same
        rw [toNat_eight_min] at retNat
        rw [bytesOfList_size] at size
        refine ⟨errnoZero, ?_, ?_, fun x member => ?_⟩
        · rw [List.singleton_append, ← List.singleton_append, randomData_append, restData]
          simp [randomData, call, retNat, ← size, bytesOfList]
        · have other : Linux.getrandomCall ≠ Linux.writeCall := by decide
          rw [List.singleton_append, ← List.singleton_append, writeData_append, restWrites]
          simp [Linux.writeData, Linux.Event.writeBytes, call, other]
        · rcases List.mem_cons.mp member with rfl | member
          · refine ⟨call, ?_, flags⟩
            rw [asked, UInt64.ofNat_toNat, toNat_eight_min]
            omega
          · exact restDrawing x member


/-- The image of a write to standard output that returned is one `write` of descriptor 1, which
took the bytes that the write took, whose input holds the bytes that the write offered, and holds
no `getrandom`.  When the write returned errno 0, the `write` returned at most its count, and when
the write returned an errno, the `write` returned an error number whose errno is the write's. -/
theorem write_image {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {offered : LeanExe.Bytes} {errno count : UInt64} {l : List Linux.Event}
    (image : Image F L I events (.write .stdout offered (.returned errno count)) l) :
    ∃ x, l = [x] ∧ x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1 ∧
      Linux.writeData 1 l = (Event.write .stdout offered (.returned errno count)).stdoutTaken ∧
      randomData l = [] ∧ x.inputs.headD [] = offered.data.data.toList ∧ (errno = 0 → Took x) ∧
      (errno ≠ 0 → Linux.isError x.ret = true ∧ errno = errnoOf (0 - x.ret)) := by
  obtain ⟨x, a, rfl, call, args, inputs, -, small, reply⟩ := image
  have wide : (UInt64.ofNat offered.data.size).toNat = offered.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  refine ⟨x, rfl, call, by simp [args, Linux.arg, Output.fd], ?_,
    by simp [randomData, call, other], by simp [inputs], fun zero => ?_, ?_⟩
  · unfold writeReply at reply
    split at reply
    · rename_i within
      obtain ⟨rfl, rfl⟩ := Transfer.returned.inj reply
      rw [wide] at within
      simp [Linux.writeData, Linux.Event.writeBytes, Event.stdoutTaken, call, args, inputs,
        Linux.arg, Output.fd, wide, within]
    · rename_i notWithin
      rw [wide] at notWithin
      split at reply
      · obtain ⟨rfl, rfl⟩ := Transfer.returned.inj reply
        simp [Linux.writeData, Linux.Event.writeBytes, Event.stdoutTaken, call, args, Linux.arg,
          Output.fd, wide, notWithin]
      · cases reply
  · unfold writeReply at reply
    split at reply
    · rename_i within
      simpa [Took, args, Linux.arg] using within
    · split at reply
      · exact absurd (Transfer.returned.inj reply).1.symm (by rw [zero]; exact (errnoOf_valid _).2)
      · cases reply
  · intro nonzero
    unfold writeReply at reply
    split at reply
    · exact absurd (Transfer.returned.inj reply).1 nonzero
    · split at reply
      · rename_i error
        exact ⟨error, (Transfer.returned.inj reply).1⟩
      · cases reply

/-- The images of writes to standard output that returned are `write` calls of descriptor 1, one
for each write, which took the bytes that the writes took and hold no `getrandom`, and each
offered the bytes that its write offered. -/
theorem writes_images {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {events : List Linux.Event} {writes : List Event} {ls : List Linux.Event}
      {out : List UInt8} {taken : Nat},
      Images F L I events writes ls →
      (∀ e ∈ writes, ∃ offered errno count, e = .write .stdout offered (.returned errno count)) →
      Offered out taken writes →
      Linux.writeData 1 ls = stdoutTaken writes ∧ randomData ls = [] ∧
        (∀ x ∈ ls, x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1) ∧
        ls.length = writes.length ∧ OfferedLayer out taken ls
  | _, _, _, _, _, .nil, _, _ => ⟨rfl, rfl, fun _ member => (nomatch member), rfl, trivial⟩
  | _, _, _, _, _, .cons image rest, shape, ⟨⟨offered', reply', same, offers⟩, offeredRest⟩ => by
    obtain ⟨offered, errno, count, rfl⟩ := shape _ (List.mem_cons_self ..)
    obtain ⟨-, rfl, -⟩ := Event.write.inj same
    obtain ⟨x, rfl, call, fd, data, noRandom, input, -, -⟩ := write_image image
    have bytes : Linux.Event.writeBytes 1 x =
        (Event.write .stdout offered (.returned errno count)).stdoutTaken := by
      simpa [Linux.writeData] using data
    obtain ⟨restData, restRandom, restShape, restLength, restOffered⟩ :=
      writes_images rest (fun e member => shape e (List.mem_cons_of_mem _ member))
        (by rw [← bytes] at offeredRest; exact offeredRest)
    refine ⟨by rw [writeData_append, data, restData, stdoutTaken_cons],
      by rw [randomData_append, noRandom, restRandom]; rfl, fun y member => ?_,
      by simp [restLength], ⟨by rw [input, offers], restOffered⟩⟩
    rcases List.mem_append.mp member with member | member
    · obtain rfl := List.mem_singleton.mp member
      exact ⟨call, fd⟩
    · exact restShape y member

/-- The images of writes to standard output that each returned errno 0 are `write` calls that
each returned at most their counts. -/
theorem writes_took {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {events : List Linux.Event} {writes : List Event} {ls : List Linux.Event},
      Images F L I events writes ls →
      (∀ e ∈ writes, ∃ offered count, e = .write .stdout offered (.returned 0 count)) →
      ∀ x ∈ ls, Took x
  | _, _, _, .nil, _ => fun _ member => (nomatch member)
  | _, _, _, .cons image rest, every => by
    obtain ⟨offered, count, rfl⟩ := every _ (List.mem_cons_self ..)
    obtain ⟨x, rfl, -, -, -, -, -, took, -⟩ := write_image image
    intro y member
    rcases List.mem_append.mp member with member | member
    · obtain rfl := List.mem_singleton.mp member
      exact took rfl
    · exact writes_took rest (fun e m => every e (List.mem_cons_of_mem _ m)) y member

/-- Under the shim's host, every run of `main` and its exit from a launch whose arguments'
strings and eight-byte pointers take at most `argsLimit` bytes, whose layer events, the images of
its WASI events, meet `Full`, ends at the accepted exit with a status that meets `Counts`. -/
theorem linux_exec_counts {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit} {ls : List Linux.Event}
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (execution : Exec (linuxHost F L I R) (main.bind fun status => Action.exit status) world T
      outcome final)
    (images : Images F L I world.events T ls) (full : Full ls) :
    ∃ c, outcome = .exited c ∧ Counts I.args ls c := by
  have fit := stringsFit_of_small small
  have accepts : ∀ {world code message final}, (linuxHost F L I R).exitTrap world code message
      final → 126 ≤ code.toNat := fun rejected => rejected.1
  cases outcome with
  | returned v => exact (Verified.Wasi.bind_exit_not_returned execution).elim
  | trapped m =>
    exfalso
    obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
    cases middle with
    | exited c => cases cont.2.1
    | trapped m' =>
      obtain ⟨e, member, trapped⟩ := main_trapped accepts mainRun
      obtain ⟨_, l, image, sub⟩ := images_mem images e (List.mem_append_left _ member)
      exact image_untrapped image trapped (full.sub sub) fit
    | returned status =>
      have low := ((main_runs mainRun).1 status rfl).1
      change Exec _ (Action.exit status) after rest (.trapped m) final at cont
      cases cont with
      | exitTrap rejected =>
        have high := rejected.1
        rw [exitStatus_of_lt (by omega)] at high
        omega
  | exited c =>
    obtain ⟨events, rfl, -, meets⟩ := exec_main execution
    refine ⟨c, rfl, ?_⟩
    obtain ⟨a, pre, rest, middle, rfl, argsRun, -, refused, accepted⟩ := meets
    obtain ⟨aZero, aBytes, preEmpty⟩ := linux_args argsRun small
    obtain ⟨l, lx, rfl, front, exitImages⟩ :=
      Verified.Examples.WasiReadAll.images_split images
    obtain ⟨lp, lr, rfl, preImages, restImages⟩ :=
      Verified.Examples.WasiReadAll.images_split front
    cases preEmpty _ _ preImages
    cases exitImages with
    | cons image tail =>
      cases tail
      cases image
      simp only [List.nil_append, List.append_nil] at full ⊢
      unfold Counts
      rw [← aBytes]
      constructor
      · intro zero
        obtain ⟨rfl, rfl⟩ := refused aZero zero
        cases restImages
        exact ⟨rfl, rfl⟩
      · intro nonzero
        obtain ⟨draws, bytes, errno, writes, rfl, drawn, -, succeeded⟩ := accepted aZero nonzero
        obtain ⟨ld, lw, rfl, drawImages, writeImages⟩ :=
          Verified.Examples.WasiReadAll.images_split restImages
        obtain ⟨errnoZero, drawData, drawWrites, drawing⟩ :=
          draws_full drawn drawImages (full.sub fun x m => List.mem_append_left _ m)
        obtain ⟨length, sum, offeredAll, prefix_, whole, kinds⟩ := succeeded errnoZero
        have shape : ∀ e ∈ writes, ∃ offered errno count,
            e = .write .stdout offered (.returned errno count) := by
          rcases kinds with ⟨all, -⟩ | ⟨-, -, before, offered, count, rfl, earlier⟩
          · intro e member
            obtain ⟨offered, count, rfl⟩ := all e member
            exact ⟨_, _, _, rfl⟩
          · intro e member
            rcases List.mem_append.mp member with member | member
            · obtain ⟨offered, count, rfl⟩ := earlier e member
              exact ⟨_, _, _, rfl⟩
            · obtain rfl := List.mem_singleton.mp member
              exact ⟨_, _, _, rfl⟩
        obtain ⟨writeBytes, noRandom, writeShape, writeLength, offeredLayer⟩ :=
          writes_images writeImages shape offeredAll
        have random : randomData (ld ++ lw) = bytes := by
          rw [randomData_append, drawData, noRandom, List.append_nil]
        have taken : Linux.writeData 1 (ld ++ lw) = stdoutTaken writes := by
          rw [writeData_append, drawWrites, writeBytes, List.nil_append]
        have asked : askedOutput (ld ++ lw) =
            (renderSpec (histogramSpec (words bytes).toArray)).data.data.toList := by
          unfold askedOutput
          rw [random]
        rw [asked, random, taken]
        refine ⟨length, sum, prefix_, whole, ld, lw, rfl, drawing, writeShape, offeredLayer, ?_⟩
        rcases kinds with ⟨all, zeroOr⟩ | ⟨failing, -, before, offered, count, rfl, earlier⟩
        · refine .inl ⟨writes_took writeImages all, ?_⟩
          rcases zeroOr with zero | ⟨seventySeven, passes⟩
          · exact .inl zero
          · exact .inr ⟨seventySeven, by rw [writeLength, passes]⟩
        · obtain ⟨lb, lf, rfl, beforeImages, lastImages⟩ :=
            Verified.Examples.WasiReadAll.images_split writeImages
          cases lastImages with
          | cons image tail =>
            cases tail
            obtain ⟨x, rfl, -, -, -, -, -, -, failed⟩ := write_image image
            obtain ⟨error, same⟩ := failed failing
            exact .inr ⟨failing, lb, x, by simp, writes_took beforeImages earlier, error, same⟩

/-! ## Replies that answer every call in full -/

/-- The arguments of a run with N of 1: the program name `h` and the argument `1`. -/
def oneArgs : List (List UInt8) := [[104], [49]]

/-- The output of a run with N of 1 whose word has residue 0: the ten lines of the counts of
`#[0]`. -/
def oneOutput : LeanExe.Bytes := renderSpec (histogramSpec #[0])

/-- The replies of a run with the arguments `oneArgs` that answer each of its calls in full: call
0, the `getrandom` of the run's one word, with 8 bytes, each 0, and every later call, the `write`
of `oneOutput` among them, with the size of `oneOutput`. -/
def fullReplies : Linux.Replies := fun k =>
  if k = 0 then ⟨8, fun _ => 0⟩ else ⟨UInt64.ofNat oneOutput.data.size, fun _ => 0⟩

/-- The replies that the events of `l ++ l'` hold from call `k` on: those of `l` from `k`, and
those of `l'` from `k` plus the length of `l`. -/
theorem carried_split {R : Linux.Replies} :
    ∀ {k : Nat} {l l' : List Linux.Event}, Carried R k (l ++ l') →
      Carried R k l ∧ Carried R (k + l.length) l'
  | _, [], _, carried => ⟨trivial, by simpa using carried⟩
  | k, _ :: l, _, ⟨carries, rest⟩ => by
    obtain ⟨first, second⟩ := carried_split rest
    refine ⟨⟨carries, first⟩, ?_⟩
    simp only [List.length_cons]
    rwa [show k + (l.length + 1) = k + 1 + l.length by omega]

/-- The images of no event are no layer event. -/
theorem images_nil {F : OpenFlags} {L : ShimLayout} {I : Launch} {events ls : List Linux.Event}
    (images : Images F L I events [] ls) : ls = [] := by
  cases images
  rfl

/-- Under the shim's host, a run of `args` for arguments that fit never traps. -/
theorem linux_args_untrapped {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {trace : List Event} {message : String}
    (run : Exec (linuxHost F L I R) args world trace (.trapped message) final)
    (fit : stringsFit I.args = true) : False := by
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap _ step =>
    obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
    rw [sysImage_argsSizes] at image
    obtain ⟨-, -, reply⟩ := image
    unfold sizesReply at reply
    rw [ite_eq_left fit] at reply
    cases reply
  | sys_return _ _ next =>
    beta_reduce at next
    split at next
    · cases next
    · split at next
      · cases next
      · cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap _ step =>
          obtain ⟨l, ⟨-, image⟩, -, -, -⟩ := step
          rw [sysImage_args] at image
          obtain ⟨-, -, reply⟩ := image
          unfold stringsReply at reply
          rw [ite_eq_left fit] at reply
          cases reply
        | sys_return _ _ next =>
          beta_reduce at next
          split at next <;> cases next

/-- The image of `random_get` of 8 bytes whose first layer event holds the reply `fullReplies 0` is
that event alone, a `getrandom` that returned the count that it asked for, and the reply is errno 0
with 8 zero bytes. -/
theorem random_one {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {reply : Transfer (List LeanExe.Bytes)} {l rest : List Linux.Event}
    (image : Image F L I events (.sys .randomGet [.space 8] reply) l)
    (carried : Carried fullReplies 0 (l ++ rest)) :
    (∃ e, l = [e] ∧ e.call = Linux.getrandomCall ∧ e.ret = Linux.arg e.args 1) ∧
      reply = .returned 0 [bytesOfList (List.replicate 8 0)] := by
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  rcases l with _ | ⟨e, more⟩
  · obtain ⟨done, -⟩ := calls
    exact absurd done (by decide)
  · obtain ⟨-, prior, ret, output, rfl, going⟩ := calls
    obtain ⟨⟨answered, filled⟩, -⟩ := carried
    simp only [fullReplies, ↓reduceIte] at answered filled
    subst answered
    rw [ite_eq_right (by decide)] at going
    obtain ⟨rfl, rfl⟩ := going
    refine ⟨⟨_, rfl, rfl, rfl⟩, ?_⟩
    rw [filled]
    rfl

/-- The loop's buffer after the one call of the run with N of 1 under `fullReplies`: 4,096 zero
bytes with the reply's 8 zero bytes at its start. -/
def oneBuffer : LeanExe.Bytes :=
  (Bytes.build 4096 fun _ => 0).splice 0 (bytesOfList (List.replicate 8 0))

/-- The output of the run with N of 1 under `fullReplies`: `render` of the counts of the word that
the first 8 bytes of `oneBuffer` hold is `oneOutput`. -/
theorem one_rendered : render (tally (LeanExe.build 10 fun _ => 0) oneBuffer 1) = oneOutput := by
  have size : (bytesOfList (List.replicate 8 0)).data.size = 8 := by
    rw [bytesOfList_size]
    rfl
  have big : oneBuffer.data.size = 4096 := (Bytes.splice_size (by simp [size])).trans (by simp)
  rw [tally_eq _ _ _ (by rw [big]; decide) (by rw [big]; decide)]
  have hTake : 8 * (1 : UInt64).toNat = (bytesOfList (List.replicate 8 0)).data.size := by
    rw [size]
    rfl
  rw [hTake, oneBuffer, splice_take (by simp [size])]
  have zero : words (bytesOfList (List.replicate 8 0)).data.data.toList = [0] := by decide
  rw [zero, ← histogram_list, histogram_eq, render_eq]
  rfl

/-- Under the shim's host with the arguments `oneArgs` and the replies `fullReplies`, every run of
`main` and its exit ends at the accepted exit with status 0, and its layer events, the images of
its WASI events, meet `Full`: a `getrandom` of 8 bytes and a `write` of `oneOutput`, each answered
in full. -/
theorem fullReplies_run {F : OpenFlags} {L : ShimLayout} {environ : List (List UInt8)}
    {granted : Bool} {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit}
    {ls : List Linux.Event}
    (execution : Exec (linuxHost F L ⟨oneArgs, environ, granted⟩ fullReplies)
      (main.bind fun status => Action.exit status) world T outcome final)
    (images : Images F L ⟨oneArgs, environ, granted⟩ world.events T ls)
    (carried : Carried fullReplies 0 ls) : outcome = .exited 0 ∧ Full ls := by
  have small : stringsSize oneArgs + 8 * oneArgs.length ≤ argsLimit := by decide
  have fit := stringsFit_of_small small
  have parsed : parseN (bytesOfList (stringsBytes oneArgs)) = 1 := by decide
  have once : ((1 : UInt64) / 512 + 1).toNat = 1 := by decide
  have outSmall : oneOutput.data.size ≤ 210 := one_rendered ▸ render_size _
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨lm, lx, rfl, mainImages, exitImages⟩ :=
    Verified.Examples.WasiReadAll.images_split images
  obtain ⟨after1, pre, middle1, rest1, argsRun, cont1, rfl⟩ := Exec.unbind args mainRun
  obtain ⟨lp, lq, rfl, preImages, restImages⟩ :=
    Verified.Examples.WasiReadAll.images_split mainImages
  cases middle1 with
  | exited c => exact absurd rfl ((args_returned argsRun).1 c)
  | trapped m => exact (linux_args_untrapped argsRun fit).elim
  | returned a =>
  obtain ⟨aZero, aBytes, preEmpty⟩ := linux_args argsRun small
  cases preEmpty _ _ preImages
  simp only at aBytes
  change Exec _ (if a.errno != 0 then Action.pure a.errno else _) after1 rest1 middle after
    at cont1
  rw [ite_eq_right (by simp [aZero])] at cont1
  dsimp only at cont1
  rw [aBytes, parsed, ite_eq_right (by decide)] at cont1
  obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont1
  obtain ⟨ld, lw, rfl, drawImages, postImages⟩ :=
    Verified.Examples.WasiReadAll.images_split restImages
  have carried' : Carried fullReplies 0 (ld ++ (lw ++ lx)) := by
    simpa [List.append_assoc] using carried
  cases loopRun with
  | loop loopRun =>
  rw [once] at loopRun
  cases loopRun with
  | stop test _ => simp at test
  | exit _ step => exact (step_not_exited (i := UInt64.ofNat 0) (fun _ _ => rfl) step).elim
  | trap _ step =>
    change Exec _ (.sys .randomGet [.space ((Bytes.build 4096 fun _ => (0 : UInt64)).windowLength 0
      (8 * min (1 : UInt64) 512))] _) _ _ _ _ at step
    rw [window_draw (by simp) 1] at step
    cases step with
    | sys_reject fits => exact absurd (randomGet_accepted 1) fits
    | sys_trap _ _ =>
      cases drawImages with
      | cons image tail =>
        cases tail
        have answered := (random_one image (rest := lw ++ lx) (by simpa using carried')).2
        cases answered
    | sys_return _ _ next =>
      simp only [Action.bind] at next
      split at next <;> cases next
  | next _ step rest =>
    change Exec _ (.sys .randomGet [.space ((Bytes.build 4096 fun _ => (0 : UInt64)).windowLength 0
      (8 * min (1 : UInt64) 512))] _) _ _ _ _ at step
    rw [window_draw (by simp) 1] at step
    cases step with
    | sys_reject fits => exact absurd (randomGet_accepted 1) fits
    | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ _ next =>
    cases drawImages with
    | cons image drawRest =>
    obtain ⟨⟨e0, rfl, drawCall, drawFull⟩, answered⟩ :=
      random_one image (by rw [List.append_assoc] at carried'; exact carried')
    obtain ⟨rfl, rfl⟩ := Transfer.returned.inj answered
    have fillErrno : ∀ (buffer bytes : LeanExe.Bytes) (start count used : UInt64),
        (FillResult.of buffer start count (sysReply 0 [bytes]).errno used
          ((sysReply 0 [bytes]).bytes 0)).errno = 0 := by
      intro buffer bytes start count used
      simp [FillResult.of, sysReply]
    have fillBuffer : ∀ (buffer bytes : LeanExe.Bytes) (start count used : UInt64),
        (FillResult.of buffer start count (sysReply 0 [bytes]).errno used
          ((sysReply 0 [bytes]).bytes 0)).buffer =
          buffer.splice (buffer.window start count).1 bytes := by
      intro buffer bytes start count used
      simp [FillResult.of, sysReply, Reply.bytes]
    simp only [Action.bind, fillErrno, fillBuffer, Bytes.window_fst, UInt64.toNat_zero,
      Nat.zero_min, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
    rw [show min (1 : UInt64) 512 = 1 by decide,
      show (Bytes.build 4096 fun _ => (0 : UInt64)).splice 0 (bytesOfList (List.replicate 8 0)) =
        oneBuffer from rfl] at next
    generalize hCounts : tally (LeanExe.build 10 fun _ => (0 : UInt64)) oneBuffer 1 = counts
      at next
    generalize oneBuffer = buffer at next
    cases next
    cases rest with
    | zero next =>
    cases next
    obtain rfl := images_nil (show Images F L ⟨oneArgs, environ, granted⟩ _ [] _ from drawRest)
    change Exec _ (if (0 : UInt64) != 0 then _ else _) loopAfter post middle after at cont2
    rw [ite_eq_right (by decide)] at cont2
    change Exec _ (Action.bind (writeAll (render counts)) fun written =>
        Action.pure (if written < (render counts).size then 77 else 0)) loopAfter post middle after
      at cont2
    rw [← hCounts, one_rendered] at cont2
    obtain ⟨writeAfter, writes, written, tail, writeRun, cont3, rfl⟩ :=
      Exec.unbind (writeAll oneOutput) cont2
    obtain ⟨lws, ltl, rfl, writeImages, tailImages⟩ :=
      Verified.Examples.WasiReadAll.images_split postImages
    have later : Carried fullReplies 1 (lws ++ (ltl ++ lx)) := by
      have whole : Carried fullReplies 0 ([e0] ++ (lws ++ (ltl ++ lx))) := by
        simpa [List.append_assoc] using carried'
      simpa using (carried_split whole).2
    have firstFull : Full [e0] := by
      intro y member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨fun _ => drawFull, fun writing => absurd (drawCall.symm.trans writing) other.symm⟩
    have finish : ∀ {value : UInt64} {before before' : List Linux.Event},
        ¬value < oneOutput.size →
        Exec (linuxHost F L ⟨oneArgs, environ, granted⟩ fullReplies)
          (Action.pure (if value < oneOutput.size then 77 else 0)) writeAfter tail
          middle after → Images F L ⟨oneArgs, environ, granted⟩ before tail ltl →
        Images F L ⟨oneArgs, environ, granted⟩ before' rest lx →
        ltl = [] ∧ lx = [] ∧ outcome = .exited 0 := by
      intro value before before' notLess test testImages exitImages
      rw [ite_eq_right notLess] at test
      obtain ⟨rfl, rfl⟩ := exec_pure test
      cases testImages
      change Exec _ (Action.exit 0) after rest outcome final at cont
      cases cont with
      | exit _ =>
        cases exitImages with
        | cons image tail =>
          cases tail
          cases image
          exact ⟨rfl, rfl, rfl⟩
      | exitTrap rejected => exact absurd rejected.1 (by decide)
    have length : oneOutput.data.data.toList.length = oneOutput.data.size := by simp
    cases writeAll_run (by omega) writeRun with
    | done ended =>
      cases writeImages
      rw [UInt64.toNat_zero] at ended
      obtain ⟨rfl, rfl, rfl⟩ := finish (value := 0) (by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [Bytes.size, UInt64.toNat_zero, UInt64.toNat_ofNat']
        omega) cont3 tailImages exitImages
      refine ⟨rfl, ?_⟩
      simpa using firstFull
    | @wrote _ count _ offered events _ left offers within rest =>
      cases writeImages with
      | cons image writeRest =>
      obtain ⟨x, a', rfl, call, args, inputs, -, small', reply⟩ := image
      obtain ⟨⟨answered, -⟩, -⟩ := later
      simp only [fullReplies, Nat.one_ne_zero, ↓reduceIte] at answered
      have sizeEq : offered.data.size = oneOutput.data.size := by
        have := congrArg List.length offers
        simpa using this
      rw [answered, sizeEq] at reply
      simp only [writeReply, le_refl, ↓reduceIte] at reply
      obtain ⟨-, rfl⟩ := Transfer.returned.inj reply
      have reached : (0 + UInt64.ofNat oneOutput.data.size).toNat = oneOutput.data.size := by
        rw [UInt64.zero_add]
        exact UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
      cases rest with
      | done _ =>
        obtain rfl :=
          images_nil (show Images F L ⟨oneArgs, environ, granted⟩ _ [] _ from writeRest)
        obtain ⟨rfl, rfl, rfl⟩ := finish (by
          rw [UInt64.lt_iff_toNat_lt, reached]
          simp only [Bytes.size, UInt64.toNat_ofNat']
          omega) cont3 tailImages exitImages
        refine ⟨rfl, fun y member => ?_⟩
        simp only [List.nil_append, List.append_nil, List.mem_append, List.mem_singleton]
          at member
        rcases member with rfl | rfl
        · exact firstFull _ (List.mem_singleton_self _)
        · refine ⟨fun drawing => absurd (call.symm.trans drawing) other, fun _ => .inr ?_⟩
          simp [args, Linux.arg, answered, sizeEq]
      | wrote left' => rw [reached] at left'; omega
      | failed left' => rw [reached] at left'; omega
      | trapped left' => rw [reached] at left'; omega
    | failed left offers nonzero =>
      cases writeImages with
      | cons image _ =>
      obtain ⟨x, a', rfl, call, args, inputs, -, small', reply⟩ := image
      obtain ⟨⟨answered, -⟩, -⟩ := later
      simp only [fullReplies, Nat.one_ne_zero, ↓reduceIte] at answered
      have sizeEq := congrArg List.length offers
      simp at sizeEq
      rw [answered, sizeEq] at reply
      simp only [writeReply, le_refl, ↓reduceIte] at reply
      exact absurd (Transfer.returned.inj reply).1 nonzero
    | trapped left offers =>
      cases writeImages with
      | cons image _ =>
      obtain ⟨x, a', rfl, call, args, inputs, -, small', reply⟩ := image
      obtain ⟨⟨answered, -⟩, -⟩ := later
      simp only [fullReplies, Nat.one_ne_zero, ↓reduceIte] at answered
      have sizeEq := congrArg List.length offers
      simp at sizeEq
      rw [answered, sizeEq] at reply
      simp only [writeReply, le_refl, ↓reduceIte] at reply
      cases reply

#print axioms main_trapped
#print axioms image_untrapped
#print axioms linux_exec_counts
#print axioms fullReplies_run

end Demos.RandomHistogram
