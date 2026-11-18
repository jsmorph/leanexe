import Demos.RandomHistogram.Native
import Verified.Examples.WasiReadAllMessage

/-! The random-residue histogram's corollary at the shim's specification level, over the layer
events of a run under `linuxHost`.

`Full ls` states that every `getrandom` of the layer events `ls` returned the count that it asked
for and every `write` the count of bytes that it offered.  `randomData ls` collects the bytes that
the `getrandom` events returned, and `Counts args ls status` states the layer events and the exit
status that the request asks of a run whose calls succeed, with the arguments `args`.  With N the
value that `parseSpec` reads from the arguments, each followed by a zero byte: when `parseSpec`
refuses the arguments, no layer event precedes `exit_group`, and the status is 2.  Otherwise the
events are calls of `getrandom`, each of at most 4,096 bytes with flags 0, followed by one `write`
of descriptor 1, the bytes that `getrandom` returned hold exactly N little-endian words `w`, the
counts of `histogramSpec w` sum to N, the bytes written to descriptor 1 are
`renderSpec (histogramSpec w)`, and the status is 0.

`linux_exec_counts` proves `Counts` for every `Exec` run of `main` and its exit under the shim's
host, from a launch whose arguments' strings and eight-byte pointers take at most `argsLimit`
bytes, whose layer events, the images of its WASI events, meet `Full`, and such a run ends at the
accepted exit.  A run that traps would have a trapped `args_sizes_get`, `args_get`,
`random_get`, or `fd_write` (`main_trapped`), whose image no event sequence that meets `Full`
gives (`image_untrapped`), and the exit of a status of at most 76 is accepted. -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The bytes that the `getrandom` events of `ls` returned, in order: for each, the first bytes of
its output region, as many as its result. -/
def randomData (ls : List Linux.Event) : List UInt8 :=
  ls.flatMap fun e => if e.call = Linux.getrandomCall then e.output.take e.ret.toNat else []

/-- Every `getrandom` of `ls` returned the count that it asked for, and every `write` of `ls` the
count of bytes that it offered. -/
def Full (ls : List Linux.Event) : Prop :=
  ∀ e ∈ ls, (e.call = Linux.getrandomCall → e.ret = Linux.arg e.args 1) ∧
    (e.call = Linux.writeCall → e.ret = Linux.arg e.args 2)

/-- A `getrandom` of at most 4,096 bytes with flags 0. -/
def Drawing (e : Linux.Event) : Prop :=
  e.call = Linux.getrandomCall ∧ (Linux.arg e.args 1).toNat ≤ 4096 ∧ Linux.arg e.args 2 = 0

/-- The layer events `ls` and the exit status `status` that the request asks of a run whose calls
succeed, with the arguments `args`, each followed by a zero byte in the buffer from which
`parseSpec` reads N.  When `parseSpec` refuses the arguments, no layer event precedes `exit_group`,
and the status is 2.  Otherwise the events are calls of `getrandom`, each of at most 4,096 bytes
with flags 0, followed by one `write` of descriptor 1, the bytes that `getrandom` returned hold
exactly N words `w`, the counts of `histogramSpec w` sum to N, the bytes written to descriptor 1
are `renderSpec (histogramSpec w)`, and the status is 0. -/
def Counts (args : List (List UInt8)) (ls : List Linux.Event) (status : UInt64) : Prop :=
  (parseSpec (bytesOfList (stringsBytes args)) = 0 → ls = [] ∧ status = 2) ∧
  (parseSpec (bytesOfList (stringsBytes args)) ≠ 0 →
    (∃ draws write, ls = draws ++ [write] ∧ (∀ e ∈ draws, Drawing e) ∧
      write.call = Linux.writeCall ∧ Linux.arg write.args 0 = 1) ∧
    (words (randomData ls)).length = (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
    ((histogramSpec (words (randomData ls)).toArray).toList.map UInt64.toNat).sum =
      (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
    Linux.writeData 1 ls =
      (renderSpec (histogramSpec (words (randomData ls)).toArray)).data.data.toList ∧
    status = 0)

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
      | sys_reject fits => exact absurd (randomGet_accepted _) fits
      | sys_trap => exact ⟨_, List.mem_singleton_self _, .inr (.inr rfl)⟩
      | sys_return _ _ next =>
        beta_reduce at next
        split at next <;> cases next

/-- A trapped run of `main` has a trapped `args_sizes_get`, `args_get`, `random_get`, or
write. -/
theorem main_trapped {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {message : String}
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
      change Exec host (if s.2.2 != 0 then Action.pure s.2.2 else _) loopAfter post _ final
        at cont2
      split at cont2
      · cases cont2
      change Exec host (.write .stdout (render s.1) fun result => .pure result.errno)
        loopAfter post _ final at cont2
      cases cont2 with
      | write_trap _ =>
        exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)),
          trivial⟩
      | write_return _ next => cases next

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
      rw [answered] at reply
      simp [writeReply] at reply
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

/-- The image of the write of `bytes` to standard output whose `write` event meets `Full` is one
`write` of descriptor 1, which returned errno 0 and took all of `bytes`. -/
theorem write_full {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {bytes : LeanExe.Bytes} {code count : UInt64} {l : List Linux.Event}
    (image : Image F L I events (.write .stdout bytes (.returned code count)) l) (full : Full l) :
    code = 0 ∧ Linux.writeData 1 l = bytes.data.data.toList ∧ randomData l = [] ∧
      ∃ x, l = [x] ∧ x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1 := by
  obtain ⟨x, a, rfl, call, args, inputs, -, small, reply⟩ := image
  have answered := (full x (List.mem_singleton_self _)).2 call
  simp only [args, Linux.arg, List.getD_cons_succ, List.getD_cons_zero] at answered
  rw [answered] at reply
  simp only [writeReply, le_refl, ↓reduceIte] at reply
  refine ⟨(Transfer.returned.inj reply).1, ?_, ?_, x, rfl, call,
    by simp [args, Linux.arg, Output.fd]⟩
  · have wide : (UInt64.ofNat bytes.data.size).toNat = bytes.data.size :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    simp [Linux.writeData, Linux.Event.writeBytes, call, args, inputs, answered, Linux.arg,
      Output.fd, wide]
  · have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
    simp [randomData, call, other]

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
  cases outcome with
  | returned v => exact (Verified.Wasi.bind_exit_not_returned execution).elim
  | trapped m =>
    exfalso
    obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
    cases middle with
    | exited c => exact (main_runs mainRun).1 c rfl
    | trapped m' =>
      obtain ⟨e, member, trapped⟩ := main_trapped mainRun
      obtain ⟨_, l, image, sub⟩ := images_mem images e (List.mem_append_left _ member)
      exact image_untrapped image trapped (full.sub sub) fit
    | returned status =>
      have low := ((main_runs mainRun).2 status rfl).1
      change Exec _ (Action.exit status) after rest (.trapped m) final at cont
      cases cont with
      | exitTrap rejected =>
        have high := rejected.1
        rw [exitStatus_small low] at high
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
        obtain ⟨draws, bytes, errno, post, rfl, drawn, -, succeeded⟩ := accepted aZero nonzero
        obtain ⟨ld, lw, rfl, drawImages, postImages⟩ :=
          Verified.Examples.WasiReadAll.images_split restImages
        obtain ⟨errnoZero, drawData, drawWrites, drawing⟩ :=
          draws_full drawn drawImages (full.sub fun x m => List.mem_append_left _ m)
        obtain ⟨length, sum, count, rfl⟩ := succeeded errnoZero
        cases postImages with
        | cons image tail =>
          cases tail
          simp only [List.append_nil] at full ⊢
          obtain ⟨rfl, written, noRandom, x, rfl, call, fd⟩ :=
            write_full image (full.sub fun x m => List.mem_append_right _ m)
          rw [randomData_append, drawData, noRandom, List.append_nil, writeData_append,
            drawWrites, written, List.nil_append]
          exact ⟨⟨_, x, rfl, drawing, call, fd⟩, length, sum, rfl, rfl⟩

#print axioms main_trapped
#print axioms image_untrapped
#print axioms linux_exec_counts

end Demos.RandomHistogram
