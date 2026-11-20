import Demos.RandomHistogram.Native
import Verified.Examples.WasiReadAllMessage
import Verified.Shim.Images

/-! The random-residue histogram's corollary at the shim's specification level, over the layer
events of a run under `linuxHost`.

`InRange ls` states that the result of every `getrandom` and `write` of the layer events `ls` lies
in the range that Linux gives for its call and that the shim accepts: every `getrandom` returned an
error number or a count of at most its length, positive for a positive length
(`LeanExe.Linux.RandomCount`), and every `write` an error number or at most its count, its third
argument.  The image of a `random_get` or a write that returned meets `InRange`
(`random_inRange`, `write_inRange`), and, when the arguments fit, no image of a trapped one does
(`image_untrapped`), so `InRange` excludes exactly the results at which the shim traps: a
`getrandom` that returned 0 or a count above its length that is no error number, and a `write` that
returned more than its count and no error number.  `Sized ls` states that each `getrandom` of
`ls` holds in its output as many bytes as it asked for, which the events of every run give
(`carried_sized`).

The shim answers one `random_get` with a group of `getrandom` calls, each for the bytes that the
calls before it did not return, and `RandomGroup a length errno 0 g` states that `g` is the group of
a `random_get` of `length` bytes at `a` that returned the errno `errno`.  `randomData ls` collects
the bytes that the `getrandom` events returned, so the bytes of a `random_get` that returned errno 0
and whose group meets `Sized` are `randomData g`, the concatenation of the outputs of its group,
each cut at its count (`random_group`).  `RandomMirrors x g` states that `g` is the group that the
shim makes for the `random_get` `x`, with the call's errno, and with the call's bytes when the
errno is 0.

`Counts args ls status` states the layer events and the exit status that the request asks of a run
with the arguments `args`.  With N the value that `parseSpec` reads from the arguments, each
followed by a zero byte: when `parseSpec` refuses the arguments, no layer event precedes
`exit_group`, and the status is 2.  Otherwise the events are groups that mirror, one for one, the
calls of `random_get` of `Draws` for N words, each for `8 · min r 512` bytes with `r` the words
still to draw, followed by calls of `write` of descriptor 1.  When the last call returned an errno
other than 0, it is the status, and no `write` follows.  Otherwise the random bytes `bytes` that the
groups returned hold exactly N little-endian words `w`, the counts of `histogramSpec w` sum to N,
the bytes that the writes took form a prefix of `renderSpec (histogramSpec w)`, of B bytes, the
writes number at most B + 1, one for each of the loop's passes at most, and each write offered at
least one byte, the bytes that the writes before it did not take (`OfferedLayer`).  The status is 0
exactly when that prefix is the whole output.  Either every write returned at most its count and
the status is 0, or 77 after one write for each of the loop's passes, or the last write returned an
error number whose errno is the status and every write before it returned at most its count.

`linux_exec_counts` proves `Counts` for every `Exec` run of `main` and its exit under the shim's
host, from a launch whose arguments' strings and eight-byte pointers take at most `argsLimit`
bytes, whose layer events, the images of its WASI events, meet `InRange` and `Sized`, and such a
run ends at the accepted exit.  A run that traps would have a trapped `args_sizes_get`, `args_get`,
`random_get`, or `fd_write` (`main_trapped`), whose image no event sequence that meets `InRange`
gives (`image_untrapped`), and the shim accepts every status of at most 77.

`short_run` states every run of `main` and its exit under the replies `shortReplies` whose layer
events hold those replies from call 0.  The replies answer calls 0 and 1 with the result 4 and zero
bytes and every later call with the size of `oneOutput`, the ten lines of the counts of one word of
residue 0.  With the arguments `oneArgs`, which give N of 1, such a run ends at the accepted exit
with status 0, and its layer events meet `InRange` and hold a `getrandom` that returned a count of
at least 1 and below its length (`ShortRead`).  `histogram_elf_witness` of
`tests/TestSupport/A64/ImageFilesRandomHistogram.lean` gives such a run of the executable. -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim

/-- The bytes that the `getrandom` events of `ls` returned, in order: for each whose result is at
most its length, the first bytes of its output region, as many as its result. -/
def randomData (ls : List Linux.Event) : List UInt8 :=
  ls.flatMap fun e =>
    if e.call = Linux.getrandomCall ∧ e.ret.toNat ≤ (Linux.arg e.args 1).toNat then
      e.output.take e.ret.toNat
    else []

/-- The result of every `getrandom` and `write` of `ls` lies in the range that Linux gives for its
call and that the shim accepts: every `getrandom` returned an error number or a count of at most
its length, positive for a positive length, and every `write` an error number or at most its
count, its third argument. -/
def InRange (ls : List Linux.Event) : Prop :=
  Linux.RandomCount ls ∧ ∀ e ∈ ls, e.call = Linux.writeCall →
    Linux.isError e.ret = true ∨ e.ret.toNat ≤ (Linux.arg e.args 2).toNat

/-- Each `getrandom` of `ls` holds in its output as many bytes as it asked for. -/
def Sized (ls : List Linux.Event) : Prop :=
  ∀ e ∈ ls, e.call = Linux.getrandomCall → e.output.length = (Linux.arg e.args 1).toNat

/-- `RandomGroup a length errno done g`: the `getrandom` calls `g` that the shim makes for a
`random_get` of `length` bytes at `a`, which returned `errno`, after calls that returned its first
`done` bytes.  Each call asks, with flags 0, for the bytes that remain, at the address after those
returned.  A call that returned a count of at least 1 and below the bytes that remain precedes the
next call.  A call that returned the bytes that remain is the last, with `errno` 0, and a call that
returned an error number above them is the last, with its WASI errno.  With no byte to fill, the
group has no call and `errno` is 0. -/
def RandomGroup (a : UInt64) (length : Nat) (errno : UInt64) : Nat → List Linux.Event → Prop
  | done, [] => done = length ∧ errno = 0
  | done, e :: g => done < length ∧ e.call = Linux.getrandomCall ∧
      e.args = [a + UInt64.ofNat done, UInt64.ofNat (length - done), 0] ∧
      ((0 < e.ret.toNat ∧ e.ret.toNat < length - done ∧
          RandomGroup a length errno (done + e.ret.toNat) g) ∨
        (e.ret.toNat = length - done ∧ g = [] ∧ errno = 0) ∨
        (Linux.isError e.ret = true ∧ length - done < e.ret.toNat ∧ g = [] ∧
          errno = errnoOf (0 - e.ret)))

/-- `RandomMirrors x g`: the WASI event `x` is a `random_get` of `n` bytes that returned the errno
`errno`, and the layer events `g` are the group of a `random_get` of `n` bytes that returned
`errno`.  When `errno` is 0, the call returned the bytes that the group returned.  No layer events
mirror any other WASI event. -/
def RandomMirrors : Event → List Linux.Event → Prop
  | .sys call [.space n] (.returned errno outputs), g =>
    call = Call.randomGet ∧ (∃ a, RandomGroup a n.toNat errno 0 g) ∧
      (errno = 0 → outputs = [bytesOfList (randomData g)])
  | _, _ => False

/-- The output that the request asks for from the words of the random bytes `bytes`: `renderSpec`
of their counts. -/
def askedOutput (bytes : List UInt8) : List UInt8 :=
  (renderSpec (histogramSpec (words bytes).toArray)).data.data.toList

/-- `OfferedLayer out taken ls`: the input of each event of `ls` holds the bytes of `out` after the
first `taken` and those that the events before it took as writes of descriptor 1. -/
def OfferedLayer (out : List UInt8) : Nat → List Linux.Event → Prop
  | _, [] => True
  | taken, e :: rest => e.inputs.headD [] = out.drop taken ∧
    OfferedLayer out (taken + (Linux.Event.writeBytes 1 e).length) rest

/-- The event `e` returned at most its count, its third argument. -/
def Took (e : Linux.Event) : Prop := e.ret.toNat ≤ (Linux.arg e.args 2).toNat

/-- The layer events `ls` and the exit status `status` that the request asks of a run with the
arguments `args`, each followed by a zero byte in the buffer from which `parseSpec` reads N.  When
`parseSpec` refuses the arguments, no layer event precedes `exit_group`, and the status is 2.
Otherwise the events are groups that mirror, one for one, the calls of `random_get` of `Draws` for
N words, followed by calls of `write` of descriptor 1.  When the calls of `random_get` end with an
errno other than 0, it is the status, and no write follows.  Otherwise the random bytes `bytes` of
`Draws` hold exactly N words `w`, and the counts of `histogramSpec w` sum to N.  The writes number
at most one more than the bytes of `renderSpec (histogramSpec w)`, each offered at least one byte,
the bytes of that output that the writes before it did not take, and the bytes that the writes
took form a prefix of that output.  The status is 0 exactly when they are the whole output.  Either
every write returned at most its count and the status is 0, or 77 after one write for each of the
loop's passes, or the last write returned an error number whose errno is the status and every
write before it returned at most its count. -/
def Counts (args : List (List UInt8)) (ls : List Linux.Event) (status : UInt64) : Prop :=
  (parseSpec (bytesOfList (stringsBytes args)) = 0 → ls = [] ∧ status = 2) ∧
  (parseSpec (bytesOfList (stringsBytes args)) ≠ 0 →
    ∃ (draws : List Event) (groups : List (List Linux.Event)) (bytes : List UInt8)
      (errno : UInt64) (writes : List Linux.Event),
      ls = groups.flatten ++ writes ∧ List.Forall₂ RandomMirrors draws groups ∧
      Draws (parseSpec (bytesOfList (stringsBytes args))) draws bytes errno ∧
      (errno ≠ 0 → status = errno ∧ writes = []) ∧
      (errno = 0 →
        (words bytes).length = (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
        ((histogramSpec (words bytes).toArray).toList.map UInt64.toNat).sum =
          (parseSpec (bytesOfList (stringsBytes args))).toNat ∧
        Linux.writeData 1 ls <+: askedOutput bytes ∧
        (status = 0 ↔ Linux.writeData 1 ls = askedOutput bytes) ∧
        (∀ e ∈ writes,
          e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1 ∧ e.inputs.headD [] ≠ []) ∧
        OfferedLayer (askedOutput bytes) 0 writes ∧
        writes.length ≤ (askedOutput bytes).length + 1 ∧
        (((∀ e ∈ writes, Took e) ∧
            (status = 0 ∨ (status = 77 ∧ writes.length = (askedOutput bytes).length + 1))) ∨
          (status ≠ 0 ∧ ∃ before e, writes = before ++ [e] ∧ (∀ x ∈ before, Took x) ∧
            Linux.isError e.ret = true ∧ status = errnoOf (0 - e.ret)))))

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

/-- A trapped loop of `main` has a trapped call of `TrapEvent` among its events. -/
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
      change Exec host (Action.bind (writeAll (render s.1) 0 (render s.1).size) fun written =>
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
          (writeAll_run_whole (by omega) writeRun).trapped_write accepts _ rfl
        exact ⟨_, List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ member)), trivial⟩

/-! ## The images under `InRange` -/

theorem InRange.sub {ls ls' : List Linux.Event} (range : InRange ls) (sub : ∀ x ∈ ls', x ∈ ls) :
    InRange ls' :=
  ⟨fun e member => range.1 e (sub e member), fun e member => range.2 e (sub e member)⟩

theorem Sized.sub {ls ls' : List Linux.Event} (sized : Sized ls) (sub : ∀ x ∈ ls', x ∈ ls) :
    Sized ls' := fun e member => sized e (sub e member)

theorem InRange.append {ls ls' : List Linux.Event} (range : InRange ls) (range' : InRange ls') :
    InRange (ls ++ ls') := by
  refine ⟨fun e member => ?_, fun e member => ?_⟩ <;> rcases List.mem_append.mp member with m | m
  · exact range.1 e m
  · exact range'.1 e m
  · exact range.2 e m
  · exact range'.2 e m

/-- The images of no event are no layer event. -/
theorem images_nil {F : OpenFlags} {L : ShimLayout} {I : Launch} {events ls : List Linux.Event}
    (images : Images F L I events [] ls) : ls = [] := by
  cases images
  rfl

/-- Events that hold their replies hold in each `getrandom`'s output as many bytes as it asked
for. -/
theorem carried_sized {R : Linux.Replies} : ∀ {k : Nat} {ls : List Linux.Event},
    Carried R k ls → Sized ls
  | _, [], _ => fun _ member => (nomatch member)
  | _, e :: ls, ⟨carries, rest⟩ => by
    intro x member call
    rcases List.mem_cons.mp member with rfl | member
    · rw [carries.2, call]
      simp [Linux.outputRegions, Linux.getrandomCall]
    · exact carried_sized rest x member call

theorem randomData_append (ls ls' : List Linux.Event) :
    randomData (ls ++ ls') = randomData ls ++ randomData ls' := by
  simp [randomData, List.flatMap_append]

theorem writeData_append (ls ls' : List Linux.Event) :
    Linux.writeData 1 (ls ++ ls') = Linux.writeData 1 ls ++ Linux.writeData 1 ls' := by
  simp [Linux.writeData, List.flatMap_append]

/-- The bytes of a `getrandom` whose result is at most its length, followed by those of the events
after it. -/
theorem randomData_cons {e : Linux.Event} {l : List Linux.Event}
    (call : e.call = Linux.getrandomCall)
    (within : e.ret.toNat ≤ (Linux.arg e.args 1).toNat) :
    randomData (e :: l) = e.output.take e.ret.toNat ++ randomData l := by
  simp [randomData, call, within]

/-- The `getrandom` events of `random_get`'s loop, which fills `length` bytes at `a` and has filled
the `done` bytes `filled`, whose results meet `LeanExe.Linux.RandomCount`, form the group of the
`random_get`, and the loop returns an errno: 0 with the bytes `filled` followed by those that the
events returned when each holds as many bytes as it asked for, or the WASI errno of the error
number that the last event returned. -/
theorem random_group {a : UInt64} {length : Nat} (small : length < 2 ^ 64) :
    ∀ {done : Nat} {filled : List UInt8} {l : List Linux.Event} {reply : Transfer (List Bytes)},
      RandomCalls a length done filled l reply → Linux.RandomCount l →
      ∃ errno outputs, reply = .returned errno outputs ∧ RandomGroup a length errno done l ∧
        (errno = 0 → Sized l → outputs = [bytesOfList (filled ++ randomData l)])
  | _, _, [], _, ⟨done, rfl⟩, _ =>
    ⟨0, _, rfl, ⟨done, rfl⟩, fun _ _ => by simp [randomData]⟩
  | done, filled, _ :: l, reply, ⟨more, prior, ret, output, rfl, going⟩, count => by
    have remaining : (UInt64.ofNat (length - done)).toNat = length - done :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    have answered := count _ (List.mem_cons_self ..) rfl
    simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, remaining] at answered
    have data : ∀ rest, ret.toNat ≤ length - done →
        randomData (⟨Linux.getrandomCall, [a + UInt64.ofNat done, UInt64.ofNat (length - done), 0],
          [], prior, ret, output⟩ :: rest) = output.take ret.toNat ++ randomData rest :=
      fun rest within => randomData_cons rfl (by
        simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, remaining]
        exact within)
    split at going
    · rename_i inner
      obtain ⟨errno, outputs, rfl, group, bytes⟩ :=
        random_group small going (fun x member => count x (List.mem_cons_of_mem _ member))
      refine ⟨errno, outputs, rfl, ⟨more, rfl, rfl, .inl ⟨inner.1, inner.2, group⟩⟩,
        fun zero sized => ?_⟩
      rw [bytes zero (sized.sub fun x member => List.mem_cons_of_mem _ member),
        data l (by omega), List.append_assoc]
    · rename_i stop
      obtain ⟨rfl, same⟩ := going
      unfold randomLast at same
      by_cases all : ret.toNat = length - done
      · rw [ite_eq_left all] at same
        refine ⟨0, _, same, ⟨more, rfl, rfl, .inr (.inl ⟨all, rfl, rfl⟩)⟩, fun _ sized => ?_⟩
        have size := sized _ (List.mem_cons_self ..) rfl
        simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, remaining] at size
        rw [data [] (by omega)]
        simp [randomData, all, List.take_of_length_le (Nat.le_of_eq size)]
      · rw [ite_eq_right all] at same
        split at same
        · rename_i error
          have above : length - done < ret.toNat := by
            have big := error
            simp only [Linux.isError, decide_eq_true_eq] at big
            omega
          exact ⟨_, _, same, ⟨more, rfl, rfl, .inr (.inr ⟨error, above, rfl, rfl⟩)⟩,
            fun zero => absurd zero (errnoOf_valid _).2⟩
        · rename_i notError
          exfalso
          rcases answered with error | ⟨within, positive⟩
          · exact notError error
          · omega

/-- The `getrandom` events of a `random_get` loop that returned meet `LeanExe.Linux.RandomCount`:
the loop returns only after results in Linux's range. -/
theorem randomCalls_count {a : UInt64} {length : Nat} (small : length < 2 ^ 64)
    {errno : UInt64} {outputs : List Bytes} :
    ∀ {done : Nat} {filled : List UInt8} {l : List Linux.Event},
      RandomCalls a length done filled l (.returned errno outputs) → Linux.RandomCount l
  | _, _, [], _ => fun _ member => (nomatch member)
  | done, filled, _ :: l, ⟨more, prior, ret, output, rfl, going⟩ => by
    have remaining : (UInt64.ofNat (length - done)).toNat = length - done :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
    intro x member call
    split at going
    · rename_i inner
      rcases List.mem_cons.mp member with rfl | member
      · simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, remaining]
        exact .inr ⟨by omega, .inr inner.1⟩
      · exact randomCalls_count small going x member call
    · obtain ⟨rfl, same⟩ := going
      obtain rfl := List.mem_singleton.mp member
      simp only [Linux.arg, List.getD_cons_succ, List.getD_cons_zero, remaining]
      unfold randomLast at same
      split at same
      · rename_i all
        exact .inr ⟨by omega, .inr (by omega)⟩
      · split at same
        · rename_i error
          exact .inl error
        · cases same

/-- The image of a `random_get` that returned meets `InRange`. -/
theorem random_inRange {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {n errno : UInt64} {outputs : List Bytes} {l : List Linux.Event}
    (image : Image F L I events (.sys .randomGet [.space n] (.returned errno outputs)) l) :
    InRange l := by
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  have other : Linux.getrandomCall ≠ Linux.writeCall := by decide
  refine ⟨randomCalls_count n.toNat_lt calls, fun x member writing => ?_⟩
  rw [randomCalls_calls calls x member] at writing
  exact absurd writing other

/-- The image of a write that returned meets `InRange`. -/
theorem write_inRange {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {output : Output} {offered : LeanExe.Bytes} {errno count : UInt64} {l : List Linux.Event}
    (image : Image F L I events (.write output offered (.returned errno count)) l) :
    InRange l := by
  obtain ⟨x, a, rfl, call, args, -, -, small, reply⟩ := image
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  have wide : (UInt64.ofNat offered.data.size).toNat = offered.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine ⟨fun y member drawing => ?_, fun y member _ => ?_⟩ <;>
    obtain rfl := List.mem_singleton.mp member
  · exact absurd (call.symm.trans drawing) other
  · simp only [args, Linux.arg, List.getD_cons_succ, List.getD_cons_zero, wide]
    unfold writeReply at reply
    split at reply
    · rename_i within
      rw [wide] at within
      exact .inr within
    · split at reply
      · rename_i error
        exact .inl error
      · cases reply

/-- No event sequence that meets `InRange` is the image of a trapped `args_sizes_get`, `args_get`,
`random_get`, or write when the arguments fit. -/
theorem image_untrapped {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {e : Event} {l : List Linux.Event} (image : Image F L I events e l) (trapped : TrapEvent e)
    (range : InRange l) (fit : stringsFit I.args = true) : False := by
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
          obtain ⟨_, _, reply, -⟩ := random_group length.toNat_lt calls range.1
          cases reply
        · exact image
  | write output bytes reply =>
    cases reply with
    | returned => exact trapped
    | trapped message committed =>
      obtain ⟨x, a, rfl, call, args, -, -, small, reply⟩ := image
      have answered := range.2 x (List.mem_singleton_self _) call
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

/-- The image of a `random_get` that returned, whose events meet `InRange` and `Sized`, is a group
that mirrors it and takes no byte as a write of descriptor 1. -/
theorem random_mirror {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {n errno : UInt64} {outputs : List Bytes} {l : List Linux.Event}
    (image : Image F L I events (.sys .randomGet [.space n] (.returned errno outputs)) l)
    (range : InRange l) (sized : Sized l) :
    RandomMirrors (.sys .randomGet [.space n] (.returned errno outputs)) l ∧
      Linux.writeData 1 l = [] := by
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  obtain ⟨_, _, same, group, bytes⟩ := random_group n.toNat_lt calls range.1
  obtain ⟨rfl, rfl⟩ := Transfer.returned.inj same
  refine ⟨⟨rfl, ⟨a, group⟩, fun zero => by simpa using bytes zero sized⟩,
    writeData_none fun x member => ?_⟩
  rw [randomCalls_calls calls x member]
  decide

/-- The images of the calls of `Draws` whose events meet `InRange` and `Sized` are groups that
mirror them, one for one, and take no byte as writes of descriptor 1. -/
theorem draws_mirrors {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {r : UInt64} {draws : List Event} {bytes : List UInt8} {errno : UInt64}
      {events ls : List Linux.Event}, Draws r draws bytes errno →
      Images F L I events draws ls → InRange ls → Sized ls →
      ∃ groups : List (List Linux.Event), ls = groups.flatten ∧
        List.Forall₂ RandomMirrors draws groups ∧ Linux.writeData 1 ls = []
  | _, _, _, _, _, _, .done, images, _, _ => by
    cases images
    exact ⟨[], rfl, .nil, rfl⟩
  | _, _, _, _, _, _, .failed _ _, images, range, sized => by
    cases images with
    | @cons _ _ l _ _ image rest =>
      cases rest
      rw [List.append_nil] at range sized ⊢
      obtain ⟨mirror, written⟩ := random_mirror image range sized
      exact ⟨[l], by simp, .cons mirror .nil, written⟩
  | _, _, _, _, _, _, .drew _ _ rest, images, range, sized => by
    cases images with
    | @cons _ _ l _ _ image restImages =>
      obtain ⟨mirror, written⟩ := random_mirror image
        (range.sub fun x m => List.mem_append_left _ m)
        (sized.sub fun x m => List.mem_append_left _ m)
      obtain ⟨groups, rfl, mirrors, restWritten⟩ := draws_mirrors rest restImages
        (range.sub fun x m => List.mem_append_right _ m)
        (sized.sub fun x m => List.mem_append_right _ m)
      refine ⟨l :: groups, by simp, .cons mirror mirrors, ?_⟩
      rw [writeData_append, written, restWritten]
      rfl

/-- The image of a write to standard output that returned is one `write` of descriptor 1, which
took the bytes that the write took and whose input holds the bytes that the write offered.  When
the write returned errno 0, the `write` returned at most its count, and when the write returned an
errno, the `write` returned an error number whose errno is the write's. -/
theorem write_image {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {offered : LeanExe.Bytes} {errno count : UInt64} {l : List Linux.Event}
    (image : Image F L I events (.write .stdout offered (.returned errno count)) l) :
    ∃ x, l = [x] ∧ x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1 ∧
      Linux.writeData 1 l = (Event.write .stdout offered (.returned errno count)).stdoutTaken ∧
      x.inputs.headD [] = offered.data.data.toList ∧ (errno = 0 → Took x) ∧
      (errno ≠ 0 → Linux.isError x.ret = true ∧ errno = errnoOf (0 - x.ret)) := by
  obtain ⟨x, a, rfl, call, args, inputs, -, small, reply⟩ := image
  have wide : (UInt64.ofNat offered.data.size).toNat = offered.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  refine ⟨x, rfl, call, by simp [args, Linux.arg, Output.fd], ?_, by simp [inputs],
    fun zero => ?_, ?_⟩
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

/-- The images of writes to standard output that returned, each of which offered at least one
byte, the bytes of `out` after the first `taken` and those that the writes before it took
(`Offered`), are `write` calls of descriptor 1, one for each write, which took the bytes that the
writes took, and whose inputs hold those bytes of `out` (`OfferedLayer`), at least one each. -/
theorem writes_images {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {events : List Linux.Event} {writes : List Event} {ls : List Linux.Event}
      {out : List UInt8} {taken : Nat},
      Images F L I events writes ls →
      (∀ e ∈ writes, ∃ offered errno count, e = .write .stdout offered (.returned errno count)) →
      (∀ e ∈ writes, WroteSome e) → Offered out taken writes →
      Linux.writeData 1 ls = stdoutTaken writes ∧
        (∀ x ∈ ls,
          x.call = Linux.writeCall ∧ Linux.arg x.args 0 = 1 ∧ x.inputs.headD [] ≠ []) ∧
        ls.length = writes.length ∧ OfferedLayer out taken ls
  | _, _, _, _, _, .nil, _, _, _ => ⟨rfl, fun _ member => (nomatch member), rfl, trivial⟩
  | _, _, _, _, _, .cons image rest, shape, wroteSome,
      ⟨⟨offered', reply', same, offers⟩, offeredRest⟩ => by
    obtain ⟨offered, errno, count, rfl⟩ := shape _ (List.mem_cons_self ..)
    obtain ⟨-, rfl, -⟩ := Event.write.inj same
    obtain ⟨offered'', reply'', same', size⟩ := wroteSome _ (List.mem_cons_self ..)
    obtain ⟨-, rfl, -⟩ := Event.write.inj same'
    obtain ⟨x, rfl, call, fd, data, input, -, -⟩ := write_image image
    have bytes : Linux.Event.writeBytes 1 x =
        (Event.write .stdout offered (.returned errno count)).stdoutTaken := by
      simpa [Linux.writeData] using data
    obtain ⟨restData, restShape, restLength, restOffered⟩ :=
      writes_images rest (fun e member => shape e (List.mem_cons_of_mem _ member))
        (fun e member => wroteSome e (List.mem_cons_of_mem _ member))
        (by rw [← bytes] at offeredRest; exact offeredRest)
    refine ⟨by rw [writeData_append, data, restData, stdoutTaken_cons], fun y member => ?_,
      by simp [restLength], ⟨by rw [input, offers], restOffered⟩⟩
    rcases List.mem_append.mp member with member | member
    · obtain rfl := List.mem_singleton.mp member
      refine ⟨call, fd, ?_⟩
      rw [input]
      intro empty
      exact size (by simpa using congrArg List.length empty)
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
    obtain ⟨x, rfl, -, -, -, -, took, -⟩ := write_image image
    intro y member
    rcases List.mem_append.mp member with member | member
    · obtain rfl := List.mem_singleton.mp member
      exact took rfl
    · exact writes_took rest (fun e m => every e (List.mem_cons_of_mem _ m)) y member

/-- Under the shim's host, every run of `main` and its exit from a launch whose arguments'
strings and eight-byte pointers take at most `argsLimit` bytes, whose layer events, the images of
its WASI events, meet `InRange` and `Sized`, ends at the accepted exit with a status that meets
`Counts`. -/
theorem linux_exec_counts {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit} {ls : List Linux.Event}
    (small : stringsSize I.args + 8 * I.args.length ≤ argsLimit)
    (execution : Exec (linuxHost F L I R) (main.bind fun status => Action.exit status) world T
      outcome final)
    (images : Images F L I world.events T ls) (range : InRange ls) (sized : Sized ls) :
    ∃ c, outcome = .exited c ∧ Counts I.args ls c := by
  have fit := stringsFit_of_le (by decide) small
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
      exact image_untrapped image trapped (range.sub sub) fit
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
    obtain ⟨aZero, aBytes, preEmpty⟩ := linux_args (by decide) (by decide) small argsRun
    obtain ⟨l, lx, rfl, front, exitImages⟩ :=
      images_split images
    obtain ⟨lp, lr, rfl, preImages, restImages⟩ :=
      images_split front
    cases preEmpty _ _ preImages
    cases exitImages with
    | cons image tail =>
      cases tail
      cases image
      simp only [List.nil_append, List.append_nil] at range sized ⊢
      unfold Counts
      rw [← aBytes]
      constructor
      · intro zero
        obtain ⟨rfl, rfl⟩ := refused aZero zero
        cases restImages
        exact ⟨rfl, rfl⟩
      · intro nonzero
        obtain ⟨draws, bytes, errno, writes, rfl, drawn, failed, succeeded⟩ :=
          accepted aZero nonzero
        obtain ⟨ld, lw, rfl, drawImages, writeImages⟩ :=
          images_split restImages
        obtain ⟨groups, rfl, mirrors, drawWrites⟩ :=
          draws_mirrors drawn drawImages (range.sub fun x m => List.mem_append_left _ m)
            (sized.sub fun x m => List.mem_append_left _ m)
        refine ⟨draws, groups, bytes, errno, lw, rfl, mirrors, drawn, fun drawFailed => ?_,
          fun errnoZero => ?_⟩
        · obtain ⟨rfl, rfl⟩ := failed drawFailed
          exact ⟨rfl, images_nil writeImages⟩
        obtain ⟨length, sum, offeredAll, fewer, wroteSome, prefix_, whole, kinds⟩ :=
          succeeded errnoZero
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
        obtain ⟨writeBytes, writeShape, writeLength, offeredLayer⟩ :=
          writes_images writeImages shape wroteSome offeredAll
        have taken : Linux.writeData 1 (groups.flatten ++ lw) = stdoutTaken writes := by
          rw [writeData_append, drawWrites, writeBytes, List.nil_append]
        rw [taken]
        refine ⟨length, sum, prefix_, whole, writeShape, offeredLayer,
          by rw [writeLength]; exact fewer, ?_⟩
        rcases kinds with ⟨all, zeroOr⟩ | ⟨failing, -, before, offered, count, rfl, earlier⟩
        · refine .inl ⟨writes_took writeImages all, ?_⟩
          rcases zeroOr with zero | ⟨seventySeven, passes⟩
          · exact .inl zero
          · exact .inr ⟨seventySeven, by rw [writeLength, passes]; rfl⟩
        · obtain ⟨lb, lf, rfl, beforeImages, lastImages⟩ :=
            images_split writeImages
          cases lastImages with
          | cons image tail =>
            cases tail
            obtain ⟨x, rfl, -, -, -, -, -, failed⟩ := write_image image
            obtain ⟨error, same⟩ := failed failing
            exact .inr ⟨failing, lb, x, by simp, writes_took beforeImages earlier, error, same⟩

/-! ## Replies with a short read -/

/-- The arguments of a run with N of 1: the program name `h` and the argument `1`. -/
def oneArgs : List (List UInt8) := [[104], [49]]

/-- The output of a run with N of 1 whose word has residue 0: the ten lines of the counts of
`#[0]`. -/
def oneOutput : LeanExe.Bytes := renderSpec (histogramSpec #[0])

/-- The replies of a run with the arguments `oneArgs` with a short read: calls 0 and 1, the
`getrandom` calls of the run's one word, with the result 4 and zero bytes over the output region,
so that the first returns 4 of the 8 bytes that it asks for, and every later call, the `write` of
`oneOutput` among them, with the result of the size of `oneOutput`. -/
def shortReplies : Linux.Replies := fun k =>
  if k < 2 then ⟨4, fun _ => 0⟩ else ⟨UInt64.ofNat oneOutput.data.size, fun _ => 0⟩

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

/-- Some `getrandom` of `ls` returned a count of at least 1 and below its length that is no error
number. -/
def ShortRead (ls : List Linux.Event) : Prop :=
  ∃ e ∈ ls, e.call = Linux.getrandomCall ∧ Linux.isError e.ret = false ∧ 0 < e.ret.toNat ∧
    e.ret.toNat < (Linux.arg e.args 1).toNat

theorem ShortRead.left {ls ls' : List Linux.Event} (short : ShortRead ls) : ShortRead (ls ++ ls') :=
  let ⟨e, member, rest⟩ := short
  ⟨e, List.mem_append_left _ member, rest⟩

/-- The image of `random_get` of 8 bytes whose layer events start at call 0 under `shortReplies`:
two events, which meet `InRange` and hold a short read (`ShortRead`), and the reply is errno 0 with
8 zero bytes. -/
theorem random_short {F : OpenFlags} {L : ShimLayout} {I : Launch} {events : List Linux.Event}
    {reply : Transfer (List LeanExe.Bytes)} {l rest : List Linux.Event}
    (image : Image F L I events (.sys .randomGet [.space 8] reply) l)
    (carried : Carried shortReplies 0 (l ++ rest)) :
    l.length = 2 ∧ InRange l ∧ ShortRead l ∧
      reply = .returned 0 [bytesOfList (List.replicate 8 0)] := by
  have first : shortReplies 0 = ⟨4, fun _ => 0⟩ := rfl
  have second : shortReplies 1 = ⟨4, fun _ => 0⟩ := rfl
  have other : Linux.getrandomCall ≠ Linux.writeCall := by decide
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  rcases l with _ | ⟨e0, l⟩
  · obtain ⟨done, -⟩ := calls
    exact absurd done (by decide)
  obtain ⟨-, prior0, ret0, output0, rfl, going⟩ := calls
  obtain ⟨⟨answered0, filled0⟩, carried⟩ := carried
  simp only [first] at answered0 filled0
  subst answered0
  rw [ite_eq_left (by decide)] at going
  rcases l with _ | ⟨e1, more⟩
  · obtain ⟨done, -⟩ := going
    exact absurd done (by decide)
  obtain ⟨-, prior1, ret1, output1, rfl, stop⟩ := going
  obtain ⟨⟨answered1, filled1⟩, -⟩ := carried
  simp only [second] at answered1 filled1
  subst answered1
  rw [ite_eq_right (by decide)] at stop
  obtain ⟨rfl, rfl⟩ := stop
  refine ⟨rfl, ⟨fun e member _ => ?_, fun e member writing => ?_⟩,
    ⟨_, List.mem_cons_self .., rfl, rfl, by simp, by simp [Linux.arg]⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .inr (by simp [Linux.arg])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact absurd writing other
  · rw [filled0, filled1]
    rfl

/-- The loop's buffer after the calls of the run with N of 1 under `shortReplies`: 4,096 zero
bytes with the reply's 8 zero bytes at its start. -/
def oneBuffer : LeanExe.Bytes :=
  (Bytes.build 4096 fun _ => 0).splice 0 (bytesOfList (List.replicate 8 0))

/-- The output of the run with N of 1 under `shortReplies`: `render` of the counts of the word that
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

/-- Under the shim's host with the arguments `oneArgs` and the replies `shortReplies`, every run of
`main` and its exit ends at the accepted exit with status 0, and its layer events, the images of
its WASI events, meet `InRange` and hold a short read. -/
theorem short_run {F : OpenFlags} {L : ShimLayout} {environ : List (List UInt8)}
    {granted : Bool} {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit}
    {ls : List Linux.Event}
    (execution : Exec (linuxHost F L ⟨oneArgs, environ, granted⟩ shortReplies)
      (main.bind fun status => Action.exit status) world T outcome final)
    (images : Images F L ⟨oneArgs, environ, granted⟩ world.events T ls)
    (carried : Carried shortReplies 0 ls) :
    outcome = .exited 0 ∧ InRange ls ∧ ShortRead ls := by
  have small : stringsSize oneArgs + 8 * oneArgs.length ≤ argsLimit := by decide
  have fit := stringsFit_of_le (by decide) small
  have parsed : parseN (bytesOfList (stringsBytes oneArgs)) = 1 := by decide
  have once : ((1 : UInt64) / 512 + 1).toNat = 1 := by decide
  have outSmall : oneOutput.data.size ≤ 210 := one_rendered ▸ render_size _
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨lm, lx, rfl, mainImages, exitImages⟩ :=
    images_split images
  obtain ⟨after1, pre, middle1, rest1, argsRun, cont1, rfl⟩ := Exec.unbind args mainRun
  obtain ⟨lp, lq, rfl, preImages, restImages⟩ :=
    images_split mainImages
  cases middle1 with
  | exited c => exact absurd rfl ((args_returned argsRun).1 c)
  | trapped m => exact (linux_args_untrapped argsRun fit).elim
  | returned a =>
  obtain ⟨aZero, aBytes, preEmpty⟩ := linux_args (by decide) (by decide) small argsRun
  cases preEmpty _ _ preImages
  simp only at aBytes
  change Exec _ (if a.errno != 0 then Action.pure a.errno else _) after1 rest1 middle after
    at cont1
  rw [ite_eq_right (by simp [aZero])] at cont1
  dsimp only at cont1
  rw [aBytes, parsed, ite_eq_right (by decide)] at cont1
  obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont1
  obtain ⟨ld, lw, rfl, drawImages, postImages⟩ :=
    images_split restImages
  have carried' : Carried shortReplies 0 (ld ++ (lw ++ lx)) := by
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
        have answered :=
          (random_short image (rest := lw ++ lx) (by simpa using carried')).2.2.2
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
    | @cons _ _ l0 _ _ image drawRest =>
    obtain ⟨two, drawRange, drawShort, answered⟩ :=
      random_short image (by rw [List.append_assoc] at carried'; exact carried')
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
    change Exec _ (Action.bind (writeAll (render counts) 0 (render counts).size) fun written =>
        Action.pure (if written < (render counts).size then 77 else 0)) loopAfter post middle after
      at cont2
    rw [← hCounts, one_rendered] at cont2
    obtain ⟨writeAfter, writes, written, tail, writeRun, cont3, rfl⟩ :=
      Exec.unbind (writeAll oneOutput 0 oneOutput.size) cont2
    obtain ⟨lws, ltl, rfl, writeImages, tailImages⟩ :=
      images_split postImages
    have later : Carried shortReplies 2 (lws ++ (ltl ++ lx)) := by
      have whole : Carried shortReplies 0 (l0 ++ (lws ++ (ltl ++ lx))) := by
        simpa [List.append_assoc] using carried'
      simpa [two] using (carried_split whole).2
    have third : shortReplies 2 = ⟨UInt64.ofNat oneOutput.data.size, fun _ => 0⟩ := rfl
    have finish : ∀ {value : UInt64} {before before' : List Linux.Event},
        ¬value < oneOutput.size →
        Exec (linuxHost F L ⟨oneArgs, environ, granted⟩ shortReplies)
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
    cases writeAll_run_whole (by omega) writeRun with
    | done ended =>
      cases writeImages
      rw [UInt64.toNat_zero] at ended
      obtain ⟨rfl, rfl, rfl⟩ := finish (value := 0) (by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [Bytes.size, UInt64.toNat_zero, UInt64.toNat_ofNat']
        omega) cont3 tailImages exitImages
      exact ⟨rfl, by simpa using drawRange, by simpa using drawShort⟩
    | @wrote _ count _ offered events _ left offers within rest =>
      cases writeImages with
      | cons image writeRest =>
      obtain ⟨x, a', rfl, call, args, inputs, -, small', reply⟩ := image
      obtain ⟨⟨answered, -⟩, -⟩ := later
      simp only [third] at answered
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
        have writeRange : InRange [x] := by
          refine ⟨fun y member drawing => ?_, fun y member _ => .inr ?_⟩ <;>
            obtain rfl := List.mem_singleton.mp member
          · exact absurd (call.symm.trans drawing) other
          · simp [args, Linux.arg, answered, sizeEq]
        exact ⟨rfl, by simpa using drawRange.append writeRange,
          by simpa using ShortRead.left (ls' := [x]) drawShort⟩
      | wrote left' => rw [reached] at left'; omega
      | failed left' => rw [reached] at left'; omega
      | trapped left' => rw [reached] at left'; omega
    | failed left offers nonzero =>
      cases writeImages with
      | cons image _ =>
      obtain ⟨x, a', rfl, call, args, inputs, -, small', reply⟩ := image
      obtain ⟨⟨answered, -⟩, -⟩ := later
      simp only [third] at answered
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
      simp only [third] at answered
      have sizeEq := congrArg List.length offers
      simp at sizeEq
      rw [answered, sizeEq] at reply
      simp only [writeReply, le_refl, ↓reduceIte] at reply
      cases reply

#print axioms main_trapped
#print axioms image_untrapped
#print axioms random_group
#print axioms random_inRange
#print axioms write_inRange
#print axioms linux_exec_counts
#print axioms short_run

end Demos.RandomHistogram
