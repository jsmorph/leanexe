import Demos.RandomChoice.Native
import Demos.RandomChoice.Output
import Demos.RandomHistogram.NativeCounts

/-! The unbiased random choice's corollary at the shim's specification level, over the layer events
of a run under `linuxHost`.

The random histogram's `Full ls` states that every `getrandom` of the layer events `ls` returned
the count that it asked for and that every `write` returned an error number or at most the count
that it offered, as Linux's `write` does, and its `randomData ls` collects the bytes that the
`getrandom` events returned.  `Mirrors x e` states that the layer event `e` is the one event that
the shim makes for the WASI event `x` of such a run: a `getrandom` of 4,096 bytes with flags 0 that
returned 4,096 for a `random_get` of 4,096 bytes that returned errno 0 and the event's output, or a
`write` of descriptor 1 that offered a write's bytes and whose result gives the write's reply.  No
layer event mirrors any other WASI event.  `Choices args ls status` states the layer events and
the exit status that the request asks of a run with the arguments `args`, from which `argN` and
`argK` read N and K, 0 for a refusal.  When `parseSpec` refuses N or K, no layer event precedes
`exit_group`, and the status is 2.  Otherwise the layer events mirror, one for
one, WASI events that make the passes of `Rounds` from K values and `passes K` passes, whose random
bytes are `randomData ls` and whose status is the run's.  The status is 0 only when the writes of
`ls` took `outputOf N chosen` for the K-tuple `chosen` of the first K accepted words of
`randomData ls`, and `capStatus` only when `randomData ls` holds the `512 · passes K` words of the
cap's passes, fewer than K of them accepted.  `Rounds` gives the other statuses: 78 when the writes
of a pass stalled, and the errno of a `write` that returned an error number.

`linux_exec_choices` proves `Choices` for every `Exec` run of `main` and its exit under the shim's
host, from a launch whose arguments' strings and eight-byte pointers take at most `argsLimit`
bytes, whose layer events, the images of its WASI events, meet `Full`, and such a run ends at the
accepted exit.  A run that traps would have a trapped `args_sizes_get`, `args_get`, `random_get`, or
write (`main_trapped`), whose image no event sequence that meets `Full` gives, and the shim accepts
every status of at most 78.  With `output_count`, the status-0 case of `Choices` gives the count of
the request: for every sequence `o` of K values in [1, N], exactly `⌊2^64 / N⌋^K` K-tuples of
accepted words make the writes take the lines of `o`.

`witness_run` shows that the premises can hold together.  The replies `witnessReplies` answer call
0 with 4,096 zero bytes and every later call with 2.  Under them, every run of `main` and its exit
with the arguments `witnessArgs`, which give N and K of 1, ends at the accepted exit with status 0
and has layer events that meet `Full`.  Its proof follows the run: a `getrandom` of 4,096 bytes
answered in full and a `write` of the line `1` that takes both of its bytes. -/

namespace Demos.RandomChoice

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline Verified.Wasi Verified.Shim
open RandomHistogram (Full randomData)

/-- N: the value that `parseSpec` reads from argument 1 of the arguments `args`, each followed by a
zero byte, and 0 when it refuses the argument. -/
def argN (args : List (List UInt8)) : UInt64 := parseSpec (bytesOfList (stringsBytes args), 1)

/-- K: the value that `parseSpec` reads from argument 2 of the arguments `args`, each followed by a
zero byte, and 0 when it refuses the argument. -/
def argK (args : List (List UInt8)) : UInt64 := parseSpec (bytesOfList (stringsBytes args), 2)

/-- `Mirrors x e`: the layer event `e` is the one event that the shim makes for the WASI event `x`
of a run whose `getrandom` calls return every byte.  For a `random_get` of 4,096 bytes, `e` is a
`getrandom` of 4,096 bytes with flags 0 that returned 4,096, and the call returned errno 0 and the
bytes of `e`'s output.  For a write to standard output, `e` is a `write` of descriptor 1 whose input
holds the write's bytes and whose length argument is their number.  When the write returned errno
0, the `write` returned the write's count, at most that number, and otherwise an error number whose
errno is the write's.  No layer event mirrors any other WASI event. -/
def Mirrors : Event → Linux.Event → Prop
  | .sys call sent (.returned errno outputs), e =>
    call = Call.randomGet ∧ sent = [.space 4096] ∧ e.call = Linux.getrandomCall ∧
      Linux.arg e.args 1 = 4096 ∧ Linux.arg e.args 2 = 0 ∧ e.ret = 4096 ∧ errno = 0 ∧
      outputs = [bytesOfList e.output]
  | .write output offered (.returned errno count), e =>
    output = .stdout ∧ e.call = Linux.writeCall ∧ Linux.arg e.args 0 = 1 ∧
      Linux.arg e.args 2 = UInt64.ofNat offered.data.size ∧
      e.inputs.headD [] = offered.data.data.toList ∧
      (errno = 0 → count = e.ret ∧ e.ret.toNat ≤ offered.data.size) ∧
      (errno ≠ 0 → Linux.isError e.ret = true ∧ errno = errnoOf (0 - e.ret))
  | _, _ => False

/-- The layer events `ls` and the exit status `status` that the request asks of a run whose
`getrandom` calls return every byte, with the arguments `args`, from which `argN` and `argK` read
N and K.  When `parseSpec` refuses N or K, so that `argN` or `argK` is 0, no layer event precedes
`exit_group`, and the status is 2.  Otherwise the layer events mirror, one for one, WASI events
that make the passes of `Rounds` from K values and `passes K` passes, whose random bytes are those
that the `getrandom` events of `ls` returned and whose status is `status`.  The status is 0 only
when the writes of `ls` took `outputOf N chosen`, the lines of the picks of the K-tuple `chosen` of
the first K accepted words of those bytes, and it is `capStatus` only when those bytes hold the
`512 · passes K` words of the cap's passes, fewer than K of them accepted. -/
def Choices (args : List (List UInt8)) (ls : List Linux.Event) (status : UInt64) : Prop :=
  ((argN args = 0 ∨ argK args = 0) → ls = [] ∧ status = 2) ∧
  (argN args ≠ 0 → argK args ≠ 0 →
    (∃ events, List.Forall₂ Mirrors events ls ∧
      Rounds (argN args) (argK args) (passes (argK args)).toNat events (randomData ls) status) ∧
    (status = 0 → ∃ chosen : Fin (argK args).toNat → UInt64,
      (∀ i, accepts (argN args) (chosen i) = true) ∧
      List.ofFn chosen = ((RandomHistogram.words (randomData ls)).filter fun w =>
        accepts (argN args) w).take (argK args).toNat ∧
      Linux.writeData 1 ls = outputOf (argN args) chosen) ∧
    (status = capStatus →
      (RandomHistogram.words (randomData ls)).length = 512 * (passes (argK args)).toNat ∧
      (accepted (argN args) (RandomHistogram.words (randomData ls))).length < (argK args).toNat))

/-! ## The images under `Full` -/

/-- A `write` gives no random bytes. -/
theorem randomData_write {e : Linux.Event} (call : e.call = Linux.writeCall) :
    randomData [e] = [] := by
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  simp [RandomHistogram.randomData, call, other]

/-- The image of a write to standard output that returned is one `write` that mirrors it. -/
theorem write_mirror {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {offered : Bytes} {errno count : UInt64} {l : List Linux.Event}
    (image : Image F L I before (.write .stdout offered (.returned errno count)) l) :
    ∃ e, l = [e] ∧ Mirrors (.write .stdout offered (.returned errno count)) e := by
  obtain ⟨e, a, rfl, call, args, inputs, -, small, reply⟩ := image
  have wide : (UInt64.ofNat offered.data.size).toNat = offered.data.size :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have fd : Linux.arg e.args 0 = 1 := by simp [args, Linux.arg, Output.fd]
  have count' : Linux.arg e.args 2 = UInt64.ofNat offered.data.size := by simp [args, Linux.arg]
  have input : e.inputs.headD [] = offered.data.data.toList := by simp [inputs]
  unfold writeReply at reply
  split at reply
  · rename_i within
    obtain ⟨rfl, rfl⟩ := Transfer.returned.inj reply
    rw [wide] at within
    exact ⟨e, rfl, rfl, call, fd, count', input, fun _ => ⟨rfl, within⟩,
      fun nonzero => absurd rfl nonzero⟩
  · split at reply
    · rename_i error
      obtain ⟨rfl, rfl⟩ := Transfer.returned.inj reply
      exact ⟨e, rfl, rfl, call, fd, count', input, fun zero => absurd zero (errnoOf_valid _).2,
        fun _ => ⟨error, rfl⟩⟩
    · cases reply

/-- The image of a `random_get` of 4,096 bytes whose `getrandom` events return the counts that they
ask for is one `getrandom` that mirrors it. -/
theorem random_mirror {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {errno : UInt64} {outputs : List Bytes} {l : List Linux.Event}
    (image : Image F L I before (.sys .randomGet [.space 4096] (.returned errno outputs)) l)
    (full : Full l) :
    ∃ e, l = [e] ∧ Mirrors (.sys .randomGet [.space 4096] (.returned errno outputs)) e := by
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  rcases RandomHistogram.random_full calls full (UInt64.toNat_lt _) with
    ⟨-, impossible, -⟩ | ⟨e, rfl, call, retNat, asked, flags, reply⟩
  · exact absurd impossible (by decide)
  · obtain ⟨rfl, rfl⟩ := Transfer.returned.inj reply
    exact ⟨e, rfl, rfl, rfl, call, asked.trans (by decide), flags, UInt64.toNat_inj.mp retNat,
      rfl, rfl⟩

/-- The random bytes of a `getrandom` that mirrors a `random_get` that filled a buffer of 4,096
bytes are the buffer's bytes. -/
theorem randomData_draw {e : Linux.Event} {errno : UInt64} {buffer : Bytes}
    (mirror : Mirrors (.sys .randomGet [.space 4096] (.returned errno [buffer])) e)
    (size : buffer.data.size = 4096) : randomData [e] = buffer.data.data.toList := by
  obtain ⟨-, -, call, -, -, ret, -, outputs⟩ := mirror
  obtain rfl := (List.cons.inj outputs).1
  rw [bytesOfList_size] at size
  simp [RandomHistogram.randomData, call, ret, bytesOfList, ← size]

/-- The images of the writes of `Writes` mirror them, one for one, and give no random bytes. -/
theorem writes_mirrors {F : OpenFlags} {L : ShimLayout} {I : Launch} :
    ∀ {p : Nat} {text : List UInt8} {writes : List Event} {status : UInt64}
      {before ls : List Linux.Event}, Writes p text writes status →
      Images F L I before writes ls → List.Forall₂ Mirrors writes ls ∧ randomData ls = []
  | _, _, _, _, _, _, .done, images => by
    cases images
    exact ⟨.nil, rfl⟩
  | _, _, _, _, _, _, .stalled _, images => by
    cases images
    exact ⟨.nil, rfl⟩
  | _, _, _, _, _, _, .failed _ _ _ _, images => by
    cases images with
    | cons image rest =>
      cases rest
      obtain ⟨e, rfl, mirror⟩ := write_mirror image
      exact ⟨.cons mirror .nil, by simpa using randomData_write mirror.2.1⟩
  | _, _, _, _, _, _, .wrote _ _ rest, images => by
    cases images with
    | cons image restImages =>
      obtain ⟨e, rfl, mirror⟩ := write_mirror image
      obtain ⟨mirrors, data⟩ := writes_mirrors rest restImages
      refine ⟨.cons mirror mirrors, ?_⟩
      rw [RandomHistogram.randomData_append, randomData_write mirror.2.1, data]
      rfl

/-- The images of the passes of `Rounds` whose `getrandom` events return the counts that they ask
for mirror them, one for one, and their random bytes are the bytes that the passes drew. -/
theorem rounds_mirrors {F : OpenFlags} {L : ShimLayout} {I : Launch} {n : UInt64} :
    ∀ {r : UInt64} {p : Nat} {events : List Event} {bytes : List UInt8} {status : UInt64}
      {before ls : List Linux.Event}, Rounds n r p events bytes status →
      Images F L I before events ls → Full ls →
      List.Forall₂ Mirrors events ls ∧ randomData ls = bytes
  | _, _, _, _, _, _, _, .done, images, _ => by
    cases images
    exact ⟨.nil, rfl⟩
  | _, _, _, _, _, _, _, .capped _, images, _ => by
    cases images
    exact ⟨.nil, rfl⟩
  | _, _, _, _, _, _, _, .drawFailed _ nonzero _, images, full => by
    cases images with
    | cons image rest =>
      cases rest
      obtain ⟨e, -, mirror⟩ := random_mirror image (by simpa using full)
      obtain ⟨-, -, -, -, -, -, zero, -⟩ := mirror
      exact absurd zero nonzero
  | _, _, _, _, _, _, _, .writeEnded _ size writes _, images, full => by
    cases images with
    | cons image rest =>
      obtain ⟨e, rfl, mirror⟩ :=
        random_mirror image (full.sub fun x m => List.mem_append_left _ m)
      obtain ⟨mirrors, data⟩ := writes_mirrors writes rest
      refine ⟨.cons mirror mirrors, ?_⟩
      rw [RandomHistogram.randomData_append, data, List.append_nil, randomData_draw mirror size]
  | _, _, _, _, _, _, _, .drew _ size writes rounds, images, full => by
    cases images with
    | cons image rest =>
      obtain ⟨lw, lr, rfl, writeImages, roundImages⟩ :=
        Verified.Examples.WasiReadAll.images_split rest
      obtain ⟨e, rfl, mirror⟩ :=
        random_mirror image (full.sub fun x m => List.mem_append_left _ m)
      obtain ⟨writeMirrors, writeRandom⟩ := writes_mirrors writes writeImages
      obtain ⟨roundMirrors, roundRandom⟩ := rounds_mirrors rounds roundImages
        (full.sub fun x m => List.mem_append_right _ (List.mem_append_right _ m))
      refine ⟨.cons mirror (List.rel_append writeMirrors roundMirrors), ?_⟩
      rw [RandomHistogram.randomData_append, RandomHistogram.randomData_append, writeRandom,
        roundRandom, randomData_draw mirror size, List.nil_append]

/-! ## Trapped runs of `main` -/

/-- A trapped run of `main` under a host that rejects no exit status below 126 has a trapped
`args_sizes_get`, `args_get`, `random_get`, or write. -/
theorem main_trapped {World : Type} {host : Host World}
    (accepts : ∀ {world code message final}, host.exitTrap world code message final →
      126 ≤ code.toNat)
    {world final : World} {trace : List Event} {message : String}
    (run : Exec host main world trace (.trapped message) final) :
    ∃ e ∈ trace, RandomHistogram.TrapEvent e := by
  obtain ⟨after, pre, middle, rest, argsRun, cont, rfl⟩ := Exec.unbind args run
  cases middle with
  | exited c => exact absurd rfl ((RandomHistogram.args_returned argsRun).1 c)
  | trapped m =>
    obtain ⟨e, member, trapped⟩ := RandomHistogram.args_trapped argsRun
    exact ⟨e, List.mem_append_left _ member, trapped⟩
  | returned a =>
    change Exec host (if a.errno != 0 then Action.pure a.errno else _) after rest _ final at cont
    split at cont
    · cases cont
    dsimp only at cont
    split at cont
    · cases cont
    obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont
    cases loopRun with
    | loop loopRun =>
    cases drawn with
    | exited c => cases cont2.2.1
    | trapped m =>
      obtain ⟨-, -, trapped⟩ := draw_loop (n := parseArg a.bytes 1) (fun _ _ => rfl)
        (fun _ _ => rfl) _ 0 _ _ _ (by simp) (by simp) loopRun
      obtain ⟨e, member, kind⟩ := trapped accepts m rfl
      refine ⟨e, List.mem_append_right _ (List.mem_append_left _ member), ?_⟩
      rcases kind with ⟨committed, rfl⟩ | ⟨offered, committed, rfl⟩
      · exact .inr (.inr rfl)
      · trivial
    | returned s =>
      change Exec host (if s.2.1 != 0 then Action.pure s.2.1
        else if s.1 != 0 then (Action.pure 77 : Action UInt64) else .pure 0) loopAfter post _ final
        at cont2
      split at cont2
      · cases cont2
      · split at cont2 <;> cases cont2

/-! ## Runs that exit -/

/-- Under the shim's host, every run of `main` and its exit from a launch whose arguments'
strings and eight-byte pointers take at most `argsLimit` bytes, whose layer events, the images of
its WASI events, meet `Full`, ends at the accepted exit with a status that meets `Choices`. -/
theorem linux_exec_choices {F : OpenFlags} {L : ShimLayout} {I : Launch} {R : Linux.Replies}
    {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit} {ls : List Linux.Event}
    (small : stringsSize I.args + 8 * I.args.length ≤ RandomHistogram.argsLimit)
    (execution : Exec (linuxHost F L I R) (main.bind fun status => Action.exit status) world T
      outcome final)
    (images : Images F L I world.events T ls) (full : Full ls) :
    ∃ c, outcome = .exited c ∧ Choices I.args ls c := by
  have fit := RandomHistogram.stringsFit_of_small small
  have accepts : ∀ {world code message final}, (linuxHost F L I R).exitTrap world code message
      final → 126 ≤ code.toNat := fun rejected => rejected.1
  cases outcome with
  | returned v => exact (bind_exit_not_returned execution).elim
  | trapped m =>
    exfalso
    obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
    cases middle with
    | exited c => cases cont.2.1
    | trapped m' =>
      obtain ⟨e, member, trapped⟩ := main_trapped accepts mainRun
      obtain ⟨_, l, image, sub⟩ :=
        RandomHistogram.images_mem images e (List.mem_append_left _ member)
      exact RandomHistogram.image_untrapped image trapped (full.sub sub) fit
    | returned status =>
      have low := ((main_runs mainRun).1 status rfl).1
      change Exec _ (Action.exit status) after rest (.trapped m) final at cont
      cases cont with
      | exitTrap rejected =>
        have high := rejected.1
        rw [exitStatus_of_le low] at high
        omega
  | exited c =>
    obtain ⟨events, rfl, -, meets⟩ := exec_main execution
    refine ⟨c, rfl, ?_⟩
    obtain ⟨a, pre, rest, middle, rfl, argsRun, -, refused, accepted⟩ := meets
    obtain ⟨aZero, aBytes, preEmpty⟩ := RandomHistogram.linux_args argsRun small
    obtain ⟨l, lx, rfl, front, exitImages⟩ := Verified.Examples.WasiReadAll.images_split images
    obtain ⟨lp, lr, rfl, preImages, restImages⟩ :=
      Verified.Examples.WasiReadAll.images_split front
    cases preEmpty _ _ preImages
    cases exitImages with
    | cons image tail =>
      cases tail
      cases image
      simp only [List.nil_append, List.append_nil] at full ⊢
      have hN : argN I.args = parseSpec (a.bytes, 1) := by unfold argN; rw [aBytes]
      have hK : argK I.args = parseSpec (a.bytes, 2) := by unfold argK; rw [aBytes]
      unfold Choices
      rw [hN, hK]
      refine ⟨fun refusal => ?_, fun hn hk => ?_⟩
      · obtain ⟨rfl, rfl⟩ := refused aZero refusal
        cases restImages
        exact ⟨rfl, rfl⟩
      · obtain ⟨bytes, rounds, zero, cap⟩ := accepted aZero hn hk
        obtain ⟨mirrors, random⟩ := rounds_mirrors rounds restImages full
        rw [random]
        refine ⟨⟨rest, mirrors, rounds⟩, fun hz => ?_, cap⟩
        obtain ⟨written, enough⟩ := zero hz
        obtain ⟨chosen, acc, first, text⟩ := first_picks _ _ _ enough
        exact ⟨chosen, acc, first, (restImages.writeData 1).trans (written.trans text)⟩

/-! ## Replies that answer every call in full -/

/-- The arguments of a run with N and K of 1: the program name `c` and the arguments `1` and
`1`. -/
def witnessArgs : List (List UInt8) := [[99], [49], [49]]

/-- The replies of a run with the arguments `witnessArgs` that answer each of its calls in full:
call 0, the `getrandom` of the run's one pass, with 4,096 bytes, each 0, and every later call, the
`write` of the line `1` among them, with 2. -/
def witnessReplies : Linux.Replies := fun k =>
  if k = 0 then ⟨4096, fun _ => 0⟩ else ⟨2, fun _ => 0⟩

/-- The draw buffer that `witnessReplies` fills: 4,096 zero bytes, as the reply's region holds
them. -/
def witnessBuffer : Bytes := bytesOfList ((List.range 4096).map fun _ => 0)

theorem witnessBuffer_size : witnessBuffer.data.size = 4096 := by
  simp only [witnessBuffer, bytesOfList_size, List.length_map, List.length_range]

/-- The pass of the run with N and K of 1 over `witnessBuffer` writes the line `1`. -/
theorem witness_text : passText 1 1 witnessBuffer = [49, 10] := by decide +kernel

theorem witness_picks : (passPicks 1 1 witnessBuffer).length = 1 := by decide +kernel

/-- The image of `random_get` of 4,096 bytes whose first layer event holds the reply
`witnessReplies 0` is that event alone, a `getrandom` that returned the count that it asked for,
and the reply is errno 0 with `witnessBuffer`. -/
theorem witness_random {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {reply : Transfer (List Bytes)} {l rest : List Linux.Event}
    (image : Image F L I before (.sys .randomGet [.space 4096] reply) l)
    (carried : Carried witnessReplies 0 (l ++ rest)) :
    (∃ e, l = [e] ∧ e.call = Linux.getrandomCall ∧ e.ret = Linux.arg e.args 1) ∧
      reply = .returned 0 [witnessBuffer] := by
  obtain ⟨-, image⟩ := image
  rw [sysImage_random] at image
  obtain ⟨a, calls⟩ := image
  rcases l with _ | ⟨e, more⟩
  · obtain ⟨done, -⟩ := calls
    exact absurd done (by decide)
  · obtain ⟨-, prior, ret, output, rfl, going⟩ := calls
    obtain ⟨⟨answered, filled⟩, -⟩ := carried
    simp only [witnessReplies, ↓reduceIte] at answered filled
    subst answered
    rw [ite_eq_right (by decide)] at going
    obtain ⟨rfl, rfl⟩ := going
    refine ⟨⟨_, rfl, rfl, rfl⟩, ?_⟩
    have size : (UInt64.ofNat (UInt64.toNat 4096 - 0)).toNat = 4096 := by decide
    have regions : Linux.outputRegions [a + UInt64.ofNat 0, UInt64.ofNat (UInt64.toNat 4096 - 0),
        0] 0 Linux.getrandomCall.params = [(a + UInt64.ofNat 0, 4096)] := by
      rw [← size]
      rfl
    rw [regions] at filled
    have out : output = (List.range 4096).map fun _ => 0 := filled
    clear filled
    unfold randomLast
    rw [ite_eq_left (by decide), List.nil_append, out]
    rfl

/-- The image of a write of 2 bytes to standard output whose first layer event holds the reply
`witnessReplies 1` is that event alone, a `write` that took both bytes, and the reply is errno 0
with the count 2. -/
theorem witness_write {F : OpenFlags} {L : ShimLayout} {I : Launch} {before : List Linux.Event}
    {offered : Bytes} {reply : Transfer UInt64} {l rest : List Linux.Event}
    (image : Image F L I before (.write .stdout offered reply) l) (two : offered.data.size = 2)
    (carried : Carried witnessReplies 1 (l ++ rest)) :
    (∃ e, l = [e] ∧ e.call = Linux.writeCall ∧ RandomHistogram.Took e) ∧
      reply = .returned 0 2 := by
  obtain ⟨e, a, rfl, call, args, -, -, -, written⟩ := image
  obtain ⟨⟨answered, -⟩, -⟩ := carried
  simp only [witnessReplies, Nat.one_ne_zero, ↓reduceIte] at answered
  rw [answered, two] at written
  refine ⟨⟨e, rfl, call, ?_⟩, by rw [written]; rfl⟩
  simp [RandomHistogram.Took, args, Linux.arg, answered, two]

/-- A step of `main`'s loop from one value to choose and the initial buffers, under the shim's host
with the arguments `witnessArgs` and the replies `witnessReplies`, whose layer events start at call
0: it returns a state with no value left and no status, and its layer events meet `Full`. -/
theorem witness_step {F : OpenFlags} {L : ShimLayout} {environ : List (List UInt8)}
    {granted : Bool} {step : UInt64 → ChooseState → Action ChooseState}
    (stepped : ChooseStep 1 step)
    {i : UInt64} {world after : LinuxWorld} {trace : List Event} {outcome : Outcome ChooseState}
    {before l rest : List Linux.Event}
    (run : Exec (linuxHost F L ⟨witnessArgs, environ, granted⟩ witnessReplies)
      (step i (1, 0, Bytes.build 4096 fun _ => 0, Bytes.build 10752 fun _ => 0)) world trace
      outcome after)
    (images : Images F L ⟨witnessArgs, environ, granted⟩ before trace l)
    (carried : Carried witnessReplies 0 (l ++ rest)) :
    ∃ draw out, outcome = .returned (0, 0, draw, out) ∧ Full l := by
  have hdraw : (Bytes.build 4096 fun _ => (0 : UInt64)).data.size = 4096 := by simp
  have hout : (Bytes.build 10752 fun _ => (0 : UInt64)).data.size = 10752 := by simp
  have other : Linux.writeCall ≠ Linux.getrandomCall := by decide
  rw [stepped] at run
  change Exec _ (.sys .randomGet [.space ((Bytes.build 4096 fun _ => (0 : UInt64)).windowLength 0
    4096)] _) _ _ _ _ at run
  rw [window_whole hdraw] at run
  cases run with
  | sys_reject fits => exact absurd random_accepted fits
  | sys_trap _ _ =>
    cases images with
    | cons image tail =>
      cases tail
      cases (witness_random (rest := rest) image (by simpa using carried)).2
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ _ next =>
    cases images with
    | cons image restImages =>
    rw [List.append_assoc] at carried
    obtain ⟨⟨e0, rfl, drawCall, drawFull⟩, answered⟩ := witness_random image carried
    obtain ⟨rfl, rfl⟩ := Transfer.returned.inj answered
    have hFill : passFill (1, 0, Bytes.build 4096 fun _ => 0, Bytes.build 10752 fun _ => 0)
        (sysReply 0 [witnessBuffer]) =
        ⟨0, 4096, (Bytes.build 4096 fun _ => (0 : UInt64)).splice 0 witnessBuffer⟩ := by
      simp [passFill, FillResult.of, sysReply, Reply.bytes, Bytes.window, window_whole hdraw]
    beta_reduce at next
    rw [hFill] at next
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
    obtain ⟨hsize, hcount, hpicks, hfilled, hW, -⟩ := pass_put 1 1 hout hdraw witnessBuffer_size
    rw [witness_text] at hcount hfilled hW
    rw [witness_picks] at hpicks
    generalize putPicks (Bytes.build 10752 fun _ => 0) 1
      ((Bytes.build 4096 fun _ => (0 : UInt64)).splice 0 witnessBuffer) 1 = put
      at hsize hcount hpicks hfilled hW next
    obtain ⟨_, wtrace, woutcome, ktrace, wrun, krun, rfl⟩ := Exec.unbind _ next
    have writeRun := writeAll_run (by omega) wrun
    rw [hfilled, hW] at writeRun
    obtain ⟨lw, lk, rfl, writeImages, tailImages⟩ :=
      Verified.Examples.WasiReadAll.images_split restImages
    have later : Carried witnessReplies 1 (lw ++ (lk ++ rest)) := by
      have whole : Carried witnessReplies 0 ([e0] ++ (lw ++ (lk ++ rest))) := by
        simpa [List.append_assoc] using carried
      simpa using (RandomHistogram.carried_split whole).2
    have drawFull' : Full [e0] := by
      intro y member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨fun _ => drawFull, fun writing => absurd (drawCall.symm.trans writing) other.symm⟩
    cases writeRun with
    | done ended => simp at ended
    | @wrote _ count _ offered events _ left offers within rest' =>
      cases writeImages with
      | @cons _ _ l1 _ lrest image writeRest =>
      have two : offered.data.size = 2 := by
        have := congrArg List.length offers
        simpa using this
      have writeCarried : Carried witnessReplies 1 (l1 ++ (lrest ++ (lk ++ rest))) := by
        simpa [List.append_assoc] using later
      obtain ⟨⟨e1, rfl, writeCall, took⟩, written⟩ := witness_write image two writeCarried
      obtain ⟨-, rfl⟩ := Transfer.returned.inj written
      cases rest' with
      | done _ =>
        cases writeRest
        change Exec _ (if (0 + 2 : UInt64) < put.2.1 then .pure _ else .pure _) _ ktrace _ _
          at krun
        rw [hcount, ite_eq_right (by decide)] at krun
        obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure krun
        cases tailImages
        have left : (1 : UInt64) - put.2.2 = 0 := by rw [hpicks]; decide
        rw [left]
        refine ⟨_, _, rfl, fun y member => ?_⟩
        simp only [List.append_nil, List.singleton_append, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact drawFull' _ (List.mem_singleton_self _)
        · exact ⟨fun drawing => absurd (writeCall.symm.trans drawing) other,
            fun _ => .inr took⟩
      | wrote left' => simp at left'
      | failed left' => simp at left'
      | trapped left' => simp at left'
    | @failed _ _ _ _ offered _ _ left offers nonzero _ _ =>
      cases writeImages with
      | @cons _ _ l1 _ lrest image _ =>
      have two : offered.data.size = 2 := by
        have := congrArg List.length offers
        simpa using this
      have writeCarried : Carried witnessReplies 1 (l1 ++ (lrest ++ (lk ++ rest))) := by
        simpa [List.append_assoc] using later
      exact absurd (Transfer.returned.inj (witness_write image two writeCarried).2).1 nonzero
    | @trapped _ _ offered _ _ left offers =>
      cases writeImages with
      | @cons _ _ l1 _ lrest image _ =>
      have two : offered.data.size = 2 := by
        have := congrArg List.length offers
        simpa using this
      have writeCarried : Carried witnessReplies 1 (l1 ++ (lrest ++ (lk ++ rest))) := by
        simpa [List.append_assoc] using later
      cases (witness_write image two writeCarried).2

/-- The loop of `main` from one value to choose and the initial buffers, with its three passes,
under the shim's host with the arguments `witnessArgs` and the replies `witnessReplies`, whose
layer events start at call 0: its first pass returns a state with no value left and no status, the
loop stops there, and its layer events meet `Full`. -/
theorem witness_loop {F : OpenFlags} {L : ShimLayout} {environ : List (List UInt8)}
    {granted : Bool} {test : UInt64 → ChooseState → Bool}
    {step : UInt64 → ChooseState → Action ChooseState}
    (tested : ∀ i s, test i s = (s.1 != 0 && s.2.1 == 0)) (stepped : ChooseStep 1 step)
    {world after : LinuxWorld} {trace : List Event} {outcome : Outcome ChooseState}
    {before l rest : List Linux.Event}
    (run : LoopExec (linuxHost F L ⟨witnessArgs, environ, granted⟩ witnessReplies) 3 0
      (1, 0, Bytes.build 4096 fun _ => 0, Bytes.build 10752 fun _ => 0) test step .pure world
      trace outcome after)
    (images : Images F L ⟨witnessArgs, environ, granted⟩ before trace l)
    (carried : Carried witnessReplies 0 (l ++ rest)) :
    ∃ draw out, outcome = .returned (0, 0, draw, out) ∧ Full l := by
  cases run with
  | stop going _ =>
    rw [tested] at going
    simp at going
  | exit _ firstStep =>
    obtain ⟨_, _, same, -⟩ := witness_step stepped firstStep images carried
    cases same
  | trap _ firstStep =>
    obtain ⟨_, _, same, -⟩ := witness_step stepped firstStep images carried
    cases same
  | next _ firstStep restLoop =>
    obtain ⟨ls1, ls2, rfl, stepImages, loopRestImages⟩ :=
      Verified.Examples.WasiReadAll.images_split images
    obtain ⟨draw, out, same, stepFull⟩ := witness_step (rest := ls2 ++ rest) stepped firstStep
      stepImages (by simpa [List.append_assoc] using carried)
    cases same
    obtain ⟨rfl, rfl⟩ := loop_stopped tested (0, 0, draw, out) (by simp) restLoop
    cases loopRestImages
    exact ⟨draw, out, rfl, by simpa using stepFull⟩

/-- Under the shim's host with the arguments `witnessArgs` and the replies `witnessReplies`, every
run of `main` and its exit ends at the accepted exit with status 0, and its layer events, the
images of its WASI events, meet `Full`. -/
theorem witness_run {F : OpenFlags} {L : ShimLayout} {environ : List (List UInt8)}
    {granted : Bool} {world final : LinuxWorld} {T : List Event} {outcome : Outcome Unit}
    {ls : List Linux.Event}
    (execution : Exec (linuxHost F L ⟨witnessArgs, environ, granted⟩ witnessReplies)
      (main.bind fun status => Action.exit status) world T outcome final)
    (images : Images F L ⟨witnessArgs, environ, granted⟩ world.events T ls)
    (carried : Carried witnessReplies 0 ls) : outcome = .exited 0 ∧ Full ls := by
  have small : stringsSize witnessArgs + 8 * witnessArgs.length ≤ RandomHistogram.argsLimit := by
    decide
  have fit := RandomHistogram.stringsFit_of_small small
  have parsedN : parseArg (bytesOfList (stringsBytes witnessArgs)) 1 = 1 := by decide +kernel
  have parsedK : parseArg (bytesOfList (stringsBytes witnessArgs)) 2 = 1 := by decide +kernel
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨lm, lx, rfl, mainImages, exitImages⟩ :=
    Verified.Examples.WasiReadAll.images_split images
  obtain ⟨after1, pre, middle1, rest1, argsRun, cont1, rfl⟩ := Exec.unbind args mainRun
  obtain ⟨lp, lq, rfl, preImages, restImages⟩ :=
    Verified.Examples.WasiReadAll.images_split mainImages
  cases middle1 with
  | exited c => exact absurd rfl ((RandomHistogram.args_returned argsRun).1 c)
  | trapped m => exact (RandomHistogram.linux_args_untrapped argsRun fit).elim
  | returned a =>
  obtain ⟨aZero, aBytes, preEmpty⟩ := RandomHistogram.linux_args argsRun small
  cases preEmpty _ _ preImages
  simp only at aBytes
  change Exec _ (if a.errno != 0 then Action.pure a.errno else _) after1 rest1 middle after
    at cont1
  rw [ite_eq_right (by simp [aZero])] at cont1
  dsimp only at cont1
  rw [aBytes, parsedN, parsedK, ite_eq_right (by decide)] at cont1
  obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont1
  obtain ⟨ld, lw, rfl, drawImages, postImages⟩ :=
    Verified.Examples.WasiReadAll.images_split restImages
  have carried' : Carried witnessReplies 0 (ld ++ (lw ++ lx)) := by
    simpa [List.append_assoc] using carried
  cases loopRun with
  | loop loopRun =>
  rw [show ((1 : UInt64) / 128 + 3).toNat = 3 by decide] at loopRun
  obtain ⟨draw, out, rfl, loopFull⟩ :=
    witness_loop (fun _ _ => rfl) (fun _ _ => rfl) loopRun drawImages carried'
  change Exec _ (if (0 : UInt64) != 0 then Action.pure 0
    else if (0 : UInt64) != 0 then (Action.pure 77 : Action UInt64) else .pure 0) loopAfter post
    middle after at cont2
  rw [ite_eq_right (by decide), ite_eq_right (by decide)] at cont2
  obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure cont2
  cases postImages
  change Exec _ (Action.exit 0) after rest outcome final at cont
  cases cont with
  | exit _ =>
    cases exitImages with
    | cons image tail =>
      cases tail
      cases image
      refine ⟨rfl, ?_⟩
      simpa using loopFull
  | exitTrap rejected => exact absurd rejected.1 (by decide)

#print axioms linux_exec_choices
#print axioms witness_run

end Demos.RandomChoice
