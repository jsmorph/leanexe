import Demos.ManifestCheck.CommandStart
import Demos.ManifestCheck.Compiled
import Verified.Examples.WasiSysTotal

/-! The resource model's charge of the manifest checker's `main`, the budget that the generated
`command.total` takes as a bound on every prefix of `main`.

`body_bounded` bounds every run and every prefix of `main`'s body by `budget M` for every host
whose successful `args_sizes_get` replies ask for at most `argsLimit` bytes and whose successful
`fd_filestat_get` replies report a size of at most `M` bytes.  The model charges a copy of an owned
value at each use after which the value stays live, and it credits no release.  The charge of
`main` holds the block of `args`, the copy of the argument that names the manifest, the read buffer
of 65,536 bytes, the charge of `readManifest`, that of `parse`, and that of `checkLines`.

`readManifest` charges the record block of `fd_filestat_get` and the call of `readBytes`, which
builds the manifest's buffer of the reported size and whose read passes charge nothing.  A run of
the reflected call of `readManifest` that returns is a run of `readManifest` that returns the same
value (`ResourceCall.erase` and `command.readManifest.related`), and with status 0 its manifest has
the reported size (`readManifest_size`, from `readBytes_run` of `CommandProof.lean`), so `parse`
charges at most `176 M + 464` bytes.  `hashFile` charges the block of `finish`'s last words, at
most `blockCost 8`, and its read passes charge nothing.  `writeAll` charges nothing
(`writeAll_bounded`).

The charges read the flags of the pure program from `flags_toList`, which the kernel computes once:
`simp` with `decide` would otherwise evaluate `Prog.flags` over the bodies of the pure functions
at each call, which exhausts the memory of a run.  The charge lemmas of the pure calls hold at
every call depth, since the effect functions run at depths 0 to 2.

A pass of `checkLines` for a line charges the copy of its name, its output line, and the call of
`hashFile`, so its charge depends on the pass's index.  `loop_bounded_sum` bounds a loop by the sum
of a charge for each index, and `lines_charge_le` bounds that sum for the lines of a manifest of
`n` bytes by `4 (n + 1)`: the lines are disjoint pieces of the manifest, so their lengths with one
byte each sum to at most `n + 1` (`lines_total`), and each line has at least 67 bytes.

`budget_le` gives the closed form `budget M ≤ 181 M + 12,649,235`.  `prefix_bound` gives the
budget premise of `total_meets` from `body_bounded`, and `total_meets_budget` states `total_meets`
with the premises on the host's replies in its place.  Linux 4.13 and later limit the strings and
pointers of `argv` and `envp` together to at most 6 MiB, `argsLimit` (`get_arg_page` of
`fs/exec.c` in v4.13, `bprm_stack_limits` in v6.12). -/

namespace Demos.ManifestCheck

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-! ## The budget -/

/-- The bytes of the arguments, with the four-byte pointer of each and three bytes of alignment,
for which the budget holds: 6 MiB, the most that Linux lets the strings and pointers of `argv` and
`envp` take together. -/
def argsLimit : Nat := 6291456

/-- The charge of `checkLines` on a manifest of `n` bytes. -/
def checkBudget (n : Nat) : Nat := 4 * (n + 1)

/-- A bound on the charge of `main` for a manifest of at most `M` bytes: the block of `args`, the
copy of the argument, the read buffer, the record block of `fd_filestat_get` and the manifest's
buffer, the charge of `parse`, and that of `checkLines`. -/
def budget (M : Nat) : Nat :=
  2 * Bytes.allocationCost argsLimit + 65584 + (120 + Bytes.allocationCost M) + (176 * M + 464) +
    checkBudget M

theorem budget_le (M : Nat) : budget M ≤ 181 * M + 12649235 := by
  have h := allocationCost_le M
  have hA : Bytes.allocationCost argsLimit = 6291504 := by decide
  unfold budget checkBudget
  omega

/-! ## Facts about the reflected program -/

/-- The type of the state of `hashFile`'s loop. -/
abbrev hashTy : Ty :=
  (Ty.elem (Elem.word.prod (Elem.word.prod (Elem.word.prod (Elem.word.prod (Elem.word.prod
    (Elem.word.prod (Elem.word.prod Elem.word)))))))).pair
    (Ty.bytes.pair (Ty.elem (Elem.word.prod (Elem.word.prod Elem.word))))

/-- The type of the state of the loops of `readBytes` and `checkLines`. -/
abbrev bufferTy : Ty := Ty.bytes.pair (Ty.elem (Elem.word.prod Elem.word))

/-- The type of eight words of a SHA-256 hash value. -/
abbrev words8Ty : Ty :=
  Ty.elem (Elem.word.prod (Elem.word.prod (Elem.word.prod (Elem.word.prod (Elem.word.prod
    (Elem.word.prod (Elem.word.prod Elem.word)))))))

/-- The type of four words of a digest. -/
abbrev words4Ty : Ty := Ty.elem (Elem.word.prod (Elem.word.prod (Elem.word.prod Elem.word)))

/-- The flags of the pure program's functions, from `argScan` back to `isHex`.  The kernel
computes them once, so that the charges of the effect bodies read a list rather than evaluate
`Prog.flags`, whose evaluation over the bodies of the earlier functions at each call exhausts the
memory of a run. -/
theorem flags_toList : command.pure.program.flags.toList =
    [([false], false), ([false, false], false), ([false, false, false], false),
      ([false, false, false, false, false, false], false), ([false, false, false], false),
      ([false, false, false], false), ([false, false, false, false], false),
      ([false, false], false), ([false, false], false),
      ([false, false, false, false, false], false),
      ([false, false, false], false), ([false], false), ([false, false, false], false),
      ([false, false, false, false, false], false), ([false, false, false, false, false], false),
      ([false], false), ([false, false], false), ([false, false], false),
      ([false, false, false], false), ([false, false], false), ([false], false),
      ([false, true, false], true), ([false, false, false], false), ([false], false),
      ([false], false)] := by
  decide +kernel

theorem ofProg_flags :
    (PureContext.ofProg command.pure.program command.pure.funs).flags =
      command.pure.program.flags :=
  rfl

theorem allocationCost_zero : Bytes.allocationCost 0 = 0 := rfl

/-- `argScan` allocates nothing. -/
theorem argScan_charge (d : UInt64) (env : Env [Ty.bytes]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get FVar.here
      env = 0 := by
  cases env with
  | cons a rest =>
    cases rest
    exact (command.pureSources.argScan.bound_eq a).trans rfl

/-- `slice` allocates its result.  The charge lemmas whose value reads the arguments take any
environment and read it with `Var.ofIndex`, which `envGet` reduces: a lemma stated on a chain of
`Env.cons` does not match the chain that `Env.ofFn` builds, whose implicit types `simp` compares at
reducible transparency. -/
theorem slice_charge (d : UInt64) (env : Env [Ty.bytes, Ty.word, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      FVar.here.there.there env =
      Bytes.allocationCost (UInt64.toNat
        (env.get (Var.ofIndex (t := Ty.word) [Ty.bytes, Ty.word, Ty.word] 2 rfl))) := by
  cases env with
  | cons b rest =>
    cases rest with
    | cons start rest =>
      cases rest with
      | cons len rest =>
        cases rest
        exact (command.pureSources.slice.bound_eq b start len).trans rfl

/-- `finishWith` allocates the words of the bytes that it packs. -/
theorem finishWith_charge (d : UInt64) (k : Array UInt64) (h : words8Ty.denote)
    (b : LeanExe.Bytes) (start n len : UInt64) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      FVar.here.there.there.there
      (Env.cons k (Env.cons h (Env.cons b (Env.cons start (Env.cons n (Env.cons len Env.nil)))))) =
      blockCost ((n + 7) >>> 3).toNat := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := h
  exact ((command.pureSources.finishWith.bound_eq k ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ b start n
    len).trans (command.pureSources.pack.bound_eq b start n)).trans rfl

/-- `updateWith` allocates nothing. -/
theorem updateWith_charge (d : UInt64)
    (env : Env [Ty.array Elem.word, words8Ty, Ty.bytes, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      FVar.here.there.there.there.there.there.there env = 0 := by
  cases env with
  | cons k rest =>
    cases rest with
    | cons h rest =>
      cases rest with
      | cons b rest =>
        cases rest with
        | cons q rest =>
          cases rest
          obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ := h
          exact (command.pureSources.updateWith.bound_eq k ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ b
            q).trans rfl

/-- `hexMatches` allocates nothing. -/
theorem hexMatches_charge (d : UInt64) (env : Env [Ty.bytes, Ty.word, words4Ty]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      (FVar.here.there.there.there.there.there.there.there.there.there.there.there.there.there.there
        |>.there.there.there.there) env = 0 := by
  cases env with
  | cons m rest =>
    cases rest with
    | cons start rest =>
      cases rest with
      | cons digest rest =>
        cases rest
        obtain ⟨w0, w1, w2, w3⟩ := digest
        exact (command.pureSources.hexMatches.bound_eq m start ⟨w0, w1, w2, w3⟩).trans rfl

/-- The charge of a call of `render`. -/
theorem render_charge (d : UInt64) (env : Env [Ty.bytes, Ty.bool]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      (FVar.here.there.there.there.there.there.there.there.there.there.there.there.there.there.there
        |>.there.there) env =
      command.pureSources.render.bound
        (env.get (Var.ofIndex (t := Ty.bytes) [Ty.bytes, Ty.bool] 0 rfl),
          env.get (Var.ofIndex (t := Ty.bool) [Ty.bytes, Ty.bool] 1 rfl)) := by
  cases env with
  | cons name rest =>
    cases rest with
    | cons ok rest =>
      cases rest
      rfl

/-- The charge of a call of `parse`. -/
theorem parse_charge (d : UInt64) (env : Env [Ty.bytes]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds d).get
      (FVar.here.there.there.there.there.there.there.there.there.there.there.there.there.there.there
        |>.there.there.there.there.there.there) env =
      command.pureSources.parse.bound (env.get (Var.ofIndex (t := Ty.bytes) [Ty.bytes] 0 rfl)) := by
  cases env with
  | cons m rest =>
    cases rest
    rfl

/-- The reflected `argScan` is `argScan`. -/
theorem argScan_reflected (a : LeanExe.Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get FVar.here
      (Env.cons a Env.nil) = argScan a := by
  rw [← command.pureSources.argScan.denote_eq]
  rfl

/-- The reflected `slice` is `slice`. -/
theorem slice_reflected (b : LeanExe.Bytes) (start len : UInt64) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get FVar.here.there.there
      (Env.cons b (Env.cons start (Env.cons len Env.nil))) = slice b start len := by
  rw [← command.pureSources.slice.denote_eq]
  rfl

set_option maxHeartbeats 1000000 in
/-- The reflected `parse` is `parse`. -/
theorem parse_reflected (m : LeanExe.Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get
      (FVar.here.there.there.there.there.there.there.there.there.there.there.there.there.there.there
        |>.there.there.there.there.there.there) (Env.cons m Env.nil) = parse m := by
  rw [← command.pureSources.parse.denote_eq]
  rfl

theorem parseStep_cost_eq (m : LeanExe.Bytes) (st : Array UInt64) (i : UInt64) :
    command.pureSources.parseStep.cost (m, ⟨st⟩, i) = compiled.parseStep.cost (m, ⟨st⟩, i) := by
  rw [command.pureSources.parseStep.cost_eq, compiled.parseStep.cost_eq]

/-- The command's `parse` charges what the pure core's does, at most `176 n + 464` bytes for a
manifest of `n` bytes. -/
theorem parse_bound_command (m : LeanExe.Bytes) (hn : m.data.size < 2 ^ 32) :
    command.pureSources.parse.bound m ≤ 176 * m.data.size + 464 := by
  refine le_of_eq_of_le (command.pureSources.parse.bound_eq m) ?_
  refine le_of_eq_of_le ?_ (parse_bound m hn)
  rw [compiled.parse.bound_eq]
  simp only [parseStep_cost_eq]

/-- The output line of a name that `slice` copies with `len` bytes charges at most the block of
`len + 9` bytes. -/
theorem render_charge_le (b : LeanExe.Bytes) (start len : UInt64) (ok : Bool) :
    command.pureSources.render.bound (slice b start len, ok) ≤
      Bytes.allocationCost (len.toNat + 9) := by
  rw [command.pureSources.render.bound_eq]
  apply allocationCost_mono
  have hs : (slice b start len).size = len := by
    unfold slice LeanExe.Bytes.size
    rw [build_size, UInt64.ofNat_toNat]
  rw [hs, UInt64.toNat_add]
  have := Nat.mod_le (len.toNat + (if ok = true then (5 : UInt64) else 9).toNat) (2 ^ 64)
  cases ok <;> simp at this ⊢ <;> omega

/-- The last block of `finish` has at most eight words. -/
theorem finish_block_le (x : UInt64) : blockCost (((x &&& 63) + 7) >>> 3).toNat ≤ 120 := by
  have hx : (x &&& 63).toNat ≤ 63 := by
    rw [UInt64.toNat_and]
    exact Nat.and_le_right
  have hs : ((x &&& 63) + 7).toNat = (x &&& 63).toNat + 7 := by
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega
  rw [blockCost_eq, UInt64.toNat_shiftRight, hs]
  simp only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
  omega

/-! ## The values that the charges read -/

private theorem exec_pure_value {World α : Type} {host : Host World} {result value : α}
    {world final : World} {trace : List Event}
    (run : Exec host (.pure result) world trace (.returned value) final) : value = result :=
  Outcome.returned.inj (exec_pure_shape run).2.1

theorem ite_same {c : Prop} (decision : Decidable c) (a : Nat) : @ite Nat c decision a a = a := by
  cases decision <;> rfl

open Lean Meta Simp in
/-- Reads `if c then a else a` as `a` for any decision procedure of `c`.  `ite_self` does not apply
where a rewrite of the condition by `simp` kept the procedure of the condition before it, whose
type matches `Decidable c` only at the default transparency. -/
simproc_decl iteSame (@ite Nat _ _ _ _) := fun e => do
  let (``ite, #[_, c, decision, a, b]) := e.getAppFnArgs | return .continue
  unless a == b do return .continue
  return .done { expr := a, proof? := some (mkApp3 (mkConst ``ite_same) c decision a) }

/-- The reflector writes the test `C` of an `if` as `if C then true else !true`, and when that
value is false, `C` is false, for any decision procedure of `C = true`. -/
theorem cond_false {C : Bool} {decision : Decidable (C = true)}
    (h : @ite Bool (C = true) decision true (!true) = false) : C = false := by
  cases decision with
  | isTrue holds =>
    have contradiction : true = false := h
    exact absurd contradiction (by decide)
  | isFalse fails => simpa using fails

private theorem ite_cost {c : Prop} {decision : Decidable c} {cost branch total : Nat}
    (bound : cost + branch ≤ total) : cost + @ite Nat c decision branch branch ≤ total := by
  cases decision <;> exact bound

/-- What a run of a command with the outcome `outcome` gives about its parts: a `ret` returns the
value of its expression, a `sys` command ends as a run of its action, a `bind` that returns has a
first command that returns and a second command that returns the same value, an `ite` that returns
has a branch that returns the same value, and a call ends as a run of the call. -/
def ReturnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    (host : Host World) (pure : PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) :
    {context : List Ty} → {result : ResultTy} → Command pureSigs effectSigs context result →
      Env context → Outcome result.denote → Prop
  | _, _, .ret value, env, .returned returned => returned = value.denote pure.funs env
  | _, _, .sys operation form args inputs buffers, env, outcome => ∃ world trace final,
      Exec host (form.runWith operation (args.map env.get) (inputs.map env.get)
        (buffers.map env.get)) world trace outcome final
  | _, _, .bind (intermediate := intermediate) first next, env, outcome => ∀ returned,
      outcome = .returned returned → ∃ value,
        Returns host pure program depth modes (bindLive intermediate next live) first env value ∧
          Returns host pure program depth (bindModes intermediate modes)
            (shift intermediate.bindCount live) next (intermediate.bindEnv value env) returned
  | _, _, .ite _ yes no, env, outcome => ∀ returned, outcome = .returned returned →
      Returns host pure program depth modes live yes env returned ∨
        Returns host pure program depth modes live no env returned
  | _, _, .call callee args, env, outcome => ∃ world trace final spent fits,
      ResourceCall host pure program callee (depth + 1)
        (Env.ofFn fun i => (args i).denote pure.funs env) world trace outcome final spent fits
  | _, _, _, _, _ => True

theorem returnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {world final : World} {trace : List Event} {outcome : Outcome result.denote} {spent : Nat}
    {fits : Bool}
    (run : ResourceExec host pure program depth modes live command env world trace outcome final
      spent fits) :
    ReturnFact host pure program depth modes live command env outcome := by
  cases run with
  | ret => rfl
  | sys execution => exact ⟨_, _, _, execution⟩
  | bind_return firstRun nextRun =>
    intro _ same
    subst same
    exact ⟨_, ⟨_, _, _, _, _, firstRun⟩, ⟨_, _, _, _, _, nextRun⟩⟩
  | bind_exit => exact fun _ same => by cases same
  | bind_trap => exact fun _ same => by cases same
  | ite_yes _ execution =>
    intro _ same
    subst same
    exact .inl ⟨_, _, _, _, _, execution⟩
  | ite_no _ execution =>
    intro _ same
    subst same
    exact .inr ⟨_, _, _, _, _, execution⟩
  | call execution => exact ⟨_, _, _, _, _, execution⟩
  | _ => trivial

theorem returns_fact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {value : result.denote}
    (returns : Returns host pure program depth modes live command env value) :
    ReturnFact host pure program depth modes live command env (.returned value) := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact returnFact run

/-- A returned record of `fd_filestat_get` with errno 0 holds the size that a successful reply of
the host gave. -/
theorem stat_got {World : Type} {host : Host World} {values : List UInt64} {world final : World}
    {trace : List Event}
    {stat : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64}
    (run : Exec host ((SysForm.record 8).runWith Call.fdFilestatGet values [] []) world trace
      (.returned stat) final)
    (zero : stat.1 = 0) :
    ∃ world args outputs after, host.sys world Call.fdFilestatGet args (.returned 0 outputs) after ∧
      stat.2.2.2.2.2.1 = statSize outputs := by
  cases run with
  | sys_reject fits next =>
    rw [exec_pure_value next] at zero
    exact absurd zero fits
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
    rw [exec_pure_value next] at zero ⊢
    have hz : errno = 0 := by simpa [SysForm.value, wordsValue, sysReply] using zero
    subst hz
    refine ⟨_, _, _, _, permitted, ?_⟩
    simp only [sysReply_zero, SysForm.value, wordsValue, Verified.Wasi.recordWords, recordOf,
      Call.fdFilestatGet, List.map_cons, List.map_nil, List.headD, List.tail, statSize]

/-- The call of `fd_filestat_get` charges 120 bytes for the block of its record, 71 bytes. -/
theorem filestat_block (trace : List Event) :
    sysCost (.record 8) Call.fdFilestatGet trace = 120 := by
  simp only [sysCost]
  decide

/-- A descriptor that `fd_filestat_get` does not reject lies below `2^32`. -/
theorem filestat_fd {fd : UInt64} (fits : Call.fdFilestatGet.reject [.word fd] = 0) :
    fd.toNat < 2 ^ 32 := by
  by_contra large
  have h : ¬ fd.toNat < 4294967296 := large
  simp [Call.reject, rejectArgs, Call.fdFilestatGet, Param.takesArg, Param.reject, Arg.value, h]
    at fits

/-- A run of `readManifest` that returns status 0 returns the manifest's bytes, as many as the size
that a successful reply of `fd_filestat_get` reported. -/
theorem readManifest_size {World : Type} {host : Host World} {M : Nat}
    (statBound : ∀ world args outputs after,
      host.sys world Call.fdFilestatGet args (.returned 0 outputs) after →
        (statSize outputs).toNat ≤ M)
    {fd : UInt64} {buffer : LeanExe.Bytes} (hbuffer : buffer.data.size = 65536)
    {world final : World} {trace : List Event} {r : UInt64 × LeanExe.Bytes × LeanExe.Bytes}
    (run : Exec host (readManifest ⟨fd⟩ buffer) world trace (.returned r) final) (ok : r.1 = 0) :
    r.2.1.data.size ≤ M ∧ r.2.1.data.size < 2 ^ 32 := by
  unfold readManifest at run
  cases run with
  | sys_reject fits next =>
    beta_reduce at next
    simp only [Action.bind] at next
    split at next
    · rw [exec_pure_value next] at ok
      exact absurd ok fits
    · rename_i zero
      simp at zero
      exact absurd zero fits
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed fits permitted next =>
    beta_reduce at next
    simp only [Action.bind] at next
    split at next
    · rename_i nonzero
      rw [exec_pure_value next] at ok
      simp [sysReply] at nonzero ok
      exact absurd ok nonzero
    rename_i zero
    have hz : errno = 0 := by simpa [sysReply] using zero
    subst hz
    split at next
    · rw [exec_pure_value next] at ok
      exact absurd (show (61 : UInt64) = 0 from ok) (by decide)
    rename_i small
    have hsmall : (statSize committed).toNat < 2 ^ 32 := by
      have : ¬ 4294967296 ≤ statSize committed := small
      rw [UInt64.le_iff_toNat_le] at this
      simp only [UInt64.reduceToNat] at this
      omega
    obtain ⟨-, results⟩ := readBytes_run (filestat_fd fits) hsmall rfl hbuffer next
    obtain ⟨bytes, body, -, same, -⟩ := results r rfl
    obtain ⟨hbytes, hsmall'⟩ := same ok
    have hlen : bytes.length = (statSize committed).toNat := by
      generalize hs : r.1 = status at body ok
      cases body with
      | statFailed nonzero => exact absurd rfl nonzero
      | tooLarge => exact absurd ok (by decide)
      | stopped _ _ nonzero => exact absurd ok nonzero
      | probed _ reads => exact reads.full_length rfl
    have hsize : r.2.1.data.size = bytes.length := by rw [← hbytes]; simp
    exact ⟨by rw [hsize, hlen]; exact statBound _ _ _ _ permitted, by omega⟩

/-- A run of the reflected call of `readManifest` from `main` that returns is a run of
`readManifest` that returns the same value. -/
theorem readManifest_call_run {World : Type} {host : Host World} {depth : UInt64}
    {fd : UInt64} {buffer : LeanExe.Bytes} {world final : World} {trace : List Event}
    {spent : Nat} {fits : Bool} {got : UInt64 × LeanExe.Bytes × LeanExe.Bytes}
    (run : ResourceCall host (.ofProg command.pure.program command.pure.funs)
      (.cons command.checkLines.func (.cons command.writeAll.func (.cons command.hashFile.func
        (.cons command.readManifest.func (.cons command.readBytes.func .nil)))))
      (.there (.there (.there .here))) depth
      (.cons Library.Hashing.Sha256.roundConstants (.cons fd (.cons buffer .nil)))
      world trace (.returned got) final spent fits) :
    Exec host (readManifest ⟨fd⟩ buffer) world trace (.returned got) final := by
  have exec := ResourceCall.erase run
  simp only [EffectProg.funs] at exec
  obtain ⟨result, nativeRun, related⟩ := (command.readManifest.related ⟨fd⟩ buffer).exec_back exec
  cases related with
  | returned same =>
    subst same
    exact nativeRun

/-- The program's test of the argument buffer accepts it only when the argument that names the
manifest has at most the buffer's bytes. -/
theorem name_size_le (a : LeanExe.Bytes) (h : a.data.size < 2 ^ 32)
    (accepted : ((argScan a).1 != 2 || a.get (a.size - 1) != 0) = false) :
    (a.size - (argScan a).2.1 - 2).toNat ≤ a.data.size := by
  obtain ⟨program, hl, -, -⟩ := (argument_cases a h).2 accepted
  have hlen := congrArg List.length hl
  have hs : (slice a ((argScan a).2.1 + 1) (a.size - (argScan a).2.1 - 2)).data.size =
      (a.size - (argScan a).2.1 - 2).toNat :=
    build_size _ _
  simp only [List.length_append, List.length_cons, List.length_nil, toList_length] at hlen
  omega

/-! ## The lines -/

theorem linesFrom_total (s : Nat) : ∀ ps : List (List UInt8),
    ((linesFrom s ps).map fun l => l.2.length + 1).sum ≤ (ps.map fun p => p.length + 1).sum
  | [] => by simp [linesFrom]
  | p :: ps => by
    have := linesFrom_total (s + p.length + 1) ps
    simp only [linesFrom, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    split
    · simp only [List.map_nil, List.sum_nil]
      omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

theorem pieces_total : ∀ ps : List (List UInt8),
    (ps.map fun p => p.length + 1).sum ≤ ([10].intercalate ps).length + 1
  | [] => by simp
  | [p] => by simp
  | p :: q :: qs => by
    have := pieces_total (q :: qs)
    rw [List.intercalate_cons_cons]
    simp only [List.map_cons, List.sum_cons, List.length_append, List.length_cons] at this ⊢
    omega

/-- The lines of a byte string, with one byte each, have at most one byte more than the string:
they are disjoint pieces of it, each followed by a newline or by its end. -/
theorem lines_total (m : List UInt8) :
    ((lines m).map fun l => l.2.length + 1).sum ≤ m.length + 1 := by
  have h1 := linesFrom_total 0 (m.splitOn 10)
  have h2 := pieces_total (m.splitOn 10)
  rw [List.intercalate_splitOn] at h2
  unfold lines
  omega

theorem sum_map_four {α : Type} (f : α → Nat) :
    ∀ ls : List α, (ls.map fun l => 4 * f l).sum = 4 * (ls.map f).sum
  | [] => rfl
  | l :: ls => by
    simp only [List.map_cons, List.sum_cons, sum_map_four f ls]
    omega

/-- The sum of `charge` over `remaining` indices from `index`. -/
def passSum (charge : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | index, remaining + 1 => charge index + passSum charge (index + 1) remaining

theorem passSum_le {α : Type} (charge : Nat → Nat) (g : α → Nat) :
    ∀ (ls : List α) (index : Nat), (∀ j (hj : j < ls.length), charge (index + j) ≤ g ls[j]) →
      passSum charge index ls.length ≤ (ls.map g).sum
  | [], _, _ => by simp [passSum]
  | l :: ls, index, h => by
    have h0 := h 0 (by simp)
    have ih := passSum_le charge g ls (index + 1) fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show index + (j + 1) = index + 1 + j by omega, List.getElem_cons_succ] at this
    simp only [List.length_cons, passSum, List.map_cons, List.sum_cons]
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    omega

/-- The length of the name of the line of pass `j` of `checkLines` with the positions
`entries`. -/
def lineLen (entries : Array UInt64) (j : Nat) : UInt64 :=
  entries[(2 * UInt64.ofNat j + 1).toNat]! - entries[(2 * UInt64.ofNat j).toNat]! - 66

/-- The charge of pass `j` of `checkLines` with the positions `entries`: the copy of the name, the
output line, and the call of `hashFile`. -/
def lineCharge (entries : Array UInt64) (j : Nat) : Nat :=
  Bytes.allocationCost (lineLen entries j).toNat +
    Bytes.allocationCost ((lineLen entries j).toNat + 9) + 120

/-- The passes of `checkLines` on a manifest of `n` bytes charge at most `4 (n + 1)` bytes. -/
theorem lines_charge_le (m : LeanExe.Bytes) (hm : m.data.size < 2 ^ 32) :
    passSum (lineCharge (parse m)) 0 ((parse m).size.toUInt64 >>> 1).toNat ≤
      4 * (m.data.size + 1) := by
  have hlsmall := lines_length m.data.data.toList
  have hlenm : m.data.data.toList.length = m.data.size := by simp
  by_cases accepted : lines m.data.data.toList ≠ [] ∧
      ∀ l ∈ lines m.data.data.toList, WellFormed l.2
  · have hparse := parse_accepted m hm accepted
    have hcount : ((parse m).size.toUInt64 >>> 1).toNat = (lines m.data.data.toList).length := by
      rw [hparse, List.size_toArray, spanWords_length]
      show (UInt64.ofNat (2 * (lines m.data.data.toList).length) >>> 1).toNat = _
      rw [UInt64.toNat_shiftRight, toNat_ofNat (by omega)]
      simp [Nat.shiftRight_eq_div_pow]
    have htotal := lines_total m.data.data.toList
    rw [hcount, hparse]
    generalize hls : lines m.data.data.toList = ls at accepted hlsmall htotal
    have hsum : passSum (lineCharge (spanWords ls).toArray) 0 ls.length ≤
        (ls.map fun l => 4 * (l.2.length + 1)).sum := by
      refine passSum_le _ _ ls 0 fun j hj => ?_
      rw [Nat.zero_add]
      have hmem : ls[j] ∈ ls := List.getElem_mem hj
      have hpos := lines_pos m.data.data.toList ls[j] (by rw [hls]; exact hmem)
      have hwell := (accepted.2 _ hmem).1
      obtain ⟨hstart, hstop⟩ := entry_get ls j hj (by omega)
      have hlen : (lineLen (spanWords ls).toArray j).toNat = ls[j].2.length - 66 := by
        unfold lineLen
        rw [hstart, hstop]
        have ha : (UInt64.ofNat ls[j].1).toNat = ls[j].1 := toNat_ofNat (by omega)
        have hb : (UInt64.ofNat (ls[j].1 + ls[j].2.length)).toNat = ls[j].1 + ls[j].2.length :=
          toNat_ofNat (by omega)
        rw [UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le, ha, hb]; omega), ha, hb]
            simp only [UInt64.reduceToNat]
            omega),
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, ha, hb]; omega), ha, hb]
        simp only [UInt64.reduceToNat]
        omega
      unfold lineCharge
      rw [hlen]
      have h1 := allocationCost_le (ls[j].2.length - 66)
      have h2 := allocationCost_le (ls[j].2.length - 66 + 9)
      omega
    have hmap := sum_map_four (fun l : Nat × List UInt8 => l.2.length + 1) ls
    omega
  · rw [parse_refused m hm accepted]
    simp [passSum]

/-! ## Loops whose passes charge by their index -/

section Loop

variable {World : Type} {host : Host World} {pureSigs : List Sig} {effectSigs : List EffectSig}
  {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
  {modes : List Mode} {live : Nat → Bool} {context : List Ty} {type : Ty}
  {test : Expr pureSigs (type :: .word :: context) .bool}
  {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
  {env : Env context}

/-- A loop whose test charges at most `t` and whose step at pass `index` is bounded by
`charge index` from every state of the invariant `held`, which every returned step keeps, charges
at most the sum of `charge` over its passes and `t` for each test. -/
theorem loop_bounded_sum (held : type.denote → Prop) {t : Nat} (charge : Nat → Nat)
    (testCost : ∀ index state, held state →
      pure.loopTestCost depth modes live test step env index state ≤ t)
    (testFits : ∀ index state, held state → pure.loopTestFits depth test env index state = true)
    (stepBounded : ∀ index state, held state →
      Bounded host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) (charge index))
    (kept : ∀ index state next, held state →
      Returns host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) next → held next) :
    ∀ remaining index state, held state →
      LoopBounded host pure program depth modes live test step env remaining index state
        (passSum charge index remaining + (remaining + 1) * t) := by
  intro remaining
  induction remaining with
  | zero =>
    intro index state _
    refine ⟨fun _ _ _ _ _ _ run => ?_, fun _ _ _ _ _ _ progress => ?_⟩
    · cases run
      exact ⟨Nat.zero_le _, rfl⟩
    · cases progress with
      | refl => exact ⟨Nat.zero_le _, rfl⟩
      | returned execution =>
        cases execution
        exact ⟨Nat.zero_le _, rfl⟩
  | succ remaining ih =>
    intro index state current
    have more : passSum charge index (remaining + 1) + (remaining + 1 + 1) * t =
        passSum charge (index + 1) remaining + (remaining + 1) * t + (t + charge index) := by
      simp only [passSum]
      rw [Nat.succ_mul]
      omega
    have cost := testCost index state current
    have valid := testFits index state current
    have exec : ∀ world trace outcome final spent fits,
        ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index
          state world trace outcome final spent fits →
        spent ≤ passSum charge index (remaining + 1) + (remaining + 1 + 1) * t ∧ fits = true := by
      intro _ _ _ _ _ _ run
      rw [more]
      cases run with
      | stop chosen => exact ⟨by omega, valid⟩
      | next chosen stepRun restRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
          (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).1 _ _ _ _ _ _ restRun
        rw [valid, stepFits, restFits]
        exact ⟨by omega, rfl⟩
      | exit chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
      | trap chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
    refine ⟨exec, fun _ _ _ _ _ _ progress => ?_⟩
    cases progress with
    | refl => exact ⟨Nat.zero_le _, rfl⟩
    | test_charge => exact ⟨by rw [more]; omega, valid⟩
    | returned execution => exact exec _ _ _ _ _ _ execution
    | step chosen progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, more]
      exact ⟨by omega, rfl⟩
    | next chosen stepRun progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
        (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, restFits, more]
      exact ⟨by omega, rfl⟩

end Loop

/-! ## The charges of the effect functions -/

/-- Proves a bound on the charge of an expression: evaluates its liveness tests, reads its
variables, and leaves the copies to `omega`. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.loopTestCost, PureContext.argumentCost, Expr.allocs,
      Var.cost, Var.ownedCost, Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost,
      Verified.Examples.WasiSys.envGet, Expr.denote, Args.get_cons_zero', Args.get_cons_zero,
      Args.get_cons_succ, Env.ofFn, argsSum, callCredits, ResultTy.bindEnv, loopEnv, loopModes,
      letPairEnv, letPairModes, modeAt, sysTakeLive, List.get_cons_zero, List.get_cons_succ',
      Flags.params, Flags.result, ofProg_flags, flags_toList, FVar.index, argScan_charge,
      slice_charge, updateWith_charge, hexMatches_charge, render_charge, parse_charge, allocCost,
      Elem.width, sumBelow_const, BinOp.apply, Path.get, allocationCost_zero, iteSame,
      UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, Nat.mul_zero, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves the frames of an expression that calls no function that takes the call depth. -/
local macro "fits" : tactic => `(tactic|
  (refine Expr.fits_of_depthCalls _ _ _ ?_ _
   decide))

/-- Proves `Bounded` of a `ret`.  The charge and the frames are goals of their own, rather than
`by` blocks inside a term, so that a charge that `charge` does not prove fails the tactic instead of
being logged and closed with `sorry` by the term's elaboration. -/
local macro "ret_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule ?_ ?_
   · charge
   · fits))

/-- Proves `Bounded` of a `write`, which charges nothing. -/
local macro "write_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule))

/-- Reduces `Bounded` of a `bind` to its parts with the budgets `first` and `next`. -/
local macro "bind_bound " first:term:max next:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $first $next ?_ ?_ ?_
   · omega))

/-- Proves `Bounded` of a `sys` command whose call charges nothing and whose take moves its
buffer or has none. -/
local macro "sys_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule ?_ ?_ <;>
     (intro _ _ _ _ _
      simp only [sysCost, PureContext.sysTakeCost]
      charge)))

/-- Reduces `Bounded` of a `bind` whose first command is a `ret` that charges nothing to its second
command with the budget `next`. -/
local macro "ret_first " next:term:max : tactic => `(tactic|
  (bind_bound 0 $next
   · ret_bound
   intro _ _))

/-- Reduces `Bounded` of an `ite` to its branches with the budget `branch` for each. -/
local macro "ite_bound " branch:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $branch $branch (ite_cost ?_) ?_ (fun _ => ?_) (fun _ => ?_)
   · charge
   · fits))

/-- Reduces `Bounded` of a `letPair` that charges nothing before its body to its body. -/
local macro "pair_free" : tactic => `(tactic|
  (refine Bounded.letPair_free ?_ ?_
   · first
     | exact letPairCost_borrowed rfl
     | exact letPairCost_dead rfl
     | fail "the pair stays live"))

/-- Proves `Bounded` with the budget 0 of a command of `bind`s, `letPair`s, `ite`s, `ret`s, and
`sys` commands that charge nothing, and leaves the commands that charge more.  The last alternative
`fail` keeps the error recovery of `first` from closing such a command with `sorry`. -/
local macro "free_bound" : tactic => `(tactic|
  (repeat (first
    | bind_bound 0 0
    | pair_free
    | ite_bound 0
    | (intro _ _)
    | ret_bound
    | sys_bound
    | fail "no rule applies")))

/-- `readBytes` charges the manifest's buffer of `size` bytes: its read passes take the buffer of
the loop's state and the last read takes the read buffer, each of which dies at the read. -/
theorem readBytes_bounded {World : Type} {host : Host World} {depth : UInt64}
    (table : Array UInt64) (file size : UInt64) (buffer : LeanExe.Bytes) :
    Bounded host (.ofProg command.pure.program command.pure.funs) .nil depth
      (entryModes command.readBytes.func.params command.readBytes.func.modes) (fun _ => false)
      command.readBytes.func.body (.cons table (.cons file (.cons size (.cons buffer .nil))))
      (Bytes.allocationCost size.toNat) := by
  bind_bound (Bytes.allocationCost size.toNat) 0
  · apply bounded_of_rule
    intro _ _ rule
    refine rule 0 (by charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded (type := bufferTy) (t := 0) (s := 0)
      (fun _ => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
    · intro index state _
      charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state _
      free_bound
    · intro _ _ _ _ _
      trivial
    · simp
  intro _ _
  free_bound

/-- `hashFile` charges the last block of `finish`: its read passes take the read buffer of the
loop's state, which dies at the read, and `update` allocates nothing. -/
theorem hashFile_bounded {World : Type} {host : Host World} {depth : UInt64}
    (env : Env [Ty.array Elem.word, Ty.word, Ty.bytes]) :
    Bounded host (.ofProg command.pure.program command.pure.funs)
      (.cons command.readManifest.func (.cons command.readBytes.func .nil)) depth
      (entryModes command.hashFile.func.params command.hashFile.func.modes) (fun _ => false)
      command.hashFile.func.body env 120 := by
  bind_bound 0 120
  · apply bounded_of_rule
    intro _ _ rule
    refine rule 0 (by charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded (type := hashTy) (t := 0) (s := 0)
      (fun _ => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
    · intro index state _
      charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state _
      free_bound
    · intro _ _ _ _ _
      trivial
    · simp
  intro _ _
  free_bound
  apply bounded_of_rule
  intro _ _ rule
  refine rule ?_ (by fits)
  simp +decide only [PureContext.ownedCost, PureContext.exprCost, Expr.allocs, Var.cost,
    Var.ownedCost, Expr.ownedCost, coerceCost, Ty.copyCost, Verified.Examples.WasiSys.envGet,
    Expr.denote, Args.get_cons_zero', Args.get_cons_zero, Args.get_cons_succ, Env.ofFn, argsSum,
    callCredits, Flags.params, ofProg_flags, flags_toList, FVar.index, ResultTy.bindEnv, letPairEnv,
    letPairModes, modeAt, finishWith_charge, updateWith_charge, BinOp.apply, List.get_cons_zero,
    List.get_cons_succ', Nat.add_zero, Nat.zero_add, ↓reduceIte]
  exact finish_block_le _

/-- `writeAll` charges nothing: it computes the window of its buffer in words, and each of its
passes binds the window of the bytes that remain and writes it from the borrowed buffer. -/
theorem writeAll_bounded {World : Type} {host : Host World} {depth : UInt64}
    (env : Env [Ty.array Elem.word, Ty.bytes, Ty.word, Ty.word]) :
    Bounded host (.ofProg command.pure.program command.pure.funs)
      (.cons command.hashFile.func (.cons command.readManifest.func
        (.cons command.readBytes.func .nil))) depth
      (entryModes command.writeAll.func.params command.writeAll.func.modes) (fun _ => false)
      command.writeAll.func.body env 0 := by
  bind_bound 0 0
  · ret_bound
  intro _ _
  bind_bound 0 0
  · ret_bound
  intro _ _
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 (by charge) ?_ ?_
  · simp only [PureContext.loopInitFits, Bool.and_eq_true]
    exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
      Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
  refine LoopBounded.mono (loop_bounded (type := .word) (t := 0) (s := 0)
    (fun _ : UInt64 => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
  · intro index written _
    charge
  · intro index written _
    exact Expr.fits_of_depthCalls _ _ _ (by decide) _
  · intro index written _
    bind_bound 0 0
    · bind_bound 0 0
      · ret_bound
      · intro _ _
        bind_bound 0 0
        · ret_bound
        · intro _ _
          write_bound
    · intro _ _
      ite_bound 0
      · ret_bound
      · ret_bound
  · intro _ _ _ _ _
    trivial
  · simp

/-- `readManifest` charges the record block of `fd_filestat_get`, 120 bytes, and the call of
`readBytes` on a size that a successful reply reported, at most `M` bytes. -/
theorem readManifest_bounded {World : Type} {host : Host World} {M : Nat}
    (statBound : ∀ world args outputs after,
      host.sys world Call.fdFilestatGet args (.returned 0 outputs) after →
        (statSize outputs).toNat ≤ M)
    (env : Env [Ty.array Elem.word, Ty.word, Ty.bytes]) :
    Bounded host (.ofProg command.pure.program command.pure.funs)
      (.cons command.readBytes.func .nil) 1
      (entryModes command.readManifest.func.params command.readManifest.func.modes)
      (fun _ => false) command.readManifest.func.body env (120 + Bytes.allocationCost M) := by
  apply bounded_of_rule
  intro _ _ rule
  refine rule 120 (Bytes.allocationCost M) (by omega) ?_ ?_
  · apply bounded_of_rule
    intro _ _ rule
    exact rule (fun _ _ _ _ _ => by rw [filestat_block]; simp only [PureContext.sysTakeCost]; omega)
      (fun _ _ _ _ _ => by rw [filestat_block]; simp only [PureContext.sysTakeCost]; omega)
  intro stat returned
  obtain ⟨_, _, _, statRun⟩ := returns_fact returned
  apply bounded_of_rule
  intro _ _ rule
  refine rule (Bytes.allocationCost M) (Bytes.allocationCost M) (ite_cost (by charge)) (by fits)
    (fun _ => ?_) (fun zero => ?_)
  · ret_bound
  apply bounded_of_rule
  intro _ _ rule
  refine rule (Bytes.allocationCost M) (Bytes.allocationCost M) (ite_cost (by charge)) (by fits)
    (fun _ => ?_) (fun _ => ?_)
  · ret_bound
  apply bounded_of_rule
  intro _ _ rule
  refine rule (Bytes.allocationCost M) (by charge) rfl
    (callBounded_here (by decide) (Bounded.mono (readBytes_bounded _ _ _ _) ?_))
  apply allocationCost_mono
  simp only [Expr.denote, CmpOp.apply, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv]
    at zero
  obtain ⟨_, _, _, _, permitted, size⟩ := stat_got statRun (by simpa [Path.get] using zero)
  have hle := statBound _ _ _ _ permitted
  rw [← size] at hle
  exact hle

set_option maxHeartbeats 4000000 in
/-- `checkLines` charges, for each line, the copy of its name, its output line, and the call of
`hashFile`: at most `checkBudget n` for a manifest of `n` bytes and the positions that `parse`
gives. -/
theorem checkLines_bounded {World : Type} {host : Host World} (table : Array UInt64)
    (m : LeanExe.Bytes) (entries : Array UInt64) (buffer : LeanExe.Bytes)
    (hm : m.data.size < 2 ^ 32) (hentries : entries = parse m) :
    Bounded host (.ofProg command.pure.program command.pure.funs)
      (.cons command.writeAll.func (.cons command.hashFile.func (.cons command.readManifest.func
        (.cons command.readBytes.func .nil)))) 1
      (entryModes command.checkLines.func.params command.checkLines.func.modes) (fun _ => false)
      command.checkLines.func.body (.cons table (.cons m (.cons entries (.cons buffer .nil))))
      (checkBudget m.data.size) := by
  subst hentries
  unfold checkBudget
  bind_bound (4 * (m.data.size + 1)) 0
  · apply bounded_of_rule
    intro _ _ rule
    refine rule (4 * (m.data.size + 1)) (by charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded_sum (type := bufferTy) (t := 0) (fun _ => True)
      (lineCharge (parse m)) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
    · intro index state _
      charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state _
      obtain ⟨buf, failed, stalled⟩ := state
      letPair_free
      apply bounded_of_rule
      intro _ _ rule
      refine rule 0 (lineCharge (parse m) index) (by omega) ?_ ?_
      · ret_bound
      intro (start : UInt64) returnedStart
      apply bounded_of_rule
      intro _ _ rule
      refine rule 0 (lineCharge (parse m) index) (by omega) ?_ ?_
      · ret_bound
      intro (stop : UInt64) returnedStop
      have hstart := returns_fact returnedStart
      have hstop := returns_fact returnedStop
      simp only [ReturnFact, Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv,
        letPairEnv, loopEnv, BinOp.apply] at hstart hstop
      have hlen : lineLen (parse m) index = stop - start - 66 := by
        rw [hstart, hstop]
        rfl
      unfold lineCharge
      rw [hlen]
      bind_bound (Bytes.allocationCost (stop - start - 66).toNat)
        (Bytes.allocationCost ((stop - start - 66).toNat + 9) + 120)
      · ret_bound
      intro (name : LeanExe.Bytes) returnedName
      have hname := returns_fact returnedName
      simp only [ReturnFact, Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv,
        BinOp.apply, Env.ofFn, Args.get_cons_zero, Args.get_cons_succ] at hname
      replace hname := hname.trans (slice_reflected m (start + 66) (stop - start - 66))
      subst hname
      bind_bound 120 (Bytes.allocationCost ((stop - start - 66).toNat + 9))
      · ret_first 120
        ret_first 120
        ret_first 120
        ret_first 120
        ret_first 120
        ret_first 120
        apply bounded_of_rule
        intro _ _ rule
        refine rule 0 120 (by omega) ?_ ?_
        · sys_bound
        intro _ _
        ite_bound 120
        · bind_bound 120 0
          · ret_bound
          · intro _ _
            ret_bound
        · ret_first 120
          apply bounded_of_rule
          intro _ _ rule
          refine rule 120 0 (by omega) ?_ ?_
          · apply bounded_of_rule
            intro _ _ rule
            exact rule 120 (by charge) rfl
              (callBounded_there (callBounded_here (by decide) (hashFile_bounded _)))
          · intro _ _
            free_bound
      intro checked _
      obtain ⟨⟨digest, ending, buf'⟩, closeErrno⟩ := checked
      letPair_free
      ret_first (Bytes.allocationCost ((stop - start - 66).toNat + 9))
      rename_i ok _
      bind_bound (Bytes.allocationCost ((stop - start - 66).toNat + 9)) 0
      · have hrender := render_charge_le m (start + 66) (stop - start - 66) ok
        ret_bound
      intro _ _
      bind_bound 0 0
      · apply bounded_of_rule
        intro _ _ rule
        exact rule 0 (by charge) rfl (callBounded_here (by decide) (writeAll_bounded _))
      intro _ _
      ret_bound
    · intro _ _ _ _ _
      trivial
    · simp only [Expr.denote, Verified.Examples.WasiSys.envGet, BinOp.apply, Nat.mul_zero,
        Nat.add_zero]
      exact lines_charge_le m hm
  intro _ _
  free_bound

/-- Every run and every prefix of `main`'s body charges at most `budget M` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes and whose successful
`fd_filestat_get` replies report a size of at most `M` bytes. -/
theorem body_bounded {World : Type} {host : Host World} {M : Nat}
    (argsBound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit)
    (statBound : ∀ world args outputs after,
      host.sys world Call.fdFilestatGet args (.returned 0 outputs) after →
        (statSize outputs).toNat ≤ M) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs)
      (.cons command.checkLines.func (.cons command.writeAll.func (.cons command.hashFile.func
        (.cons command.readManifest.func (.cons command.readBytes.func .nil))))) 0
      (entryModes command.main.func.params command.main.func.modes) (fun _ => false)
      command.main.func.body mainArgs (budget M) := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    (inputs := []) (buffers := []) argsBound (Nat.le_refl (Bytes.allocationCost argsLimit))
  have observedArgs : ∀ world outputs after, (observedHost host).sys world
      Call.argsGet.reporterCall [] (.returned 0 outputs) after → reportedSize outputs ≤ argsLimit :=
    fun _ _ _ permitted => argsBound _ _ _ permitted.1
  have observedStat : ∀ world args outputs after, (observedHost host).sys world
      Call.fdFilestatGet args (.returned 0 outputs) after → (statSize outputs).toNat ≤ M :=
    fun _ _ _ _ permitted => statBound _ _ _ _ permitted.1
  unfold budget checkBudget
  generalize hA : Bytes.allocationCost argsLimit = A at reported ⊢
  generalize hB : Bytes.allocationCost M = B
  bind_bound A (A + 65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1))
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  obtain ⟨_, _, _, argsRun⟩ := returns_fact returned
  obtain ⟨errno, count, size, bytes⟩ := arguments
  have hbytes : bytes.data.size ≤ argsLimit :=
    Verified.Examples.WasiSys.args_bytes_le observedArgs argsRun
  letPair_free
  ite_bound (A + 65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1))
  · ret_bound
  bind_bound 0 (A + 65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1))
  · ret_bound
  intro (scan : UInt64 × UInt64 × UInt64) returnedScan
  have hscan := returns_fact returnedScan
  simp only [ReturnFact, Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv,
    letPairEnv, Env.ofFn, Args.get_cons_zero] at hscan
  replace hscan := hscan.trans (argScan_reflected bytes)
  subst hscan
  apply bounded_of_rule
  intro _ _ rule
  refine rule (A + 65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1))
    (A + 65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1)) (ite_cost (by charge)) (by fits)
    (fun _ => ?_) (fun accepted => ?_)
  · ret_bound
  have haccept : ((argScan bytes).1 != 2 || bytes.get (bytes.size - 1) != 0) = false := by
    simp only [Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv, letPairEnv,
      CmpOp.apply, BinOp.apply, Path.get] at accepted
    exact cond_false accepted
  have hcopy := allocationCost_mono
    ((name_size_le bytes (by unfold argsLimit at hbytes; omega) haccept).trans hbytes)
  rw [hA] at hcopy
  bind_bound A (65584 + (120 + B) + (176 * M + 464) + 4 * (M + 1))
  · ret_bound
  intro _ _
  bind_bound 65584 ((120 + B) + (176 * M + 464) + 4 * (M + 1))
  · ret_bound
  intro (buffer : LeanExe.Bytes) returnedBuffer
  have hbuffer : buffer.data.size = 65536 := by
    have h := returns_fact returnedBuffer
    simp only [ReturnFact, Expr.denote] at h
    rw [h, build_size]
    rfl
  bind_bound (120 + B) ((176 * M + 464) + 4 * (M + 1))
  · ret_first (120 + B)
    ret_first (120 + B)
    ret_first (120 + B)
    ret_first (120 + B)
    ret_first (120 + B)
    ret_first (120 + B)
    apply bounded_of_rule
    intro _ _ rule
    refine rule 0 (120 + B) (by omega) ?_ ?_
    · sys_bound
    intro _ _
    ite_bound (120 + B)
    · bind_bound (120 + B) 0
      · ret_bound
      · intro _ _
        ret_bound
    · ret_first (120 + B)
      apply bounded_of_rule
      intro _ _ rule
      refine rule (120 + B) 0 (by omega) ?_ ?_
      · apply bounded_of_rule
        intro _ _ rule
        refine rule (120 + B) (by charge) rfl ?_
        rw [← hB]
        exact callBounded_there (callBounded_there (callBounded_there
          (callBounded_here (by decide) (readManifest_bounded observedStat _))))
      · intro _ _
        free_bound
  intro (gotPair : (UInt64 × LeanExe.Bytes × LeanExe.Bytes) × UInt64)
    returnedBracket
  have hsize : gotPair.1.1 = 0 →
      gotPair.1.2.1.data.size ≤ M ∧ gotPair.1.2.1.data.size < 2 ^ 32 := by
    obtain ⟨_, -, r1⟩ := returns_fact returnedBracket _ rfl
    obtain ⟨_, -, r2⟩ := returns_fact r1 _ rfl
    obtain ⟨_, -, r3⟩ := returns_fact r2 _ rfl
    obtain ⟨_, -, r4⟩ := returns_fact r3 _ rfl
    obtain ⟨_, -, r5⟩ := returns_fact r4 _ rfl
    obtain ⟨_, -, r6⟩ := returns_fact r5 _ rfl
    obtain ⟨_, -, r7⟩ := returns_fact r6 _ rfl
    rcases returns_fact r7 _ rfl with r8 | r8
    · obtain ⟨failed, hfailed, r9⟩ := returns_fact r8 _ rfl
      have e1 := returns_fact hfailed
      have e2 := returns_fact r9
      simp only [ReturnFact, Expr.denote] at e1 e2
      have hempty : gotPair.1.2.1.data.size = 0 := by
        rw [e2]
        subst e1
        exact build_size 0 fun _ => 0
      intro _
      omega
    · obtain ⟨handle, -, r9⟩ := returns_fact r8 _ rfl
      obtain ⟨got, hgot, r10⟩ := returns_fact r9 _ rfl
      obtain ⟨closeErrno, -, r11⟩ := returns_fact r10 _ rfl
      have e := returns_fact r11
      simp only [ReturnFact, Expr.denote] at e
      obtain ⟨_, _, _, _, _, callRun⟩ := returns_fact hgot
      have nativeRun := readManifest_call_run callRun
      rw [e]
      exact readManifest_size observedStat hbuffer nativeRun
  obtain ⟨⟨status, mbytes, rbuf⟩, closeErrno⟩ := gotPair
  replace hsize : status = 0 → mbytes.data.size ≤ M ∧ mbytes.data.size < 2 ^ 32 := hsize
  letPair_free
  apply bounded_of_rule
  intro _ _ rule
  refine rule ((176 * M + 464) + 4 * (M + 1)) ((176 * M + 464) + 4 * (M + 1))
    (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun ok => ?_)
  · ret_bound
  have hstatus : status = 0 := by
    simp only [Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv, letPairEnv,
      CmpOp.apply] at ok
    simpa using cond_false ok
  obtain ⟨hm, hm32⟩ := hsize hstatus
  ite_bound ((176 * M + 464) + 4 * (M + 1))
  · ret_bound
  have hparse := parse_bound_command mbytes hm32
  bind_bound (176 * M + 464) (4 * (M + 1))
  · ret_bound
  intro (entries : Array UInt64) returnedEntries
  have hentries := returns_fact returnedEntries
  simp only [ReturnFact, Expr.denote, Verified.Examples.WasiSys.envGet, ResultTy.bindEnv,
    letPairEnv, Env.ofFn, Args.get_cons_zero] at hentries
  replace hentries := hentries.trans (parse_reflected mbytes)
  ite_bound (4 * (M + 1))
  · ret_bound
  apply bounded_of_rule
  intro _ _ rule
  exact rule (4 * (M + 1)) (by charge) rfl (callBounded_here (by decide)
    (Bounded.mono (checkLines_bounded Library.Hashing.Sha256.roundConstants mbytes entries rbuf
      hm32 hentries) (by unfold checkBudget; omega)))

/-- The budget premise of `total_meets` from `body_bounded`. -/
theorem prefix_bound {World : Type} {host : Host World} {M : Nat}
    (argsBound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit)
    (statBound : ∀ world args outputs after,
      host.sys world Call.fdFilestatGet args (.returned 0 outputs) after →
        (statSize outputs).toNat ≤ M)
    (world : Observed World) :
    Resource.CallPrefixBound (observedHost host) (.ofProg command.pure.program command.pure.funs)
      command.program .here 0 mainArgs world (budget M) := by
  intro trace residual final spent fits progress
  exact Resource.call_prefix_rule (budget M) progress rfl
    ((body_bounded argsBound statBound).2 world)

/-- `total_meets` with its budget premise given by the host's replies: every successful
`args_sizes_get` reply asks for at most `argsLimit` bytes, and every successful `fd_filestat_get`
reply reports a size of at most `M` bytes, for a budget `budget M` that fits the free memory of the
command's initial store. -/
theorem total_meets_budget {World : Type} {host : Host World} (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls))
    {M : Nat}
    (argsBound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit)
    (statBound : ∀ world args outputs after,
      host.sys world Call.fdFilestatGet args (.returned 0 outputs) after →
        (statSize outputs).toNat ≤ M)
    (room : (Verified.initialStaticHeap command.literalPool).Within
      (PureTransport.erase (initialStore world)) command.pure.module (budget M))
    (safe : host.NoTrapsAlong (main.bind fun status => Action.exit (α := Unit) status)
      world.world) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final code events,
      run fuel command.module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        host.exited final.host.world = some code ∧ final.host.events = world.events ++ events ++
          [.exit code] ∧ code.toNat ≤ 77 ∧ Meets host world.world events code :=
  total_meets world targetHost valid room (prefix_bound argsBound statBound world) safe

#print axioms body_bounded
#print axioms prefix_bound
#print axioms total_meets_budget

end Demos.ManifestCheck
