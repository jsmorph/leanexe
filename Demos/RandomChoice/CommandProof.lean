import Demos.RandomChoice.Command
import Demos.RandomChoice.CommandSpec
import Demos.RandomChoice.PicksProof
import Demos.RandomChoice.Unbiased
import Demos.RandomHistogram.CommandProof

/-! Every run of the command's `main` followed by its exit, under every host, that ends with an
exit status meets the request (`exec_main`): its events are those of `Meets` followed by the exit.

The proof follows `main`.  A returned `args` result has a buffer of fewer than `2^32` bytes, so
`parseArg` computes `parseSpec` on it.  A call of `random_get` that returns errno 0 fills the whole
draw buffer with the reply's 4,096 bytes (`splice_whole`), so `putPicks` writes the lines of the
picks of the reply's accepted words, at most the values that remain, which `pass_put` derives from
`putPicks_eq`, and the window of the output buffer from position 0 that the count of bytes names
holds those lines.  The loop of `writeAll` makes the
writes of `Writes` (`writes_of_run`), and the loop of `main` makes the passes of `Rounds`
(`draw_loop`), or, when it traps under a host that rejects no exit status below 126, a trapped
`random_get` or write.  `Rounds.output` gives the bytes written by passes that end with status 0,
`renderSpec` of the first K picks of the accepted words that they drew, and `Rounds.cap` the words
of passes that reach the cap.  `cap_count` bounds the part of the word sequences of the cap's passes
that hold fewer than K accepted words, from `short_count`, since `512 · (K / 128 + 3) ≥ 4 K + 1024`.
-/

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi Verified.Wasi

/-! ## The picks of a buffer -/

theorem accepted_append (n : UInt64) (a b : List UInt64) :
    accepted n (a ++ b) = accepted n a ++ accepted n b := by
  simp [accepted, List.filter_append]

theorem accepted_single (n w : UInt64) :
    accepted n [w] = if pickSpec (n, w) != 0 then [pickSpec (n, w)] else [] := by
  by_cases h : (pickSpec (n, w) != 0) = true <;> simp [accepted, List.filter, h]

/-- The values of `valuesOf` are the picks of `accepted`. -/
theorem valuesOf_eq_accepted (n : UInt64) : ∀ ws : List UInt64, valuesOf n ws = accepted n ws
  | [] => rfl
  | w :: ws => by
    rw [show w :: ws = [w] ++ ws from rfl, valuesOf_append, accepted_append,
      valuesOf_eq_accepted n ws, valuesOf_single, accepted_single]
    by_cases h : accepts n w = true
    · have hne : pickSpec (n, w) ≠ 0 := (pickSpec_eq_zero n w).not.mpr (by simp [h])
      rw [ite_eq_left h, ite_eq_left (by simpa using hne)]
    · have hz : pickSpec (n, w) = 0 := (pickSpec_eq_zero n w).mpr (by simpa using h)
      rw [ite_eq_right h, ite_eq_right (by simp [hz])]

/-! ## The cap -/

theorem passes_toNat (k : UInt64) : (passes k).toNat = k.toNat / 128 + 3 := by
  have := k.toNat_lt
  rw [passes, UInt64.toNat_add, UInt64.toNat_div]
  simp only [UInt64.reduceToNat]
  omega

/-- At most a `2^-512` part of the sequences of the `512 · passes k` words of the cap's passes hold
fewer than `k` words that `n ≥ 1` accepts. -/
theorem cap_count (n k : UInt64) (hn : n ≠ 0) :
    2 ^ 512 * (Finset.univ.filter fun ws : Fin (512 * (passes k).toNat) → UInt64 =>
      (Finset.univ.filter fun i => accepts n (ws i) = true).card < k.toNat).card ≤
        2 ^ (64 * (512 * (passes k).toNat)) :=
  short_count n hn k.toNat _ (by rw [passes_toNat]; omega)

/-! ## The summaries of `Writes` and `Rounds` -/

theorem renderSpec_append (a b : List UInt64) :
    (renderSpec (a ++ b).toArray).data.data.toList =
      (renderSpec a.toArray).data.data.toList ++ (renderSpec b.toArray).data.data.toList := by
  simp [renderSpec]

theorem committedWrites_cons (e : Event) (rest : List Event) :
    Verified.Shim.committedWrites 1 (e :: rest) =
      Verified.Shim.eventWrites 1 e ++ Verified.Shim.committedWrites 1 rest := by
  simp [Verified.Shim.committedWrites]

theorem committedWrites_append (a b : List Event) :
    Verified.Shim.committedWrites 1 (a ++ b) =
      Verified.Shim.committedWrites 1 a ++ Verified.Shim.committedWrites 1 b := by
  simp [Verified.Shim.committedWrites]

theorem eventWrites_random (args : List Arg) (reply : Transfer (List Bytes)) :
    Verified.Shim.eventWrites 1 (.sys .randomGet args reply) = [] := by
  cases reply <;> simp [Verified.Shim.eventWrites, Call.randomGet, Call.fdWrite]

/-- The writes of `Writes` that end with status 0 took the bytes `text`. -/
theorem Writes.committed {p : Nat} {text : List UInt8} {events : List Event} {status : UInt64}
    (h : Writes p text events status) (zero : status = 0) :
    Verified.Shim.committedWrites 1 events = text := by
  induction h with
  | done => rfl
  | stalled _ => exact absurd zero (by decide)
  | failed _ _ he _ => exact absurd zero he
  | @wrote _ text offered count _ _ _ ho _ ih =>
    rw [committedWrites_cons, ih zero]
    simp [Verified.Shim.eventWrites, Output.fd, Transfer.committed, ho]

/-- The status of `Writes` is 0, `stalledStatus`, or an errno of at most 76. -/
theorem Writes.status_cases {p : Nat} {text : List UInt8} {events : List Event} {status : UInt64}
    (h : Writes p text events status) :
    status = 0 ∨ status = stalledStatus ∨ (status ≠ 0 ∧ status.toNat ≤ 76) := by
  induction h with
  | done => exact .inl rfl
  | stalled _ => exact .inr (.inl rfl)
  | failed _ _ he hb => exact .inr (.inr ⟨he, hb⟩)
  | wrote _ _ _ ih => exact ih

theorem words_buffer {buffer : Bytes} (hsize : buffer.data.size = 4096) (rest : List UInt8) :
    RandomHistogram.words (buffer.data.data.toList ++ rest) =
      RandomHistogram.words buffer.data.data.toList ++ RandomHistogram.words rest :=
  RandomHistogram.words_append (by simp [hsize]) rest

theorem words_buffer_length {buffer : Bytes} (hsize : buffer.data.size = 4096) :
    (RandomHistogram.words buffer.data.data.toList).length = 512 := by
  rw [RandomHistogram.words_length]
  simp [hsize]

theorem passPicks_length (n r : UInt64) (buffer : Bytes) :
    (passPicks n r buffer).length ≤ r.toNat := by
  simp [passPicks]

theorem rest_toNat (n r : UInt64) (buffer : Bytes) :
    (r - UInt64.ofNat (passPicks n r buffer).length).toNat =
      r.toNat - (accepted n (RandomHistogram.words buffer.data.data.toList)).length := by
  have hle := passPicks_length n r buffer
  have hlt : r.toNat < 2 ^ 64 := r.toNat_lt
  have hsize : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by omega)]
    exact hle), UInt64.toNat_ofNat_of_lt' (by omega)]
  simp only [passPicks, List.length_take]
  omega

/-- The passes of `Rounds` that end with status 0 wrote the lines of the first `r` picks of the
accepted words that they drew, and they drew at least `r` accepted words. -/
theorem Rounds.output {n r : UInt64} {p : Nat} {events : List Event} {bytes : List UInt8}
    {status : UInt64} (h : Rounds n r p events bytes status) (zero : status = 0) :
    Verified.Shim.committedWrites 1 events =
        (renderSpec ((accepted n (RandomHistogram.words bytes)).take r.toNat).toArray).data.data.toList ∧
      r.toNat ≤ (accepted n (RandomHistogram.words bytes)).length := by
  induction h with
  | done => simp [Verified.Shim.committedWrites, renderSpec, RandomHistogram.words, accepted]
  | capped _ => exact absurd zero (by decide)
  | drawFailed _ he _ => exact absurd zero he
  | writeEnded _ _ _ hs => exact absurd zero hs
  | @drew r _ buffer writes events bytes _ _ hsize hw _ ih =>
    obtain ⟨hrest, hle⟩ := ih zero
    rw [rest_toNat] at hrest hle
    rw [committedWrites_append, committedWrites_cons, eventWrites_random, List.nil_append,
      hw.committed rfl, hrest, words_buffer hsize, accepted_append, passText, passPicks]
    generalize accepted n (RandomHistogram.words buffer.data.data.toList) = A at hle ⊢
    generalize accepted n (RandomHistogram.words bytes) = B at hle ⊢
    rw [← renderSpec_append, ← List.take_append, List.length_append]
    exact ⟨rfl, by omega⟩

/-- The passes of `Rounds` that reach the cap drew `512 p` words, fewer than `r` of them
accepted. -/
theorem Rounds.cap {n r : UInt64} {p : Nat} {events : List Event} {bytes : List UInt8}
    {status : UInt64} (h : Rounds n r p events bytes status) (capped : status = capStatus) :
    (RandomHistogram.words bytes).length = 512 * p ∧
      (accepted n (RandomHistogram.words bytes)).length < r.toNat := by
  induction h with
  | done => exact absurd capped (by decide)
  | @capped r hr =>
    refine ⟨by simp [RandomHistogram.words], ?_⟩
    have : r.toNat ≠ 0 := fun e => hr (UInt64.toNat_inj.mp (by simpa using e))
    simp [RandomHistogram.words, accepted]
    omega
  | drawFailed _ _ hb =>
    rw [capped] at hb
    exact absurd hb (by decide)
  | writeEnded _ _ hw hs =>
    rcases hw.status_cases with e | e | ⟨_, hb⟩
    · exact absurd e hs
    · rw [capped] at e
      exact absurd e (by decide)
    · rw [capped] at hb
      exact absurd hb (by decide)
  | @drew r _ buffer _ _ bytes _ _ hsize _ _ ih =>
    obtain ⟨hlen, hlt⟩ := ih capped
    rw [rest_toNat] at hlt
    rw [words_buffer hsize, List.length_append, words_buffer_length hsize, hlen, accepted_append,
      List.length_append]
    constructor
    · ring
    · omega

/-- The status of `Rounds` is at most 78. -/
theorem Rounds.status_le {n r : UInt64} {p : Nat} {events : List Event} {bytes : List UInt8}
    {status : UInt64} (h : Rounds n r p events bytes status) : status.toNat ≤ 78 := by
  induction h with
  | done => decide
  | capped _ => decide
  | drawFailed _ _ hb => omega
  | writeEnded _ _ hw _ =>
    rcases hw.status_cases with e | e | ⟨_, hb⟩
    · rw [e]; decide
    · rw [e]; decide
    · omega
  | drew _ _ _ _ ih => exact ih

/-! ## The writes of `writeAll` -/

/-- A run of the loop of `writeAll` over `text` from `written` bytes makes the writes of `Writes`
with its passes left.  When it returns `v`, the status is `stalledStatus` when `v` falls short of
the text and 0 otherwise.  When it exits, it exits with a nonzero status `c` that `Writes` gives
the writes before the exit. -/
theorem writes_of_run {World : Type} {host : Host World} {text : List UInt8}
    (small : text.length < 2 ^ 64) {written : UInt64} {passes : Nat} {events : List Event}
    {outcome : Outcome UInt64} (run : WriteAllRun host text written passes events outcome) :
    written.toNat ≤ text.length →
      (∀ v, outcome = .returned v → v.toNat ≤ text.length ∧
        Writes passes (text.drop written.toNat) events
          (if v.toNat < text.length then stalledStatus else 0)) ∧
      (∀ c, outcome = .exited c → ∃ before, events = before ++ [.exit c] ∧ c ≠ 0 ∧
        Writes passes (text.drop written.toNat) before c) := by
  induction run with
  | done ended =>
    intro le
    refine ⟨fun v h => ?_, fun _ h => by cases h⟩
    cases h
    refine ⟨le, ?_⟩
    rw [ite_eq_right (by omega), List.drop_eq_nil_of_le ended]
    exact .done
  | spent left =>
    intro le
    refine ⟨fun v h => ?_, fun _ h => by cases h⟩
    cases h
    refine ⟨le, ?_⟩
    rw [ite_eq_left left]
    exact .stalled (by simp; omega)
  | @wrote written count passes offered events outcome left offers within rest ih =>
    intro le
    have sum : (written + count).toNat = written.toNat + count.toNat := by
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨returned, exited⟩ := ih (by omega)
    have hdrop : (text.drop written.toNat).drop count.toNat = text.drop (written + count).toNat := by
      rw [List.drop_drop, sum, Nat.add_comm]
    have hne : text.drop written.toNat ≠ [] := by
      simp
      omega
    refine ⟨fun v h => ?_, fun c h => ?_⟩
    · obtain ⟨vle, writes⟩ := returned v h
      rw [← hdrop] at writes
      exact ⟨vle, .wrote hne offers writes⟩
    · obtain ⟨before, rfl, hc, writes⟩ := exited c h
      rw [← hdrop] at writes
      exact ⟨_, by simp, hc, .wrote hne offers writes⟩
  | @failed written errno count passes offered events outcome left offers nonzero valid ended =>
    intro _
    obtain ⟨_, _, ended⟩ := ended
    refine ⟨fun v h => ?_, fun c h => ?_⟩
    · subst h
      cases ended
    · subst h
      cases ended with
      | exit _ =>
        rw [exitStatus_of_lt (by omega)]
        exact ⟨[.write .stdout offered (.returned errno count)], rfl, nonzero,
          .failed (by simp; omega) offers nonzero valid⟩
  | trapped left offers =>
    intro _
    exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

/-! ## A pass -/

/-- A reply of the draw buffer's size fills the whole buffer. -/
theorem splice_whole {draw bytes : Bytes} (h : bytes.data.size = draw.data.size) :
    (draw.splice 0 bytes).data.data.toList = bytes.data.data.toList := by
  have hsize := Bytes.splice_size (buffer := draw) (bytes := bytes) (first := 0) (by omega)
  have htake := RandomHistogram.splice_take (buffer := draw) (bytes := bytes) (by omega)
  rwa [List.take_of_length_le (by simp [hsize]; omega)] at htake

/-- What a pass of `main`'s loop from `r` values to choose makes of the output buffer `out` and the
draw buffer after `random_get` placed the reply `bytes` in it: the output buffer keeps its size,
the count of bytes is that of `passText`, the count of values that of `passPicks`, and the window
of the output buffer from position 0 of that count holds `passText`, which fits the buffer. -/
theorem pass_put (n r : UInt64) {out draw bytes : Bytes} (hout : out.data.size = 10752)
    (hdraw : draw.data.size = 4096) (hbytes : bytes.data.size = 4096) :
    (putPicks out n (draw.splice 0 bytes) r).1.data.size = 10752 ∧
      (putPicks out n (draw.splice 0 bytes) r).2.1 = UInt64.ofNat (passText n r bytes).length ∧
      (putPicks out n (draw.splice 0 bytes) r).2.2 = UInt64.ofNat (passPicks n r bytes).length ∧
      ((putPicks out n (draw.splice 0 bytes) r).1.range 0
        (putPicks out n (draw.splice 0 bytes) r).2.1).data.data.toList = passText n r bytes ∧
      ((putPicks out n (draw.splice 0 bytes) r).1.window 0
        (putPicks out n (draw.splice 0 bytes) r).2.1).2 = (passText n r bytes).length ∧
      (passText n r bytes).length ≤ 10752 := by
  have hsplice := splice_whole (draw := draw) (bytes := bytes) (by omega)
  have hsize := Bytes.splice_size (buffer := draw) (bytes := bytes) (first := 0) (by omega)
  have hwords : (RandomHistogram.words bytes.data.data.toList).length = 512 :=
    words_buffer_length hbytes
  have hpicks : (passPicks n r bytes).length ≤ 512 := by
    simp only [passPicks, List.length_take]
    have : (accepted n (RandomHistogram.words bytes.data.data.toList)).length ≤ 512 := by
      rw [← hwords]
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  have htext : (passText n r bytes).length ≤ 10752 := by
    rw [passText, renderSpec_toList]
    simp only [List.length_map]
    have := textWords_length_le (passPicks n r bytes)
    omega
  have heq := putPicks_eq out n (draw.splice 0 bytes) r (by omega)
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hvalues : (valuesOf n (wordsOf (draw.splice 0 bytes).data.data.toList)).take r.toNat =
      passPicks n r bytes := by
    rw [hsplice, wordsOf_eq, valuesOf_eq_accepted]
    rfl
  have hspec : putPicksSpec (out, n, draw.splice 0 bytes, r) =
      (⟨⟨((passText n r bytes).take out.data.data.toList.length ++
          out.data.data.toList.drop (passText n r bytes).length).toArray⟩⟩,
        UInt64.ofNat (passText n r bytes).length, UInt64.ofNat (passPicks n r bytes).length) := by
    unfold putPicksSpec
    simp only [hvalues]
    rfl
  have hol : out.data.data.toList.length = 10752 := by simp [hout]
  have hlen : (UInt64.ofNat (passText n r bytes).length).toNat = (passText n r bytes).length :=
    UInt64.toNat_ofNat_of_lt' (by omega)
  rw [heq, hspec, hol, List.take_of_length_le htext]
  set B : Bytes := ⟨⟨(passText n r bytes ++
    out.data.data.toList.drop (passText n r bytes).length).toArray⟩⟩ with hBdef
  have hBlist : B.data.data.toList =
      passText n r bytes ++ out.data.data.toList.drop (passText n r bytes).length := rfl
  have hBsize : B.data.size = 10752 := by
    have := congrArg List.length hBlist
    simp only [Array.length_toList, ByteArray.size_data, List.length_append, List.length_drop,
      hol] at this
    omega
  have hW : (B.window 0 (UInt64.ofNat (passText n r bytes).length)).2 =
      (passText n r bytes).length := by
    rw [Bytes.window_snd, hBsize, hlen]
    simp only [UInt64.toNat_zero]
    omega
  refine ⟨hBsize, rfl, rfl, ?_, hW, htext⟩
  rw [Bytes.range_toList, hW, Bytes.window_fst]
  simp only [UInt64.toNat_zero, Nat.zero_min, List.drop_zero]
  rw [hBlist, List.take_left' rfl]

/-! ## The loop of `main` -/

/-- The state of `main`'s loop: the values still to choose, the status of a failed call, the draw
buffer, and the output buffer. -/
abbrev ChooseState := UInt64 × UInt64 × Bytes × Bytes

/-- The fill of `main`'s call of `randomGet` on the state `s` from the reply `reply`. -/
def passFill (s : ChooseState) (reply : Reply) : FillResult :=
  FillResult.of s.2.2.1 0 4096 reply.errno (s.2.2.1.windowLength 0 4096) (reply.bytes 0)

/-- A step of `main`'s loop, written out. -/
def ChooseStep (n : UInt64) (step : UInt64 → ChooseState → Action ChooseState) : Prop :=
  ∀ i (s : ChooseState), step i s =
    .sys .randomGet [.space (s.2.2.1.windowLength 0 4096)] fun reply =>
      if (passFill s reply).errno != 0 then
        .pure (s.1, (passFill s reply).errno, (passFill s reply).buffer, s.2.2.2)
      else
        (writeAll (putPicks s.2.2.2 n (passFill s reply).buffer s.1).1 0
            (putPicks s.2.2.2 n (passFill s reply).buffer s.1).2.1).bind fun written =>
          if written < (putPicks s.2.2.2 n (passFill s reply).buffer s.1).2.1 then
            .pure (s.1, 78, (passFill s reply).buffer,
              (putPicks s.2.2.2 n (passFill s reply).buffer s.1).1)
          else
            .pure (s.1 - (putPicks s.2.2.2 n (passFill s reply).buffer s.1).2.2, 0,
              (passFill s reply).buffer, (putPicks s.2.2.2 n (passFill s reply).buffer s.1).1)

/-- The status that `main` returns from the loop's final state. -/
def finalStatus (s : ChooseState) : UInt64 :=
  if s.2.1 != 0 then s.2.1 else if s.1 != 0 then capStatus else 0

theorem random_accepted : Call.randomGet.reject [.space 4096] = 0 := by
  simp [Call.reject, Call.randomGet, rejectArgs, Param.takesArg, Param.reject, Arg.capacity]

/-- The window of 4,096 bytes from the start of a buffer of 4,096 bytes is all of them. -/
theorem window_whole {buffer : Bytes} (size : buffer.data.size = 4096) :
    buffer.windowLength 0 4096 = 4096 := by
  apply UInt64.toNat_inj.mp
  rw [Bytes.windowLength_toNat, Bytes.window_snd, size]
  simp

/-- A loop of `main` from a state that its test refuses returns that state and has no event. -/
theorem loop_stopped {World : Type} {host : Host World}
    {test : UInt64 → ChooseState → Bool} {step : UInt64 → ChooseState → Action ChooseState}
    (tested : ∀ i s, test i s = (s.1 != 0 && s.2.1 == 0)) (s : ChooseState)
    (stopped : (s.1 != 0 && s.2.1 == 0) = false) :
    ∀ {remaining index world trace} {outcome : Outcome ChooseState} {final},
      LoopExec host remaining index s test step .pure world trace outcome final →
      trace = [] ∧ outcome = .returned s
  | 0, _, _, _, _, _, run => by
    cases run with
    | zero next => exact RandomHistogram.exec_pure next
  | _ + 1, _, _, _, _, _, run => by
    cases run with
    | stop _ next => exact RandomHistogram.exec_pure next
    | next test => rw [tested, stopped] at test; cases test
    | exit test => rw [tested, stopped] at test; cases test
    | trap test => rw [tested, stopped] at test; cases test

/-- The loop of `main` from `r` values to choose, with a draw buffer of 4,096 bytes and an output
buffer of 10,752 bytes, makes the passes of `Rounds`.  When it returns, the status that `main`
gives its final state is the passes' status.  When it exits, it exits with the status that
`Rounds` gives the events before the exit.  When it traps under a host that rejects no exit
status below 126, its events hold a trapped `random_get` of 4,096 bytes or a trapped write to
standard output. -/
theorem draw_loop {World : Type} {host : Host World} {n : UInt64}
    {test : UInt64 → ChooseState → Bool} {step : UInt64 → ChooseState → Action ChooseState}
    (tested : ∀ i s, test i s = (s.1 != 0 && s.2.1 == 0)) (stepped : ChooseStep n step) :
    ∀ (remaining index : Nat) (r : UInt64) (draw out : Bytes) {world trace}
      {outcome : Outcome ChooseState} {final},
      draw.data.size = 4096 → out.data.size = 10752 →
      LoopExec host remaining index (r, 0, draw, out) test step .pure world trace outcome final →
      (∀ s, outcome = .returned s → ∃ bytes, Rounds n r remaining trace bytes (finalStatus s)) ∧
      (∀ c, outcome = .exited c → ∃ events bytes, trace = events ++ [.exit c] ∧
        Rounds n r remaining events bytes c) ∧
      ((∀ {world code message final}, host.exitTrap world code message final →
          126 ≤ code.toNat) →
        ∀ m, outcome = .trapped m → ∃ e ∈ trace,
          (∃ committed, e = .sys .randomGet [.space 4096] (.trapped m committed)) ∨
            ∃ offered committed, e = .write .stdout offered (.trapped m committed))
  | 0, _, r, draw, out, _, _, _, _, _, _, run => by
    cases run with
    | zero next =>
      obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure next
      refine ⟨fun s h => ?_, fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
      cases h
      by_cases hr : r = 0
      · subst hr
        exact ⟨[], .done⟩
      · have hs : finalStatus (r, 0, draw, out) = capStatus := by simp [finalStatus, hr]
        rw [hs]
        exact ⟨[], .capped hr⟩
  | remaining + 1, index, r, draw, out, _, _, _, _, hdraw, hout, run => by
    have hWindow : draw.windowLength 0 4096 = 4096 := window_whole hdraw
    have hsz : UInt64.size = 2 ^ 64 := rfl
    cases run with
    | stop test next =>
      obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure next
      have hr : r = 0 := by simpa [tested] using test
      subst hr
      refine ⟨fun s h => ?_, fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
      cases h
      exact ⟨[], .done⟩
    | trap _ step =>
      refine ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun accepts m h => ?_⟩
      cases h
      rw [stepped] at step
      change Exec host (.sys .randomGet [.space (draw.windowLength 0 4096)] _) _ _ _ _ at step
      rw [hWindow] at step
      cases step with
      | sys_reject fits => exact absurd random_accepted fits
      | sys_trap => exact ⟨_, List.mem_singleton_self _, .inl ⟨_, rfl⟩⟩
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        have shape : committed.map (·.data.size) = [4096] := (host.sys_bound permitted).1
        by_cases zero : errno = 0
        · subst zero
          rcases committed with _ | ⟨bytes, _ | ⟨_, _⟩⟩ <;> simp at shape
          have hFill : passFill (r, 0, draw, out) (sysReply 0 [bytes]) =
              ⟨0, 4096, draw.splice 0 bytes⟩ := by
            simp [passFill, FillResult.of, sysReply, Reply.bytes, Bytes.window, hWindow]
          beta_reduce at next
          rw [hFill] at next
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
          obtain ⟨hsize', -⟩ := pass_put n r hout hdraw shape
          generalize putPicks out n (draw.splice 0 bytes) r = put at hsize' next
          obtain ⟨_, wtrace, woutcome, ktrace, wrun, krun, rfl⟩ := Exec.unbind _ next
          cases woutcome with
          | returned w =>
            change Exec host (if w < put.2.1 then .pure _ else .pure _) _ ktrace _ _ at krun
            split at krun <;> cases krun
          | exited c =>
            obtain ⟨-, h, -⟩ := krun
            cases h
          | trapped m' =>
            obtain ⟨rfl, h, -⟩ := krun
            cases h
            obtain ⟨offered, committed, member⟩ :=
              (writeAll_run (by omega) wrun).trapped_write accepts _ rfl
            exact ⟨_, List.mem_cons_of_mem _ (List.mem_append_left _ member), .inr ⟨_, _, rfl⟩⟩
        · have hErrno : (passFill (r, 0, draw, out) (sysReply errno committed)).errno = errno := by
            simp [passFill, FillResult.of, sysReply, zero]
          beta_reduce at next
          rw [ite_eq_left (by simp [hErrno, zero])] at next
          cases next
    | next test step rest =>
      have hr : r ≠ 0 := by simpa [tested] using test
      rw [stepped] at step
      change Exec host (.sys .randomGet [.space (draw.windowLength 0 4096)] _) _ _ _ _ at step
      rw [hWindow] at step
      cases step with
      | sys_reject fits => exact absurd random_accepted fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        have errnoValid : errno.toNat ≤ 76 := (host.sys_bound permitted).2
        have shape : committed.map (·.data.size) = [4096] := (host.sys_bound permitted).1
        by_cases zero : errno = 0
        · subst zero
          rcases committed with _ | ⟨bytes, _ | ⟨_, _⟩⟩ <;> simp at shape
          have hFill : passFill (r, 0, draw, out) (sysReply 0 [bytes]) =
              ⟨0, 4096, draw.splice 0 bytes⟩ := by
            simp [passFill, FillResult.of, sysReply, Reply.bytes, Bytes.window, hWindow]
          beta_reduce at next
          rw [hFill] at next
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
          obtain ⟨hsize', hcount, hpicks, hfilled, hW, htext⟩ := pass_put n r hout hdraw shape
          have hsplice : (draw.splice 0 bytes).data.size = 4096 :=
            (Bytes.splice_size (by omega)).trans hdraw
          generalize putPicks out n (draw.splice 0 bytes) r = put
            at hsize' hcount hpicks hfilled hW next
          obtain ⟨_, wtrace, woutcome, ktrace, wrun, krun, rfl⟩ := Exec.unbind _ next
          have wfacts := writes_of_run (by rw [hfilled]; omega)
            (writeAll_run (by omega) wrun) (by simp)
          rw [hfilled, hW] at wfacts
          simp only [UInt64.toNat_zero, List.drop_zero] at wfacts
          cases woutcome with
          | exited c =>
            obtain ⟨-, h, -⟩ := krun
            cases h
          | trapped m =>
            obtain ⟨-, h, -⟩ := krun
            cases h
          | returned w =>
          obtain ⟨wle, writes⟩ := wfacts.1 w rfl
          change Exec host (if w < put.2.1 then .pure (r, 78, draw.splice 0 bytes, put.1)
            else .pure (r - put.2.2, 0, draw.splice 0 bytes, put.1)) _ ktrace _ _ at krun
          have hless : w < put.2.1 ↔ w.toNat < (passText n r bytes).length := by
            rw [hcount, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]
          by_cases hstall : w.toNat < (passText n r bytes).length
          · rw [ite_eq_left (hless.mpr hstall)] at krun
            obtain ⟨rfl, hs⟩ := RandomHistogram.exec_pure krun
            cases hs
            rw [ite_eq_left hstall] at writes
            obtain ⟨rfl, rfl⟩ := loop_stopped tested (r, 78, _, put.1) (by simp) rest
            refine ⟨fun s h => ?_, fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
            cases h
            have hs : finalStatus (r, 78, draw.splice 0 bytes, put.1) = stalledStatus := rfl
            rw [hs]
            exact ⟨bytes.data.data.toList, by
              simpa using Rounds.writeEnded (p := remaining) hr shape writes (by decide)⟩
          · rw [ite_eq_right (fun h => hstall (hless.mp h))] at krun
            obtain ⟨rfl, hs⟩ := RandomHistogram.exec_pure krun
            cases hs
            rw [ite_eq_right hstall] at writes
            rw [hpicks] at rest
            obtain ⟨returned, exited, trapped⟩ :=
              draw_loop tested stepped remaining (index + 1) _ _ _ hsplice hsize' rest
            refine ⟨fun s h => ?_, fun c h => ?_, fun accepts m h => ?_⟩
            · obtain ⟨bytes', rounds⟩ := returned s h
              exact ⟨_, by simpa using Rounds.drew hr shape writes rounds⟩
            · obtain ⟨events, bytes', rfl, rounds⟩ := exited c h
              exact ⟨_, _, by simp, Rounds.drew hr shape writes rounds⟩
            · obtain ⟨e, member, kind⟩ := trapped accepts m h
              exact ⟨e, List.mem_append_right _ member, kind⟩
        · have hErrno : (passFill (r, 0, draw, out) (sysReply errno committed)).errno = errno := by
            simp [passFill, FillResult.of, sysReply, zero]
          beta_reduce at next
          rw [ite_eq_left (by simp [hErrno, zero])] at next
          obtain ⟨rfl, hs⟩ := RandomHistogram.exec_pure next
          cases hs
          rw [hErrno] at rest
          obtain ⟨rfl, rfl⟩ := loop_stopped tested (r, errno, _, out) (by simp [zero]) rest
          refine ⟨fun s h => ?_, fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
          cases h
          have hs : finalStatus (r, errno, (passFill (r, 0, draw, out) (sysReply errno committed)).buffer,
              out) = errno := by simp [finalStatus, zero]
          rw [hs]
          exact ⟨[], .drawFailed hr zero errnoValid⟩
    | exit test step =>
      have hr : r ≠ 0 := by simpa [tested] using test
      rw [stepped] at step
      change Exec host (.sys .randomGet [.space (draw.windowLength 0 4096)] _) _ _ _ _ at step
      rw [hWindow] at step
      cases step with
      | sys_reject fits => exact absurd random_accepted fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        have shape : committed.map (·.data.size) = [4096] := (host.sys_bound permitted).1
        by_cases zero : errno = 0
        · subst zero
          rcases committed with _ | ⟨bytes, _ | ⟨_, _⟩⟩ <;> simp at shape
          have hFill : passFill (r, 0, draw, out) (sysReply 0 [bytes]) =
              ⟨0, 4096, draw.splice 0 bytes⟩ := by
            simp [passFill, FillResult.of, sysReply, Reply.bytes, Bytes.window, hWindow]
          beta_reduce at next
          rw [hFill] at next
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
          obtain ⟨hsize', -, -, hfilled, hW, htext⟩ := pass_put n r hout hdraw shape
          generalize putPicks out n (draw.splice 0 bytes) r = put at hsize' hfilled hW next
          obtain ⟨_, wtrace, woutcome, ktrace, wrun, krun, rfl⟩ := Exec.unbind _ next
          have wfacts := writes_of_run (by rw [hfilled]; omega)
            (writeAll_run (by omega) wrun) (by simp)
          rw [hfilled, hW] at wfacts
          simp only [UInt64.toNat_zero, List.drop_zero] at wfacts
          cases woutcome with
          | returned w =>
            change Exec host (if w < put.2.1 then .pure _ else .pure _) _ ktrace _ _ at krun
            split at krun <;> cases krun
          | trapped m =>
            obtain ⟨-, h, -⟩ := krun
            cases h
          | exited c' =>
            obtain ⟨rfl, h, -⟩ := krun
            cases h
            obtain ⟨events, rfl, hc, writes⟩ := wfacts.2 _ rfl
            refine ⟨fun _ h => (nomatch h), fun c h => ?_, fun _ _ h => (nomatch h)⟩
            cases h
            exact ⟨_, bytes.data.data.toList, by simp,
              Rounds.writeEnded (p := remaining) hr shape writes hc⟩
        · have hErrno : (passFill (r, 0, draw, out) (sysReply errno committed)).errno = errno := by
            simp [passFill, FillResult.of, sysReply, zero]
          beta_reduce at next
          rw [ite_eq_left (by simp [hErrno, zero])] at next
          cases next

/-! ## `main` -/

theorem exitStatus_of_le {code : UInt64} (h : code.toNat ≤ 78) : exitStatus code = code := by
  apply UInt64.toNat_inj.mp
  simp only [exitStatus_toNat]
  omega

/-- The passes of a run whose arguments give N and K, and the facts of `Meets` about them. -/
theorem rounds_meets {n k : UInt64} {events : List Event} {bytes : List UInt8} {status : UInt64}
    (rounds : Rounds n k (passes k).toNat events bytes status) :
    ∃ bytes, Rounds n k (passes k).toNat events bytes status ∧
      (status = 0 →
        Verified.Shim.committedWrites 1 events =
          (renderSpec ((accepted n (RandomHistogram.words bytes)).take k.toNat).toArray).data.data.toList ∧
        k.toNat ≤ (accepted n (RandomHistogram.words bytes)).length) ∧
      (status = capStatus →
        (RandomHistogram.words bytes).length = 512 * (passes k).toNat ∧
        (accepted n (RandomHistogram.words bytes)).length < k.toNat) :=
  ⟨bytes, rounds, rounds.output, rounds.cap⟩

/-- Every run of `main` that returns a status, or exits, has events that meet `Meets` and a status
of at most 78. -/
theorem main_runs {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (run : Exec host main world trace outcome final) :
    (∀ status, outcome = .returned status → status.toNat ≤ 78 ∧ Meets host world trace status) ∧
      (∀ c, outcome = .exited c → ∃ events, trace = events ++ [.exit c] ∧ c.toNat ≤ 78 ∧
        Meets host world events c) := by
  obtain ⟨after, pre, middle, rest, argsRun, cont, rfl⟩ := Exec.unbind args run
  obtain ⟨argsNoExit, argsFacts⟩ := RandomHistogram.args_returned argsRun
  cases middle with
  | exited c => exact absurd rfl (argsNoExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | returned a =>
    obtain ⟨aValid, aSize⟩ := argsFacts a rfl
    have parsedN : parseArg a.bytes 1 = parseSpec (a.bytes, 1) := parseArg_eq _ _ (by omega)
    have parsedK : parseArg a.bytes 2 = parseSpec (a.bytes, 2) := parseArg_eq _ _ (by omega)
    change Exec host (if a.errno != 0 then Action.pure a.errno else _) after rest outcome final
      at cont
    split at cont
    · rename_i nonzero
      have hne : a.errno ≠ 0 := by simpa using nonzero
      obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure cont
      refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
      cases h
      exact ⟨by omega, a, pre, [], after, by simp, argsRun, fun _ => ⟨rfl, rfl⟩,
        fun e => absurd e hne, fun e => absurd e hne⟩
    · rename_i zero
      have hz : a.errno = 0 := by simpa using zero
      dsimp only at cont
      rw [parsedN, parsedK] at cont
      split at cont
      · rename_i refused
        have hp : parseSpec (a.bytes, 1) = 0 ∨ parseSpec (a.bytes, 2) = 0 := by
          simpa using refused
        obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure cont
        refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
        cases h
        refine ⟨by decide, a, pre, [], after, by simp, argsRun, fun e => absurd hz e,
          fun _ _ => ⟨rfl, rfl⟩, fun _ h1 h2 => ?_⟩
        rcases hp with h | h
        · exact absurd h h1
        · exact absurd h h2
      · rename_i accepted
        have hp : parseSpec (a.bytes, 1) ≠ 0 ∧ parseSpec (a.bytes, 2) ≠ 0 := by
          simpa [not_or] using accepted
        generalize hn : parseSpec (a.bytes, 1) = n at hp cont
        generalize hk : parseSpec (a.bytes, 2) = k at hp cont
        obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont
        cases loopRun with
        | loop loopRun =>
        have hpasses : (k / 128 + 3).toNat = (passes k).toNat := rfl
        rw [hpasses] at loopRun
        obtain ⟨loopReturned, loopExited, -⟩ := draw_loop (n := n) (fun _ _ => rfl) (fun _ _ => rfl)
          _ 0 k _ _ (by simp) (by simp) loopRun
        cases drawn with
        | exited c =>
          obtain ⟨rfl, h, -⟩ := cont2
          cases h
          refine ⟨fun _ h => (nomatch h), fun c' h => ?_⟩
          cases h
          obtain ⟨events, bytes, rfl, rounds⟩ := loopExited c rfl
          refine ⟨pre ++ events, by simp, rounds.status_le, a, pre, events, after, rfl, argsRun,
            fun e => absurd hz e, fun _ h => ?_, fun _ _ _ => ?_⟩
          · rw [hn, hk] at h
            rcases h with h | h
            · exact absurd h hp.1
            · exact absurd h hp.2
          · rw [hn, hk]
            exact rounds_meets rounds
        | trapped m =>
          obtain ⟨-, rfl, -⟩ := cont2
          exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
        | returned s =>
          obtain ⟨bytes, rounds⟩ := loopReturned s rfl
          have final : (if s.2.1 != 0 then Action.pure s.2.1
              else if s.1 != 0 then (Action.pure 77 : Action UInt64) else .pure 0) =
              .pure (finalStatus s) := by
            unfold finalStatus capStatus
            by_cases h1 : (s.2.1 != 0) = true <;> by_cases h2 : (s.1 != 0) = true <;>
              simp [h1, h2]
          change Exec host (if s.2.1 != 0 then Action.pure s.2.1
            else if s.1 != 0 then (Action.pure 77 : Action UInt64) else .pure 0) _ post _ _ at cont2
          rw [final] at cont2
          obtain ⟨rfl, rfl⟩ := RandomHistogram.exec_pure cont2
          refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
          cases h
          refine ⟨rounds.status_le, a, pre, draws ++ [], after, rfl, argsRun,
            fun e => absurd hz e, fun _ h => ?_, fun _ _ _ => ?_⟩
          · rw [hn, hk] at h
            rcases h with h | h
            · exact absurd h hp.1
            · exact absurd h hp.2
          · rw [hn, hk, List.append_nil]
            exact rounds_meets rounds

/-- Every run of the command's `main` followed by its exit, under every host, that ends with the
exit status `code` has the events of `Meets` followed by the exit, and `code` is at most 78. -/
theorem exec_main {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {code : UInt64}
    (execution : Exec host (main.bind fun status => Action.exit (α := Unit) status) world trace
      (.exited code) final) :
    ∃ events, trace = events ++ [.exit code] ∧ code.toNat ≤ 78 ∧ Meets host world events code := by
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨returned, exited⟩ := main_runs mainRun
  cases middle with
  | exited c =>
    obtain ⟨rfl, h, -⟩ := cont
    cases h
    obtain ⟨events', rfl, small, meets⟩ := exited _ rfl
    exact ⟨events', by simp, small, meets⟩
  | trapped m =>
    obtain ⟨-, h, -⟩ := cont
    cases h
  | returned status =>
    obtain ⟨small, hm⟩ := returned status rfl
    change Exec host (Action.exit status) after rest (.exited code) final at cont
    cases cont with
    | exit _ =>
      rw [exitStatus_of_le small]
      exact ⟨events, rfl, small, hm⟩

end Demos.RandomChoice
