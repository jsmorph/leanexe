import Demos.RandomHistogram.Command
import Demos.RandomHistogram.CommandSpec
import Demos.RandomHistogram.Proof
import Verified.Wasi.SysWords
import LeanExe.Wasi.Bind

/-! Every run of the command's `main` followed by its exit, under every host, that ends with an
exit status meets the request (`exec_main`): its events are those of `Meets` followed by the exit.

The proof follows `main`.  A returned `args` result has an errno of at most 76 and a buffer of
fewer than `2^32` bytes (`args_returned`), so `parseN` computes `parseSpec` on it.  The loop of
`main` draws the words of `Draws` into the buffer of 4,096 bytes that its state carries and holds
the counts of their residues (`draw_loop`).  A call that returns errno 0 places the reply's bytes
at the buffer's start (`splice_take`), `tally` counts the first words of the buffer (`tally_eq`,
`wordAt_eq`), and the words of a concatenation of whole words are the words of its parts
(`words_append`).  The counts are then
`histogram` of the words, so `render` of them is `renderSpec (histogramSpec w)` by `histogram_eq`
and `render_eq`, at most 210 bytes (`render_size`).  `write_tail` gives the writes of `Written`
from `WriteAllRun.taken` of `LeanExe/Wasi/WriteAll.lean`: a run of `writeAll` that returns `v`
took the first `v` bytes of the output, so `main`'s test `v < B` returns 77 exactly when bytes
remain, and a run that exits does so with the errno of its last write. -/

namespace Demos.RandomHistogram

open LeanExe LeanExe.Wasi Verified.Wasi

/-! ## Words -/

theorem words_length (l : List UInt8) : (words l).length = l.length / 8 := by
  simp [words]

theorem words_getElem (l : List UInt8) (j : Nat) (h : j < (words l).length) :
    (words l)[j] = UInt64.ofNat (leValue ((l.drop (8 * j)).take 8)) := by
  simp [words]

/-- The words of a concatenation whose first part is whole words are the words of the parts. -/
theorem words_append {a : List UInt8} (h : a.length % 8 = 0) (b : List UInt8) :
    words (a ++ b) = words a ++ words b := by
  apply List.ext_getElem
  · simp only [words_length, List.length_append]
    omega
  · intro j h1 h2
    have h1' : j < (a.length + b.length) / 8 := by
      simpa [words_length] using h1
    rw [words_getElem _ _ h1]
    by_cases hj : j < a.length / 8
    · rw [List.getElem_append_left (by rw [words_length]; exact hj), words_getElem,
        List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    · rw [List.getElem_append_right (by rw [words_length]; omega), words_getElem, words_length]
      have he : 8 * j = a.length + 8 * (j - a.length / 8) := by omega
      rw [he, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        Nat.add_sub_cancel_left]

/-! ## The running histogram -/

/-- `wordAt` reads the little-endian word of eight bytes. -/
theorem wordAt_eq (bytes : Bytes) (p : Nat) (hp : p + 8 ≤ bytes.data.size)
    (hs : bytes.data.size < 2 ^ 64) :
    wordAt bytes (UInt64.ofNat p) =
      UInt64.ofNat (leValue ((bytes.data.data.toList.drop p).take 8)) := by
  have hlen : ((bytes.data.data.toList.drop p).take 8).length = 8 := by
    simp
    omega
  generalize hc : (bytes.data.data.toList.drop p).take 8 = chunk at hlen ⊢
  have hbyte : ∀ t, t < 8 → ∀ (ht : 7 - t < chunk.length),
      bytes.get (UInt64.ofNat p + 7 - UInt64.ofNat t) = (chunk[7 - t]'ht).toUInt64 := by
    intro t ht ht'
    have hidx : (UInt64.ofNat p + 7 - UInt64.ofNat t).toNat = p + (7 - t) := by
      rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      simp only [UInt64.reduceToNat, Nat.reducePow]
      omega
    have hin : p + (7 - t) < bytes.data.size := by omega
    subst hc
    simp only [Bytes.get, hidx, hin, ↓reduceDIte, List.getElem_take, List.getElem_drop,
      Array.getElem_toList, ByteArray.getElem_eq_getElem_data]
  have key := LeanExe.Dialect.loop_induction (n := 8) (init := (0 : UInt64))
    (f := fun t w => 256 * w + bytes.get (UInt64.ofNat p + 7 - t))
    (fun t w => w.toNat = leValue (chunk.drop (8 - t)) ∧ w.toNat < 256 ^ t)
    ⟨by rw [Nat.sub_zero, List.drop_eq_nil_of_le (by omega)]; rfl, by simp⟩
    (by
      intro t w ht ⟨hw, hb⟩
      simp only [UInt64.reduceToNat] at ht
      have hpow : 256 ^ t ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have h7 : (256 : Nat) ^ 7 = 72057594037927936 := by norm_num
      have hdrop : chunk.drop (8 - (t + 1)) = chunk[7 - t]'(by omega) :: chunk.drop (8 - t) := by
        rw [show 8 - (t + 1) = 7 - t by omega, List.drop_eq_getElem_cons (by omega),
          show 7 - t + 1 = 8 - t by omega]
      have hg := (chunk[7 - t]'(by omega)).toNat_lt
      rw [hbyte t ht (by omega), hdrop]
      have hval : (256 * w + (chunk[7 - t]'(by omega)).toUInt64).toNat =
          256 * w.toNat + (chunk[7 - t]'(by omega)).toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_mul]
        simp only [UInt64.reduceToNat, UInt8.toNat_toUInt64]
        omega
      rw [hval, pow_succ]
      simp only [leValue, List.foldr_cons] at hw ⊢
      constructor
      · omega
      · omega)
  simp only [UInt64.reduceToNat, Nat.sub_self, List.drop_zero] at key
  apply UInt64.toNat_inj.mp
  have hlt : leValue chunk < 2 ^ 64 := by
    rw [← key.1]
    exact (wordAt bytes (UInt64.ofNat p)).toNat_lt
  rw [UInt64.toNat_ofNat_of_lt' hlt]
  exact key.1

/-- `tally` counts the residues of the first `count` little-endian words of a buffer. -/
theorem tally_eq (counts : Array UInt64) (bytes : Bytes) (count : UInt64)
    (hc : 8 * count.toNat ≤ bytes.data.size) (hs : bytes.data.size < 2 ^ 64) :
    tally counts bytes count =
      (words (bytes.data.data.toList.take (8 * count.toNat))).foldl countWord counts := by
  have hlen : (words (bytes.data.data.toList.take (8 * count.toNat))).length = count.toNat := by
    simp only [words_length, List.length_take, Array.length_toList, ByteArray.size_data]
    omega
  have key := LeanExe.Dialect.loop_induction (n := count) (init := counts)
    (f := fun j c => countWord c (wordAt bytes (8 * j)))
    (fun k c => c =
      ((words (bytes.data.data.toList.take (8 * count.toNat))).take k).foldl countWord counts)
    (by simp)
    (by
      intro k c hk hc'
      have h8 : (8 : UInt64) * UInt64.ofNat k = UInt64.ofNat (8 * k) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
        omega
      have hw := words_getElem (bytes.data.data.toList.take (8 * count.toNat)) k (by omega)
      have htake : (words (bytes.data.data.toList.take (8 * count.toNat))).take (k + 1) =
          (words (bytes.data.data.toList.take (8 * count.toNat))).take k ++
            [(words (bytes.data.data.toList.take (8 * count.toNat)))[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hchunk : ((bytes.data.data.toList.take (8 * count.toNat)).drop (8 * k)).take 8 =
          (bytes.data.data.toList.drop (8 * k)).take 8 := by
        rw [List.drop_take, List.take_take]
        congr 1
        omega
      show countWord c (wordAt bytes (8 * UInt64.ofNat k)) = _
      rw [h8, wordAt_eq bytes (8 * k) (by omega) hs, hc', htake, List.foldl_append, hw, hchunk]
      rfl)
  rw [show tally counts bytes count =
      LeanExe.loop count counts (fun j c => countWord c (wordAt bytes (8 * j))) from rfl,
    key, List.take_of_length_le (by omega)]

/-- The first bytes of a buffer with `bytes` placed at its start are `bytes`. -/
theorem splice_take {buffer bytes : Bytes} (h : bytes.data.size ≤ buffer.data.size) :
    (buffer.splice 0 bytes).data.data.toList.take bytes.data.size = bytes.data.data.toList := by
  have hSize := Bytes.splice_size (first := 0) (by omega : 0 + bytes.data.size ≤ buffer.data.size)
  apply List.ext_getElem
  · simp only [List.length_take, Array.length_toList, ByteArray.size_data, hSize]
    omega
  · intro i h1 h2
    have hi : i < bytes.data.size := by simpa using h2
    rw [List.getElem_take, Array.getElem_toList, Array.getElem_toList,
      ← ByteArray.getElem_eq_getElem_data, ← ByteArray.getElem_eq_getElem_data,
      Bytes.splice_get_inside (by omega) (Nat.zero_le _) (by omega)]
    simp

/-- `histogram` of an array is the fold of `countWord` over its words from ten zero counts. -/
theorem histogram_list (ws : List UInt64) :
    histogram ws.toArray = ws.foldl countWord (LeanExe.build 10 fun _ => 0) := by
  show ws.toArray.foldl countWord (LeanExe.build 10 fun _ => 0) = _
  rw [← Array.foldl_toList, List.toList_toArray]

/-! ## The calls -/

/-- A `sys` action that returns a value made a call that the host answered with a reply. -/
theorem exec_sys_returned {World α : Type} {host : Host World} {call : Call} {args : List Arg}
    {next : Reply → Action α} {world final : World} {trace : List Event} {value : α}
    (run : Exec host (.sys call args next) world trace (.returned value) final)
    (accepted : call.reject args = 0) :
    ∃ errno committed after rest, trace = .sys call args (.returned errno committed) :: rest ∧
      host.sys world call args (.returned errno committed) after ∧
      Exec host (next (sysReply errno committed)) after rest (.returned value) final := by
  cases run with
  | sys_reject fits => exact absurd accepted fits
  | sys_return _ permitted next => exact ⟨_, _, _, _, rfl, permitted, next⟩

/-- A run of `pure` returns its value and has no event. -/
theorem exec_pure {World α : Type} {host : Host World} {value : α} {world final : World}
    {trace : List Event} {outcome : Outcome α}
    (run : Exec host (.pure value) world trace outcome final) :
    trace = [] ∧ outcome = .returned value := by
  cases run
  exact ⟨rfl, rfl⟩

/-- `args` never exits, and a returned result has an errno of at most 76 and a buffer of fewer
than `2^32` bytes: the size that the reporter's four-byte word gives. -/
theorem args_returned {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {outcome : Outcome ArgsResult}
    (run : Exec host args world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧
      ∀ a, outcome = .returned a → a.errno.toNat ≤ 76 ∧ a.bytes.data.size < 2 ^ 32 := by
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | @sys_return _ _ _ _ _ _ _ _ _ errno sizes _ reporter next =>
    have errnoValid : errno.toNat ≤ 76 := (host.sys_bound reporter).2
    beta_reduce at next
    split at next
    · obtain ⟨-, rfl⟩ := exec_pure next
      refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
      cases h
      exact ⟨by simpa [sysReply] using errnoValid, by simp [Bytes.empty]⟩
    · split at next
      · obtain ⟨-, rfl⟩ := exec_pure next
        refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
        cases h
        exact ⟨by decide, by simp [Bytes.empty]⟩
      · rename_i nonzero _
        have zero : errno = 0 := by simpa [sysReply] using nonzero
        subst zero
        cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
        | @sys_return _ _ _ _ _ _ _ _ _ errno got _ getter next =>
          have gotValid : errno.toNat ≤ 76 := (host.sys_bound getter).2
          beta_reduce at next
          split at next
          · obtain ⟨-, rfl⟩ := exec_pure next
            refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
            cases h
            exact ⟨by simpa [sysReply] using gotValid, by simp [Bytes.empty]⟩
          · rename_i gotNonzero
            have gotZero : errno = 0 := by simpa [sysReply] using gotNonzero
            subst gotZero
            obtain ⟨-, rfl⟩ := exec_pure next
            refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
            cases h
            have shape : sizes.map (·.data.size) = [4, 4] := (host.sys_bound reporter).1
            rcases sizes with _ | ⟨count, _ | ⟨size, _ | ⟨_, _⟩⟩⟩ <;> simp at shape
            have sizeSmall := littleEndian_four_lt shape.2
            have gotShape : got.map (·.data.size) = [1 * (littleEndian size).toNat] := by
              have permitted := (host.sys_bound getter).1
              rw [host.sys_reports (call := Call.argsGet) reporter rfl] at permitted
              exact permitted
            rcases got with _ | ⟨shown, _ | ⟨_, _⟩⟩ <;> simp at gotShape
            refine ⟨Nat.zero_le _, ?_⟩
            simp only [sysReply, ↓reduceIte, Reply.bytes, List.getElem?_cons_zero,
              Option.getD_some]
            omega

/-! ## The loop of `main` -/

/-- The state of `main`'s loop: the counts, the buffer, the words still to draw, and the errno of a
failed call. -/
abbrev DrawState := Array UInt64 × Bytes × UInt64 × UInt64

theorem toNat_min512 (r : UInt64) : (min r 512).toNat = min r.toNat 512 := by
  show (if r ≤ 512 then r else 512).toNat = _
  split
  · rename_i h
    have := UInt64.le_iff_toNat_le.mp h
    simp only [UInt64.reduceToNat] at this
    omega
  · rename_i h
    have := mt UInt64.le_iff_toNat_le.mpr h
    simp only [UInt64.reduceToNat] at this ⊢
    omega

theorem toNat_eight_min (r : UInt64) : (8 * min r 512).toNat = 8 * min r.toNat 512 := by
  rw [UInt64.toNat_mul, toNat_min512]
  simp only [UInt64.reduceToNat]
  omega

theorem randomGet_accepted (r : UInt64) : Call.randomGet.reject [.space (8 * min r 512)] = 0 := by
  have h8 : (8 * min r 512).toNat < 4294967296 := by
    rw [toNat_eight_min]
    omega
  generalize 8 * min r 512 = c at h8 ⊢
  simp [Call.reject, Call.randomGet, rejectArgs, Param.takesArg, Param.reject, Arg.capacity, h8]

/-- `random_get` of a window of at most `8 · min r 512` bytes of any buffer is accepted. -/
theorem randomGet_window_accepted (buffer : Bytes) (r : UInt64) :
    Call.randomGet.reject [.space (buffer.windowLength 0 (8 * min r 512))] = 0 := by
  have h8 : (buffer.windowLength 0 (8 * min r 512)).toNat < 4294967296 := by
    rw [Bytes.windowLength_toNat, Bytes.window_snd, toNat_eight_min]
    omega
  generalize buffer.windowLength 0 (8 * min r 512) = c at h8 ⊢
  simp [Call.reject, Call.randomGet, rejectArgs, Param.takesArg, Param.reject, Arg.capacity, h8]

/-- The window of `8 · min r 512` bytes from the start of a buffer of 4,096 bytes is all of them. -/
theorem window_draw {buffer : Bytes} (size : buffer.data.size = 4096) (r : UInt64) :
    buffer.windowLength 0 (8 * min r 512) = 8 * min r 512 := by
  apply UInt64.toNat_inj.mp
  rw [Bytes.windowLength_toNat, Bytes.window_snd, toNat_eight_min, size]
  simp only [UInt64.toNat_zero]
  omega

/-- A loop of `main` from a state with no word to draw returns that state and has no event. -/
theorem loop_stopped {World : Type} {host : Host World} {test : UInt64 → DrawState → Bool}
    {step : UInt64 → DrawState → Action DrawState}
    (tested : ∀ i s, test i s = (s.2.2.1 != 0)) (counts : Array UInt64) (buffer : Bytes)
    (errno : UInt64) :
    ∀ {remaining index world trace} {outcome : Outcome DrawState} {final},
      LoopExec host remaining index (counts, buffer, 0, errno) test step .pure world trace outcome
        final →
      trace = [] ∧ outcome = .returned (counts, buffer, 0, errno)
  | 0, _, _, _, _, _, run => by
    cases run with
    | zero next => exact exec_pure next
  | _ + 1, _, _, _, _, _, run => by
    cases run with
    | stop _ next => exact exec_pure next
    | next test => simp [tested] at test
    | exit test => simp [tested] at test
    | trap test => simp [tested] at test

/-- The fill of `main`'s call of `randomGet` on the state `s` from the reply `reply`. -/
def drawFill (s : DrawState) (reply : Reply) : FillResult :=
  FillResult.of s.2.1 0 (8 * min s.2.2.1 512) reply.errno
    (s.2.1.windowLength 0 (8 * min s.2.2.1 512)) (reply.bytes 0)

/-- A step of `main`'s loop, written out. -/
def DrawStep (step : UInt64 → DrawState → Action DrawState) : Prop :=
  ∀ i (s : DrawState), step i s =
    .sys .randomGet [.space (s.2.1.windowLength 0 (8 * min s.2.2.1 512))] fun reply =>
      if (drawFill s reply).errno != 0 then
        .pure (s.1, (drawFill s reply).buffer, 0, (drawFill s reply).errno)
      else
        .pure (tally s.1 (drawFill s reply).buffer (min s.2.2.1 512), (drawFill s reply).buffer,
          s.2.2.1 - min s.2.2.1 512, 0)

/-- A step of `main`'s loop never exits. -/
theorem step_not_exited {World : Type} {host : Host World} {step} (stepped : DrawStep step)
    {i : UInt64} {s : DrawState} {world trace code final}
    (run : Exec host (step i s) world trace (.exited code) final) : False := by
  rw [stepped] at run
  cases run with
  | sys_reject fits => exact fits (randomGet_window_accepted _ _)
  | sys_return _ _ next =>
    beta_reduce at next
    split at next
    · cases next
    · cases next

/-- The loop of `main` from `r` words to draw and a buffer of 4,096 bytes, with enough passes
left, never exits, and when it returns, it made the calls of `Draws r`, its state holds their
errno, which is at most 76, and, when that errno is 0, the counts of the residues of the words that
the calls returned. -/
theorem draw_loop {World : Type} {host : Host World} {test : UInt64 → DrawState → Bool}
    {step : UInt64 → DrawState → Action DrawState}
    (tested : ∀ i s, test i s = (s.2.2.1 != 0)) (stepped : DrawStep step) :
    ∀ (remaining index : Nat) (counts : Array UInt64) (buffer : Bytes) (r : UInt64)
      {world trace} {outcome : Outcome DrawState} {final},
      buffer.data.size = 4096 → r.toNat ≤ 512 * remaining →
      LoopExec host remaining index (counts, buffer, r, 0) test step .pure world trace outcome
        final →
      (∀ c, outcome ≠ .exited c) ∧
      ∀ s, outcome = .returned s → ∃ bytes errno, Draws r trace bytes errno ∧ s.2.2.2 = errno ∧
        errno.toNat ≤ 76 ∧ (errno = 0 → s.1 = (words bytes).foldl countWord counts)
  | 0, _, counts, buffer, r, _, _, _, _, _, enough, run => by
    have hr : r = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hr
    obtain ⟨rfl, rfl⟩ := loop_stopped tested counts buffer 0 run
    refine ⟨fun _ h => (nomatch h), fun s h => ?_⟩
    cases h
    exact ⟨[], 0, .done, rfl, by decide, fun _ => rfl⟩
  | remaining + 1, index, counts, buffer, r, _, _, _, _, size, enough, run => by
    cases run with
    | stop test next =>
      obtain ⟨rfl, rfl⟩ := exec_pure next
      have hr : r = 0 := by simpa [tested] using test
      subst hr
      refine ⟨fun _ h => (nomatch h), fun s h => ?_⟩
      cases h
      exact ⟨[], 0, .done, rfl, by decide, fun _ => rfl⟩
    | exit _ step => exact (step_not_exited stepped step).elim
    | trap _ _ => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
    | next test step rest =>
      have hr : r ≠ 0 := by simpa [tested] using test
      have hrn : r.toNat ≠ 0 := fun e => hr (UInt64.toNat_inj.mp (by simpa using e))
      rw [stepped] at step
      have hWindow : buffer.windowLength 0 (8 * min r 512) = 8 * min r 512 := window_draw size r
      change Exec host (.sys .randomGet [.space (buffer.windowLength 0 (8 * min r 512))] _) _ _ _ _
        at step
      rw [hWindow] at step
      cases step with
      | sys_reject fits => exact absurd (randomGet_accepted r) fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        have errnoValid : errno.toNat ≤ 76 := (host.sys_bound permitted).2
        have shape : committed.map (·.data.size) = [(8 * min r 512).toNat] :=
          (host.sys_bound permitted).1
        beta_reduce at next
        split at next
        · rename_i nonzero
          have hne : errno ≠ 0 := by
            intro hz
            subst hz
            simp [drawFill, FillResult.of, sysReply] at nonzero
          have hErrno : (drawFill (counts, buffer, r, 0) (sysReply errno committed)).errno =
              errno := by
            simp [drawFill, FillResult.of, sysReply, hne]
          obtain ⟨rfl, hs⟩ := exec_pure next
          cases hs
          rw [hErrno] at rest
          obtain ⟨rfl, rfl⟩ := loop_stopped tested counts _ errno rest
          refine ⟨fun _ h => (nomatch h), fun s h => ?_⟩
          cases h
          exact ⟨[], errno, .failed hr hne, rfl, errnoValid, fun e => absurd e hne⟩
        · rename_i zero
          have hz : errno = 0 := by
            by_contra hne
            simp [drawFill, FillResult.of, sysReply, hne] at zero
          subst hz
          obtain ⟨rfl, hs⟩ := exec_pure next
          cases hs
          rcases committed with _ | ⟨bytes, _ | ⟨_, _⟩⟩
          · simp at shape
          rotate_left
          · simp at shape
          have hmin := toNat_min512 r
          have hsize : bytes.data.size = 8 * min r.toNat 512 :=
            (List.cons.inj (shape : [bytes.data.size] = _)).1.trans (toNat_eight_min r)
          have hsub : (r - min r 512).toNat = r.toNat - min r.toNat 512 := by
            rw [UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le, hmin]
              omega), hmin]
          have hFill : (drawFill (counts, buffer, r, 0) (sysReply 0 [bytes])).buffer =
              buffer.splice 0 bytes := by
            simp [drawFill, FillResult.of, sysReply, Reply.bytes, Bytes.window]
          have spliced : (buffer.splice 0 bytes).data.size = 4096 :=
            (Bytes.splice_size (by omega)).trans size
          rw [hFill] at rest
          obtain ⟨noExit, returned⟩ := draw_loop tested stepped remaining (index + 1)
            (tally counts (buffer.splice 0 bytes) (min r 512)) (buffer.splice 0 bytes)
            (r - min r 512) spliced (by rw [hsub]; omega) rest
          refine ⟨noExit, fun s h => ?_⟩
          obtain ⟨drawn, errno, draws, hs, hvalid, hcounts⟩ := returned s h
          refine ⟨bytes.data.data.toList ++ drawn, errno, .drew hr hsize draws, hs, hvalid,
            fun e => ?_⟩
          have hTake : 8 * (min r 512).toNat = bytes.data.size := by rw [hmin, hsize]
          rw [hcounts e, tally_eq counts _ _ (by rw [spliced, hmin]; omega) (by omega), hTake,
            splice_take (by omega), words_append (by simp [hsize]), List.foldl_append]

/-! ## The writes -/

/-- The output of `render` holds at most 210 bytes. -/
theorem render_size (counts : Array UInt64) : (render counts).data.size ≤ 210 := by
  have hsize := render_text_size counts
  obtain ⟨t, ht⟩ : ∃ t, LeanExe.loop 10 (#[] : Array UInt64)
      (fun m t => appendLine t counts[m.toNat]!) = t := ⟨_, rfl⟩
  rw [ht] at hsize
  have hrender : render counts = Bytes.build t.size.toUInt64 fun i => t[i.toNat]! := by
    unfold render
    simp only [ht]
  rw [hrender, build_words t (by omega)]
  simpa [ByteArray.size] using hsize

/-- A run of `writeAll out` followed by `main`'s test of the bytes written, for an output of at most
210 bytes, meets `Written`: when it returns a status, 0 or 77, with its events, and when it exits,
with a status from 1 to 76, with its events before the exit. -/
theorem write_tail {World : Type} {host : Host World} {out : Bytes} (small : out.data.size ≤ 210)
    {world final : World} {trace : List Event} {outcome : Outcome UInt64}
    (run : Exec host (Action.bind (writeAll out) fun written =>
      Action.pure (if written < out.size then 77 else 0)) world trace outcome final) :
    (∀ status, outcome = .returned status →
      (status = 0 ∨ status = 77) ∧ Written out.data.data.toList trace status) ∧
    (∀ code, outcome = .exited code → code ≠ 0 ∧ code.toNat ≤ 76 ∧
      ∃ writes, trace = writes ++ [.exit code] ∧ Written out.data.data.toList writes code) := by
  obtain ⟨after, writes, middle, tail, writeRun, cont, rfl⟩ := Exec.unbind (writeAll out) run
  have length : out.data.data.toList.length = out.data.size := by simp
  have facts := (writeAll_run (by omega) writeRun).taken (by rw [length]; omega) (by simp)
  have wide : out.size.toNat = out.data.size := by
    simp only [Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  cases middle with
  | returned value =>
    obtain ⟨shape, -, high, taken, offeredAll, counted⟩ := facts.1 value rfl
    simp only [UInt64.toNat_zero, List.drop_zero, Nat.sub_zero] at taken offeredAll
    change Exec host (Action.pure (if value < out.size then 77 else 0)) after tail outcome final
      at cont
    obtain ⟨rfl, rfl⟩ := exec_pure cont
    have takenLength : (stdoutTaken writes).length = value.toNat := by
      rw [taken, List.length_take]
      omega
    refine ⟨fun status same => ?_, fun _ same => (by cases same)⟩
    cases same
    rw [List.append_nil]
    by_cases short : value < out.size
    · rw [ite_eq_left short]
      have below : value.toNat < out.data.size := by
        rw [UInt64.lt_iff_toNat_lt, wide] at short
        exact short
      refine ⟨.inr rfl, offeredAll, by rw [taken]; exact List.take_prefix _ _, ?_,
        .inl ⟨shape, .inr ⟨rfl, by rw [counted (by omega), length]⟩⟩⟩
      refine ⟨fun same => absurd same (by decide), fun whole => ?_⟩
      have := congrArg List.length whole
      omega
    · rw [ite_eq_right short]
      have above : out.data.size ≤ value.toNat := by
        rw [UInt64.lt_iff_toNat_lt, wide] at short
        omega
      refine ⟨.inl rfl, offeredAll, by rw [taken]; exact List.take_prefix _ _, ?_,
        .inl ⟨shape, .inl rfl⟩⟩
      exact ⟨fun _ => by rw [taken, List.take_of_length_le (by omega)], fun _ => rfl⟩
  | exited code =>
    obtain ⟨rfl, rfl, rfl⟩ := cont
    obtain ⟨nonzero, valid, ⟨before, offered, count, shape, earlier, offeredBefore⟩, prefix_,
      bound⟩ := facts.2 code rfl
    simp only [UInt64.toNat_zero] at offeredBefore
    refine ⟨fun _ same => (by cases same), fun code' same => ?_⟩
    cases same
    have dropped : stdoutTaken (before ++ [.write .stdout offered (.returned code count)]) =
        stdoutTaken writes := by
      rw [shape]
      simp [stdoutTaken_append, Event.stdoutTaken, nonzero]
    refine ⟨nonzero, valid, before ++ [.write .stdout offered (.returned code count)],
      by rw [List.append_nil, shape]; simp, offeredBefore, ?_, ?_,
      .inr ⟨nonzero, valid, before, offered, count, rfl, earlier⟩⟩
    · rw [dropped]
      simpa using prefix_
    · rw [dropped]
      refine ⟨fun same => absurd same nonzero, fun whole => ?_⟩
      have := congrArg List.length whole
      simp only [UInt64.toNat_zero, Nat.zero_add] at bound
      omega
  | trapped message =>
    obtain ⟨rfl, rfl, rfl⟩ := cont
    exact ⟨fun _ same => (by cases same), fun _ same => by cases same⟩

/-! ## `main` -/

/-- The bytes that `Draws` collects with errno 0 hold exactly the drawn words. -/
theorem Draws.length {r : UInt64} {events : List Event} {bytes : List UInt8} {errno : UInt64}
    (h : Draws r events bytes errno) (hz : errno = 0) : bytes.length = 8 * r.toNat := by
  induction h with
  | done => rfl
  | failed _ he => exact absurd hz he
  | @drew r _ buffer _ _ hr hsize _ ih =>
    have hmin := toNat_min512 r
    have hsub : (r - min r 512).toNat = r.toNat - min r.toNat 512 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hmin]; omega), hmin]
    simp only [List.length_append, Array.length_toList, ByteArray.size_data] at ih ⊢
    rw [hsize, ih hz, hsub]
    omega

/-- Every run of `main` that returns a status has a status of at most 77 and events that meet
`Meets`, and every run that exits does so with a status of at most 76 and events that meet `Meets`
followed by the exit. -/
theorem main_runs {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (run : Exec host main world trace outcome final) :
    (∀ status, outcome = .returned status → status.toNat ≤ 77 ∧ Meets host world trace status) ∧
    (∀ code, outcome = .exited code → code.toNat ≤ 76 ∧
      ∃ events, trace = events ++ [.exit code] ∧ Meets host world events code) := by
  obtain ⟨after, pre, middle, rest, argsRun, cont, rfl⟩ := Exec.unbind args run
  obtain ⟨argsNoExit, argsFacts⟩ := args_returned argsRun
  cases middle with
  | exited c => exact absurd rfl (argsNoExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | returned a =>
    obtain ⟨aValid, aSize⟩ := argsFacts a rfl
    have parsed : parseN a.bytes = parseSpec a.bytes := parseN_eq a.bytes (by omega)
    change Exec host (if a.errno != 0 then Action.pure a.errno else _) after rest outcome final
      at cont
    split at cont
    · rename_i nonzero
      have hne : a.errno ≠ 0 := by simpa using nonzero
      obtain ⟨rfl, rfl⟩ := exec_pure cont
      refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
      cases h
      exact ⟨by omega, a, pre, [], after, rfl, argsRun, fun _ => ⟨rfl, rfl⟩,
        fun e => absurd e hne, fun e => absurd e hne⟩
    · rename_i zero
      have hz : a.errno = 0 := by simpa using zero
      dsimp only at cont
      rw [parsed] at cont
      split at cont
      · rename_i refused
        have hp : parseSpec a.bytes = 0 := by simpa using refused
        obtain ⟨rfl, rfl⟩ := exec_pure cont
        refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
        cases h
        exact ⟨by decide, a, pre, [], after, rfl, argsRun, fun e => absurd hz e,
          fun _ _ => ⟨rfl, rfl⟩, fun _ e => absurd hp e⟩
      · rename_i accepted
        have hp : parseSpec a.bytes ≠ 0 := by simpa using accepted
        generalize hn : parseSpec a.bytes = n at hp cont
        obtain ⟨loopAfter, draws, drawn, post, loopRun, cont2, rfl⟩ := Exec.unbind _ cont
        cases loopRun with
        | loop loopRun =>
        have passes : n.toNat ≤ 512 * (n / 512 + 1).toNat := by
          have := n.toNat_lt
          have : (n / 512 + 1).toNat = n.toNat / 512 + 1 := by
            rw [UInt64.toNat_add, UInt64.toNat_div]
            simp only [UInt64.reduceToNat]
            omega
          rw [this]
          omega
        obtain ⟨loopNoExit, loopFacts⟩ := draw_loop (fun _ _ => rfl) (fun _ _ => rfl) _ 0 _ _ n
          (by simp) passes loopRun
        cases drawn with
        | exited c => exact absurd rfl (loopNoExit c)
        | trapped m =>
          obtain ⟨-, rfl, -⟩ := cont2
          exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
        | returned s =>
          obtain ⟨bytes, errno, drawsOk, hs, errnoValid, hcounts⟩ := loopFacts s rfl
          change Exec host (if s.2.2.2 != 0 then Action.pure s.2.2.2 else _) loopAfter post
            outcome final at cont2
          split at cont2
          · rename_i failed
            have he : errno ≠ 0 := by rw [← hs]; simpa using failed
            obtain ⟨rfl, rfl⟩ := exec_pure cont2
            refine ⟨fun status h => ?_, fun _ h => (nomatch h)⟩
            cases h
            refine ⟨by rw [hs]; omega, a, pre, draws ++ [], after, rfl, argsRun,
              fun e => absurd hz e, fun _ e => absurd (hn.symm.trans e) hp, fun _ _ => ?_⟩
            rw [hn]
            exact ⟨draws, bytes, errno, [], rfl, drawsOk, fun _ => ⟨hs, rfl⟩, fun e => absurd e he⟩
          · rename_i succeeded
            have he : errno = 0 := by rw [← hs]; simpa using succeeded
            have counted := hcounts he
            have hlen : bytes.length = 8 * n.toNat := drawsOk.length he
            have wlen : (words bytes).length = n.toNat := by
              rw [words_length, hlen]
              omega
            have sum : ((histogramSpec (words bytes).toArray).toList.map UInt64.toNat).sum =
                n.toNat := by
              rw [histogramSpec_sum _ (by rw [List.size_toArray, wlen]; exact n.toNat_lt),
                List.size_toArray, wlen]
            have rendered : render s.1 = renderSpec (histogramSpec (words bytes).toArray) := by
              rw [counted, ← histogram_list, histogram_eq, render_eq]
            change Exec host (Action.bind (writeAll (render s.1)) fun written =>
                Action.pure (if written < (render s.1).size then 77 else 0))
              loopAfter post outcome final at cont2
            have tail := write_tail (render_size s.1) cont2
            rw [rendered] at tail
            refine ⟨fun status h => ?_, fun code h => ?_⟩
            · obtain ⟨kind, written⟩ := tail.1 status h
              have small : status.toNat ≤ 77 := by rcases kind with rfl | rfl <;> decide
              refine ⟨small, a, pre, _, after, rfl, argsRun, fun e => absurd hz e,
                fun _ e => absurd (hn.symm.trans e) hp, fun _ _ => ?_⟩
              rw [hn]
              exact ⟨draws, bytes, errno, post, rfl, drawsOk, fun e => absurd he e,
                fun _ => ⟨wlen, sum, written⟩⟩
            · obtain ⟨-, small, writes, rfl, written⟩ := tail.2 code h
              refine ⟨small, pre ++ (draws ++ writes), by simp, a, pre, _, after, rfl, argsRun,
                fun e => absurd hz e, fun _ e => absurd (hn.symm.trans e) hp, fun _ _ => ?_⟩
              rw [hn]
              exact ⟨draws, bytes, errno, writes, rfl, drawsOk, fun e => absurd he e,
                fun _ => ⟨wlen, sum, written⟩⟩

/-- Every run of the command's `main` followed by its exit, under every host, that ends with the
exit status `code` has the events of `Meets` followed by the exit: the status is the errno of
`args`, 2 for a refused argument, the errno of a failed `random_get`, or, after the calls of
`random_get` returned the N words `w`, whose counts sum to N, the status of the writes of
`renderSpec (histogramSpec w)` that `Written` states: 0 exactly when they took every byte of it,
the errno of a write that failed, or 77 after one write for each of the loop's passes with bytes
unwritten.  Each write offered the bytes that the writes before it did not take.  The status is at
most 77. -/
theorem exec_main {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {code : UInt64}
    (execution : Exec host (main.bind fun status => Action.exit (α := Unit) status) world trace
      (.exited code) final) :
    ∃ events, trace = events ++ [.exit code] ∧ code.toNat ≤ 77 ∧ Meets host world events code := by
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨returned, exited⟩ := main_runs mainRun
  cases middle with
  | exited c =>
    obtain ⟨rfl, same, -⟩ := cont
    obtain ⟨small, steps, rfl, meets⟩ := exited c rfl
    cases same
    exact ⟨steps, by rw [List.append_nil], by omega, meets⟩
  | trapped m =>
    obtain ⟨-, h, -⟩ := cont
    cases h
  | returned status =>
    obtain ⟨small, hm⟩ := returned status rfl
    change Exec host (Action.exit status) after rest (.exited code) final at cont
    cases cont with
    | exit _ =>
      rw [exitStatus_of_lt (by omega)]
      exact ⟨events, rfl, small, hm⟩

end Demos.RandomHistogram
