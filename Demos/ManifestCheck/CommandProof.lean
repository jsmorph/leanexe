import Demos.ManifestCheck.Command
import Demos.ManifestCheck.CommandSpec
import Demos.ManifestCheck.Proof
import Library.Hashing.Sha256.StreamProof
import Verified.Wasi.FunctionEntry
import Verified.Wasi.Handles
import LeanExe.Wasi.Bind

/-! The runs of the command's reads.  `join_toList` and `slice_toList` give the bytes of `join` and
`slice`, and `argScan_eq` the zero bytes of the argument buffer that `argScan` counts.
`Hashed` relates the state of `hashFile`'s loop to the bytes that the reads returned: the length,
the bytes after the last whole block, and the implementation's hash value after the whole blocks.
`hashed_step` keeps it across a read, through `update_toVec32` and `blocksFold_append`, and
`hashed_finish` gives the digest bytes of `SHS.SHA256.Impl.sha256` of the bytes.  `hash_loop` and
`manifest_loop` follow the loops of `hashFile` and `readManifest` by induction on their passes and
give the reads of `FileReads` and `ManifestReads`. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Library.Hashing.Words Library.Hashing.Sha256 Verified.Wasi

/-! ## Bytes -/

theorem build_toList (count : UInt64) (f : UInt64 → UInt64) :
    (Bytes.build count f).data.data.toList =
      List.ofFn (n := count.toNat) fun i => (f (UInt64.ofNat i)).toUInt8 := by
  simp [Bytes.build, Array.toList_ofFn]

theorem get_toUInt8 (b : Bytes) (i : Nat) (hi : i < b.data.size) (h64 : i < 2 ^ 64) :
    (b.get (UInt64.ofNat i)).toUInt8 = b.data.data.toList[i]'(by simpa using hi) := by
  rw [Bytes.get_eq_get!, toNat_ofNat h64, Bytes.get!_of_lt _ hi, UInt8.toUInt8_toUInt64,
    Array.getElem_toList]
  rfl

theorem join_toList (a b : Bytes) (h : a.data.size + b.data.size < 2 ^ 64) :
    (join a b).data.data.toList = a.data.data.toList ++ b.data.data.toList := by
  have ha := Bytes.size_toNat a (by omega)
  have hb := Bytes.size_toNat b (by omega)
  have hn : (a.size + b.size).toNat = a.data.size + b.data.size := by
    rw [UInt64.toNat_add, ha, hb]
    omega
  unfold join
  rw [build_toList]
  apply List.ext_getElem
  · simp [hn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    have hi : i < a.data.size + b.data.size := by
      simp only [List.length_ofFn, hn] at h1
      exact h1
    have hi64 : i < 2 ^ 64 := by omega
    by_cases hlt : i < a.data.size
    · have hc : (UInt64.ofNat i < a.size) = True := by
        simp only [eq_iff_iff, iff_true]
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat hi64, ha]
        exact hlt
      simp only [hc, ↓reduceIte]
      rw [List.getElem_append_left (by simpa using hlt), get_toUInt8 a i hlt hi64]
    · have hc : (UInt64.ofNat i < a.size) = False := by
        simp only [eq_iff_iff, iff_false]
        rw [UInt64.lt_iff_toNat_lt, toNat_ofNat hi64, ha]
        exact hlt
      simp only [hc, ↓reduceIte]
      have hsub : UInt64.ofNat i - a.size = UInt64.ofNat (i - a.data.size) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, toNat_ofNat hi64, ha]; omega),
          toNat_ofNat hi64, ha, toNat_ofNat (by omega)]
      rw [hsub, List.getElem_append_right (by simpa using Nat.not_lt.mp hlt),
        get_toUInt8 b _ (by omega) (by omega)]
      simp

theorem slice_toList (b : Bytes) (start len : Nat) (h : start + len ≤ b.data.size)
    (h64 : b.data.size < 2 ^ 64) :
    (slice b (UInt64.ofNat start) (UInt64.ofNat len)).data.data.toList =
      (b.data.data.toList.drop start).take len := by
  unfold slice
  rw [build_toList]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data, toNat_ofNat (show len < 2 ^ 64 by omega)]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    have hi : i < len := by
      simp only [List.length_ofFn, toNat_ofNat (show len < 2 ^ 64 by omega)] at h1
      exact h1
    have hadd : UInt64.ofNat start + UInt64.ofNat i = UInt64.ofNat (start + i) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega),
        toNat_ofNat (by omega)]
      omega
    simp only [toNat_ofNat (show i < 2 ^ 64 by omega)]
    rw [show UInt64.ofNat i = UInt64.ofNat i from rfl, hadd,
      get_toUInt8 b _ (by omega) (by omega)]

/-! ## The argument -/

/-- The state of `argScan` after the first `k` bytes of `l`. -/
def argState (l : List UInt8) (k : Nat) : UInt64 × UInt64 × UInt64 :=
  (UInt64.ofNat ((l.take k).count 0), UInt64.ofNat (if (0 : UInt8) ∈ l.take k then l.idxOf 0 else 0),
    UInt64.ofNat k)

theorem argScan_eq (a : Bytes) (h : a.data.size < 2 ^ 63) :
    argScan a = argState a.data.data.toList a.data.size := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hlen : a.data.data.toList.length = a.data.size := by simp
  have key := LeanExe.Dialect.loop_induction (n := a.size)
    (init := ((0 : UInt64), (0 : UInt64), (0 : UInt64)))
    (f := fun i st => argStep st (a.get i))
    (fun k st => st = argState a.data.data.toList k) (by simp [argState])
    (by
      intro k st hk hst
      rw [hs] at hk
      subst hst
      have hget : a.get (UInt64.ofNat k) = (a.data.data.toList[k]'(by omega)).toUInt64 := by
        rw [Bytes.get_eq_getD, toNat_ofNat (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        rfl
      have htake : a.data.data.toList.take (k + 1) =
          a.data.data.toList.take k ++ [a.data.data.toList[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hcount : (a.data.data.toList.take k).count 0 ≤ k := by
        have := List.count_le_length (l := a.data.data.toList.take k) (a := 0)
        simp at this
        omega
      show argStep (argState _ k) (a.get (UInt64.ofNat k)) = argState _ (k + 1)
      rw [hget]
      unfold argStep argState
      rw [htake]
      generalize hb : a.data.data.toList[k]'(by omega) = b
      by_cases hb0 : b = 0
      · subst hb0
        have hz : ((0 : UInt8).toUInt64 == 0) = true := rfl
        rw [hz]
        simp only [↓reduceIte, List.count_append, List.count_singleton_self, List.mem_append,
          List.mem_singleton, or_true]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, toNat_ofNat (show (a.data.data.toList.take k).count 0 < 2 ^ 64
            by omega), toNat_ofNat (show (a.data.data.toList.take k).count 0 + 1 < 2 ^ 64 by omega)]
          simp
          omega
        · dsimp only
          by_cases hmem : (0 : UInt8) ∈ a.data.data.toList.take k
          · have hne : (a.data.data.toList.take k).count 0 ≠ 0 := List.count_pos_iff.mpr hmem |>.ne'
            have hneq : (UInt64.ofNat ((a.data.data.toList.take k).count 0) == 0) = false := by
              rw [beq_toNat, toNat_ofNat (by omega)]
              simpa using hne
            simp [hmem, hneq]
          · have hz' : (a.data.data.toList.take k).count 0 = 0 := List.count_eq_zero.mpr hmem
            have hidx : a.data.data.toList.idxOf 0 = k := by
              rw [← List.take_append_drop k a.data.data.toList, List.idxOf_append_of_notMem hmem,
                List.drop_eq_getElem_cons (by omega), hb]
              simp
              omega
            simp [hmem, hz', hidx]
        · apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
          simp only [UInt64.reduceToNat]
          omega
      · have hz : (b.toUInt64 == 0) = false := by
          have : b.toUInt64 ≠ 0 := fun e => hb0 (by
            have := congrArg UInt64.toNat e
            simp at this
            exact UInt8.toNat_inj.mp (by simpa using this))
          simpa using this
        rw [hz]
        have hb0' : (0 : UInt8) ≠ b := fun e => hb0 e.symm
        simp only [Bool.false_eq_true, ↓reduceIte, List.count_append, List.mem_append,
          List.mem_singleton, hb0', or_false]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp [List.count_singleton, hb0]
        · rfl
        · apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
          simp only [UInt64.reduceToNat]
          omega)
  rw [hs] at key
  exact key

/-! ## The streaming hash -/

theorem bytesOf_append (l₁ l₂ : List UInt8) :
    (bytesOf (l₁ ++ l₂)).data = (bytesOf l₁).data ++ (bytesOf l₂).data := by
  apply ByteArray.ext
  simp [bytesOf]

theorem bytesOf_size (l : List UInt8) : (bytesOf l).data.size = l.length := rfl

theorem bytesOf_data (b : Bytes) : (bytesOf b.data.data.toList).data = b.data := by
  apply ByteArray.ext
  simp [bytesOf]

/-- The state of `hashFile`'s loop after the reads returned `bytes`: their number, below `2^61`,
the bytes after their last whole block, and the implementation's hash value after their whole
blocks. -/
def Hashed (h : Words8) (carry : Bytes) (len : UInt64) (bytes : List UInt8) : Prop :=
  bytes.length < 2 ^ 61 ∧ len.toNat = bytes.length ∧
    carry.data.data.toList = bytes.drop (64 * (bytes.length / 64)) ∧
    h.toVec32 = blocksFold (bytesOf bytes).data (bytes.length / 64) SHS.SHA256.Impl.H256_256

theorem hashed_init : Hashed iv256 (Bytes.build 0 fun _ => 0) 0 [] := by
  refine ⟨by decide, rfl, ?_, rfl⟩
  rw [build_toList]
  rfl

/-- The bytes of `bytes` up to their last whole block, and those after it. -/
theorem split_whole (bytes : List UInt8) :
    bytes = bytes.take (64 * (bytes.length / 64)) ++ bytes.drop (64 * (bytes.length / 64)) :=
  (List.take_append_drop _ _).symm

theorem hashed_step {h : Words8} {carry : Bytes} {len : UInt64} {bytes : List UInt8}
    (hs : Hashed h carry len bytes) (c : Bytes) (hc : bytes.length + c.data.size < 2 ^ 61) :
    Hashed (update h (join carry c))
      (slice (join carry c) (((join carry c).size >>> 6) <<< 6)
        ((join carry c).size - (((join carry c).size >>> 6) <<< 6)))
      (len + c.size) (bytes ++ c.data.data.toList) := by
  obtain ⟨hlt, hlen, hcarry, hh⟩ := hs
  have hcl : carry.data.size = bytes.length - 64 * (bytes.length / 64) := by
    have := congrArg List.length hcarry
    simpa using this
  have hj := join_toList carry c (by omega)
  rw [hcarry] at hj
  generalize hJ : join carry c = J at hj ⊢
  have hJs : J.data.size = bytes.length - 64 * (bytes.length / 64) + c.data.size := by
    have := congrArg List.length hj
    simp only [List.length_append, List.length_drop, Array.length_toList,
      ByteArray.size_data] at this
    omega
  have hJn : J.size.toNat = J.data.size := Bytes.size_toNat J (by omega)
  have hwhole : (J.size >>> 6) <<< 6 = UInt64.ofNat (64 * (J.data.size / 64)) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hJn, toNat_ofNat (by omega)]
    simp only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMod,
      Nat.reducePow]
    omega
  have hrest : J.size - UInt64.ofNat (64 * (J.data.size / 64)) =
      UInt64.ofNat (J.data.size - 64 * (J.data.size / 64)) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hJn, toNat_ofNat (by omega)]; omega),
      hJn, toNat_ofNat (by omega), toNat_ofNat (by omega)]
  rw [hwhole, hrest]
  have hp : (bytes.length + c.data.size) / 64 =
      bytes.length / 64 + J.data.size / 64 := by
    rw [hJs]
    omega
  have hcl' : c.data.data.toList.length = c.data.size := by simp
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · rw [UInt64.toNat_add, hlen, Bytes.size_toNat c (by omega)]
    simp
    omega
  · rw [slice_toList J _ _ (by omega) (by omega), hj, List.length_append, hcl', hp,
      List.take_of_length_le (by simp only [List.length_drop, List.length_append, hcl']; omega),
      ← List.drop_append_of_le_length (by omega), List.drop_drop]
    congr 1
    omega
  · rw [update_toVec32 _ _ (by omega), hh, List.length_append, hcl', hp]
    have hpre : (bytesOf (bytes.take (64 * (bytes.length / 64)))).data.size =
        64 * (bytes.length / 64) := by
      rw [bytesOf_size, List.length_take]
      omega
    have hsplit : (bytesOf (bytes ++ c.data.data.toList)).data =
        (bytesOf (bytes.take (64 * (bytes.length / 64)))).data ++ J.data := by
      rw [← bytesOf_data J, hj, ← bytesOf_append, ← List.append_assoc, ← split_whole]
    have hold : (bytesOf bytes).data = (bytesOf (bytes.take (64 * (bytes.length / 64)))).data ++
        (bytesOf (bytes.drop (64 * (bytes.length / 64)))).data := by
      rw [← bytesOf_append, ← split_whole]
    rw [hsplit, blocksFold_append _ J.data _ hpre, hold,
      blocksFold_append_tail _ _ _ (by rw [hpre])]

/-- The digest that `finish` gives from the state after the bytes `bytes` is the
implementation's SHA-256 of them. -/
theorem hashed_finish {h : Words8} {carry : Bytes} {len : UInt64} {bytes : List UInt8}
    (hs : Hashed h carry len bytes) :
    (finish h carry len).bytes 32 = SHS.SHA256.Impl.sha256 (bytesOf bytes).data := by
  obtain ⟨hlt, hlen, hcarry, hh⟩ := hs
  have hpre : (bytesOf (bytes.take (64 * (bytes.length / 64)))).data.size =
      64 * (bytes.length / 64) := by
    rw [bytesOf_size, List.length_take]
    omega
  have hcl : carry.data.size = bytes.length - 64 * (bytes.length / 64) := by
    have := congrArg List.length hcarry
    simpa using this
  have hold : (bytesOf bytes).data = (bytesOf (bytes.take (64 * (bytes.length / 64)))).data ++
      carry.data := by
    rw [← bytesOf_data carry, hcarry, ← bytesOf_append, ← split_whole]
  rw [hold] at hh ⊢
  rw [blocksFold_append_tail _ _ _ (by rw [hpre])] at hh
  exact finish_bytes _ _ hpre h hh carry len (by rw [hpre, hcl]; omega) (by omega)

/-! ## The reads -/

theorem fdRead_accepted (fd : UInt64) (hfd : fd.toNat < 2 ^ 32) :
    Call.fdRead.reject [.word fd, .space 65536] = 0 := by
  have h : fd.toNat < 4294967296 := hfd
  simp [Call.reject, rejectArgs, Call.fdRead, Param.takesArg, Param.reject, Arg.capacity,
    Arg.value, h]

/-- A read of 65,536 bytes returns an errno of at most 76 and, with errno 0, at most 65,536
bytes: those of `returned`. -/
theorem read_reply {World : Type} {host : Host World} {world after : World} {fd errno : UInt64}
    {committed : List Bytes}
    (permitted : host.sys world .fdRead [.word fd, .space 65536] (.returned errno committed)
      after) :
    errno.toNat ≤ 76 ∧ (errno = 0 →
      ((sysReply errno committed).prefixBytes 0 ((sysReply errno committed).word 1)).data.size ≤
        65536 ∧
      ((sysReply errno committed).prefixBytes 0
        ((sysReply errno committed).word 1)).data.data.toList = returned committed) := by
  obtain ⟨shape, valid⟩ := host.sys_bound permitted
  refine ⟨valid, fun zero => ?_⟩
  subst zero
  have hsizes : committed.map (·.data.size) = [65536, 4] := shape
  rcases committed with _ | ⟨buffer, _ | ⟨count, _ | ⟨_, _⟩⟩⟩ <;> simp at hsizes
  refine ⟨?_, rfl⟩
  simp only [sysReply, Reply.prefixBytes, Reply.bytes, ↓reduceIte, List.getElem?_cons_zero,
    Option.getD_some, ByteArray.size_extract]
  omega

/-- A loop from a state at which the test fails returns that state and has no event. -/
theorem loop_done {World σ : Type} {host : Host World} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {s : σ} (stops : ∀ i, test i s = false) :
    ∀ {remaining index : Nat} {world : World} {trace : List Event} {outcome : Outcome σ}
      {final : World},
      LoopExec host remaining index s test step .pure world trace outcome final →
      trace = [] ∧ outcome = .returned s
  | 0, _, _, _, _, _, run => by
    cases run with
    | zero next => exact ⟨(exec_pure_shape next).1, (exec_pure_shape next).2.1⟩
  | _ + 1, _, _, _, _, _, run => by
    cases run with
    | stop _ next => exact ⟨(exec_pure_shape next).1, (exec_pure_shape next).2.1⟩
    | next test => rw [stops] at test; cases test
    | exit test => rw [stops] at test; cases test
    | trap test => rw [stops] at test; cases test

/-- The state of `hashFile`'s loop. -/
abbrev HashState := Words8 × Bytes × UInt64 × Bool × Bool

/-- A step of `hashFile`'s loop on the descriptor `fd`, written out. -/
def HashStep (fd : UInt64) (step : UInt64 → HashState → Action HashState) : Prop :=
  ∀ i (s : HashState), step i s = .sys .fdRead [.word fd, .space 65536] fun reply =>
    if reply.errno != 0 then .pure (s.1, s.2.1, s.2.2.1, false, true)
    else if (reply.prefixBytes 0 (reply.word 1)).size == 0 then
      .pure (s.1, s.2.1, s.2.2.1, true, true)
    else .pure (update s.1 (join s.2.1 (reply.prefixBytes 0 (reply.word 1))),
      slice (join s.2.1 (reply.prefixBytes 0 (reply.word 1)))
        (((join s.2.1 (reply.prefixBytes 0 (reply.word 1))).size >>> 6) <<< 6)
        ((join s.2.1 (reply.prefixBytes 0 (reply.word 1))).size -
          (((join s.2.1 (reply.prefixBytes 0 (reply.word 1))).size >>> 6) <<< 6)),
      s.2.2.1 + (reply.prefixBytes 0 (reply.word 1)).size, false, false)

theorem size_beq_zero (b : Bytes) (h : b.data.size < 2 ^ 64) :
    (b.size == 0) = decide (b.data.data.toList = []) := by
  rw [beq_toNat, Bytes.size_toNat b h]
  by_cases e : b.data.size = 0
  · have : b.data.data.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using e
    simp [e, this]
  · have : b.data.data.toList ≠ [] := by
      intro hl
      apply e
      have := congrArg List.length hl
      simpa using this
    simp [e, this]

/-- The loop of `hashFile` on `fd` from the state after the bytes `bytes`, with `remaining`
passes, never exits, and when it returns it made the reads of `FileReads`, its state is the state
after the bytes that they returned, and its flag holds when the last read returned no bytes. -/
theorem hash_loop {World : Type} {host : Host World} {fd : UInt64}
    {test : UInt64 → HashState → Bool} {step : UInt64 → HashState → Action HashState}
    (tested : ∀ i s, test i s = !s.2.2.2.2) (stepped : HashStep fd step)
    (hfd : fd.toNat < 2 ^ 32) :
    ∀ (remaining index : Nat) (h : Words8) (carry : Bytes) (len : UInt64) (bytes : List UInt8)
      {world : World} {trace : List Event} {outcome : Outcome HashState} {final : World},
      Hashed h carry len bytes → bytes.length + 65536 * remaining < 2 ^ 61 →
      LoopExec host remaining index (h, carry, len, false, false) test step .pure world trace
        outcome final →
      (∀ c, outcome ≠ .exited c) ∧
      ∀ s, outcome = .returned s → ∃ more ending, FileReads fd remaining trace more ending ∧
        Hashed s.1 s.2.1 s.2.2.1 (bytes ++ more) ∧ s.2.2.2.1 = decide (ending = .eof)
  | 0, _, h, carry, len, bytes, _, _, _, _, hs, _, run => by
    cases run with
    | zero next =>
      obtain ⟨rfl, rfl, -⟩ := exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
      cases e
      exact ⟨[], .cut, .cut, by simpa using hs, rfl⟩
  | remaining + 1, index, h, carry, len, bytes, _, _, _, _, hs, hbound, run => by
    cases run with
    | stop test next => simp [tested] at test
    | trap _ _ => exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
    | exit _ step =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd hfd) fits
      | sys_return _ _ next =>
        beta_reduce at next
        split at next
        · cases next
        · split at next <;> cases next
    | next _ step rest =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd hfd) fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        obtain ⟨-, replied⟩ := read_reply permitted
        beta_reduce at next
        split at next
        · rename_i nonzero
          have hne : errno ≠ 0 := by simpa [sysReply] using nonzero
          obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
          cases hs'
          obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
          refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
          cases e
          exact ⟨[], .failed errno, .failed hne, by simpa using hs, rfl⟩
        · rename_i zero
          have hz : errno = 0 := by simpa [sysReply] using zero
          subst hz
          obtain ⟨hsmall, hbytes⟩ := replied rfl
          generalize hc : (sysReply 0 committed).prefixBytes 0 ((sysReply 0 committed).word 1) = c
            at next hsmall hbytes
          rw [size_beq_zero c (by omega)] at next
          split at next
          · rename_i empty
            have he : c.data.data.toList = [] := by simpa using empty
            obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
            cases hs'
            obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
            refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
            cases e
            exact ⟨[], .eof, .eof (by rw [← hbytes, he]), by simpa using hs, rfl⟩
          · rename_i some
            have hne : c.data.data.toList ≠ [] := by simpa using some
            obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
            cases hs'
            have hcsize : c.data.size ≤ 65536 := hsmall
            obtain ⟨noExit, returned⟩ := hash_loop tested stepped hfd remaining (index + 1) _ _ _
              (bytes ++ c.data.data.toList) (hashed_step hs c (by omega))
              (by simp; omega) rest
            refine ⟨noExit, fun s e => ?_⟩
            obtain ⟨more, ending, reads, hashed, flag⟩ := returned s e
            refine ⟨c.data.data.toList ++ more, ending, ?_, by simpa using hashed, flag⟩
            rw [hbytes]
            exact .more (by rw [← hbytes]; exact hne) reads

/-- The state of `readManifest`'s loop. -/
abbrev ManifestState := Bytes × UInt64 × Bool

/-- A step of `readManifest`'s loop on the descriptor `fd`, written out. -/
def ManifestStep (fd : UInt64) (step : UInt64 → ManifestState → Action ManifestState) : Prop :=
  ∀ i (s : ManifestState), step i s = .sys .fdRead [.word fd, .space 65536] fun reply =>
    if reply.errno != 0 then .pure (s.1, reply.errno, true)
    else if (reply.prefixBytes 0 (reply.word 1)).size == 0 then .pure (s.1, 0, true)
    else .pure (join s.1 (reply.prefixBytes 0 (reply.word 1)), 0,
      1048576 < (join s.1 (reply.prefixBytes 0 (reply.word 1))).size)

/-- The errno that ends a sequence of reads: the errno of a failed read, and 0 otherwise. -/
def endErrno : Ending → UInt64
  | .failed e => e
  | _ => 0

/-- The loop of `readManifest` on `fd` from the bytes `held`, at most 1,048,576 of them, with more
passes than bytes may still be added, never exits, and when it returns it made the reads of
`ManifestReads`, holds the bytes that they collected, at most 65,536 more than 1,048,576, and holds
the errno of a read that failed, or 0. -/
theorem manifest_loop {World : Type} {host : Host World} {fd : UInt64}
    {test : UInt64 → ManifestState → Bool} {step : UInt64 → ManifestState → Action ManifestState}
    (tested : ∀ i s, test i s = !s.2.2) (stepped : ManifestStep fd step)
    (hfd : fd.toNat < 2 ^ 32) :
    ∀ (remaining index : Nat) (held : Bytes)
      {world : World} {trace : List Event} {outcome : Outcome ManifestState} {final : World},
      held.data.size ≤ 1048576 → 1048576 - held.data.size < remaining →
      LoopExec host remaining index (held, 0, false) test step .pure world trace outcome final →
      (∀ c, outcome ≠ .exited c) ∧
      ∀ s, outcome = .returned s → ∃ ending, ManifestReads fd held.data.data.toList trace
        s.1.data.data.toList ending ∧ s.1.data.size ≤ 1048576 + 65536 ∧ s.2.1 = endErrno ending
  | 0, _, _, _, _, _, _, _, hrem, _ => by omega
  | remaining + 1, index, held, _, _, _, _, hheld, hrem, run => by
    cases run with
    | stop test next => simp [tested] at test
    | trap _ _ => exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
    | exit _ step =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd hfd) fits
      | sys_return _ _ next =>
        beta_reduce at next
        split at next
        · cases next
        · split at next <;> cases next
    | next _ step rest =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd hfd) fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        obtain ⟨-, replied⟩ := read_reply permitted
        beta_reduce at next
        split at next
        · rename_i nonzero
          have hne : errno ≠ 0 := by simpa [sysReply] using nonzero
          obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
          cases hs'
          obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
          refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
          cases e
          exact ⟨.failed errno, .failed hne, by dsimp only; omega,
            by simp [sysReply, hne, endErrno]⟩
        · rename_i zero
          have hz : errno = 0 := by simpa [sysReply] using zero
          subst hz
          obtain ⟨hsmall, hbytes⟩ := replied rfl
          generalize hc : (sysReply 0 committed).prefixBytes 0 ((sysReply 0 committed).word 1) = c
            at next hsmall hbytes
          rw [size_beq_zero c (by omega)] at next
          split at next
          · rename_i empty
            have he : c.data.data.toList = [] := by simpa using empty
            obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
            cases hs'
            obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
            refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
            cases e
            exact ⟨.eof, .eof (by rw [← hbytes, he]), by dsimp only; omega, rfl⟩
          · rename_i some
            have hne : c.data.data.toList ≠ [] := by simpa using some
            have hcsize : c.data.size ≤ 65536 := hsmall
            have hcpos : 0 < c.data.size := by
              rcases Nat.eq_zero_or_pos c.data.size with h0 | h0
              · exfalso
                apply hne
                apply List.eq_nil_of_length_eq_zero
                simpa using h0
              · exact h0
            obtain ⟨rfl, hs', -⟩ := exec_pure_shape next
            cases hs'
            have hj := join_toList held c (by omega)
            have hjs : (join held c).data.size = held.data.size + c.data.size := by
              have := congrArg List.length hj
              simpa using this
            have hjn : (join held c).size.toNat = (join held c).data.size :=
              Bytes.size_toNat _ (by omega)
            by_cases large : 1048576 < (join held c).data.size
            · have hflag : decide (1048576 < (join held c).size) = true :=
                decide_eq_true (by rw [UInt64.lt_iff_toNat_lt, hjn]; exact large)
              rw [hflag] at rest
              obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
              refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
              cases e
              refine ⟨.cut, ?_, by dsimp only; omega, rfl⟩
              dsimp only
              rw [hj, hbytes, List.append_nil]
              exact .over (by rw [← hbytes]; exact hne)
                (by rw [List.length_append, ← hbytes]; simp; omega)
            · have hflag : decide (1048576 < (join held c).size) = false :=
                decide_eq_false (by rw [UInt64.lt_iff_toNat_lt, hjn]; exact large)
              rw [hflag] at rest
              obtain ⟨noExit, returned⟩ := manifest_loop tested stepped hfd remaining (index + 1)
                (join held c) (by omega) (by omega) rest
              refine ⟨noExit, fun s e => ?_⟩
              obtain ⟨ending, reads, hsize, herr⟩ := returned s e
              refine ⟨ending, ?_, hsize, herr⟩
              rw [hj, hbytes] at reads
              exact .more (by rw [← hbytes]; exact hne)
                (by rw [List.length_append, ← hbytes]; simp; omega) reads

/-! ## The argument -/

theorem count_append_cons (p r : List UInt8) (b : UInt8) :
    (p ++ b :: r).count 0 = p.count 0 + (if b = 0 then 1 else 0) + r.count 0 := by
  simp [List.count_append, List.count_cons]
  split <;> omega

/-- The buffer of one argument after the program name holds two zero bytes, the last one at its
end, and the argument is the bytes between them. -/
theorem oneArgument_shape {l name : List UInt8} (h : OneArgument l name) :
    l.count 0 = 2 ∧ l.getLastD 1 = 0 ∧ l.idxOf 0 + name.length + 2 = l.length ∧
      name = (l.drop (l.idxOf 0 + 1)).take (l.length - l.idxOf 0 - 2) := by
  obtain ⟨program, rfl, hp, hn⟩ := h
  have hidx : (program ++ 0 :: (name ++ [0])).idxOf 0 = program.length := by
    rw [List.idxOf_append_of_notMem hp, List.idxOf_cons_self]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [count_append_cons, List.count_append, List.count_eq_zero.mpr hp,
      List.count_eq_zero.mpr hn]
    simp
  · have e : program ++ 0 :: (name ++ [0]) = (program ++ 0 :: name) ++ [0] := by simp
    rw [e, List.getLastD_eq_getLast?, List.getLast?_concat]
    rfl
  · rw [hidx, List.length_append, List.length_cons, List.length_append, List.length_singleton]
    omega
  · rw [hidx]
    have e : program ++ 0 :: (name ++ [0]) = (program ++ [0]) ++ (name ++ [0]) := by simp
    rw [e, List.drop_left' (by simp), List.take_left' (by simp <;> omega)]

/-- A buffer with two zero bytes, the last one at its end, holds one argument. -/
theorem oneArgument_of {l : List UInt8} (hc : l.count 0 = 2) (hl : l.getLastD 1 = 0) :
    OneArgument l ((l.drop (l.idxOf 0 + 1)).take (l.length - l.idxOf 0 - 2)) := by
  have hmem : (0 : UInt8) ∈ l := List.count_pos_iff.mp (by omega)
  have hidx := List.idxOf_lt_length_iff.mpr hmem
  have hsplit : l = l.take (l.idxOf 0) ++ 0 :: l.drop (l.idxOf 0 + 1) := by
    conv_lhs => rw [← List.take_append_drop (l.idxOf 0) l]
    rw [List.drop_eq_getElem_cons hidx, List.getElem_idxOf hidx]
  have hpre : (0 : UInt8) ∉ l.take (l.idxOf 0) := fun h =>
    lt_irrefl _ ((List.mem_take_iff_idxOf_lt hmem).mp h)
  generalize hr : l.drop (l.idxOf 0 + 1) = r at hsplit
  have hrc : r.count 0 = 1 := by
    have := hc
    rw [hsplit, count_append_cons, List.count_eq_zero.mpr hpre] at this
    simp at this
    omega
  have hrne : r ≠ [] := by
    intro e
    rw [e] at hrc
    simp at hrc
  have hrl : r.getLastD 1 = 0 := by
    rw [hsplit] at hl
    rw [List.getLastD_eq_getLast?] at hl ⊢
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at hl
    rw [List.getLast?_cons] at hl
    cases e : r.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp e) hrne
    | some x => rw [e] at hl; simpa using hl
  have hrsplit : r = r.dropLast ++ [0] := by
    conv_lhs => rw [← List.dropLast_append_getLast hrne]
    congr 2
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hrne] at hrl
    simpa using hrl
  have hname : (0 : UInt8) ∉ r.dropLast := by
    intro hm
    have := hrc
    rw [hrsplit, List.count_append, List.count_singleton_self] at this
    have := List.count_pos_iff.mpr hm
    omega
  have hlen : l.length = l.idxOf 0 + 1 + r.length := by
    rw [← hr, List.length_drop]
    omega
  refine ⟨l.take (l.idxOf 0), ?_, hpre, ?_⟩
  · have htake : r.take (l.length - l.idxOf 0 - 2) = r.dropLast := by
      rw [List.dropLast_eq_take]
      congr 1
      omega
    rw [htake]
    conv_lhs => rw [hsplit, hrsplit]
  · have htake : r.take (l.length - l.idxOf 0 - 2) = r.dropLast := by
      rw [List.dropLast_eq_take]
      congr 1
      omega
    rw [htake]
    exact hname

theorem getLastD_eq_get (a : Bytes) (h : a.data.size < 2 ^ 32) (hpos : 0 < a.data.size) :
    a.get (a.size - 1) = (a.data.data.toList.getLastD 1).toUInt64 := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hi : (a.size - 1).toNat = a.data.size - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hs]; simp; omega), hs]
    rfl
  have hne : a.data.data.toList ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [Array.length_toList, ByteArray.size_data]
    exact hpos
  rw [Bytes.get_eq_getD, hi, List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne,
    List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- The program's test of the argument buffer refuses it exactly when it does not hold one
argument after the program name, and otherwise the slice it opens is that argument. -/
theorem argument_cases (a : Bytes) (h : a.data.size < 2 ^ 32) :
    (((argScan a).1 != 2 || a.get (a.size - 1) != 0) = true →
      ∀ name, ¬ OneArgument a.data.data.toList name) ∧
    (((argScan a).1 != 2 || a.get (a.size - 1) != 0) = false →
      OneArgument a.data.data.toList
        (slice a ((argScan a).2.1 + 1) (a.size - (argScan a).2.1 - 2)).data.data.toList) := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hlen : a.data.data.toList.length = a.data.size := by simp
  rw [argScan_eq a (by omega)]
  unfold argState
  generalize hl : a.data.data.toList = l at hlen
  rw [List.take_of_length_le (by omega)]
  have hcl : l.count 0 ≤ l.length := List.count_le_length
  constructor
  · intro hrefuse name hone
    obtain ⟨hc, hlast, -, -⟩ := oneArgument_shape hone
    have hpos : 0 < a.data.size := by
      rw [← hlen]
      rcases l with _ | ⟨x, l⟩
      · simp at hc
      · simp
    rw [getLastD_eq_get a h hpos, hl, hlast] at hrefuse
    simp only [hc] at hrefuse
    simp at hrefuse
  · intro haccept
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at haccept
    obtain ⟨hc2, hlast0⟩ := haccept
    have hc : l.count 0 = 2 := by
      have := congrArg UInt64.toNat hc2
      rw [toNat_ofNat (by omega)] at this
      simpa using this
    have hpos : 0 < a.data.size := by
      rw [← hlen]
      rcases l with _ | ⟨x, l⟩
      · simp at hc
      · simp
    rw [getLastD_eq_get a h hpos, hl] at hlast0
    have hlast : l.getLastD 1 = 0 := by
      have := congrArg UInt64.toNat hlast0
      simp at this
      exact UInt8.toNat_inj.mp (by simpa using this)
    have hmem : (0 : UInt8) ∈ l := List.count_pos_iff.mp (by omega)
    have hone := oneArgument_of hc hlast
    obtain ⟨-, -, hsum, -⟩ := oneArgument_shape hone
    simp only [hmem, ↓reduceIte]
    have hi : (UInt64.ofNat (l.idxOf 0) + 1) = UInt64.ofNat (l.idxOf 0 + 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
      simp
      omega
    have hn : a.size - UInt64.ofNat (l.idxOf 0) - 2 = UInt64.ofNat (l.length - l.idxOf 0 - 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, hs, toNat_ofNat (by omega)]; omega), hs,
            toNat_ofNat (by omega)]
          simp
          omega),
        UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, hs, toNat_ofNat (by omega)]; omega),
        hs, toNat_ofNat (by omega), toNat_ofNat (by omega)]
      simp
      omega
    rw [hi, hn, slice_toList a _ _ (by omega) (by omega), hl]
    exact hone

/-! ## The runs of the reads -/

theorem fileReads_eq : fileReads.toNat = 35184372088831 := rfl

/-- A run of `hashFile` on `fd` never exits, and when it returns, it made the reads of
`FileReads` within `2^45 - 1` reads, its digest is the implementation's SHA-256 of the bytes that
they returned, and its flag holds when the last read returned no bytes. -/
theorem hashFile_run {World : Type} {host : Host World} {fd : UInt64} (hfd : fd.toNat < 2 ^ 32)
    {world final : World} {trace : List Event} {outcome : Outcome (Words4 × Bool)}
    (run : Exec host (hashFile ⟨fd⟩) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧
      ∀ r, outcome = .returned r → ∃ bytes ending,
        FileReads fd 35184372088831 trace bytes ending ∧ bytes.length < 2 ^ 61 ∧
        r.1.bytes 32 = SHS.SHA256.Impl.sha256 (bytesOf bytes).data ∧
        r.2 = decide (ending = .eof) := by
  unfold hashFile at run
  obtain ⟨after, first, middle, rest, loopRun, cont, rfl⟩ := Exec.unbind _ run
  cases loopRun with
  | loop loopRun =>
  rw [fileReads_eq] at loopRun
  obtain ⟨noExit, returned⟩ := hash_loop (fun _ _ => rfl) (fun _ _ => rfl) hfd _ 0 _ _ _ []
    hashed_init (by norm_num) loopRun
  cases middle with
  | exited c => exact absurd rfl (noExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
  | returned s =>
    obtain ⟨more, ending, reads, hashed, flag⟩ := returned s rfl
    obtain ⟨rfl, rfl, -⟩ := exec_pure_shape cont
    refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
    cases e
    simp only [List.nil_append] at hashed
    exact ⟨more, ending, by simpa using reads, hashed.1, hashed_finish hashed, flag⟩

/-- A run of `readManifest` on `fd` never exits, and when it returns, it made the reads of
`ManifestReads` from no bytes, its bytes are those that they collected, at most 65,536 more than
1,048,576, and its errno is that of a failed read, or 0. -/
theorem readManifest_run {World : Type} {host : Host World} {fd : UInt64}
    (hfd : fd.toNat < 2 ^ 32) {world final : World} {trace : List Event}
    {outcome : Outcome (Bytes × UInt64)}
    (run : Exec host (readManifest ⟨fd⟩) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧
      ∀ r, outcome = .returned r → ∃ ending,
        ManifestReads fd [] trace r.1.data.data.toList ending ∧
        r.1.data.size ≤ 1048576 + 65536 ∧ r.2 = endErrno ending := by
  unfold readManifest at run
  obtain ⟨after, first, middle, rest, loopRun, cont, rfl⟩ := Exec.unbind _ run
  cases loopRun with
  | loop loopRun =>
  have hcount : (manifestLimit + 2).toNat = 1048578 := rfl
  rw [hcount] at loopRun
  have hheld : (Bytes.build 0 fun _ => 0).data.size = 0 := by simp
  obtain ⟨noExit, returned⟩ := manifest_loop (fun _ _ => rfl) (fun _ _ => rfl) hfd _ 0 _
    (by omega) (by omega) loopRun
  cases middle with
  | exited c => exact absurd rfl (noExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
  | returned s =>
    obtain ⟨ending, reads, hsize, herr⟩ := returned s rfl
    obtain ⟨rfl, rfl, -⟩ := exec_pure_shape cont
    refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
    cases e
    have h0 : (Bytes.build 0 fun _ => 0).data.data.toList = [] := by
      rw [build_toList]
      rfl
    rw [h0] at reads
    exact ⟨ending, by simpa using reads, hsize, herr⟩

/-! ## The opens -/

theorem pathOpen_accepted (name : Bytes) (h : name.data.size < 2 ^ 32) :
    Call.pathOpen.reject [.word 3, .word 1, .bytes name, .word 0, .word 2, .word 0, .word 0] = 0 := by
  have h' : name.data.size < 4294967296 := h
  simp [Call.reject, rejectArgs, Call.pathOpen, Param.takesArg, Param.reject, Arg.value,
    Arg.length, h']
  decide

theorem fdClose_accepted (fd : UInt64) (hfd : fd.toNat < 2 ^ 32) :
    Call.fdClose.reject [.word fd] = 0 := by
  have h : fd.toNat < 4294967296 := hfd
  simp [Call.reject, rejectArgs, Call.fdClose, Param.takesArg, Param.reject, Arg.value, h]

/-- The events and the result of a run of `withOpen` under descriptor 3 with the flag
`symlink_follow`, the right `fd_read`, an error continuation that returns `fallback errno`, and a
body that never exits: the open's event, and, when it returned errno 0, the body's events and the
close's event. -/
theorem withOpen_run {World α : Type} {host : Host World} {name : Bytes}
    (hname : name.data.size < 2 ^ 32) {fallback : UInt64 → α} {body : Handle → Action α}
    {world final : World} {trace : List Event} {outcome : Outcome (α × UInt64)}
    (bodyNoExit : ∀ fd w t (o : Outcome α) f, Exec host (body ⟨fd⟩) w t o f → ∀ c, o ≠ .exited c)
    (run : Exec host (withOpen .preopened 1 name 0 2 0 0 (fun errno => pure (fallback errno)) body)
      world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → ∃ errno outputs,
      (errno ≠ 0 ∧ trace = [.sys .pathOpen [.word 3, .word 1, .bytes name, .word 0, .word 2,
        .word 0, .word 0] (.returned errno outputs)] ∧ r = (fallback errno, 0)) ∨
      (errno = 0 ∧ (openedDescriptor outputs).toNat < 2 ^ 32 ∧ ∃ events after closing closeErrno
          committed, trace = .sys .pathOpen [.word 3, .word 1, .bytes name, .word 0, .word 2,
            .word 0, .word 0] (.returned 0 outputs) :: events ++
            [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)] ∧
        Exec host (body ⟨openedDescriptor outputs⟩) after events (.returned r.1) closing ∧
        r.2 = closeErrno) := by
  unfold withOpen at run
  cases run with
  | sys_reject fits => exact absurd (pathOpen_accepted name hname) fits
  | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
    by_cases zero : errno = 0
    · subst zero
      have small := openedDescriptor_lt rfl ⟨_, (host.sys_bound permitted).1⟩
      have hReply : sysReply 0 committed = ⟨0, committed⟩ := rfl
      simp only [hReply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
      obtain ⟨closing, first, middle, rest, bodyRun, closeRun, rfl⟩ := Exec.unbind _ next
      have noExit := bodyNoExit _ _ _ _ _ bodyRun
      cases middle with
      | exited c => exact absurd rfl (noExit c)
      | trapped m =>
        obtain ⟨-, rfl, -⟩ := closeRun
        exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
      | returned value =>
        simp only [Continue] at closeRun
        cases closeRun with
        | sys_reject fits => exact absurd (fdClose_accepted _ small) fits
        | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
        | @sys_return _ _ _ _ _ _ _ _ _ closeErrno closeCommitted _ _ last =>
          obtain ⟨rfl, rfl, -⟩ := exec_pure_shape last
          refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
          cases e
          exact ⟨0, committed, .inr ⟨rfl, small, first, _, _, closeErrno, closeCommitted, rfl,
            bodyRun, rfl⟩⟩
    · have hReply : sysReply errno committed = ⟨errno, []⟩ := by simp [sysReply, zero]
      have off : ((errno != 0) = true) = True := eq_true (bne_iff_ne.mpr zero)
      simp only [hReply, off, ↓reduceIte] at next
      have hpure : Action.bind (pure (fallback errno)) (fun result => Action.pure (result, (0 : UInt64))) =
          Action.pure (fallback errno, 0) := rfl
      rw [hpure] at next
      obtain ⟨rfl, rfl, -⟩ := exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
      cases e
      exact ⟨errno, committed, .inl ⟨zero, rfl, rfl⟩⟩

end Demos.ManifestCheck
