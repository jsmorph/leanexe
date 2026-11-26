module

public import Verified.ShimA64.Open
public import LeanExe.A64.Proof.WasiFilestat

@[expose] public section

/-!
The stub of `fd_filestat_get` of `LeanExe/A64/WasiFiles.lean` against the shim's
`filestatInvoke`.  `sysCall_statxEvent` evaluates the layer's rule for the stub's `statx`, whose
path, a zero byte, and record, 256 zero bytes, the stub writes into the scratch before the call,
as `step_statx` requires.  `filestat_reply` relates the stub's conversions of the `statx` record,
`stampsValue`, and the words that it stores, `filestatWords`, to `filestatReply` of the record:
the trap for nanoseconds of `10^9` or more, errno 61 for a time of `2^64` nanoseconds or more,
and otherwise the bytes of `filestatBytes`.  `stampValue_eq` states the stub's test against the
quotient of `UDIV` as the specification's test of the time's range, `leValue_mod` the low bytes of
a word as its value modulo a power of 256, and `fileType_eq` the stub's lookup in
`filetypeTable` as `filetypeOf`.

`filestatStub_run` follows the stub from its entry to its end on a platform `P` for every store
and arguments, as `StubEnd` states, and `filestatStub_sim` proves `Machine.StubSim` on
`shimMachine` from it: the stub's writes of the scratch lie from the path buffer at byte 1,080 to
the end of the `statx` record at byte 1,344, above the scratch's first 1,040 bytes, so
`ScratchHolds` holds after the call, which neither opens nor closes a descriptor.  `fileStub_sim`
takes the case of each stub of `fileStubs`, those of `path_open`, `fd_close`, `fd_read`,
`fd_write`, and `fd_filestat_get`, from its simulation theorem.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## The call of `statx` -/

theorem table_statx :
    Linux.table.find? (fun c => c.arm64 == 291) = some Linux.statxCall := rfl

theorem argWords_five {s : State} {c : Linux.Call} (hc : c.words = 5) :
    argWords s c = [s.x 0, s.x 1, s.x 2, s.x 3, s.x 4] := by
  simp only [argWords, hc]
  rfl

/-- `statx` of the path buffer and the `statx` record of the layout `L`, which hold a zero byte
and zeros, gives `statxEvent` and writes the reply's bytes into the record. -/
theorem sysCall_statxEvent {R : Linux.Replies} {P : Platform} {p : Proc} (L : ShimLayout)
    (h1 : p.core.x 1 = L.path) (h2 : p.core.x 2 = statxFlags) (h3 : p.core.x 3 = statxMask)
    (h4 : p.core.x 4 = L.statx) (empty : p.core.mem L.path = 0)
    (cleared : readList p.core.mem L.statx 256 = List.replicate 256 0)
    (mappedPath : P.mapped L.path 1 = true) (mapped : P.mapped L.statx 256 = true) :
    sysCall R P Linux.statxCall p = some (p.ret (R p.trace.length).ret
      (writeList p.core.mem L.statx ((List.range 256).map (R p.trace.length).bytes))
      (.sys (statxEvent L (p.core.x 0) (R p.trace.length)))) := by
  unfold sysCall
  rw [argWords_five (show Linux.statxCall.words = 5 from rfl), h1, h2, h3, h4,
    step_statx (a64Memory P) p.core.mem L (p.core.x 0) _ empty mappedPath mapped
      (by rw [readBytes_a64]; exact cleared), writeBytes_a64]
  rfl

/-! ## Words and bytes -/

theorem zeroWords_writeList : ∀ (n : Nat) (m : UInt64 → UInt8) (a : UInt64),
    zeroWords m a n = writeList m a (List.replicate (8 * n) 0)
  | 0, _, _ => rfl
  | n + 1, m, a => by
    have hz : (List.range 8).map (LeanExe.A64.byteOf 0) = List.replicate 8 0 := by decide
    rw [zeroWords, zeroWords_writeList n, store64_writeList, hz,
      show 8 * (n + 1) = 8 + 8 * n by omega, List.replicate_add, writeList_append]
    rfl

theorem storedWords_writeList : ∀ (ws : List UInt64) (m : UInt64 → UInt8) (a : UInt64),
    storedWords m a ws =
      writeList m a (ws.flatMap fun w => (List.range 8).map (LeanExe.A64.byteOf w))
  | [], _, _ => rfl
  | w :: ws, m, a => by
    rw [storedWords, storedWords_writeList ws, store64_writeList, List.flatMap_cons,
      writeList_append]
    rfl

/-- The eight bytes of a word as Talos's `byteOf` of its value. -/
theorem bytes_word (w : UInt64) :
    (List.range 8).map (Verified.Wasi.byteOf w.toNat) =
      (List.range 8).map (LeanExe.A64.byteOf w) := by
  have h := leBytes_eight (UInt64.toNat_lt w)
  rw [UInt64.ofNat_toNat] at h
  rw [← h]
  simp [leBytes, bytesOfList]

/-- `b + 256 X` modulo `256 M` for a byte `b`. -/
theorem byte_add_mod {b X M : Nat} (hb : b < 256) (hM : 0 < M) :
    (b + 256 * X) % (M * 256) = b + 256 * (X % M) := by
  have hd := Nat.div_add_mod X M
  have e : b + 256 * X = (b + 256 * (X % M)) + (M * 256) * (X / M) := by
    rw [Nat.mul_right_comm M 256 (X / M)]
    generalize M * (X / M) = Q at hd ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt X hM
  omega

/-- The value of bytes modulo `256^k` is the value of their first `k`. -/
theorem leValue_mod : ∀ (k : Nat) (bs : List UInt8),
    Linux.leValue bs % 256 ^ k = Linux.leValue (bs.take k)
  | 0, bs => by rw [Nat.pow_zero, Nat.mod_one, List.take_zero]; rfl
  | _ + 1, [] => by simp [Linux.leValue]
  | k + 1, b :: bs => by
    simp only [Linux.leValue, List.take_succ_cons]
    rw [← leValue_mod k bs, Nat.pow_succ]
    exact byte_add_mod b.toNat_lt (Nat.pow_pos (by decide))

/-- The low 32 bits of the word of up to eight bytes are the value of their first four. -/
theorem leWord_low {bs : List UInt8} (h : bs.length ≤ 8) :
    (leWord bs).toUInt32.toUInt64.toNat = Linux.leValue (bs.take 4) := by
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, (leWord_toNat bs h).1,
    show 2 ^ 32 = 256 ^ 4 from rfl, leValue_mod]

/-- A word `x` has bit 11 clear exactly when `x &&& 2048` is 0. -/
theorem and_2048 (x : Nat) : x &&& 2048 = 0 ↔ x / 2048 % 2 = 0 := by
  have h2 : (2048 : Nat) = 2 ^ 11 := rfl
  have bit : x.testBit 11 = decide (x / 2048 % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, ← h2]
  rw [h2]
  constructor
  · intro h
    have hb := Nat.testBit_and x (2 ^ 11) 11
    rw [h, Nat.zero_testBit, Nat.testBit_two_pow_self, Bool.and_true, bit] at hb
    rw [← h2]
    have : ¬ x / 2048 % 2 = 1 := fun e => by simp [e] at hb
    omega
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
    by_cases hi : 11 = i
    · subst hi
      rw [bit, ← h2] at *
      simp [h]
    · rw [decide_eq_false hi, Bool.and_false]

/-- The stub's conversion of a timestamp as the specification's test of its range. -/
theorem stampValue_eq (sec ns : UInt64) :
    stampValue sec ns = if ns.toUInt32.toUInt64.toNat < 10 ^ 9 then
      (if 2 ^ 64 ≤ sec.toNat * 10 ^ 9 + ns.toUInt32.toUInt64.toNat then some none
        else some (some (UInt64.ofNat (sec.toNat * 10 ^ 9 + ns.toUInt32.toUInt64.toNat))))
      else none := by
  unfold stampValue
  generalize ns.toUInt32.toUInt64 = n
  have hnIff : 999999999 < n ↔ ¬ n.toNat < 10 ^ 9 := by
    rw [UInt64.lt_iff_toNat_lt]
    simp only [UInt64.reduceToNat]
    omega
  by_cases hn : 999999999 < n
  · rw [ite_eq_left hn, ite_eq_right (hnIff.mp hn)]
  have hn' : n.toNat < 10 ^ 9 := Classical.not_not.mp fun h => hn (hnIff.mpr h)
  rw [ite_eq_right hn, ite_eq_left hn']
  have hq := clock_quotient_iff (sec := sec) hn'
  by_cases hover : (0 - n - 1) / 1000000000 < sec
  · rw [ite_eq_left hover, ite_eq_left (by
      have := hq.mp hover
      have := sec.toNat_lt
      simp only [Nat.reducePow] at *
      omega)]
  · rw [ite_eq_right hover, ite_eq_right (by
      have := hq.not.mp hover
      simp only [Nat.reducePow] at *
      omega)]
    congr 2
    rw [← clock_time_toNat hn' hover, UInt64.ofNat_toNat]

/-- The table's four bits at four times `k` are the file type of a mode whose bits `S_IFMT` are
`k`. -/
theorem table_lookup : ∀ k < 16,
    (filetypeTable >>> UInt64.ofNat (4 * k)) &&& 15 = UInt64.ofNat (filetypeOf (4096 * k)) := by
  decide

/-- The stub's file type of byte 29 of the record, the high byte of `stx_mode`, is `filetypeOf`
of the mode that bytes 28 and 29 hold. -/
theorem fileType_eq (out : List UInt8) (hl : 30 ≤ out.length) :
    fileTypeOf (out.getD 29 0) = UInt64.ofNat (filetypeOf (fieldAt out 28 2)) := by
  have hk : (out.getD 29 0).toNat / 16 < 16 := by have := (out.getD 29 0).toNat_lt; omega
  have hshift : ((out.getD 29 0).toUInt64 >>> 4 + (out.getD 29 0).toUInt64 >>> 4 +
      ((out.getD 29 0).toUInt64 >>> 4 + (out.getD 29 0).toUInt64 >>> 4)) % 64 =
      UInt64.ofNat (4 * ((out.getD 29 0).toNat / 16)) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt8.toNat_toUInt64,
      UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
      Nat.reducePow]
    have := (out.getD 29 0).toNat_lt
    omega
  unfold fileTypeOf
  rw [hshift, table_lookup _ hk]
  congr 1
  unfold filetypeOf
  have hbytes := leWord_toNat ((out.drop 28).take 2) (by simp)
  have hhigh := leValue_byte ((out.drop 28).take 2) 1
  have hget : ((out.drop 28).take 2).getD 1 0 = out.getD 29 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rfl
  rw [hget] at hhigh
  have hlt := hbytes.2
  simp only [List.length_take, List.length_drop] at hlt
  unfold fieldAt
  generalize Linux.leValue ((out.drop 28).take 2) = v at hhigh hlt ⊢
  have hlen : min 2 (out.length - 28) = 2 := by omega
  rw [hlen] at hlt
  have e1 : v / 4096 % 16 = (out.getD 29 0).toNat / 16 := by
    simp only [pow_one] at hhigh
    omega
  have e2 : 4096 * ((out.getD 29 0).toNat / 16) / 4096 % 16 = (out.getD 29 0).toNat / 16 := by
    omega
  rw [e1, e2]

/-! ## The reply -/

/-- The bytes of words given as their values. -/
theorem flatMap_bytes (ws : List UInt64) (vs : List Nat) (h : vs = ws.map UInt64.toNat) :
    vs.flatMap (fun v => (List.range 8).map (Verified.Wasi.byteOf v)) =
      ws.flatMap fun w => (List.range 8).map (LeanExe.A64.byteOf w) := by
  subst h
  rw [List.flatMap_map]
  congr 1
  funext w
  exact bytes_word w

theorem filetypeOf_lt (mode : Nat) : filetypeOf mode < 8 := by
  unfold filetypeOf
  split <;> decide

/-- `filestatReply` of a result of 0 by the first timestamp that `find?` gives. -/
theorem reply_find (out : List UInt8) :
    filestatReply 0 out =
      match (stampOffsets out).find? (fun o => !stampValid out o || 2 ^ 64 ≤ stampTime out o) with
      | some o => if stampValid out o then .returned 61 [zeros 64] else .trapped shimTrap [zeros 64]
      | none => .returned 0 [filestatBytes out] := by
  unfold filestatReply
  rw [ite_eq_left rfl]
  rfl

/-- The test of `find?` of a timestamp that `stampValid` refuses. -/
theorem stamp_invalid {out : List UInt8} {o : Nat} (h : stampValid out o = false) :
    (!stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) = true := by
  rw [h]
  rfl

/-- The test of `find?` of a valid timestamp of `2^64` nanoseconds or more. -/
theorem stamp_over {out : List UInt8} {o : Nat} (h : stampValid out o = true)
    (hov : 2 ^ 64 ≤ stampTime out o) :
    (!stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) = true := by
  rw [h, decide_eq_true hov]
  rfl

/-- The test of `find?` of a valid timestamp below `2^64` nanoseconds. -/
theorem stamp_pass {out : List UInt8} {o : Nat} (h : stampValid out o = true)
    (hov : ¬ 2 ^ 64 ≤ stampTime out o) :
    (!stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) = false := by
  rw [h, decide_eq_false hov]
  rfl

/-- `find?` stops at a timestamp whose test holds. -/
theorem find_stop {out : List UInt8} {o : Nat} {rest : List Nat}
    (h : (!stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) = true) :
    (o :: rest).find? (fun o => !stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) =
      some o :=
  List.find?_cons_of_pos (p := fun o => !stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) h

/-- `find?` passes a timestamp whose test fails. -/
theorem find_skip {out : List UInt8} {o : Nat} {rest : List Nat}
    (h : (!stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) = false) :
    (o :: rest).find? (fun o => !stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) =
      rest.find? (fun o => !stampValid out o || decide (2 ^ 64 ≤ stampTime out o)) :=
  List.find?_cons_of_neg (p := fun o => !stampValid out o || decide (2 ^ 64 ≤ stampTime out o))
    (by rw [h]; decide)

/-- The stub's conversions and words for the `statx` record `out` written from `r`, against
`filestatReply` of a result of 0: the trap of the shim, errno 61, or the bytes of `filestatBytes`,
which are those of the eight words that the stub stores. -/
theorem filestat_reply (m : UInt64 → UInt8) (r : UInt64) (out : List UInt8)
    (hl : out.length = 256) :
    match stampsValue (writeList m r out) r with
    | none => filestatReply 0 out = .trapped shimTrap [zeros 64]
    | some none => filestatReply 0 out = .returned 61 [zeros 64]
    | some (some (ta, tm, tb)) => filestatReply 0 out = .returned 0 [filestatBytes out] ∧
        (filestatBytes out).data.data.toList =
          (filestatWords (writeList m r out) r ta tm tb).flatMap
            fun w => (List.range 8).map (LeanExe.A64.byteOf w) := by
  have hlt : out.length < 2 ^ 64 := by rw [hl]; decide
  have hw : ∀ j, j + 8 ≤ 256 → load64 (writeList m r out) (r + UInt64.ofNat j) =
      leWord ((out.drop j).take 8) := fun j hj => load64_writeList m out r (by omega) hlt
  have hw0 : load64 (writeList m r out) r = leWord (out.take 8) := by
    have := hw 0 (by decide)
    rwa [add_ofNat_zero, List.drop_zero] at this
  have hb29 : writeList m r out (r + UInt64.ofNat 29) = out.getD 29 0 :=
    writeList_at m out r 29 (by omega) hlt
  have sec : ∀ j, (leWord ((out.drop j).take 8)).toNat = fieldAt out j 8 := fun j =>
    (leWord_toNat _ (by simp)).1
  have nsec : ∀ j, (leWord ((out.drop j).take 8)).toUInt32.toUInt64.toNat = fieldAt out j 4 :=
    fun j => by
      rw [leWord_low (by simp), List.take_take]
      rfl
  have hmask : leWord (out.take 8) &&& 2048 = 0 ↔ hasBirth out = false := by
    have hv := (leWord_toNat (out.take 8) (by simp)).1
    have h4 : fieldAt out 0 4 = Linux.leValue (out.take 8) % 256 ^ 4 := by
      rw [leValue_mod, List.take_take]
      rfl
    rw [← UInt64.toNat_inj, UInt64.toNat_and, hv, show (2048 : UInt64).toNat = 2048 from rfl,
      UInt64.toNat_zero, and_2048]
    unfold hasBirth
    rw [h4]
    simp only [beq_eq_false_iff_ne, ne_eq, Nat.reducePow]
    omega
  have word : ∀ (S N : Nat), ¬ 2 ^ 64 ≤ S * 10 ^ 9 + N →
      (UInt64.ofNat (S * 10 ^ 9 + N)).toNat = S * 10 ^ 9 + N := fun S N h =>
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)
  have hft : (fileTypeOf (out.getD 29 0)).toNat = filetypeOf (fieldAt out 28 2) := by
    rw [fileType_eq out (by omega), UInt64.toNat_ofNat_of_lt'
      (Nat.lt_trans (filetypeOf_lt _) (by decide))]
  have succ : ∀ ta tm tb : UInt64, ta.toNat = stampTime out 64 → tm.toNat = stampTime out 112 →
      tb.toNat = (if hasBirth out then stampTime out 80 else 0) →
      (filestatBytes out).data.data.toList =
        (filestatWords (writeList m r out) r ta tm tb).flatMap
          fun w => (List.range 8).map (LeanExe.A64.byteOf w) := by
    intro ta tm tb hta htm htb
    unfold filestatWords
    rw [hw 32 (by decide), hb29, hw 16 (by decide), hw 40 (by decide)]
    simp only [filestatBytes, bytesOfList, List.toList_toArray]
    apply flatMap_bytes
    simp only [List.map_cons, List.map_nil, sec, nsec, hft, hta, htm, htb]
    rfl
  have valid : ∀ o j, j = o + 8 → (fieldAt out j 4 < 10 ^ 9 ↔ stampValid out o = true) := by
    intro o j hj
    subst hj
    unfold stampValid
    exact decide_eq_true_iff.symm
  unfold stampsValue
  rw [hw 64 (by decide), hw 72 (by decide), hw 112 (by decide), hw 120 (by decide),
    hw 80 (by decide), hw 88 (by decide), hw0, stampValue_eq, stampValue_eq, stampValue_eq,
    sec 64, sec 112, sec 80, nsec 72, nsec 120, nsec 88, reply_find]
  by_cases a1 : fieldAt out 72 4 < 10 ^ 9
  swap
  · rw [ite_eq_right a1]
    dsimp only
    rw [show stampOffsets out = 64 :: ([112] ++ if hasBirth out then [80] else []) from rfl,
      find_stop (stamp_invalid (by
        rw [← Bool.not_eq_true, ← valid 64 72 rfl]; exact a1))]
    dsimp only
    rw [ite_eq_right (by rw [← valid 64 72 rfl]; exact a1)]
  have v1 := (valid 64 72 rfl).mp a1
  by_cases a2 : 2 ^ 64 ≤ fieldAt out 64 8 * 10 ^ 9 + fieldAt out 72 4
  · rw [ite_eq_left a1, ite_eq_left a2]
    dsimp only
    rw [show stampOffsets out = 64 :: ([112] ++ if hasBirth out then [80] else []) from rfl,
      find_stop (stamp_over v1 a2)]
    dsimp only
    rw [ite_eq_left v1]
  rw [ite_eq_left a1, ite_eq_right a2]
  dsimp only
  rw [show stampOffsets out = 64 :: 112 :: (if hasBirth out then [80] else []) from rfl,
    find_skip (stamp_pass v1 a2)]
  by_cases b1 : fieldAt out 120 4 < 10 ^ 9
  swap
  · rw [ite_eq_right b1]
    dsimp only
    rw [find_stop (stamp_invalid (by
        rw [← Bool.not_eq_true, ← valid 112 120 rfl]; exact b1))]
    dsimp only
    rw [ite_eq_right (by rw [← valid 112 120 rfl]; exact b1)]
  have v2 := (valid 112 120 rfl).mp b1
  by_cases b2 : 2 ^ 64 ≤ fieldAt out 112 8 * 10 ^ 9 + fieldAt out 120 4
  · rw [ite_eq_left b1, ite_eq_left b2]
    dsimp only
    rw [find_stop (stamp_over v2 b2)]
    dsimp only
    rw [ite_eq_left v2]
  rw [ite_eq_left b1, ite_eq_right b2]
  dsimp only
  rw [find_skip (stamp_pass v2 b2)]
  by_cases hb : hasBirth out
  swap
  · have hm : leWord (out.take 8) &&& 2048 = 0 := hmask.mpr (by simpa using hb)
    rw [ite_eq_left hm]
    dsimp only
    rw [show (if hasBirth out = true then [80] else []) = ([] : List Nat) from by rw [ite_eq_right hb]]
    refine ⟨rfl, succ _ _ _ (by rw [word _ _ a2]; rfl) (by rw [word _ _ b2]; rfl) ?_⟩
    rw [ite_eq_right hb]
    rfl
  have hm : ¬ leWord (out.take 8) &&& 2048 = 0 := fun h => by
    have := hmask.mp h
    rw [hb] at this
    exact Bool.noConfusion this
  rw [ite_eq_right hm]
  rw [show (if hasBirth out = true then [80] else []) = [80] from by rw [ite_eq_left hb]]
  by_cases c1 : fieldAt out 88 4 < 10 ^ 9
  swap
  · rw [ite_eq_right c1]
    dsimp only
    rw [find_stop (stamp_invalid (by
        rw [← Bool.not_eq_true, ← valid 80 88 rfl]; exact c1))]
    dsimp only
    rw [ite_eq_right (by rw [← valid 80 88 rfl]; exact c1)]
  have v3 := (valid 80 88 rfl).mp c1
  by_cases c2 : 2 ^ 64 ≤ fieldAt out 80 8 * 10 ^ 9 + fieldAt out 88 4
  · rw [ite_eq_left c1, ite_eq_left c2]
    dsimp only
    rw [find_stop (stamp_over v3 c2)]
    dsimp only
    rw [ite_eq_left v3]
  rw [ite_eq_left c1, ite_eq_right c2]
  dsimp only
  rw [find_skip (stamp_pass v3 c2)]
  refine ⟨rfl, succ _ _ _ (by rw [word _ _ a2]; rfl) (by rw [word _ _ b2]; rfl) ?_⟩
  rw [ite_eq_left hb, word _ _ c2]
  rfl

/-! ## The stub's run -/

section Run

variable {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-- The stub of `fd_filestat_get` from its entry, with the descriptor in X0, the record's pointer
in X1, the store `st` in the area at X17, and the scratch `scratch` bytes above the area, whose
first 1,344 bytes are Normal memory below the stack's limit and hold in their bytes from 16 the
shim's descriptors of the world's events (`hheld`), ends as `filestatInvoke` of the replies `R'`
answers, when the path buffer and the `statx` record of the layout `L` lie at the scratch's bytes
1,080 and 1,088 and the reply of the world's next call is that of the process's next call.  The
trace gains at most the `statx` event, and the memory changes only in the guest's memory and the
264 bytes from the path buffer. -/
theorem filestatStub_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {S : Shared}
    {a svc en : UInt64} {scratch : Nat} {is : List Instr}
    (hg : filestatStub a svc S.trapUnreachable en scratch = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (L : ShimLayout) (I : Launch) (R' : Linux.Replies) (st : Store (Observed LinuxWorld))
    (q : Proc) (fd ptr : UInt32) (hpc : q.core.pc = a) (hstk : StackOk P q.core)
    (hsr : StoreRel P S.cap S.globalTypes st q.core) (hf : q.fpcr = fpcrValue)
    (x0 : q.core.x 0 = fd.toUInt64) (x1 : q.core.x 1 = ptr.toUInt64)
    (hscr : areaSize S.cap ≤ scratch)
    (hP : L.path = q.core.x 17 + UInt64.ofNat (scratch + 1080))
    (hX : L.statx = q.core.x 17 + UInt64.ofNat (scratch + 1088))
    (hlim : (q.core.x 17).toNat + scratch + 1344 ≤ (q.core.x 18).toNat)
    (hmapS : ∀ j < 1344, P.normal (q.core.x 17 + UInt64.ofNat scratch + UInt64.ofNat j) = true)
    (hU : P.normal P.uart = false)
    (hheld : (q.core.x 0 ≤ 1023 ∧
        q.core.mem (q.core.x 17 + UInt64.ofNat scratch + q.core.x 0 + 16) ≠ 0) ↔
      fd.toUInt64 ∈ openNumbers I st.host.world.events)
    (hR : R' st.host.world.events.length = R q.trace.length) :
    StubEnd R P code S [.i32] (· = statxEvent L fd.toUInt64 (R' st.host.world.events.length))
      L.path 264 st q (filestatInvoke L I R' st [.i32 fd, .i32 ptr]) := by
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hlimit := hstk.limit
  have hbelow := hsr.below
  have hp32 := ptr.toNat_lt
  have h17lt := (q.core.x 17).toNat_lt
  have h18lt := (q.core.x 18).toNat_lt
  unfold areaSize at hscr hbelow
  have hmap17 : ∀ k < 8, P.normal (q.core.x 17 + UInt64.ofNat k) = true := fun k hk =>
    hsr.mapped k (by unfold areaSize; omega)
  obtain ⟨u1, r1, sp1, io1, x17_1, x18_1, h1⟩ :=
    run_filestatFront P code hg hcode hpc hmap17 hmapS hU
  have hsize : (load64 q.core.mem (q.core.x 17)).toNat = st.mem.pages * 65536 - 8 := by
    rw [hsr.size, UInt64.toNat_ofNat_of_lt' (show _ < 2 ^ 64 by omega)]
  have hcheck : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + 64 ↔
      ¬ (ptr.toNat + 64 ≤ st.mem.pages * 65536 ∧ ptr.toNat + 64 < 2 ^ 32) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add, hsize, x1,
      UInt32.toNat_toUInt64]
    have : st.mem.pages * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    simp only [UInt64.reduceToNat, Nat.reducePow] at *
    omega
  -- the scratch's addresses
  have hPn : L.path.toNat = (q.core.x 17).toNat + scratch + 1080 := by
    rw [hP, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hXP : L.statx = L.path + UInt64.ofNat 8 := by
    rw [hX, hP, add_ofNat_add]
  have hXn : L.statx.toNat = (q.core.x 17).toNat + scratch + 1088 := by
    rw [hX, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have ePath : q.core.x 17 + UInt64.ofNat scratch + UInt64.ofNat 1080 = L.path := by
    rw [hP, add_ofNat_add]
  have eRec : q.core.x 17 + UInt64.ofNat scratch + UInt64.ofNat 1088 = L.statx := by
    rw [hX, add_ofNat_add]
  unfold filestatInvoke
  dsimp only
  by_cases hbad : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 1 + 64
  · rw [ite_eq_left hbad] at h1
    rw [ite_eq_right (hcheck.mp hbad)]
    obtain ⟨p1, m1⟩ := h1
    dsimp only [StubEnd]
    exact ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1, io1, rfl, p1, hf, by simp,
      by simp, by simp, fun b _ _ => by show u1.mem b = _; rw [m1]⟩
  rw [ite_eq_right hbad] at h1
  have hok : ptr.toNat + 64 ≤ st.mem.pages * 65536 ∧ ptr.toNat + 64 < 2 ^ 32 :=
    Classical.not_not.mp fun h => hbad (hcheck.mpr h)
  rw [ite_eq_left hok]
  by_cases hheldq : q.core.x 0 ≤ 1023 ∧
      q.core.mem (q.core.x 17 + UInt64.ofNat scratch + q.core.x 0 + 16) ≠ 0
  swap
  · rw [ite_eq_right hheldq] at h1
    rw [ite_eq_right (mt hheld.mpr hheldq)]
    obtain ⟨p1, x01, m1⟩ := h1
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1,
      ⟨p1, sp1, x18_1, io1, fun b _ => by show u1.mem b = _; rw [m1], by simp,
        ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩,
      StoreRel.answered (hsr.regs x17_1 x18_1 m1) _ _, hf, x17_1, rfl, by simp, by simp,
      fun b _ _ => by show u1.mem b = _; rw [m1]⟩
    simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show u1.x 0 = (8 : UInt64).toUInt32.toUInt64
    rw [x01]
    rfl
  rw [ite_eq_left hheldq] at h1
  rw [ite_eq_left (hheld.mp hheldq)]
  obtain ⟨p1, x01, x11, x21, x31, x41, x81, x191, x201, x211, m1⟩ := h1
  rw [ePath, eRec] at m1
  rw [ePath] at x11
  rw [eRec] at x41
  rw [zeroWords_writeList] at m1
  -- the call
  obtain ⟨_gr, _g11, _g14, _g8a, _g14a, _g8m, _g14m, _g8b, _g14b, _gt, _g56, _g93, gs, _ge, -, -,
    -, -, -, -, -, -, -, -, -, hgs, -, -, -, -, -, -, -, -, cC, -, -, -, -, -, -, -⟩ :=
    filestat_code code hg hcode
  have cbl : code (after a 55) = some (encode (.bl gs)) := by
    have := cC 5 (by simp)
    simpa [after_after] using this
  have cnext := cC 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, Nat.reduceAdd] at cnext
  have hnext : (after (after a 55) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hTab : Linux.table.find? (fun c => c.arm64 == ({ q with core := u1 } : Proc).core.x 8) =
      some Linux.statxCall := by
    show Linux.table.find? (fun c => c.arm64 == u1.x 8) = _
    rw [x81]
    exact table_statx
  have hempty : u1.mem L.path = 0 := by
    rw [m1, writeList_other _ _ _ _ (by
      rw [hXP]
      simp only [List.length_replicate, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat',
        Nat.reducePow]
      have := L.path.toNat_lt
      omega)]
    simp [store8]
  have hcleared : readList u1.mem L.statx 256 = List.replicate 256 0 := by
    rw [m1]
    exact readList_writeList _ _ _ (by rw [List.length_replicate])
      (by rw [List.length_replicate]; decide)
  have hmapP : P.mapped L.path 1 = true := by
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    obtain rfl : i = 0 := by omega
    rw [add_ofNat_zero, ← ePath]
    exact hmapS 1080 (by decide)
  have hmapX : P.mapped L.statx 256 = true := by
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [← eRec, add_ofNat_add]
    exact hmapS (1088 + i) (by omega)
  have hsys := sysCall_statxEvent (R := R) (P := P)
    (p := ({ q with core := u1 } : Proc).call (after a 55) svc) L
    (by rw [Proc.call_x _ _ _ (by decide)]; exact x11)
    (by rw [Proc.call_x _ _ _ (by decide)]; exact x21)
    (by rw [Proc.call_x _ _ _ (by decide)]; exact x31)
    (by rw [Proc.call_x _ _ _ (by decide)]; exact x41)
    (by rw [Proc.call_mem]; exact hempty) (by rw [Proc.call_mem]; exact hcleared) hmapP hmapX
  obtain ⟨q3, rq3, p3, x03, x303, k3, sp3, m3, io3, f3, tr3⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl hgs hdom hnext
      (p := { q with core := u1 }) p1 hTab rfl hsys
  simp only [Proc.call_trace, Proc.call_mem] at x03 m3 tr3
  rw [Proc.call_x _ _ _ (by decide)] at tr3
  change q3.core.x 0 = (R q.trace.length).ret at x03
  change q3.core.mem = writeList u1.mem L.statx
    ((List.range 256).map (R q.trace.length).bytes) at m3
  change q3.trace = q.trace ++ [A64.Event.sys (statxEvent L (u1.x 0) (R q.trace.length))] at tr3
  rw [x01, x0, ← hR] at tr3
  rw [← hR] at x03 m3
  generalize hE : statxEvent L fd.toUInt64 (R' st.host.world.events.length) = E at tr3 ⊢
  have hEret : E.ret = (R' st.host.world.events.length).ret := by rw [← hE]; rfl
  have hEout : E.output = (List.range 256).map (R' st.host.world.events.length).bytes := by
    rw [← hE]; rfl
  rw [hEret, hEout]
  generalize R' st.host.world.events.length = rr at x03 m3 hEret hEout ⊢
  generalize hout : (List.range 256).map rr.bytes = out at m3 hEout ⊢
  have hlen : out.length = 256 := by rw [← hout]; simp
  -- the state after the call
  have q3x : ∀ r : Fin 32, r ≠ 0 → r ≠ 30 → q3.core.x r = u1.x r := fun r h0 h30 => k3 r h0 h30
  have q3x17 : q3.core.x 17 = q.core.x 17 := by rw [q3x 17 (by decide) (by decide), x17_1]
  have q3x18 : q3.core.x 18 = q.core.x 18 := by rw [q3x 18 (by decide) (by decide), x18_1]
  have q3x19 : q3.core.x 19 = q.core.x 30 := by rw [q3x 19 (by decide) (by decide), x191]
  have q3x20 : q3.core.x 20 = q.core.x 17 + UInt64.ofNat scratch := by
    rw [q3x 20 (by decide) (by decide), x201]
  have q3x21 : q3.core.x 21 = ptr.toUInt64 := by rw [q3x 21 (by decide) (by decide), x211, x1]
  have q3sp : q3.core.sp = q.core.sp := by rw [sp3]; show u1.sp = _; exact sp1
  have q3io : q3.core.io = q.core.io := by rw [io3]; show u1.io = _; exact io1
  have hf3 : q3.fpcr = fpcrValue := by rw [f3]; exact hf
  -- the memory after the call
  have hscratchW : ∀ b : UInt64, ¬ (b - L.path).toNat < 264 → q3.core.mem b = q.core.mem b := by
    intro b hb
    have hb8 : ¬ (b - L.statx).toNat < 256 := by
      rw [hXP]
      simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at hb ⊢
      have := L.path.toNat_lt
      have := b.toNat_lt
      omega
    rw [m3, writeList_other _ _ _ _ (by rw [hlen]; exact hb8), m1,
      writeList_other _ _ _ _ (by rw [List.length_replicate]; exact hb8)]
    refine store8_other _ _ _ _ fun same => hb ?_
    rw [same, UInt64.sub_self]
    decide
  have hkeep3 : KeptOutside (q.core.x 17) S.cap L.path 264 q.core.mem q3.core.mem :=
    fun b _ hb => hscratchW b hb
  have habove3 : ∀ b : UInt64, q.core.sp.toNat ≤ b.toNat → q3.core.mem b = q.core.mem b :=
    fun b hb => hscratchW b (sub_not_lt (by omega))
  have hsr3 : StoreRel P S.cap S.globalTypes st q3.core :=
    StoreRel.congrArea hsr q3x17 q3x18 fun j hj => by
      unfold areaSize at hj
      exact hscratchW _ (sub_not_lt_below (by
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
        omega) (by omega))
  -- the result
  have hrec : ∀ k < 256, P.normal (q3.core.x 20 + UInt64.ofNat (1088 + k)) = true := fun k hk => by
    rw [q3x20]
    exact hmapS (1088 + k) (by omega)
  have hgA : ∀ k : Nat, q.core.x 17 + ptr.toUInt64 + UInt64.ofNat (4096 + k) =
      q.core.x 17 + UInt64.ofNat (4096 + (ptr.toNat + k)) := fun k => guest_addr' _ _ _
  have hpg' := Nat.mul_le_mul_right 65536 hpg.2
  have houtN : ∀ k < 64, P.normal (q3.core.x 17 + q3.core.x 21 + UInt64.ofNat (4096 + k)) = true :=
    fun k hk => by
      rw [q3x17, q3x21, hgA]
      exact hsr.mapped _ (by unfold areaSize; omega)
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ :=
    run_filestatBack P code hg hcode hen (s := q3.core) (by rw [p3, after_after]) hrec houtN
  rw [x03, q3x20, eRec, m3, q3x19, q3x17, q3x21] at ht
  have hrch : ProcRunWith Linux.table R P code q { q3 with core := t } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq3 hf3) (ProcRunWith.ofReach hf3 rt))
  have htr : ({ q3 with core := t } : Proc).trace = q.trace ++ [E].map A64.Event.sys := by
    show q3.trace = _
    rw [tr3]
    rfl
  have tsp : t.sp = q.core.sp := by rw [spt, q3sp]
  have tio : t.io = q.core.io := by rw [iot, q3io]
  have t17 : t.x 17 = q.core.x 17 := by rw [x17t, q3x17]
  have t18 : t.x 18 = q.core.x 18 := by rw [x18t, q3x18]
  have hres : ∀ (v : UInt64) (vs : List Value), vs = [.i32 v.toUInt32] → t.x 0 = v →
      v.toNat < 2 ^ 32 → StackRel t (vs.take [ValueType.i32].length) := by
    intro v vs hvs hx hv
    subst hvs
    refine ⟨by simp, fun k hk => ?_⟩
    simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show t.x 0 = v.toUInt32.toUInt64
    rw [hx]
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    omega
  by_cases hr0 : rr.ret = 0
  swap
  · rw [ite_eq_left hr0] at ht
    obtain ⟨mt, ht⟩ := ht
    simp only [filestatReply, hr0, ↓reduceIte]
    by_cases he : 0 - rr.ret ≤ 4095
    · rw [ite_eq_left he] at ht
      obtain ⟨pt, x0t⟩ := ht
      rw [ite_eq_left ((isError_iff_ne hr0).mpr he),
        placeReply_errno _ _ _ (errnoOf_valid _).2]
      dsimp only [sysAnswer, sysResult, StubEnd]
      refine ⟨{ q3 with core := t }, [E], hrch,
        ⟨pt, tsp, t18, tio, fun b hb => ?_, by simp,
          hres _ _ rfl (by rw [x0t, errnoOf_lookup])
            (by have := (errnoOf_valid (0 - rr.ret)).1; omega),
          by simp [Typed, HasType]⟩,
        StoreRel.answered (hsr3.regs (by rw [t17, q3x17]) (by rw [t18, q3x18])
          (mt.trans m3.symm)) _ _, hf3, t17, rfl, htr, by simp, fun b h1 h2 => ?_⟩
      · show t.mem b = _
        rw [mt, ← m3]
        exact habove3 b (by simpa using hb)
      · show t.mem b = _
        rw [mt, ← m3]
        exact hkeep3 b h1 h2
    · rw [ite_eq_right he] at ht
      rw [ite_eq_right (fun h => he ((isError_iff_ne hr0).mp h))]
      dsimp only [placeReply, sysAnswer, sysResult, StubEnd]
      exact ⟨{ q3 with core := t }, [E], hrch, tio, rfl, ht, hf3, rfl, htr, by simp,
        fun b h1 h2 => by show t.mem b = _; rw [mt, ← m3]; exact hkeep3 b h1 h2⟩
  rw [ite_eq_right (not_not.mpr hr0)] at ht
  rw [hr0]
  have hrep := filestat_reply u1.mem L.statx out hlen
  rcases hS : stampsValue (writeList u1.mem L.statx out) L.statx with _ | _ | ⟨ta, tm, tb⟩
  · rw [hS] at ht hrep
    dsimp only at ht hrep
    obtain ⟨pt, mt⟩ := ht
    rw [hrep]
    dsimp only [placeReply, sysAnswer, sysResult, StubEnd]
    exact ⟨{ q3 with core := t }, [E], hrch, tio, rfl, pt, hf3, rfl, htr, by simp,
      fun b h1 h2 => by show t.mem b = _; rw [mt, ← m3]; exact hkeep3 b h1 h2⟩
  · rw [hS] at ht hrep
    dsimp only at ht hrep
    obtain ⟨pt, x0t, mt⟩ := ht
    rw [hrep, placeReply_errno _ _ _ (by decide)]
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨{ q3 with core := t }, [E], hrch,
      ⟨pt, tsp, t18, tio, fun b hb => ?_, by simp, hres 61 _ rfl x0t (by decide),
        by simp [Typed, HasType]⟩,
      StoreRel.answered (hsr3.regs (by rw [t17, q3x17]) (by rw [t18, q3x18])
        (by rw [mt, ← m3])) _ _, hf3, t17, rfl, htr, by simp, fun b h1 h2 => ?_⟩
    · show t.mem b = _
      rw [mt, ← m3]
      exact habove3 b (by simpa using hb)
    · show t.mem b = _
      rw [mt, ← m3]
      exact hkeep3 b h1 h2
  rw [hS] at ht hrep
  dsimp only at ht hrep
  obtain ⟨pt, x0t, mt⟩ := ht
  obtain ⟨hrep, hbytes⟩ := hrep
  rw [hrep]
  have hA0 : q.core.x 17 + ptr.toUInt64 + UInt64.ofNat 4096 =
      q.core.x 17 + UInt64.ofNat (4096 + (ptr.toNat + 0)) := hgA 0
  rw [storedWords_writeList, ← hbytes, ← m3, hA0] at mt
  have hplace : placeReply st.mem (fun outputs => [(ptr, outputs.headD Bytes.empty)])
      (.returned 0 [filestatBytes out]) =
      st.mem.writeBytes ptr.toNat (filestatBytes out).data.data.toList := rfl
  rw [hplace]
  dsimp only [sysAnswer, sysResult, StubEnd]
  have hblen : (filestatBytes out).data.data.toList.length = 64 := by
    have := filestatBytes_size out
    simpa using this
  have hAn : (q.core.x 17 + UInt64.ofNat (4096 + (ptr.toNat + 0))).toNat =
      (q.core.x 17).toNat + 4096 + ptr.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  have hother : ∀ b : UInt64,
      ¬ (b - (q.core.x 17 + UInt64.ofNat (4096 + (ptr.toNat + 0)))).toNat < 64 →
      t.mem b = q3.core.mem b := fun b hb => by
    rw [mt, writeList_other _ _ _ _ (by rw [hblen]; exact hb)]
  refine ⟨{ q3 with core := t }, [E], hrch,
    ⟨pt, tsp, t18, tio, fun b hb => ?_, by simp, hres 0 _ rfl x0t (by decide),
      by simp [Typed, HasType]⟩,
    StoreRel.withHost (StoreRel.ofWriteList P _ hsr3 (by rw [hblen]; exact hok.1)
      (by rw [t17, q3x17]) (by rw [t18, q3x18]) (by rw [mt, q3x17]; rfl)) _, hf3,
    t17, rfl, htr, by simp, fun b h1 h2 => ?_⟩
  · show t.mem b = _
    have hb' : q.core.sp.toNat ≤ b.toNat := by simpa using hb
    rw [hother b (sub_not_lt (by omega)), habove3 b hb']
  · show t.mem b = _
    rw [hother b ?_, hkeep3 b h1 h2]
    have := b.toNat_lt
    have h4096 : (q.core.x 17 + UInt64.ofNat 4096).toNat = (q.core.x 17).toNat + 4096 := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
      omega
    simp only [UInt64.toNat_sub, h4096, hAn, Nat.reducePow] at h1 ⊢
    omega

end Run

/-! ## The stub on the shim's machine -/

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- The stub of `fd_filestat_get` stands for the shim's `fd_filestat_get`, when the area and the
scratch lie in the data segment and the UART outside the module's Normal memory. -/
theorem filestatStub_sim (S : Shared) (n : Nat) {fs svc en : UInt64} {is : List Instr}
    (hg : filestatStub fs svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code fs is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU' : (modulePlatform L G).normal (modulePlatform L G).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.fdFilestatGet)
      fs := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = fs at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨fd, ptr, rfl⟩ := typed_i32x2 hlen hty
  have x0 : q.core.x 0 = fd.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = ptr.toUInt64 := hregs 1 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr'
  change q.core.x 17 = L.area at h17
  change L.area.toNat + areaSize S.cap + scratchSize ≤ (q.core.x 18).toNat at hgap
  have hPP := modulePlatform_le_wasi L G sp₀ top
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      Call.fdFilestatGet).invoke st [.i32 fd, .i32 ptr] =
      filestatInvoke (shimLayout L.area G) I (fun j => R (l₀.length + j)) st
        [.i32 fd, .i32 ptr] := by
    simp (config := { decide := true }) only [sysFn, sysInvoke, ↓reduceIte]
  rw [hinv]
  have hLA := hL
  unfold scratchSize at hdata hgap
  have hGn : G.base.toNat = L.area.toNat + areaSize S.cap := by
    rw [hGb, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at hLA ⊢
    omega
  have hG17 : q.core.x 17 + UInt64.ofNat (areaSize S.cap) = G.base := by rw [h17, hGb]
  have hPath : (shimLayout L.area G).path = q.core.x 17 + UInt64.ofNat (areaSize S.cap + 1080) := by
    show G.base + 1080 = _
    rw [← add_ofNat_add, hG17]
    rfl
  have hStatx : (shimLayout L.area G).statx =
      q.core.x 17 + UInt64.ofNat (areaSize S.cap + 1088) := by
    show G.base + 1088 = _
    rw [← add_ofNat_add, hG17]
    rfl
  have hlim : (q.core.x 17).toNat + areaSize S.cap + 1344 ≤ (q.core.x 18).toNat := by
    rw [h17]
    omega
  have hscrP := scratch_wasi (sp := sp₀) (top := top) hL hGb hdata
  have hmapS : ∀ j < 1344, (wasiPlatform L sp₀ top).normal
      (q.core.x 17 + UInt64.ofNat (areaSize S.cap) + UInt64.ofNat j) = true := fun j hj => by
    rw [hG17]
    exact hscrP j (by unfold scratchSize; omega)
  have hU := wasiPlatform_uart (top := top) (elfPlatform_uart hU' (scratch_pos hL hGb hdata))
    hK.stack.above
  have hheld : (q.core.x 0 ≤ 1023 ∧ q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize S.cap) +
      q.core.x 0 + 16) ≠ 0) ↔ fd.toUInt64 ∈ openNumbers I st.host.world.events := by
    rw [hG17, x0]
    exact held_byte hK fd.toUInt64
  have hR : (fun j => R (l₀.length + j)) st.host.world.events.length = R q.trace.length := by
    simp only [htr.1, List.length_map, List.length_append]
  have hrun := filestatStub_run (P := wasiPlatform L sp₀ top) hdom hg hcode hsvc hen
    (shimLayout L.area G) I (fun j => R (l₀.length + j)) st q fd ptr hpc (StackOk.toLe hstk hPP)
    (StoreRel.toLe hst hPP) hf x0 x1 (Nat.le_refl _) hPath hStatx hlim hmapS hU hheld hR
  have hPn : (shimLayout L.area G).path.toNat = G.base.toNat + 1080 := by
    show (G.base + 1080).toNat = _
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat, Nat.reducePow] at hLA ⊢
    omega
  refine stubResult_of_end hsr (fun e he => ?_) (fun m' hkp => ⟨fun j hj => ?_, fun a ha => ?_⟩)
    hrun
  · subst he
    exact ⟨rfl, fun h => absurd h (by decide : Linux.statxCall ≠ Linux.closeCall),
      .inr (.inr ⟨rfl, rfl⟩)⟩
  · have e : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow] at hLA ⊢
      omega
    exact kept_scratch hkp (by rw [e, hGn, h17]; omega) (.inl (by rw [e, hPn]; omega))
      (by rw [h17]; simp only [Nat.reducePow] at hLA ⊢; omega)
      (by rw [hPn]; simp only [Nat.reducePow] at hLA ⊢; omega)
  · exact kept_scratch hkp (by rw [h17]; omega) (.inr (by rw [hPn]; omega))
      (by rw [h17]; simp only [Nat.reducePow] at hLA ⊢; omega)
      (by rw [hPn]; simp only [Nat.reducePow] at hLA ⊢; omega)

/-! ## The file stubs of `flatStubs` -/

theorem shimCall_files {c : Call} (hc : c ∈ shimCalls) :
    (c.name = "path_open" → c = Call.pathOpen) ∧ (c.name = "fd_close" → c = Call.fdClose) ∧
      (c.name = "fd_read" → c = Call.fdRead) ∧ (c.name = "fd_write" → c = Call.fdWrite) ∧
      (c.name = "fd_filestat_get" → c = Call.fdFilestatGet) := by
  revert c
  decide

/-- The code of a stub of `fileStubs` at `a`, generated with the routine `SVC #0; RET` at `svc`,
the trap stub, the routine of errnos at `en`, and the scratch `areaSize S.cap` bytes above the
area, stands for the shim's function of the call `c` of `shimCalls` whose import is the stub's,
when the area and the scratch lie in the data segment.  `flatStub_sim` takes its cases for these
stubs from here. -/
theorem fileStub_sim {s : FlatStub} (hs : s ∈ fileStubs) {c : Call} (hc : c ∈ shimCalls)
    (hd : ABI.callImport c = s.decl) (S : Shared) (n : Nat) {a svc en : UInt64}
    {is : List Instr} (hg : s.gen a svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code a is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false)
    (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      s.decl.params s.decl.results
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) c) a := by
  have hn : c.name = s.decl.name := congrArg ImportDecl.name hd
  obtain ⟨n1, n2, n3, n4, n5⟩ := shimCall_files hc
  simp only [fileStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · obtain rfl := n1 hn
    exact openStub_sim S n hg hcode hsvc hen hGb hdata hU
  · obtain rfl := n2 hn
    exact closeStub_sim S n hg hcode hsvc hen hGb hdata hU
  · obtain rfl := n3 hn
    exact handleReadStub_sim S n hg hcode hsvc hen hGb hdata hU hsize
  · obtain rfl := n4 hn
    exact handleWriteStub_sim S n hg hcode hsvc hen hGb hdata hU
  · obtain rfl := n5 hn
    exact filestatStub_sim S n hg hcode hsvc hen hGb hdata hU

end Verified.ShimA64
