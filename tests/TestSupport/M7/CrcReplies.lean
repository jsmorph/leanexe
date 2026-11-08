import TestSupport.M7.Crc
import Library.Hashing.Crc.Proof
import LeanExe.Requests.Records

/-!
What the CRC-32 step writes, in terms of the bytes that it reads.  For a register map `u` whose
receive and status registers differ, `crcTick u` is `crcPhases` of `tests/TestSupport/M7/Crc.lean`
with the map's registers and CRC-32's table, and `crc_replies` states for every bus, every
sequence `σ` of the values read, and every number `N` of windows from `crcInit`: the values that
the windows write to the transmit register begin `crcReplies` of the bytes that they read from the
receive register, the low byte of CRC-32 of each nonempty prefix of those bytes, and at most one
byte read has no reply yet.  CRC-32 is `Library.Hashing.Crc.Spec.crc32`, the 32-bit frame check
sequence of ITU-T V.42 as a polynomial remainder over GF(2), the integer that `zlib.crc32` reports.

The proof carries `CrcAt` over the windows.  The state's low byte is the phase, its second byte
the reply, and its upper 32 bits the register, which holds the division's state after the bytes
read, `regOf`, as `Holds` of `Library/Hashing/Crc/Proof.lean` states.  In phases 0 and 3 every
byte read has its reply; in phase 1 the last byte read, the value of the last request, waits for
the table's step, which `byteStep_holds` relates to the division; and in phase 2 the reply to the
last byte lies in the second byte, and the next write sends it.  `crcUsart3_replies` and
`crcCmsdk_replies` instantiate the theorem for the two steps' maps.
-/

namespace TestSupport.M7.Crc

open LeanExe.Requests Library.Hashing.Crc Library.Hashing.Crc.Division Library.Hashing.Crc.Proof
open LeanExe.Native (readReq writeReq)

/-- USART3's registers in `crcStepWith`. -/
def crcUsart3 : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

/-- UART0's registers in `crcCmsdkWith`. -/
def crcCmsdk : Uart := ⟨0x1000, 0x1000, 0x1001, 2, 1, 0⟩

/-- The CRC-32 step by CRC-32's table for the register map `u`. -/
def crcTick (u : Uart) : UInt64 → UInt64 → UInt64 × UInt64 :=
  crcPhases u.rx u.tx u.status u.rxFull u.txMask u.txRoom crc32Table

/-- The reply to the bytes `bs`: the low byte of their CRC-32. -/
noncomputable def crcByte (bs : List UInt64) : UInt64 :=
  UInt64.ofNat (Spec.crc32 (bs.map UInt64.toUInt8) % 256)

/-- The replies to the bytes `bs`: the low byte of the CRC-32 of each nonempty prefix. -/
noncomputable def crcReplies (bs : List UInt64) : List UInt64 :=
  (List.range bs.length).map fun i => crcByte (bs.take (i + 1))

/-- The division's state after the bytes `bs` from 32 ones. -/
def regOf (bs : List UInt64) : Spec.Bits :=
  lfsr (lowBits 0x04C11DB7) (List.replicate 32 true) (Spec.bitsOfBytes (bs.map UInt64.toUInt8))

/-! ## Bytes, registers, and replies -/

theorem length_crcReplies (bs : List UInt64) : (crcReplies bs).length = bs.length := by
  simp [crcReplies]

theorem crcReplies_snoc (bs : List UInt64) (b : UInt64) :
    crcReplies (bs ++ [b]) = crcReplies bs ++ [crcByte (bs ++ [b])] := by
  unfold crcReplies
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton,
    List.take_of_length_le (show (bs ++ [b]).length ≤ bs.length + 1 by simp)]
  refine congrArg (· ++ [crcByte (bs ++ [b])]) (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [List.take_append_of_le_length (l₂ := [b]) (show i + 1 ≤ bs.length by omega)]

theorem regOf_snoc (bs : List UInt64) (b : UInt64) :
    regOf (bs ++ [b]) = lfsr (lowBits 0x04C11DB7) (regOf bs) (natBits 8 b.toNat) := by
  unfold regOf
  rw [List.map_append, List.map_singleton, bitsOfBytes_append, lfsr_append,
    bitsOfBytes_singleton, UInt64.toNat_toUInt8, natBits_mod]

theorem low_not (a : Nat) : (a ^^^ 0xFFFFFFFF) % 256 = a % 256 ^^^ 255 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    Nat.testBit_xor, Nat.testBit_mod_two_pow, show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one]
  by_cases h : i < 8
  · simp [h, show i < 32 by omega]
  · simp [h]

theorem toNat_low (s : UInt64) : (s &&& 255).toNat = s.toNat % 256 := by
  rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- A register that holds the division's state after the bytes `bs` gives their reply: the low
byte of the register's ones complement. -/
theorem crcByte_of_holds {bs : List UInt64} {r : UInt64} (hr : Holds r (regOf bs)) :
    crcByte bs = (r &&& 255) ^^^ 255 := by
  have hc : Spec.crc32 (bs.map UInt64.toUInt8) = r.toNat ^^^ 0xFFFFFFFF := by
    have h := toNat_eq_bitsValue (holds_not hr)
    rw [UInt64.toNat_xor] at h
    rw [crc32_eq, crc32Eval, crcBits]
    exact h.symm
  have hx : ((r &&& 255) ^^^ 255).toNat = r.toNat % 256 ^^^ 255 := by
    rw [UInt64.toNat_xor, toNat_low]
    rfl
  have h2 : r.toNat % 256 ^^^ 255 < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by decide)
  apply UInt64.toNat_inj.mp
  rw [hx, crcByte, hc, UInt64.toNat_ofNat', low_not]
  omega

theorem toNat_reg (s : UInt64) : (s >>> 32).toNat = s.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem toNat_second (s : UInt64) : ((s >>> 8) &&& 255).toNat = s.toNat / 256 % 256 := by
  rw [toNat_low, UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl,
    Nat.shiftRight_eq_div_pow]

theorem toNat_hi {r : UInt64} (hr : r.toNat < 2 ^ 32) : (r <<< 32).toNat = r.toNat * 2 ^ 32 := by
  rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_shl8 {x : UInt64} (hx : x.toNat < 256) : (x <<< 8).toNat = x.toNat * 2 ^ 8 := by
  rw [UInt64.toNat_shiftLeft, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]

/-- A register below 2^32 in the upper half and a value below 2^32 in the lower. -/
theorem toNat_pack {r c : UInt64} (hr : r.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (r <<< 32 ||| c).toNat = r.toNat * 2 ^ 32 + c.toNat := by
  rw [UInt64.toNat_or, toNat_hi hr, Nat.mul_comm r.toNat (2 ^ 32),
    ← Nat.two_pow_add_eq_or_of_lt hc]

theorem reg_lt (s : UInt64) : (s >>> 32).toNat < 2 ^ 32 := by
  rw [toNat_reg]
  have := s.toNat_lt
  omega

/-! ## The steps of the phases -/

section

variable (u : Uart) (s v : UInt64)

theorem tick_phase0 (hp : s &&& 255 = 0) :
    crcTick u s v = if (v &&& u.rxFull != 0) = true then (s >>> 32 <<< 32 ||| 1, readReq u.rx)
      else (s >>> 32 <<< 32, readReq u.status) := by
  dsimp only [crcTick, crcPhases]
  rw [hp]
  rfl

theorem tick_phase1 (hp : s &&& 255 = 1) :
    crcTick u s v = (((2 : UInt64) ||| (((byteStep crc32Table (s >>> 32) (v &&& 255) &&& 255) ^^^
      255) <<< 8)) ||| (byteStep crc32Table (s >>> 32) (v &&& 255) <<< 32), readReq u.status) := by
  dsimp only [crcTick, crcPhases]
  rw [hp]
  rfl

theorem tick_phase2 (hp : s &&& 255 = 2) :
    crcTick u s v = if (v &&& u.txMask == u.txRoom) = true then
        (s >>> 32 <<< 32 ||| 3, writeReq u.tx ((s >>> 8) &&& 255))
      else (s, readReq u.status) := by
  dsimp only [crcTick, crcPhases]
  rw [hp]
  rfl

theorem tick_phase3 (hp : s &&& 255 = 3) :
    crcTick u s v = (s >>> 32 <<< 32, readReq u.status) := by
  dsimp only [crcTick, crcPhases]
  rw [hp]
  rfl

end

/-- The state with the register `r` and the phase `c`. -/
theorem pack_phase {r c : UInt64} (hr : r.toNat < 2 ^ 32) (hc : c.toNat < 256) :
    (r <<< 32 ||| c) &&& 255 = c ∧ (r <<< 32 ||| c) >>> 32 = r := by
  have h := toNat_pack hr (by omega : c.toNat < 2 ^ 32)
  constructor
  · apply UInt64.toNat_inj.mp
    rw [toNat_low, h]
    omega
  · apply UInt64.toNat_inj.mp
    rw [toNat_reg, h]
    omega

theorem hi_phase {r : UInt64} (hr : r.toNat < 2 ^ 32) :
    (r <<< 32) &&& 255 = 0 ∧ (r <<< 32) >>> 32 = r := by
  have h := toNat_hi hr
  constructor
  · apply UInt64.toNat_inj.mp
    rw [toNat_low, h]
    show _ = 0
    omega
  · apply UInt64.toNat_inj.mp
    rw [toNat_reg, h]
    omega

/-- The state of phase 2 with the reply `x` and the register `r`. -/
theorem reply_phase {r x : UInt64} (hx : x.toNat < 256) :
    ((2 : UInt64) ||| (x <<< 8)) ||| (r <<< 32) = r <<< 32 ||| ((2 : UInt64) ||| (x <<< 8)) ∧
      ((2 : UInt64) ||| (x <<< 8)).toNat = 2 + x.toNat * 256 := by
  refine ⟨UInt64.toNat_inj.mp (by simp only [UInt64.toNat_or]; exact Nat.or_comm _ _), ?_⟩
  rw [UInt64.toNat_or, toNat_shl8 hx, show (2 : UInt64).toNat = 2 from rfl,
    Nat.mul_comm x.toNat (2 ^ 8), Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by decide : 2 < 2 ^ 8)]
  omega

/-! ## The invariant -/

/-- The step's state `s` with the last value read `v`, after the bytes `ins` read and the values
`outs` written: in phase 0 or 3 every byte has its reply; in phase 1 the last byte, the low byte
of `v`, waits; in phase 2 the second byte holds the reply to the last byte, which waits. -/
def CrcAt (s v : UInt64) (ins outs : List UInt64) : Prop :=
  ((s &&& 255 = 0 ∨ s &&& 255 = 3) ∧ Holds (s >>> 32) (regOf ins) ∧ outs = crcReplies ins) ∨
  (s &&& 255 = 1 ∧ ∃ ins0, ins = ins0 ++ [v &&& 255] ∧ Holds (s >>> 32) (regOf ins0) ∧
    outs = crcReplies ins0) ∨
  (s &&& 255 = 2 ∧ Holds (s >>> 32) (regOf ins) ∧ (s >>> 8) &&& 255 = crcByte ins ∧
    crcReplies ins = outs ++ [crcByte ins])

section

variable {α : Type} (B : Bus α) (u : Uart) (hrx : u.rx.toNat < 65536)
  (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status)
  (σ : Nat → UInt32) (s v : UInt64) (k : Nat) {ins outs : List UInt64}

/-- The invariant after the window from the state `s`, the last value `v`, and `k` reads. -/
def CrcNext (ins outs : List UInt64) : Prop :=
  CrcAt (reqNext (crcTick u) σ ⟨s, v, k⟩).state (reqNext (crcTick u) σ ⟨s, v, k⟩).last
    (ins ++ dataIn B u [reqEvent B (crcTick u) σ ⟨s, v, k⟩])
    (outs ++ dataOut B u [reqEvent B (crcTick u) σ ⟨s, v, k⟩])

include hrx hs hrs in
/-- After a window whose request reads the status, the invariant needs only the new state. -/
theorem crcNext_status {g : UInt64} (ht : crcTick u s v = (g, readReq u.status))
    (h : ∀ x, CrcAt g x ins outs) : CrcNext B u σ s v k ins outs := by
  obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨s, v, k⟩) ht (reqWrite_readReq hs)
  unfold CrcNext
  rw [h1, h2, h3, reqReg_readReq hs, dataIn_status B u hrx hs hrs, dataOut_read B u,
    List.append_nil, List.append_nil]
  exact h _

include hrx hs hrs in
theorem crcNext_phase0 (hp : s &&& 255 = 0) (hr : Holds (s >>> 32) (regOf ins))
    (ho : outs = crcReplies ins) : CrcNext B u σ s v k ins outs := by
  have hreg := reg_lt s
  by_cases hx : (v &&& u.rxFull != 0) = true
  · have ht : crcTick u s v = (s >>> 32 <<< 32 ||| 1, readReq u.rx) := by
      rw [tick_phase0 u s v hp, ite_eq_left_of_eq_true _ _ (eq_true hx)]
    obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨s, v, k⟩) ht (reqWrite_readReq hrx)
    obtain ⟨p1, p2⟩ := pack_phase (c := 1) hreg (by decide)
    unfold CrcNext
    rw [h1, h2, h3, reqReg_readReq hrx, dataIn_data B u, dataOut_read B u, List.append_nil]
    exact Or.inr (Or.inl ⟨p1, ins, rfl, by rw [p2]; exact hr, ho⟩)
  · obtain ⟨p1, p2⟩ := hi_phase hreg
    exact crcNext_status B u hrx hs hrs σ s v k
      (by rw [tick_phase0 u s v hp, ite_eq_right_of_eq_false _ _ (eq_false hx)])
      (fun _ => Or.inl ⟨Or.inl p1, by rw [p2]; exact hr, ho⟩)

include hrx hs hrs in
theorem crcNext_phase3 (hp : s &&& 255 = 3) (hr : Holds (s >>> 32) (regOf ins))
    (ho : outs = crcReplies ins) : CrcNext B u σ s v k ins outs := by
  obtain ⟨p1, p2⟩ := hi_phase (reg_lt s)
  exact crcNext_status B u hrx hs hrs σ s v k (tick_phase3 u s v hp)
    (fun _ => Or.inl ⟨Or.inl p1, by rw [p2]; exact hr, ho⟩)

include hrx hs hrs in
theorem crcNext_phase1 {ins0 : List UInt64} (hp : s &&& 255 = 1) (hin : ins = ins0 ++ [v &&& 255])
    (hr : Holds (s >>> 32) (regOf ins0)) (ho : outs = crcReplies ins0) :
    CrcNext B u σ s v k ins outs := by
  have hr' : Holds (byteStep crc32Table (s >>> 32) (v &&& 255)) (regOf ins) := by
    rw [hin, regOf_snoc ins0]
    exact byteStep_holds (length_lowBits _) crc32Table_of hr _
  generalize hR : byteStep crc32Table (s >>> 32) (v &&& 255) = R at hr'
  have hR32 : R.toNat < 2 ^ 32 := hr'.1
  have hx : ((R &&& 255) ^^^ 255).toNat < 256 := by
    rw [UInt64.toNat_xor, toNat_low]
    exact Nat.xor_lt_two_pow (n := 8) (by omega) (by decide)
  obtain ⟨e1, e2⟩ := reply_phase (r := R) hx
  have hpk := toNat_pack hR32 (by rw [e2]; omega)
  refine crcNext_status B u hrx hs hrs σ s v k
    (g := ((2 : UInt64) ||| ((R &&& 255) ^^^ 255) <<< 8) ||| R <<< 32)
    (by rw [tick_phase1 u s v hp, hR]) (fun _ => ?_)
  refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)
  · apply UInt64.toNat_inj.mp
    rw [e1, toNat_low, hpk, e2]
    show _ = 2
    omega
  · have : (((2 : UInt64) ||| ((R &&& 255) ^^^ 255) <<< 8) ||| R <<< 32) >>> 32 = R := by
      apply UInt64.toNat_inj.mp
      rw [e1, toNat_reg, hpk, e2]
      omega
    rw [this]
    exact hr'
  · have : ((((2 : UInt64) ||| ((R &&& 255) ^^^ 255) <<< 8) ||| R <<< 32) >>> 8) &&& 255 =
        (R &&& 255) ^^^ 255 := by
      apply UInt64.toNat_inj.mp
      rw [e1, toNat_second, hpk, e2]
      omega
    rw [this, crcByte_of_holds hr']
  · rw [hin, crcReplies_snoc, ho]

include hrx htx hs hrs in
theorem crcNext_phase2 (hp : s &&& 255 = 2) (hr : Holds (s >>> 32) (regOf ins))
    (hy : (s >>> 8) &&& 255 = crcByte ins) (ho : crcReplies ins = outs ++ [crcByte ins]) :
    CrcNext B u σ s v k ins outs := by
  by_cases hx : (v &&& u.txMask == u.txRoom) = true
  · have ht : crcTick u s v = (s >>> 32 <<< 32 ||| 3, writeReq u.tx ((s >>> 8) &&& 255)) := by
      rw [tick_phase2 u s v hp, ite_eq_left_of_eq_true _ _ (eq_true hx)]
    obtain ⟨h1, h2, h3⟩ :=
      next_write (B := B) (σ := σ) (r := ⟨s, v, k⟩) ht (reqWrite_writeReq _ htx)
    obtain ⟨p1, p2⟩ := pack_phase (c := 3) (reg_lt s) (by decide)
    have hb : ((s >>> 8) &&& 255).toNat < 256 := by rw [toNat_second]; omega
    unfold CrcNext
    rw [h1, h2, h3, reqReg_writeReq _ htx, dataIn_write B u, dataOut_write B u htx hb,
      List.append_nil]
    exact Or.inl ⟨Or.inr p1, by rw [p2]; exact hr, by rw [ho, hy]⟩
  · exact crcNext_status B u hrx hs hrs σ s v k
      (by rw [tick_phase2 u s v hp, ite_eq_right_of_eq_false _ _ (eq_false hx)])
      (fun _ => Or.inr (Or.inr ⟨hp, hr, hy, ho⟩))

include hrx htx hs hrs in
/-- One window keeps the invariant. -/
theorem crcAt_next (r : ReqState UInt64) (h : CrcAt r.state r.last ins outs) :
    CrcAt (reqNext (crcTick u) σ r).state (reqNext (crcTick u) σ r).last
      (ins ++ dataIn B u [reqEvent B (crcTick u) σ r])
      (outs ++ dataOut B u [reqEvent B (crcTick u) σ r]) := by
  obtain ⟨s, v, k⟩ := r
  change CrcAt s v ins outs at h
  change CrcNext B u σ s v k ins outs
  rcases h with ⟨hp | hp, hr, ho⟩ | ⟨hp, ins0, hin, hr, ho⟩ | ⟨hp, hr, hy, ho⟩
  · exact crcNext_phase0 B u hrx hs hrs σ s v k hp hr ho
  · exact crcNext_phase3 B u hrx hs hrs σ s v k hp hr ho
  · exact crcNext_phase1 B u hrx hs hrs σ s v k hp hin hr ho
  · exact crcNext_phase2 B u hrx htx hs hrs σ s v k hp hr hy ho

include hrx htx hs hrs in
/-- The invariant holds before every window from `crcInit`. -/
theorem crcAt_run : ∀ n,
    CrcAt (reqRun (crcTick u) crcInit σ n).state (reqRun (crcTick u) crcInit σ n).last
      (dataIn B u (windows (reqTrace B (crcTick u) crcInit σ) n))
      (dataOut B u (windows (reqTrace B (crcTick u) crcInit σ) n))
  | 0 => Or.inl ⟨Or.inr (show crcInit &&& 255 = 3 by decide),
      show Holds (crcInit >>> 32) (regOf []) by unfold Holds; decide, rfl⟩
  | n + 1 => by
      rw [windows, dataIn_append, dataOut_append]
      exact crcAt_next B u hrx htx hs hrs σ _ (crcAt_run n)

include hrx htx hs hrs in
/-- For every sequence `σ` of the values read and every number `N` of windows from `crcInit`, the
values that the windows write to the transmit register begin the low bytes of the CRC-32 of the
nonempty prefixes of the bytes that they read from the receive register, and at most one byte
read waits for its reply. -/
theorem crc_replies (N : Nat) :
    dataOut B u (windows (reqTrace B (crcTick u) crcInit σ) N) <+:
        crcReplies (dataIn B u (windows (reqTrace B (crcTick u) crcInit σ) N)) ∧
      (dataIn B u (windows (reqTrace B (crcTick u) crcInit σ) N)).length ≤
        (dataOut B u (windows (reqTrace B (crcTick u) crcInit σ) N)).length + 1 := by
  rcases crcAt_run B u hrx htx hs hrs σ N with ⟨-, -, ho⟩ | ⟨-, ins0, hin, -, ho⟩ | ⟨-, -, -, ho⟩
  · rw [ho, length_crcReplies]
    exact ⟨⟨[], List.append_nil _⟩, Nat.le_succ _⟩
  · rw [hin, ho, crcReplies_snoc, length_crcReplies, List.length_append, List.length_singleton]
    exact ⟨⟨_, rfl⟩, Nat.le_refl _⟩
  · rw [ho]
    refine ⟨⟨_, rfl⟩, ?_⟩
    have := congrArg List.length ho
    rw [length_crcReplies, List.length_append, List.length_singleton] at this
    omega

end

/-- `crc_replies` for `crcUsart3Tick` over USART3's registers. -/
theorem crcUsart3_replies {α : Type} (B : Bus α) (σ : Nat → UInt32) (N : Nat) :
    dataOut B crcUsart3 (windows (reqTrace B crcUsart3Tick crcInit σ) N) <+:
        crcReplies (dataIn B crcUsart3 (windows (reqTrace B crcUsart3Tick crcInit σ) N)) ∧
      (dataIn B crcUsart3 (windows (reqTrace B crcUsart3Tick crcInit σ) N)).length ≤
        (dataOut B crcUsart3 (windows (reqTrace B crcUsart3Tick crcInit σ) N)).length + 1 :=
  crc_replies B crcUsart3 (by decide) (by decide) (by decide) (by decide) σ N

/-- `crc_replies` for `crcCmsdkTick` over UART0's registers. -/
theorem crcCmsdk_replies {α : Type} (B : Bus α) (σ : Nat → UInt32) (N : Nat) :
    dataOut B crcCmsdk (windows (reqTrace B crcCmsdkTick crcInit σ) N) <+:
        crcReplies (dataIn B crcCmsdk (windows (reqTrace B crcCmsdkTick crcInit σ) N)) ∧
      (dataIn B crcCmsdk (windows (reqTrace B crcCmsdkTick crcInit σ) N)).length ≤
        (dataOut B crcCmsdk (windows (reqTrace B crcCmsdkTick crcInit σ) N)).length + 1 :=
  crc_replies B crcCmsdk (by decide) (by decide) (by decide) (by decide) σ N

end TestSupport.M7.Crc
