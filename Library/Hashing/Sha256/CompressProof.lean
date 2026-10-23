import Library.Hashing.Sha256.WordProof
import Library.Hashing.Sha2.Equiv.SHA256.Main

/-! `compress` computes the compression `SHS.SHA256.compress` of FIPS 180-4 §6.2.2 on the 32-bit
words that the low halves of its words hold, and therefore equals `SHS.SHA256.Impl.compress`,
which `SHS.Equiv.SHA256.compress_correct` relates to the same function.  The program keeps
sixteen schedule words in a window: after `t` rounds the window holds the words `t` to `t + 15`
of the specification's schedule, whose recurrence `schedule_succ` states. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words
open SHS.Equiv.SHA256.Lift SHS.Equiv.SHA256.Foldl.Schedule SHS.Equiv.SHA256.Foldl.Sequential
  SHS.Equiv.SHA256.Foldl.Fused

/-- The 32-bit words of eight words, as the implementation's state. -/
def _root_.Library.Hashing.Words.Words8.toVec32 (s : Words8) : SHS.SHA256.Impl.State :=
  #v[s.w0.toUInt32, s.w1.toUInt32, s.w2.toUInt32, s.w3.toUInt32, s.w4.toUInt32, s.w5.toUInt32,
    s.w6.toUInt32, s.w7.toUInt32]

/-- The 32-bit words of sixteen words, as the implementation's block. -/
def _root_.Library.Hashing.Words.Words16.toVec32 (m : Words16) : SHS.SHA256.Impl.Block :=
  #v[m.w0.toUInt32, m.w1.toUInt32, m.w2.toUInt32, m.w3.toUInt32, m.w4.toUInt32, m.w5.toUInt32,
    m.w6.toUInt32, m.w7.toUInt32, m.w8.toUInt32, m.w9.toUInt32, m.w10.toUInt32, m.w11.toUInt32,
    m.w12.toUInt32, m.w13.toUInt32, m.w14.toUInt32, m.w15.toUInt32]

/-- Word `k` of a window. -/
def _root_.Library.Hashing.Words.Words16.get (m : Words16) (k : Nat) : UInt64 :=
  #[m.w0, m.w1, m.w2, m.w3, m.w4, m.w5, m.w6, m.w7, m.w8, m.w9, m.w10, m.w11, m.w12, m.w13, m.w14,
    m.w15][k]!

@[simp] theorem get0 (m : Words16) : m.get 0 = m.w0 := rfl
@[simp] theorem get1 (m : Words16) : m.get 1 = m.w1 := rfl
@[simp] theorem get9 (m : Words16) : m.get 9 = m.w9 := rfl
@[simp] theorem get14 (m : Words16) : m.get 14 = m.w14 := rfl
@[simp] theorem get15 (m : Words16) : m.get 15 = m.w15 := rfl

/-- The specification's schedule after `j` steps, as `Nat.fold`. -/
def schedulePrefix (M : Vector (BitVec 32) 16) (j : Nat) : Vector (BitVec 32) 64 :=
  Nat.fold j (fun t _ W => specScheduleStep M t W) (Vector.replicate 64 default)

/-- Steps after `j` leave word `j` unchanged. -/
theorem schedulePrefix_stable (M : Vector (BitVec 32) 16) (j : Nat) :
    ∀ n, j < n → (schedulePrefix M n)[j]! = (schedulePrefix M (j + 1))[j]! := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j + 1 = n + 1
    · rw [h]
    · have hjn : j < n := by omega
      unfold schedulePrefix at ih ⊢
      rw [Nat.fold_succ (n := n), getElem!_specScheduleStep_ne _ _ _ _ (by omega)]
      exact ih hjn

/-- The value that step `t` writes, from the words before it. -/
def scheduleValue (M : Vector (BitVec 32) 16) (t : Nat) (W : Vector (BitVec 32) 64) : BitVec 32 :=
  if t < 16 then M[t]!
  else SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! + SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!

theorem scheduleStep_eq (M : Vector (BitVec 32) 16) (t : Nat) (W : Vector (BitVec 32) 64)
    (ht : t < 64) : (specScheduleStep M t W)[t]! = scheduleValue M t W := by
  unfold specScheduleStep scheduleValue
  split <;>
    rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ ht,
      SHS.Equiv.VecBridge.set_bang_eq_set _ _ ht, Vector.getElem_set_self]

theorem scheduleValue_congr (M : Vector (BitVec 32) 16) (t : Nat) (W W' : Vector (BitVec 32) 64)
    (h : ∀ j, j < t → W[j]! = W'[j]!) : scheduleValue M t W = scheduleValue M t W' := by
  unfold scheduleValue
  split
  · rfl
  · rw [h (t - 2) (by omega), h (t - 7) (by omega), h (t - 15) (by omega), h (t - 16) (by omega)]

/-- The specification's schedule satisfies the recurrence of §6.2.2 step 1. -/
theorem schedule_succ (M : Vector (BitVec 32) 16) (t : Nat) (ht : t < 64) :
    (SHS.SHA256.schedule M)[t]! = scheduleValue M t (SHS.SHA256.schedule M) := by
  have hfull : SHS.SHA256.schedule M = schedulePrefix M 64 := by
    rw [schedule_eq_foldl]
    unfold schedulePrefix
    exact finFoldl_eq_fold 64 (fun t W => specScheduleStep M t W) _
  rw [hfull, schedulePrefix_stable M t 64 ht]
  unfold schedulePrefix
  rw [Nat.fold_succ (n := t), scheduleStep_eq _ _ _ ht]
  apply scheduleValue_congr
  intro j hj
  have := schedulePrefix_stable M j 64 (by omega)
  have h2 := schedulePrefix_stable M j t hj
  unfold schedulePrefix at this h2
  rw [this, h2]

theorem toSpecBlock_get (m : Words16) (k : Nat) (hk : k < 16) :
    (toSpecBlock m.toVec32)[k]! = (m.get k).toUInt32.toBitVec := by
  interval_cases k <;> simp [toSpecBlock, Words16.toVec32, Words16.get, getElem!_pos]

/-- After `t` advances, word `k` of the window holds word `t + k` of the schedule of the first
window. -/
theorem window (m : Words16) : ∀ t k, k < 16 → t + k < 64 →
    ((advance^[t] m).get k).toUInt32.toBitVec =
      (SHS.SHA256.schedule (toSpecBlock m.toVec32))[t + k]! := by
  intro t
  induction t with
  | zero =>
    intro k hk _
    rw [Function.iterate_zero_apply, Nat.zero_add, schedule_succ _ _ (by omega)]
    unfold scheduleValue
    rw [ite_eq_left hk, toSpecBlock_get m k hk]
  | succ t ih =>
    intro k hk htk
    rw [Function.iterate_succ_apply']
    by_cases h15 : k < 15
    · have := ih (k + 1) (by omega) (by omega)
      rw [show t + 1 + k = t + (k + 1) by omega, ← this]
      interval_cases k <;> rfl
    · have hk15 : k = 15 := by omega
      subst hk15
      rw [show t + 1 + 15 = t + 16 by omega, schedule_succ _ _ (by omega)]
      unfold scheduleValue
      rw [ite_eq_right (by omega)]
      simp only [show t + 16 - 2 = t + 14 by omega, show t + 16 - 7 = t + 9 by omega,
        show t + 16 - 15 = t + 1 by omega, show t + 16 - 16 = t by omega]
      have h0 := ih 0 (by omega) (by omega)
      rw [Nat.add_zero] at h0
      rw [← ih 14 (by omega) (by omega), ← ih 9 (by omega) (by omega),
        ← ih 1 (by omega) (by omega), ← h0]
      generalize advance^[t] m = w
      show (smallSigma1 w.w14 + w.w9 + smallSigma0 w.w1 + w.w0).toUInt32.toBitVec = _
      simp only [get0, get1, get9, get14, UInt64.toUInt32_add, UInt32.toBitVec_add,
        smallSigma0_toUInt32, smallSigma1_toUInt32, SHS.Equiv.SHA256.Functions.smallSigma0_toBitVec,
        SHS.Equiv.SHA256.Functions.smallSigma1_toBitVec]

theorem roundConstants_get (t : Nat) (ht : t < 64) :
    (roundConstants[t]!).toUInt32.toBitVec = SHS.SHA256.K[t]! := by
  interval_cases t <;> rfl

set_option maxHeartbeats 1600000 in
/-- One round of the program is the specification's round. -/
theorem roundStep_spec (W : Vector (BitVec 32) 64) (t : Nat) (k w : UInt64) (s : Words8)
    (hk : k.toUInt32.toBitVec = SHS.SHA256.K[t]!) (hw : w.toUInt32.toBitVec = W[t]!) :
    toSpecState (roundStep k w s).toVec32 = specRoundStep W t (toSpecState s.toVec32) := by
  unfold specRoundStep
  rw [← hk, ← hw]
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [roundStep, Words8.toVec32, toSpecState, Vector.getElem_map, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toUInt32_add,
      UInt32.toBitVec_add, bigSigma0_toUInt32, bigSigma1_toUInt32, ch_toUInt32, maj_toUInt32,
      SHS.Equiv.SHA256.Functions.bigSigma0_toBitVec, SHS.Equiv.SHA256.Functions.bigSigma1_toBitVec,
      SHS.Equiv.SHA256.Functions.Ch_toBitVec, SHS.Equiv.SHA256.Functions.Maj_toBitVec]

/-- The rounds of the program, as a fold over the round index. -/
theorem rounds (k : Array UInt64) (h : Words8) (m : Words16) (n : Nat) :
    Nat.fold n (fun i _ sw => (roundStep k[(UInt64.ofNat i).toNat]! sw.2.w0 sw.1, advance sw.2))
        (h, m) =
      (Nat.fold n (fun i _ s => roundStep k[(UInt64.ofNat i).toNat]! (advance^[i] m).w0 s) h,
        advance^[n] m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ih, Function.iterate_succ_apply']

theorem rounds_spec (h : Words8) (m : Words16) : ∀ n, n ≤ 64 →
    toSpecState (Nat.fold n (fun i _ s => roundStep roundConstants[(UInt64.ofNat i).toNat]!
        (advance^[i] m).w0 s) h).toVec32 =
      Fin.foldl n (fun s (t : Fin n) =>
        specRoundStep (SHS.SHA256.schedule (toSpecBlock m.toVec32)) t.val s)
        (toSpecState h.toVec32) := by
  intro n hn
  rw [finFoldl_eq_fold n
    (fun t s => specRoundStep (SHS.SHA256.schedule (toSpecBlock m.toVec32)) t s)]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ← ih (by omega)]
    have hn' : (UInt64.ofNat n).toNat = n := by rw [UInt64.toNat_ofNat']; omega
    rw [hn']
    apply roundStep_spec _ n _ _ _ (roundConstants_get n (by omega))
    have := window m n 0 (by omega) (by omega)
    simpa using this

theorem initVars_toSpecState (s : SHS.SHA256.Impl.State) :
    initVars (toSpecState s) = toSpecState s := by
  apply Vector.ext
  intro i hi
  simp [initVars, toSpecState, getElem!_pos]

/-- `compress` with the round constants is the specification's compression. -/
theorem compress_spec (h : Words8) (m : Words16) :
    toSpecState (compress roundConstants h m).toVec32 =
      SHS.SHA256.compress (toSpecState h.toVec32) (toSpecBlock m.toVec32) := by
  rw [spec_compress_eq_seq, specCompressSeq, initVars_toSpecState]
  have hs : toSpecState (LeanExe.loop 64 (h, m) fun t sw =>
      (roundStep roundConstants[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1.toVec32 =
      Fin.foldl 64 (fun s (t : Fin 64) =>
        specRoundStep (SHS.SHA256.schedule (toSpecBlock m.toVec32)) t.val s)
        (toSpecState h.toVec32) := by
    rw [LeanExe.loop, rounds]
    exact rounds_spec h m 64 (by decide)
  unfold compress
  generalize (LeanExe.loop 64 (h, m) fun t sw =>
      (roundStep roundConstants[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1 = s at hs ⊢
  simp only [← hs]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [addH, toSpecState, Words8.toVec32, UInt64.toUInt32_add,
    UInt32.toBitVec_add, getElem!_pos]

theorem toSpecState_injective {a b : SHS.SHA256.Impl.State}
    (h : toSpecState a = toSpecState b) : a = b := by
  apply Vector.ext
  intro i hi
  have := congrArg (·[i]) h
  simp only [toSpecState, Vector.getElem_map] at this
  exact UInt32.toBitVec_inj.mp this

/-- `compress` with the round constants is the implementation's compression. -/
theorem compress_toVec32 (h : Words8) (m : Words16) :
    (compress roundConstants h m).toVec32 = SHS.SHA256.Impl.compress h.toVec32 m.toVec32 := by
  apply toSpecState_injective
  rw [SHS.Equiv.SHA256.compress_correct]
  exact compress_spec h m

end Library.Hashing.Sha256
