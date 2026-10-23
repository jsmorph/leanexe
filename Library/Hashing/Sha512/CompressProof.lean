import Library.Hashing.Sha512.Program
import Library.Hashing.Sha2.Equiv.SHA512.Compress.Impl

/-! `compress` equals `SHS.SHA512.Impl.compress`, the compression of FIPS 180-4 §6.4.2 in the
copied implementation, which `SHS.Equiv.SHA512.compress_correct` proves equal to the
specification.  The program keeps sixteen schedule words in a window: after `t` rounds the window
holds the words `t` to `t + 15` of the full schedule, whose recurrence `schedule_succ` states. -/

namespace Library.Hashing.Sha512

open Library.Hashing.Words
open SHS.Equiv.SHA512.Compress.Impl

/-- The eight words as the implementation's state, `w0` to `w7` in order. -/
def _root_.Library.Hashing.Words.Words8.toVec (s : Words8) : SHS.SHA512.Impl.State :=
  #v[s.w0, s.w1, s.w2, s.w3, s.w4, s.w5, s.w6, s.w7]

/-- The sixteen words as the implementation's block, `w0` to `w15` in order. -/
def _root_.Library.Hashing.Words.Words16.toVec (m : Words16) : SHS.SHA512.Impl.Block :=
  #v[m.w0, m.w1, m.w2, m.w3, m.w4, m.w5, m.w6, m.w7, m.w8, m.w9, m.w10, m.w11, m.w12, m.w13,
    m.w14, m.w15]

theorem xor_ones (x : UInt64) : x ^^^ 0xFFFFFFFFFFFFFFFF = ~~~x := by
  apply UInt64.toBitVec_inj.mp
  have h : (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 := by decide
  rw [UInt64.toBitVec_xor, UInt64.toBitVec_not, h, BitVec.xor_allOnes]

/-- `Fin.foldl` over the indices below `n` as `Nat.fold`. -/
theorem finFoldl_eq_fold {β : Type} (n : Nat) (g : Nat → β → β) (init : β) :
    Fin.foldl n (fun x (i : Fin n) => g i.val x) init = Nat.fold n (fun i _ x => g i x) init := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Nat.fold_succ]
    exact congrArg (g n) ih

/-- The schedule after `j` steps, as `Nat.fold`. -/
def schedulePrefix (b : SHS.SHA512.Impl.Block) (j : Nat) : SHS.SHA512.Impl.Schedule :=
  Nat.fold j (fun t _ w => implScheduleStep b t w) (Vector.replicate 80 0)

theorem scheduleStep_ne (b : SHS.SHA512.Impl.Block) (t : Nat) (w : SHS.SHA512.Impl.Schedule)
    (j : Nat) (hj : j ≠ t) : (implScheduleStep b t w)[j]! = w[j]! := by
  have key : ∀ v : UInt64, (w.set! t v)[j]! = w[j]! := by
    intro v
    by_cases hj' : j < 80
    · rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ hj',
        SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ hj']
      by_cases ht : t < 80
      · rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ ht, Vector.getElem_set, if_neg (Ne.symm hj)]
      · rw [SHS.Equiv.VecBridge.set_bang_oob _ _ _ ht]
    · rw [SHS.Equiv.VecBridge.getElem_bang_oob _ _ hj', SHS.Equiv.VecBridge.getElem_bang_oob _ _ hj']
  unfold implScheduleStep
  split <;> apply key

/-- Steps after `j` leave word `j` unchanged. -/
theorem schedulePrefix_stable (b : SHS.SHA512.Impl.Block) (j : Nat) :
    ∀ n, j < n → (schedulePrefix b n)[j]! = (schedulePrefix b (j + 1))[j]! := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : j + 1 = n + 1
    · rw [h]
    · have hjn : j < n := by omega
      unfold schedulePrefix at ih ⊢
      rw [Nat.fold_succ (n := n), scheduleStep_ne _ _ _ _ (by omega)]
      exact ih hjn

/-- The value that step `t` writes, from the words before it. -/
def scheduleValue (b : SHS.SHA512.Impl.Block) (t : Nat) (w : SHS.SHA512.Impl.Schedule) : UInt64 :=
  if t < 16 then b[t]!
  else
    let w15 := w[t - 15]!
    let s0 := (SHS.SHA512.Impl.UInt64.rotr w15 1) ^^^ (SHS.SHA512.Impl.UInt64.rotr w15 8) ^^^
      (w15 >>> 7)
    let w2 := w[t - 2]!
    let s1 := (SHS.SHA512.Impl.UInt64.rotr w2 19) ^^^ (SHS.SHA512.Impl.UInt64.rotr w2 61) ^^^
      (w2 >>> 6)
    w[t - 16]! + s0 + w[t - 7]! + s1

theorem scheduleStep_eq (b : SHS.SHA512.Impl.Block) (t : Nat) (w : SHS.SHA512.Impl.Schedule)
    (ht : t < 80) : (implScheduleStep b t w)[t]! = scheduleValue b t w := by
  unfold implScheduleStep scheduleValue
  split <;>
    rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem _ _ ht,
      SHS.Equiv.VecBridge.set_bang_eq_set _ _ ht, Vector.getElem_set_self]

/-- `scheduleValue` reads only the words before `t`. -/
theorem scheduleValue_congr (b : SHS.SHA512.Impl.Block) (t : Nat) (w w' : SHS.SHA512.Impl.Schedule)
    (h : ∀ j, j < t → w[j]! = w'[j]!) : scheduleValue b t w = scheduleValue b t w' := by
  unfold scheduleValue
  split
  · rfl
  · rw [h (t - 15) (by omega), h (t - 2) (by omega), h (t - 16) (by omega), h (t - 7) (by omega)]

/-- The full schedule satisfies the recurrence of §6.4.2 step 1. -/
theorem schedule_succ (b : SHS.SHA512.Impl.Block) (t : Nat) (ht : t < 80) :
    (implScheduleFoldl b)[t]! = scheduleValue b t (implScheduleFoldl b) := by
  have hfull : implScheduleFoldl b = schedulePrefix b 80 := by
    unfold implScheduleFoldl schedulePrefix
    exact finFoldl_eq_fold 80 (fun t w => implScheduleStep b t w) _
  rw [hfull, schedulePrefix_stable b t 80 ht]
  unfold schedulePrefix
  rw [Nat.fold_succ (n := t), scheduleStep_eq _ _ _ ht]
  apply scheduleValue_congr
  intro j hj
  have := schedulePrefix_stable b j 80 (by omega)
  have h2 := schedulePrefix_stable b j t hj
  unfold schedulePrefix at this h2
  rw [this, h2]

/-- Word `k` of a window. -/
def _root_.Library.Hashing.Words.Words16.get (m : Words16) (k : Nat) : UInt64 := m.toVec[k]!

@[simp] theorem get0 (m : Words16) : m.get 0 = m.w0 := rfl
@[simp] theorem get1 (m : Words16) : m.get 1 = m.w1 := rfl
@[simp] theorem get9 (m : Words16) : m.get 9 = m.w9 := rfl
@[simp] theorem get14 (m : Words16) : m.get 14 = m.w14 := rfl
@[simp] theorem get15 (m : Words16) : m.get 15 = m.w15 := rfl

/-- After `t` advances, word `k` of the window is word `t + k` of the schedule of the first
window. -/
theorem window (m : Words16) : ∀ t k, k < 16 → t + k < 80 →
    (advance^[t] m).get k = (implScheduleFoldl m.toVec)[t + k]! := by
  intro t
  induction t with
  | zero =>
    intro k hk _
    rw [Function.iterate_zero_apply, Nat.zero_add, schedule_succ _ _ (by omega)]
    unfold scheduleValue
    rw [if_pos hk]
    rfl
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
      rw [if_neg (by omega)]
      simp only [show t + 16 - 15 = t + 1 by omega, show t + 16 - 2 = t + 14 by omega,
        show t + 16 - 16 = t by omega, show t + 16 - 7 = t + 9 by omega]
      have h0 := ih 0 (by omega) (by omega)
      rw [Nat.add_zero] at h0
      rw [← ih 1 (by omega) (by omega), ← ih 14 (by omega) (by omega), ← h0,
        ← ih 9 (by omega) (by omega)]
      generalize advance^[t] m = w
      show w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14 = _
      simp only [get0, get1, get9, get14, smallSigma0, smallSigma1, rotr,
        SHS.SHA512.Impl.UInt64.rotr]

theorem roundConstants_get (t : Nat) (ht : t < 80) :
    roundConstants[t]! = SHS.SHA512.Impl.K64[t]! := by
  interval_cases t <;> rfl

set_option maxHeartbeats 1600000 in
/-- One round of the program is the implementation's round. -/
theorem roundStep_toVec (W : SHS.SHA512.Impl.Schedule) (t : Nat) (s : Words8)
    (ht : t < 80) :
    (roundStep roundConstants[t]! W[t]! s).toVec = implRoundStep W t s.toVec := by
  rw [roundConstants_get t ht]
  unfold implRoundStep
  generalize SHS.SHA512.Impl.K64[t]! = k
  generalize W[t]! = w
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [roundStep, Words8.toVec, ch, maj, bigSigma0, bigSigma1, rotr, xor_ones,
      SHS.SHA512.Impl.UInt64.rotr]

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

theorem rounds_toVec (h : Words8) (m : Words16) : ∀ n, n ≤ 80 →
    (Nat.fold n (fun i _ s => roundStep roundConstants[(UInt64.ofNat i).toNat]!
        (advance^[i] m).w0 s) h).toVec =
      Fin.foldl n (fun s (t : Fin n) => implRoundStep (implScheduleFoldl m.toVec) t.val s)
        h.toVec := by
  intro n hn
  rw [finFoldl_eq_fold n (fun t s => implRoundStep (implScheduleFoldl m.toVec) t s)]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.fold_succ, Nat.fold_succ, ← ih (by omega)]
    have hw : (advance^[n] m).w0 = (implScheduleFoldl m.toVec)[n]! := by
      have := window m n 0 (by omega) (by omega)
      simpa [Words16.get, Words16.toVec] using this
    have hn' : (UInt64.ofNat n).toNat = n := by
      rw [UInt64.toNat_ofNat']; omega
    rw [hn', hw]
    exact roundStep_toVec _ n _ (by omega)

/-- `compress` with the round constants is the implementation's compression. -/
theorem compress_toVec (h : Words8) (m : Words16) :
    (compress roundConstants h m).toVec = SHS.SHA512.Impl.compress h.toVec m.toVec := by
  rw [← impl_compress_eq_foldl]
  have hs : (LeanExe.loop 80 (h, m) fun t sw =>
      (roundStep roundConstants[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1.toVec =
      Fin.foldl 80 (fun x (t : Fin 80) => implRoundStep (implScheduleFoldl m.toVec) t.val x)
        h.toVec := by
    rw [LeanExe.loop, rounds]
    exact rounds_toVec h m 80 (by decide)
  unfold compress
  generalize (LeanExe.loop 80 (h, m) fun t sw =>
      (roundStep roundConstants[t.toNat]! sw.2.w0 sw.1, advance sw.2)).1 = s at hs ⊢
  rw [implCompressFoldl]
  rw [← messageSchedule_eq_foldl] at hs
  simp only [← hs]
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Words8.toVec]

end Library.Hashing.Sha512
