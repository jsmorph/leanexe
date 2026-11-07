import LeanExe.M7.Div
import LeanExe.M7.Proof.Straight
import LeanExe.M7.Proof.Pair

/-!
The theorem of `udivmod64`: from the routine's entry, with a nonzero divisor in r2 and r3, the
model reaches the return to LR with the quotient and the remainder of Lean's `UInt64` division in
r0 and r1 and in r2 and r3, keeping SP, LR, r8 to r12, the memory, the device trace, and the
number of device reads.  Each piece of the routine has a lemma that runs it from a state at its
address.  The tests and the comparison branch to the piece whose condition holds, `low` and `high`
return the results of `UDIV` and `MLS`, and `small` returns the dividend as the remainder.
`count`, `shift`, and `clear` set up the loop, whose invariant `LoopInv` describes the state after
each pass with the number of passes left: the shifted divisor is the divisor times `2^k / 2`, and
the quotient bits so far and the remainder give the dividend with the remainder below the divisor
times `2^k`.  `run_pass` keeps the invariant with one pass fewer, and after the last pass `done`
returns the quotient and the remainder.
-/

namespace LeanExe.M7

open Udiv

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Arithmetic -/

theorem div_mod_eq {n d q r : Nat} (h : n = q * d + r) (hr : r < d) : n / d = q ∧ n % d = r := by
  have hd : 0 < d := by omega
  constructor
  · rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The quotient and the remainder by a divisor whose low word is 0. -/
theorem div_high {n0 n1 d1 : Nat} (hn0 : n0 < 4294967296) (hd : 0 < d1) :
    (n1 * 4294967296 + n0) / (d1 * 4294967296) = n1 / d1 ∧
      (n1 * 4294967296 + n0) % (d1 * 4294967296) = n1 % d1 * 4294967296 + n0 := by
  apply div_mod_eq
  · have h := Nat.div_add_mod' n1 d1
    have e : n1 / d1 * (d1 * 4294967296) = n1 / d1 * d1 * 4294967296 := by
      rw [Nat.mul_assoc]
    rw [e]
    generalize n1 / d1 * d1 = p at *
    omega
  · have := Nat.mod_lt n1 hd
    omega

/-- The shift that the leading zero counts `cd` of the divisor and `cn` of the dividend give puts
the divisor's top bit at the dividend's, so the shifted divisor fits 64 bits and twice it exceeds
the dividend. -/
theorem norm_arith {N D cd cn : Nat} (hcd : cd ≤ 63) (hD1 : 2 ^ (63 - cd) ≤ D)
    (hD2 : D < 2 ^ (64 - cd)) (hN2 : N < 2 ^ (64 - cn)) (hle : D ≤ N) :
    cn ≤ cd ∧ D * 2 ^ (cd - cn) < 18446744073709551616 ∧ N < D * 2 ^ (cd - cn + 1) := by
  have hcn : cn ≤ cd := by
    apply Nat.le_of_not_lt
    intro h
    have : 2 ^ (64 - cn) ≤ 2 ^ (63 - cd) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨hcn, ?_, ?_⟩
  · calc D * 2 ^ (cd - cn) < 2 ^ (64 - cd) * 2 ^ (cd - cn) :=
          Nat.mul_lt_mul_of_pos_right hD2 (Nat.two_pow_pos _)
      _ = 2 ^ (64 - cn) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  · calc N < 2 ^ (64 - cn) := hN2
      _ = 2 ^ (63 - cd) * 2 ^ (cd - cn + 1) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ D * 2 ^ (cd - cn + 1) := Nat.mul_le_mul_right _ hD1

/-- Adding the divisor `X` back after a subtraction modulo 2^64 that borrowed restores the
remainder `R`.  A lemma of its own keeps the many hypotheses of the pass out of `omega`'s
problem. -/
theorem restore_eq {n q2 R X : Nat} (hR : R < 18446744073709551616)
    (hX : X < 18446744073709551616) (heq : n = q2 + R) (hlt : R < X) :
    n = q2 + ((R + 18446744073709551616 - X) % 18446744073709551616 + X) % 18446744073709551616 := by
  omega

/-- A pass with the shifted divisor `X` and the remainder `R < 2X` keeps `n = q · 2X + R` as
`n = q' · X + R'` with `R' < X`, where `q'` is `2q + 1` and `R'` is `R - X` when `X ≤ R`, and `q'`
is `2q` and `R'` is `R` otherwise; `q'` fits 64 bits. -/
theorem pass_arith {n q R X : Nat} (hX : 0 < X) (hn : n < 18446744073709551616)
    (heq : n = q * (2 * X) + R) (hlt : R < 2 * X) :
    (X ≤ R → n = (2 * q + 1) * X + (R - X) ∧ R - X < X ∧ 2 * q + 1 < 18446744073709551616) ∧
      (¬ X ≤ R → n = 2 * q * X + R ∧ R < X ∧ 2 * q < 18446744073709551616) := by
  have e1 : q * (2 * X) = 2 * (q * X) := by rw [Nat.mul_left_comm]
  have e2 : (2 * q + 1) * X = 2 * (q * X) + X := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e3 : 2 * q * X = 2 * (q * X) := Nat.mul_assoc _ _ _
  have hq : q ≤ q * X := Nat.le_mul_of_pos_right _ hX
  rw [e1] at heq
  rw [e2, e3]
  generalize q * X = A at *
  constructor <;> intro h <;> refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Addresses and pieces -/

/-- `addr_eq` for addresses that name the pieces of `udivmod64`. -/
macro "udiv_addr" : tactic =>
  `(tactic| ((try simp only [Udiv.test, Udiv.low, Udiv.high, Udiv.compare, Udiv.count, Udiv.shift,
    Udiv.clear, Udiv.pass, Udiv.done, Udiv.small]); addr_eq))

theorem udivmod64_pieces {a : UInt32} (hc : CodeAt code a udivmod64) :
    CodeAt code a test ∧ CodeAt code (a + 16) low ∧ CodeAt code (a + 32) high ∧
      CodeAt code (a + 56) compare ∧ CodeAt code (a + 68) count ∧ CodeAt code (a + 92) shift ∧
      CodeAt code (a + 128) clear ∧ CodeAt code (a + 136) pass ∧ CodeAt code (a + 192) done ∧
      CodeAt code (a + 212) small := by
  simp only [udivmod64, List.append_assoc, CodeAt.append, add_ofNat_add] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## Results -/

/-- From `s` the model reaches the return to LR with the quotient of `n` by `d` in r0 and r1 and
the remainder in r2 and r3, and keeps what `Keeps` names. -/
def Returns (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16) (s : State)
    (n d : Nat) : Prop :=
  ∃ t, Reach P σ code s t ∧ t.pc = s.lr &&& 0xFFFFFFFE ∧ pairNat (t.r 0) (t.r 1) = n / d ∧
    pairNat (t.r 2) (t.r 3) = n % d ∧ Keeps s t

theorem Returns.back {s u : State} {n d : Nat} (hr : Reach P σ code s u) (hk : Keeps s u)
    (h : Returns P σ code u n d) : Returns P σ code s n d := by
  obtain ⟨t, ht, hpc, hq, hm, hkt⟩ := h
  exact ⟨t, hr.trans ht, by rw [hpc, hk.lr], hq, hm, hk.trans hkt⟩

/-- Placed straight-line register code followed by `BX LR` returns the results that its last
state holds. -/
theorem returns_seq {xs : List Instr} {s t : State} {n d : Nat} (hf : xs.all Instr.falls = true)
    (hr : xs.all Instr.regOnly = true) (hc : CodeAt code s.pc (xs ++ [.bxLr]))
    (he : execSeq P σ xs s = some t) (hlr : s.lr % 2 = 1) (hq : pairNat (t.r 0) (t.r 1) = n / d)
    (hm : pairNat (t.r 2) (t.r 3) = n % d) : Returns P σ code s n d := by
  obtain ⟨c1, c2⟩ := CodeAt.append.mp hc
  obtain ⟨r1, p1, k1⟩ := run_block hf hr c1 he
  rw [← p1] at c2
  exact ⟨_, r1.trans (reach_bxLr c2 (by rw [k1.lr]; exact hlr)), by simp [k1.lr], hq, hm,
    k1.withPc _⟩

/-! ## The tests -/

/-- `CMP r2, #0` and `BEQ high`. -/
theorem run_test0 {a : UInt32} {s : State} (hc : CodeAt code a test) (hpc : s.pc = a) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ (∀ i, t.r i = s.r i) ∧
      t.pc = if s.r 2 = 0 then a + 32 else a + 8 := by
  rw [show test = ([.cmpImm 2 0] ++ [Instr.bcondTo 0 24]) ++
    ([.orrReg 1 4 1 3] ++ [Instr.bcondTo 1 40]) from rfl] at hc
  obtain ⟨c1, -⟩ := CodeAt.append.mp hc
  rw [← hpc] at c1
  obtain ⟨u, hr, hk, hregs, hp⟩ := run_branch (P := P) (σ := σ) (t := _)
    (a + 32) (a + 8) rfl rfl c1 rfl (by decide) (by decide) (by decide) (by rw [hpc]; udiv_addr)
    (by rw [hpc]; udiv_addr)
  state_simp at hp
  rw [cmp_imm0] at hp
  refine ⟨u, hr, hk, fun i => ?_, ?_⟩
  · rw [State.r_of_regs hregs]
    state_simp
  · rw [hp]
    by_cases h : s.r 2 = 0 <;> simp [h]

/-- `ORRS r4, r1, r3` and `BNE compare`. -/
theorem run_test1 {a : UInt32} {s : State} (hc : CodeAt code a test) (hpc : s.pc = a + 8) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ t.r 0 = s.r 0 ∧ t.r 1 = s.r 1 ∧ t.r 2 = s.r 2 ∧
      t.r 3 = s.r 3 ∧ t.pc = if s.r 1 = 0 ∧ s.r 3 = 0 then a + 16 else a + 56 := by
  rw [show test = ([.cmpImm 2 0] ++ [Instr.bcondTo 0 24]) ++
    ([.orrReg 1 4 1 3] ++ [Instr.bcondTo 1 40]) from rfl] at hc
  obtain ⟨-, c2⟩ := CodeAt.append.mp hc
  rw [show a + UInt32.ofNat (codeSize ([.cmpImm 2 0] ++ [Instr.bcondTo 0 24])) = s.pc by
    rw [hpc]; udiv_addr] at c2
  obtain ⟨u, hr, hk, hregs, hp⟩ := run_branch (P := P) (σ := σ) (t := _)
    (a + 56) (a + 16) rfl rfl c2 rfl (by decide) (by decide) (by decide) (by rw [hpc]; udiv_addr)
    (by rw [hpc]; udiv_addr)
  state_simp at hp
  refine ⟨u, hr, hk, ?_, ?_, ?_, ?_, ?_⟩
  iterate 4 (rw [State.r_of_regs hregs]; state_simp)
  rw [hp]
  by_cases h : s.r 1 = 0 ∧ s.r 3 = 0
  · simp [h]
  · have : s.r 1 ||| s.r 3 ≠ 0 := fun e => h (UInt32.or_eq_zero_iff.mp e)
    simp [h, this]

/-- `SUBS r4, r0, r2`, `SBCS r4, r1, r3`, and `BCC small`. -/
theorem run_compare {a : UInt32} {s : State} (hc : CodeAt code (a + 56) compare)
    (hpc : s.pc = a + 56) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ t.r 0 = s.r 0 ∧ t.r 1 = s.r 1 ∧ t.r 2 = s.r 2 ∧
      t.r 3 = s.r 3 ∧
      t.pc = if pairNat (s.r 2) (s.r 3) ≤ pairNat (s.r 0) (s.r 1) then a + 68 else a + 212 := by
  rw [show compare = [.subReg 1 4 0 2, .sbcReg 1 4 1 3] ++ [Instr.bcondTo 3 144] from rfl,
    ← hpc] at hc
  obtain ⟨u, hr, hk, hregs, hp⟩ := run_branch (P := P) (σ := σ) (t := _)
    (a + 212) (a + 68) rfl rfl hc rfl (by decide) (by decide) (by decide) (by rw [hpc]; udiv_addr)
    (by rw [hpc]; udiv_addr)
  state_simp at hp
  have hcarry := (sub_pair (s.r 0) (s.r 1) (s.r 2) (s.r 3)).2
  refine ⟨u, hr, hk, ?_, ?_, ?_, ?_, ?_⟩
  iterate 4 (rw [State.r_of_regs hregs]; state_simp)
  rw [hp]
  by_cases h : pairNat (s.r 2) (s.r 3) ≤ pairNat (s.r 0) (s.r 1)
  · rw [hcarry.mpr h]
    simp [h]
  · rw [Bool.eq_false_iff.mpr (fun hb => h (hcarry.mp hb))]
    simp [h]

/-! ## The returns without a loop -/

/-- `low` returns the quotient and the remainder of the low words when both high words are 0. -/
theorem run_low {a : UInt32} {s : State} (hc : CodeAt code (a + 16) low) (hpc : s.pc = a + 16)
    (hlr : s.lr % 2 = 1) (h1 : s.r 1 = 0) (h3 : s.r 3 = 0) (h2 : s.r 2 ≠ 0) :
    Returns P σ code s (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3)) := by
  rw [show low = (.udiv 4 0 2 :: ([.mls 2 4 2 0, Instr.lslBy 0 4 0] ++ [.bxLr])) ++ [.bxLr]
    from rfl, ← hpc] at hc
  obtain ⟨c0, c1⟩ := CodeAt.cons.mp (CodeAt.append.mp hc).1
  refine Returns.back (reach_exec c0 (exec_udiv h2) (.refl _))
    (((Keeps.refl s).setR _ _).withPc _) ?_
  refine returns_seq (t := _) rfl rfl c1 rfl hlr ?_ ?_
  · state_simp
    rw [shl_zero, h1, h3]
    simp [pairNat, UInt32.toNat_div]
  · state_simp
    rw [sub_div_mul, h1, h3]
    simp [pairNat, UInt32.toNat_mod]

/-- `high` returns the quotient and the remainder when the divisor's low word is 0. -/
theorem run_high {a : UInt32} {s : State} (hc : CodeAt code (a + 32) high) (hpc : s.pc = a + 32)
    (hlr : s.lr % 2 = 1) (h2 : s.r 2 = 0) (h3 : s.r 3 ≠ 0) :
    Returns P σ code s (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3)) := by
  rw [show high = (.udiv 4 1 3 ::
    ([.mls 3 4 3 1, Instr.lslBy 2 0 0, Instr.lslBy 0 4 0, .movImm 1 0] ++ [.bxLr])) ++ [.bxLr]
    from rfl, ← hpc] at hc
  obtain ⟨c0, c1⟩ := CodeAt.cons.mp (CodeAt.append.mp hc).1
  refine Returns.back (reach_exec c0 (exec_udiv h3) (.refl _))
    (((Keeps.refl s).setR _ _).withPc _) ?_
  have hd : 0 < (s.r 3).toNat := by
    have : (s.r 3).toNat ≠ 0 := fun e => h3 (UInt32.toNat_inj.mp e)
    omega
  have hdh := div_high (n1 := (s.r 1).toNat) (toNat_lt32 (s.r 0)) hd
  have hD : pairNat (s.r 2) (s.r 3) = (s.r 3).toNat * 4294967296 := by simp [pairNat, h2]
  refine returns_seq (t := _) rfl rfl c1 rfl hlr ?_ ?_
  · state_simp
    rw [shl_zero, ofNat_imm0, hD]
    unfold pairNat
    rw [hdh.1]
    simp [UInt32.toNat_div]
  · state_simp
    rw [shl_zero, sub_div_mul, hD]
    unfold pairNat
    rw [hdh.2, UInt32.toNat_mod]

/-- `small` returns the dividend as the remainder when it lies below the divisor. -/
theorem run_small {a : UInt32} {s : State} (hc : CodeAt code (a + 212) small)
    (hpc : s.pc = a + 212) (hlr : s.lr % 2 = 1)
    (hlt : pairNat (s.r 0) (s.r 1) < pairNat (s.r 2) (s.r 3)) :
    Returns P σ code s (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3)) := by
  rw [show small = [Instr.lslBy 2 0 0, Instr.lslBy 3 1 0, .movImm 0 0, .movImm 1 0] ++ [.bxLr]
    from rfl, ← hpc] at hc
  refine returns_seq (t := _) rfl rfl hc rfl hlr ?_ ?_
  · state_simp
    rw [ofNat_imm0, Nat.div_eq_of_lt hlt]
    rfl
  · state_simp
    rw [shl_zero, shl_zero, Nat.mod_eq_of_lt hlt]

/-! ## The loop's setup -/

/-- `count` leaves in r4 the leading zero count of the divisor less that of the dividend's high
word. -/
theorem run_count {a : UInt32} {s : State} (hc : CodeAt code (a + 68) count)
    (hpc : s.pc = a + 68) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ t.pc = a + 92 ∧ t.r 0 = s.r 0 ∧ t.r 1 = s.r 1 ∧
      t.r 2 = s.r 2 ∧ t.r 3 = s.r 3 ∧ t.r 4 = clzPair (s.r 2) (s.r 3) - clz32 (s.r 1) := by
  rw [← hpc] at hc
  obtain ⟨hr, hp, hk⟩ := run_block (P := P) (σ := σ) (t := _) rfl rfl hc rfl
  refine ⟨_, hr, hk, by rw [hp, hpc]; udiv_addr, ?_, ?_, ?_, ?_, ?_⟩
  iterate 4 state_simp
  state_simp
  rw [sub_addWithCarry]
  rfl

/-- `shift` shifts the divisor in r2 and r3 left by r4. -/
theorem run_shift {a : UInt32} {s : State} (hc : CodeAt code (a + 92) shift)
    (hpc : s.pc = a + 92) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ t.pc = a + 128 ∧ t.r 0 = s.r 0 ∧ t.r 1 = s.r 1 ∧
      t.r 2 = shl (s.r 2) ((s.r 4).toNat % 256) ∧ t.r 3 = shlHigh (s.r 2) (s.r 3) (s.r 4) ∧
      t.r 4 = s.r 4 := by
  rw [← hpc] at hc
  obtain ⟨hr, hp, hk⟩ := run_block (P := P) (σ := σ) (t := _) rfl rfl hc rfl
  refine ⟨_, hr, hk, by rw [hp, hpc]; udiv_addr, ?_, ?_, ?_, ?_, ?_⟩
  iterate 3 state_simp
  · state_simp
    rw [sub_addWithCarry, sub_addWithCarry, ofNat_imm32]
    rfl
  · state_simp

/-- `clear` sets the quotient in r5 and r6 to 0. -/
theorem run_clear {a : UInt32} {s : State} (hc : CodeAt code (a + 128) clear)
    (hpc : s.pc = a + 128) :
    ∃ t, Reach P σ code s t ∧ Keeps s t ∧ t.pc = a + 136 ∧ t.r 0 = s.r 0 ∧ t.r 1 = s.r 1 ∧
      t.r 2 = s.r 2 ∧ t.r 3 = s.r 3 ∧ t.r 4 = s.r 4 ∧ t.r 5 = 0 ∧ t.r 6 = 0 := by
  rw [← hpc] at hc
  obtain ⟨hr, hp, hk⟩ := run_block (P := P) (σ := σ) (t := _) rfl rfl hc rfl
  refine ⟨_, hr, hk, by rw [hp, hpc]; udiv_addr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 5 state_simp
  · state_simp; exact ofNat_imm0
  · state_simp; exact ofNat_imm0

/-! ## The loop -/

/-- The state at the loop's head or exit after a pass, with `k` passes left, for the dividend `n`
and the divisor `d`: the shifted divisor in r2 and r3 is `d · 2^k / 2`, and the quotient bits so
far in r5 and r6 and the remainder in r0 and r1 give `n`, with the remainder below `d · 2^k`.
Before the first pass, `k` is the number of passes. -/
structure LoopInv (n d k : Nat) (t : State) : Prop where
  div : pairNat (t.r 2) (t.r 3) = d * 2 ^ k / 2
  eq : n = pairNat (t.r 5) (t.r 6) * (d * 2 ^ k) + pairNat (t.r 0) (t.r 1)
  lt : pairNat (t.r 0) (t.r 1) < d * 2 ^ k

/-- A pass from the loop's head with `j + 1` passes left leaves `j` passes, and returns to the
head when `j` is not 0 and leaves the loop otherwise. -/
theorem run_pass {a : UInt32} {n d j : Nat} {t : State} (hc : CodeAt code (a + 136) pass)
    (hpc : t.pc = a + 136) (hd : 0 < d) (hn : n < 18446744073709551616)
    (h4 : (t.r 4).toNat = j) (hinv : LoopInv n d (j + 1) t) :
    ∃ u, Reach P σ code t u ∧ Keeps t u ∧ LoopInv n d j u ∧ (j = 0 → u.pc = a + 192) ∧
      (j ≠ 0 → u.pc = a + 136 ∧ (u.r 4).toNat = j - 1) := by
  rw [show pass = ([.subReg 1 0 0 2, .sbcReg 1 1 1 3, Instr.lsrBy 7 5 31, Instr.addLsl 0 6 7 6 1,
      .adcReg 5 5 5] ++ [Instr.bcondTo 2 8]) ++ ([Instr.addLsl 1 0 0 2 0, .adcReg 1 1 3] ++
      ([Instr.lsrBy 2 2 1, Instr.addLsl 0 2 2 3 31, Instr.lsrBy 3 3 1, .cmpImm 4 0,
        .subImm 4 4 1] ++ [Instr.bcondTo 1 (-56)])) from rfl] at hc
  obtain ⟨cA, hc⟩ := CodeAt.append.mp hc
  obtain ⟨cR, cB⟩ := CodeAt.append.mp hc
  have cR' : CodeAt code (a + 160) _ := cR.at_eq (by udiv_addr)
  have cB' : CodeAt code (a + 168) _ := cB.at_eq (by udiv_addr)
  clear cR cB hc
  have hX : d * 2 ^ (j + 1) = 2 * (d * 2 ^ j) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_left_comm]
  have hX0 : 0 < d * 2 ^ j := Nat.mul_pos hd (Nat.two_pow_pos j)
  have hdiv := hinv.div
  have heq := hinv.eq
  have hlt := hinv.lt
  rw [hX, show 2 * (d * 2 ^ j) / 2 = d * 2 ^ j by omega] at hdiv
  rw [hX] at heq hlt
  rw [← hpc] at cA
  obtain ⟨u1, r1, k1, g1, p1⟩ := run_branch (P := P) (σ := σ) (t := _) (a + 168) (a + 160) rfl rfl
    cA rfl (by decide) (by decide) (by decide) (by rw [hpc]; udiv_addr) (by rw [hpc]; udiv_addr)
  state_simp at p1
  have e0 : u1.r 0 = (addWithCarry (t.r 0) (~~~(t.r 2)) true).1 := by
    rw [State.r_of_regs g1]; state_simp
  have e1 : u1.r 1 =
      (addWithCarry (t.r 1) (~~~(t.r 3)) (addWithCarry (t.r 0) (~~~(t.r 2)) true).2.1).1 := by
    rw [State.r_of_regs g1]; state_simp
  have e2 : u1.r 2 = t.r 2 := by rw [State.r_of_regs g1]; state_simp
  have e3 : u1.r 3 = t.r 3 := by rw [State.r_of_regs g1]; state_simp
  have e4 : u1.r 4 = t.r 4 := by rw [State.r_of_regs g1]; state_simp
  have e5 : u1.r 5 = (addWithCarry (t.r 5) (t.r 5) (addWithCarry (t.r 1) (~~~(t.r 3))
      (addWithCarry (t.r 0) (~~~(t.r 2)) true).2.1).2.1).1 := by
    rw [State.r_of_regs g1]; state_simp
  have e6 : u1.r 6 = (addWithCarry (shr (t.r 5) 31) (shl (t.r 6) 1) false).1 := by
    rw [State.r_of_regs g1]; state_simp
  have hs := sub_pair (t.r 0) (t.r 1) (t.r 2) (t.r 3)
  rw [← e0, ← e1, hdiv] at hs
  have hq := double_pair (t.r 5) (t.r 6)
    (addWithCarry (t.r 1) (~~~(t.r 3)) (addWithCarry (t.r 0) (~~~(t.r 2)) true).2.1).2.1
  rw [← e5, ← e6] at hq
  have hpa := pass_arith hX0 hn heq hlt
  have hR := pairNat_lt (t.r 0) (t.r 1)
  have hXlt : d * 2 ^ j < 18446744073709551616 := by rw [← hdiv]; exact pairNat_lt _ _
  generalize (addWithCarry (t.r 1) (~~~(t.r 3)) (addWithCarry (t.r 0) (~~~(t.r 2)) true).2.1).2.1
    = c at p1 hs hq
  have keep : ∃ v, Reach P σ code t v ∧ Keeps t v ∧ v.pc = a + 168 ∧ v.r 2 = t.r 2 ∧
      v.r 3 = t.r 3 ∧ v.r 4 = t.r 4 ∧
      n = pairNat (v.r 5) (v.r 6) * (d * 2 ^ j) + pairNat (v.r 0) (v.r 1) ∧
      pairNat (v.r 0) (v.r 1) < d * 2 ^ j := by
    cases c
    · have hn' : ¬ d * 2 ^ j ≤ pairNat (t.r 0) (t.r 1) := fun h => by
        have := hs.2.mpr h; cases this
      obtain ⟨heq', hlt', hb⟩ := hpa.2 hn'
      have p1' : u1.pc = a + 160 := p1
      rw [← p1'] at cR'
      obtain ⟨r2, p2, k2⟩ := run_block (P := P) (σ := σ) (t := _) rfl rfl cR' rfl
      refine ⟨_, r1.trans r2, k1.trans k2, by rw [p2, p1']; udiv_addr, ?_, ?_, ?_, ?_, ?_⟩
      · state_simp; exact e2
      · state_simp; exact e3
      · state_simp; exact e4
      · state_simp
        rw [shl_zero, add_pair, hq, hs.1, e2, e3, hdiv]
        rw [show 2 * pairNat (t.r 5) (t.r 6) + false.toNat = 2 * pairNat (t.r 5) (t.r 6) from
          Nat.add_zero _, Nat.mod_eq_of_lt hb]
        exact restore_eq hR hXlt heq' hlt'
      · state_simp
        rw [shl_zero, add_pair, hs.1, e2, e3, hdiv]
        omega
    · have hy : d * 2 ^ j ≤ pairNat (t.r 0) (t.r 1) := hs.2.mp rfl
      obtain ⟨heq', hlt', hb⟩ := hpa.1 hy
      have p1' : u1.pc = a + 168 := p1
      refine ⟨u1, r1, k1, p1', e2, e3, e4, ?_, ?_⟩
      · rw [hq, hs.1]
        simp only [Bool.toNat_true]
        rw [Nat.mod_eq_of_lt hb]
        omega
      · rw [hs.1]
        omega
  obtain ⟨v, rv, kv, pv, v2, v3, v4, veq, vlt⟩ := keep
  rw [← pv] at cB'
  obtain ⟨w, rw', kw, gw, pw⟩ := run_branch (P := P) (σ := σ) (t := _) (a + 136) (a + 192) rfl rfl
    cB' rfl (by decide) (by decide) (by decide) (by rw [pv]; udiv_addr) (by rw [pv]; udiv_addr)
  state_simp at pw
  rw [cmp_imm0, v4] at pw
  have w0 : w.r 0 = v.r 0 := by rw [State.r_of_regs gw]; state_simp
  have w1 : w.r 1 = v.r 1 := by rw [State.r_of_regs gw]; state_simp
  have w5 : w.r 5 = v.r 5 := by rw [State.r_of_regs gw]; state_simp
  have w6 : w.r 6 = v.r 6 := by rw [State.r_of_regs gw]; state_simp
  have w23 : pairNat (w.r 2) (w.r 3) = d * 2 ^ j / 2 := by
    rw [State.r_of_regs gw, State.r_of_regs gw]
    state_simp
    rw [half_pair, v2, v3, hdiv]
  have w4 : w.r 4 = t.r 4 - 1 := by
    rw [State.r_of_regs gw]
    state_simp
    rw [sub_imm, ofNat_imm1, v4]
  refine ⟨w, rv.trans rw', kv.trans kw, ⟨w23, ?_, ?_⟩, fun hj => ?_, fun hj => ⟨?_, ?_⟩⟩
  · rw [w0, w1, w5, w6]; exact veq
  · rw [w0, w1]; exact vlt
  · have : t.r 4 = 0 := UInt32.toNat_inj.mp (by rw [h4, hj]; rfl)
    rw [pw, this]
    rfl
  · have : t.r 4 ≠ 0 := fun e => hj (by rw [← h4, e]; rfl)
    rw [pw]
    simp [this]
  · have : 1 ≤ (t.r 4).toNat := by omega
    have := toNat_lt32 (t.r 4)
    rw [w4, UInt32.toNat_sub, h4]
    simp only [UInt32.toNat_one, Nat.reducePow]
    omega

/-- The loop from its head with `j + 1` passes left reaches its exit after the last pass. -/
theorem run_loop {a : UInt32} {n d : Nat} (hc : CodeAt code (a + 136) pass) (hd : 0 < d)
    (hn : n < 18446744073709551616) :
    ∀ (j : Nat) (t : State), t.pc = a + 136 → (t.r 4).toNat = j → LoopInv n d (j + 1) t →
      ∃ u, Reach P σ code t u ∧ Keeps t u ∧ LoopInv n d 0 u ∧ u.pc = a + 192 := by
  intro j
  induction j with
  | zero =>
      intro t hpc h4 hinv
      obtain ⟨u, hr, hk, hi, h0, -⟩ := run_pass (P := P) (σ := σ) hc hpc hd hn h4 hinv
      exact ⟨u, hr, hk, hi, h0 rfl⟩
  | succ j ih =>
      intro t hpc h4 hinv
      obtain ⟨u, hr, hk, hi, -, h1⟩ := run_pass (P := P) (σ := σ) hc hpc hd hn h4 hinv
      obtain ⟨hpu, h4u⟩ := h1 (by omega)
      obtain ⟨w, hw, kw, iw, pw⟩ := ih u hpu (by rw [h4u]; omega) hi
      exact ⟨w, hr.trans hw, hk.trans kw, iw, pw⟩

/-- `done` returns the loop's quotient and remainder. -/
theorem run_done {a : UInt32} {n d : Nat} {s : State} (hc : CodeAt code (a + 192) done)
    (hpc : s.pc = a + 192) (hlr : s.lr % 2 = 1) (hinv : LoopInv n d 0 s) :
    Returns P σ code s n d := by
  rw [show done = ([Instr.lslBy 2 0 0, Instr.lslBy 3 1 0, Instr.lslBy 0 5 0, Instr.lslBy 1 6 0] ++
    [.bxLr]) ++ [.bxLr] from rfl, ← hpc] at hc
  replace hc := (CodeAt.append.mp hc).1
  have heq := hinv.eq
  have hlt := hinv.lt
  rw [Nat.pow_zero, Nat.mul_one] at heq hlt
  have h := div_mod_eq heq hlt
  refine returns_seq (t := _) rfl rfl hc rfl hlr ?_ ?_
  · state_simp
    rw [shl_zero, shl_zero]
    exact h.1.symm
  · state_simp
    rw [shl_zero, shl_zero]
    exact h.2.symm

/-- `count`, `shift`, `clear`, the loop, and `done` return the quotient and the remainder of a
dividend at least the divisor, whose high word is not 0. -/
theorem run_general {a : UInt32} {s : State} (cN : CodeAt code (a + 68) count)
    (cS : CodeAt code (a + 92) shift) (cZ : CodeAt code (a + 128) clear)
    (cP : CodeAt code (a + 136) pass) (cD : CodeAt code (a + 192) done) (hpc : s.pc = a + 68)
    (hlr : s.lr % 2 = 1) (hle : pairNat (s.r 2) (s.r 3) ≤ pairNat (s.r 0) (s.r 1))
    (hn1 : s.r 1 ≠ 0) (hD : pairNat (s.r 2) (s.r 3) ≠ 0) :
    Returns P σ code s (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3)) := by
  obtain ⟨t1, r1, k1, p1, a0, a1, a2, a3, a4⟩ := run_count (P := P) (σ := σ) cN hpc
  obtain ⟨t2, r2, k2, p2, b0, b1, b2, b3, b4⟩ := run_shift (P := P) (σ := σ) cS p1
  obtain ⟨t3, r3, k3, p3, c0, c1, c2, c3, c4, c5, c6⟩ := run_clear (P := P) (σ := σ) cZ p2
  obtain ⟨hcd, hD1, hD2⟩ := clzPair_bounds hD
  obtain ⟨-, hN2⟩ := pair_bounds_of_hi (lo := s.r 0) hn1
  obtain ⟨hle', hfit, hgt⟩ := norm_arith hcd hD1 hD2 hN2 hle
  have hsh : (t1.r 4).toNat = (clzPair (s.r 2) (s.r 3)).toNat - (clz32 (s.r 1)).toNat := by
    rw [a4, UInt32.toNat_sub]
    have := toNat_lt32 (clzPair (s.r 2) (s.r 3))
    simp only [Nat.reducePow]
    omega
  have hk : (t3.r 4).toNat = (clzPair (s.r 2) (s.r 3)).toNat - (clz32 (s.r 1)).toNat := by
    rw [c4, b4, hsh]
  have hshl := shl_pair (t1.r 2) (t1.r 3) (t1.r 4) (by rw [hsh]; omega)
  rw [← b2, ← b3, a2, a3, hsh, Nat.mod_eq_of_lt hfit, ← c2, ← c3] at hshl
  have hinv : LoopInv (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3))
      ((clzPair (s.r 2) (s.r 3)).toNat - (clz32 (s.r 1)).toNat + 1) t3 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hshl, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
    · rw [c5, c6, c0, c1, b0, b1, a0, a1]
      simp [pairNat]
    · rw [c0, c1, b0, b1, a0, a1]
      exact hgt
  obtain ⟨u, ru, ku, iu, pu⟩ := run_loop (P := P) (σ := σ) cP (Nat.pos_of_ne_zero hD)
    (pairNat_lt _ _) _ t3 p3 hk hinv
  have kall := k1.trans (k2.trans (k3.trans ku))
  exact Returns.back (r1.trans (r2.trans (r3.trans ru))) kall
    (run_done cD pu (by rw [kall.lr]; exact hlr) iu)

/-! ## The routine -/

/-- From the routine's entry, with a nonzero divisor, the model returns the quotient and the
remainder of the pairs' numbers. -/
theorem udivmod64_nat {a : UInt32} {s : State} (hc : CodeAt code a udivmod64) (hpc : s.pc = a)
    (hlr : s.lr % 2 = 1) (hd : pairNat (s.r 2) (s.r 3) ≠ 0) :
    Returns P σ code s (pairNat (s.r 0) (s.r 1)) (pairNat (s.r 2) (s.r 3)) := by
  obtain ⟨cT, cL, cH, cC, cN, cS, cZ, cP, cD, cM⟩ := udivmod64_pieces hc
  obtain ⟨t1, r1, k1, e1, p1⟩ := run_test0 (P := P) (σ := σ) cT hpc
  have hlr1 : t1.lr % 2 = 1 := by rw [k1.lr]; exact hlr
  refine Returns.back r1 k1 ?_
  rw [← e1 0, ← e1 1, ← e1 2, ← e1 3]
  by_cases h2 : s.r 2 = 0
  · rw [ite_eq_left h2] at p1
    have h3 : s.r 3 ≠ 0 := fun h3 => hd (by simp [pairNat, h2, h3])
    exact run_high cH p1 hlr1 (by rw [e1]; exact h2) (by rw [e1]; exact h3)
  · rw [ite_eq_right h2] at p1
    obtain ⟨t2, r2, k2, f0, f1, f2, f3, p2⟩ := run_test1 (P := P) (σ := σ) cT p1
    have hlr2 : t2.lr % 2 = 1 := by rw [k2.lr]; exact hlr1
    refine Returns.back r2 k2 ?_
    rw [← f0, ← f1, ← f2, ← f3]
    by_cases h13 : t1.r 1 = 0 ∧ t1.r 3 = 0
    · rw [ite_eq_left h13] at p2
      exact run_low cL p2 hlr2 (by rw [f1]; exact h13.1) (by rw [f3]; exact h13.2)
        (by rw [f2, e1]; exact h2)
    · rw [ite_eq_right h13] at p2
      obtain ⟨t3, r3, k3, g0, g1, g2, g3, p3⟩ := run_compare (P := P) (σ := σ) cC p2
      have hlr3 : t3.lr % 2 = 1 := by rw [k3.lr]; exact hlr2
      refine Returns.back r3 k3 ?_
      rw [← g0, ← g1, ← g2, ← g3]
      by_cases hle : pairNat (t3.r 2) (t3.r 3) ≤ pairNat (t3.r 0) (t3.r 1)
      · rw [g0, g1, g2, g3] at hle
        rw [ite_eq_left hle] at p3
        rw [← g0, ← g1, ← g2, ← g3] at hle
        have hn1 : t3.r 1 ≠ 0 := by
          intro h1
          have hd3 : t1.r 3 ≠ 0 := fun h3 => h13 ⟨by rw [← f1, ← g1]; exact h1, h3⟩
          have := toNat_lt32 (t3.r 0)
          have h3' : (t3.r 3).toNat ≠ 0 := by
            rw [g3, f3]; exact fun e => hd3 (UInt32.toNat_inj.mp e)
          rw [h1] at hle
          simp only [pairNat, UInt32.toNat_zero, Nat.zero_mul, Nat.zero_add] at hle
          omega
        have hD : pairNat (t3.r 2) (t3.r 3) ≠ 0 := by rw [g2, g3, f2, f3, e1, e1]; exact hd
        exact run_general cN cS cZ cP cD p3 hlr3 hle hn1 hD
      · rw [g0, g1, g2, g3] at hle
        rw [ite_eq_right hle] at p3
        rw [← g0, ← g1, ← g2, ← g3] at hle
        exact run_small cM p3 hlr3 (Nat.lt_of_not_le hle)

/-- From the entry of `udivmod64` placed at `a`, with the dividend `n` in r0 and r1 and a nonzero
divisor `d` in r2 and r3, each with its low word first, and with bit 0 of LR set, the model
reaches the return to LR with Lean's `n / d` in r0 and r1 and `n % d` in r2 and r3, keeping SP,
LR, r8 to r12, the memory, the device trace, and the number of device reads. -/
theorem udivmod64_spec {a : UInt32} {s : State} {n d : UInt64} (hc : CodeAt code a udivmod64)
    (hpc : s.pc = a) (hlr : s.lr % 2 = 1) (h0 : s.r 0 = n.toUInt32)
    (h1 : s.r 1 = (n >>> 32).toUInt32) (h2 : s.r 2 = d.toUInt32)
    (h3 : s.r 3 = (d >>> 32).toUInt32) (hd : d ≠ 0) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.lr &&& 0xFFFFFFFE ∧
      t.r 0 = (n / d).toUInt32 ∧ t.r 1 = ((n / d) >>> 32).toUInt32 ∧
      t.r 2 = (n % d).toUInt32 ∧ t.r 3 = ((n % d) >>> 32).toUInt32 ∧ Keeps s t := by
  have hN : pairNat (s.r 0) (s.r 1) = n.toNat := by rw [h0, h1, pairNat_toUInt32]
  have hD : pairNat (s.r 2) (s.r 3) = d.toNat := by rw [h2, h3, pairNat_toUInt32]
  have hd' : pairNat (s.r 2) (s.r 3) ≠ 0 := by
    rw [hD]; exact fun e => hd (UInt64.toNat_inj.mp e)
  obtain ⟨t, hr, hp, hq, hm, hk⟩ := udivmod64_nat (P := P) (σ := σ) hc hpc hlr hd'
  rw [hN, hD, ← UInt64.toNat_div] at hq
  rw [hN, hD, ← UInt64.toNat_mod] at hm
  obtain ⟨q0, q1⟩ := eq_of_pairNat hq
  obtain ⟨m0, m1⟩ := eq_of_pairNat hm
  exact ⟨t, hr, hp, q0, q1, m0, m1, hk⟩

end LeanExe.M7
