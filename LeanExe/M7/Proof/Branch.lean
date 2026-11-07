import LeanExe.M7.Proof.Ops
import LeanExe.M7.Proof.Div

/-!
Branches with offsets that the generator computes, and the simulation of `divUI64` and
`remUI64`.  `offsetTo_ok` states that an offset that the generator accepts is even, fits its
field, and leads from the branch to its target, and `exec_bTo` and `exec_blTo` that `B.W` and `BL`
built from such an offset branch by it.  A division loads the dividend into r0:r1 and the
divisor into r2:r3, tests the divisor with `ORRS r4, r2, r3`, branches to the trap stub when it is
0, and calls `udivmod64`, whose theorem `udivmod64_spec` gives the quotient in r0:r1 and the
remainder in r2:r3.  The store of the pair that the form keeps completes the outcome.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Offsets -/

theorem toNat_ofInt32 (d : Int) : (UInt32.ofInt d).toNat = (d % 4294967296).toNat := by
  unfold UInt32.ofInt
  rw [UInt32.toNat_ofNat']
  have h0 : 0 ≤ d % (2 ^ 32 : Int) := Int.emod_nonneg _ (by decide)
  have h1 : d % (2 ^ 32 : Int) < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  simp only [Int.reducePow, Nat.reducePow] at *
  omega

theorem offsetTo_ok {bits : Nat} {here target : UInt32} {d : Int}
    (h : offsetTo bits here target = .ok d) :
    d % 2 = 0 ∧ -((2 ^ bits : Nat) : Int) ≤ d ∧ d < ((2 ^ bits : Nat) : Int) ∧
      here + 4 + UInt32.ofInt d = target := by
  unfold offsetTo at h
  simp only at h
  split at h
  · exact absurd h except_throw_ok
  · rename_i hc
    have e := (except_pure_ok.mp h).symm
    subst e
    simp only [not_or, Decidable.not_not] at hc
    refine ⟨hc.1, by omega, by omega, ?_⟩
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_add, toNat_ofInt32, show (4 : UInt32).toNat = 4 from rfl]
    have := toNat_lt32 here
    have := toNat_lt32 target
    simp only [Nat.reducePow]
    omega

theorem bcondAt_ok {c : Fin 14} {here target : UInt32} {i : Instr}
    (h : bcondAt c here target = .ok i) :
    ∃ off, i = Instr.bcondTo c off ∧ off % 2 = 0 ∧ -1048576 ≤ off ∧ off < 1048576 ∧
      here + 4 + UInt32.ofInt off = target := by
  unfold bcondAt at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨off, ho, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := offsetTo_ok ho
  exact ⟨off, rfl, h1, by simpa using h2, by simpa using h3, h4⟩

theorem bAt_ok {here target : UInt32} {i : Instr} (h : bAt here target = .ok i) :
    ∃ off, i = Instr.bTo off ∧ off % 2 = 0 ∧ -16777216 ≤ off ∧ off < 16777216 ∧
      here + 4 + UInt32.ofInt off = target := by
  unfold bAt at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨off, ho, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := offsetTo_ok ho
  exact ⟨off, rfl, h1, by simpa using h2, by simpa using h3, h4⟩

theorem blAt_ok {here target : UInt32} {i : Instr} (h : blAt here target = .ok i) :
    ∃ off, i = Instr.blTo off ∧ off % 2 = 0 ∧ -16777216 ≤ off ∧ off < 16777216 ∧
      here + 4 + UInt32.ofInt off = target := by
  unfold blAt at h
  simp only [except_bind_ok, except_pure_ok] at h
  obtain ⟨off, ho, rfl⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := offsetTo_ok ho
  exact ⟨off, rfl, h1, by simpa using h2, by simpa using h3, h4⟩

/-- `I1` of `B.W` and `BL`, `NOT(J1 EOR S)`, for the `J1` that `branchFields` computes from the
bit `x` and the sign `y`, is `x`. -/
theorem bit_fix {x : Nat} (y : Nat) (hx : x < 2) : 1 - ((1 - x + y) % 2 + y % 2) % 2 = x := by
  omega

/-- The fields that `branchFields` computes from an even byte offset from -2^24 to 2^24 - 2 give
that offset as a 32-bit word. -/
theorem branchOffset_branchFields {off : Int} (he : off % 2 = 0) (hlo : -16777216 ≤ off)
    (hhi : off < 16777216) :
    branchOffset (branchFields off).1 (branchFields off).2.1 (branchFields off).2.2.1
      (branchFields off).2.2.2.1 (branchFields off).2.2.2.2 = UInt32.ofInt off := by
  simp only [branchFields, branchOffset, field]
  generalize hv : (off % 33554432).toNat = v
  have hv' : (v : Int) = off % 33554432 := by
    rw [← hv]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [bit_fix _ (Nat.mod_lt _ (by decide)), bit_fix _ (Nat.mod_lt _ (by decide))]
  have hsum : v / 16777216 % 2 % 2 * 16777216 + v / 8388608 % 2 * 8388608 +
      v / 4194304 % 2 * 4194304 + v / 4096 % 1024 * 4096 + v / 2 % 2048 * 2 = v := by omega
  rw [hsum]
  apply UInt32.toNat_inj.mp
  simp only [sext, UInt32.ofInt, Nat.reduceSub, Nat.reducePow, Int.reducePow]
  split
  · rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    omega
  · rw [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat']
    omega

/-- `B.W` that `Instr.bTo` builds from an even byte offset from -2^24 to 2^24 - 2 branches by that
offset from its address plus 4. -/
theorem exec_bTo {off : Int} (he : off % 2 = 0) (hlo : -16777216 ≤ off) (hhi : off < 16777216)
    (s : State) : exec P σ (Instr.bTo off) s = some { s with pc := s.pc + 4 + UInt32.ofInt off } := by
  rw [← branchOffset_branchFields he hlo hhi]
  rfl

/-- `BL` that `Instr.blTo` builds from an even byte offset from -2^24 to 2^24 - 2 sets LR to the
next address with bit 0 set and branches by that offset from its address plus 4. -/
theorem exec_blTo {off : Int} (he : off % 2 = 0) (hlo : -16777216 ≤ off) (hhi : off < 16777216)
    (s : State) :
    exec P σ (Instr.blTo off) s =
      some { s with lr := (s.pc + 4) ||| 1, pc := s.pc + 4 + UInt32.ofInt off } := by
  rw [← branchOffset_branchFields he hlo hhi]
  rfl

/-- The return address that `BL` sets, with bit 0 cleared, is the next address when that is
even. -/
theorem or1_and (x : UInt32) (h : x.toNat % 2 = 0) : (x ||| 1) &&& 0xFFFFFFFE = x := by
  apply UInt32.toNat_inj.mp
  have hx := toNat_lt32 x
  rw [UInt32.toNat_and, UInt32.toNat_or, show (1 : UInt32).toNat = 1 from rfl,
    show (0xFFFFFFFE : UInt32).toNat = 2 * (2 ^ 31 - 1) from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or]
  cases i with
  | zero =>
      simp only [Nat.testBit_zero]
      simp [h]
  | succ j =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show 2 * (2 ^ 31 - 1) / 2 = 2 ^ 31 - 1 by omega, Nat.testBit_two_pow_sub_one,
        show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit, Bool.or_false]
      by_cases hj : j < 31
      · simp [hj]
      · have : (x.toNat / 2).testBit j = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega)
            (Nat.pow_le_pow_right (n := 2) (i := 31) (by decide) (by omega)))
        simp [hj, this]

theorem even_after {a : UInt32} (ha : a.toNat % 2 = 0) (n : Nat) : (after a n).toNat % 2 = 0 := by
  rw [after_eq, UInt32.toNat_add, UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

theorem or1_odd (x : UInt32) : (x ||| 1) % 2 = 1 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, UInt32.toNat_or, show (1 : UInt32).toNat = 1 from rfl,
    show (2 : UInt32).toNat = 2 from rfl]
  have h := Nat.testBit_or x.toNat 1 0
  simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.or_true,
    decide_eq_true_eq] at h
  exact h

/-! ## The outcome of a write after a run -/

/-- The outcome when the model reaches, from `ms`, the end of an instruction's code with SP, the
device trace, and the read count unchanged and the memory that of `ms` with the slot of height
`k` holding `r`, the top of the new stack `r :: vs`. -/
theorem outcome_store {E : Env} {ctl : List Ctl} {σs σ' : List ValueType} {sl : Locals}
    {ms z : State} {endA : UInt32} {α : Type} {st : Store α} {k : Nat} {vs : List Value}
    {r : Value} {w0 w1 : UInt32} (hinv : Inv P E σs sl ms) (hsr : StoreOk P E.toShared st ms)
    (hr' : Reach P σ code ms z)
    (hp : z.pc = endA) (hsp : z.sp = ms.sp) (htr : z.trace = ms.trace) (hrd : z.reads = ms.reads)
    (hmem : z.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) (hb : curBase ctl ≤ k) (hvs : vs.length = k)
    (hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v)
    (hr : SlotRel r w0 w1) (hty : Typed σ' (r :: vs)) :
    Outcome P σ code E ctl (some σ') endA (.Fallthrough st { sl with values := r :: vs }) ms :=
  ⟨σ', rfl, z, hr', hp, hsp, htr, hrd, keeps_write_op hinv.frame hmem hk,
    below_write_op hinv.frame hmem hk hb, Inv.write_op hinv hsp hmem hk hvs hbelow hr hty,
    hsr.congr (keepsBelow_write_op hinv.frame hmem hk)⟩

/-! ## Division -/

theorem gen_div {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {res : Fin 8 × Fin 8} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genDiv E ctl σs a res = .ok (is, fin)) :
    curBase ctl + 2 ≤ σs.length ∧ σs.length - 1 < E.frame.height ∧ ∃ h0 h1 h2 h3 h4 h5 oq ob,
      oq % 2 = 0 ∧ -1048576 ≤ oq ∧ oq < 1048576 ∧
      after a 5 + 4 + UInt32.ofInt oq = E.trapDiv ∧
      ob % 2 = 0 ∧ -16777216 ≤ ob ∧ ob < 16777216 ∧
      after a 6 + 4 + UInt32.ofInt ob = E.udivmod ∧
      is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
        .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩,
        .ldrSp 3 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ++
        [.orrReg 1 4 2 3, Instr.bcondTo condEQ oq, Instr.blTo ob] ++
        [.strSp res.1 ⟨E.frame.opAt (σs.length - 2), h4⟩,
          .strSp res.2 ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩] ∧
      fin = some (.i64 :: σs.drop 2) := by
  unfold genDiv at hg
  by_cases hc : σs.length < curBase ctl + 2
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨x, hx, y, hy, l1, hl1, l2, hl2, i1, hi1, i2, hi2, l3, hl3, rfl, rfl⟩ := hg
    obtain ⟨-, rfl⟩ := Env.op_ok hx
    obtain ⟨hlt, rfl⟩ := Env.op_ok hy
    obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl1
    obtain ⟨h2, h3, rfl⟩ := ldPair_ok hl2
    obtain ⟨oq, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi1
    obtain ⟨ob, rfl, b1, b2, b3, b4⟩ := blAt_ok hi2
    obtain ⟨h4, h5, rfl⟩ := stPair_ok hl3
    exact ⟨by omega, hlt, h0, h1, h2, h3, h4, h5, oq, ob, q1, q2, q3, q4, b1, b2, b3, b4, rfl, rfl⟩

theorem pair_ne_zero {b : UInt64} (hb : b ≠ 0) : b.toUInt32 ||| (b >>> 32).toUInt32 ≠ 0 := by
  intro h
  obtain ⟨h0, h1⟩ := UInt32.or_eq_zero_iff.mp h
  apply hb
  apply UInt64.toNat_inj.mp
  rw [← pairNat_toUInt32 b, h0, h1]
  rfl

/-- The simulation of a division that the generator compiles with `genDiv`, whose result `op a b`
for the dividend `a` and the nonzero divisor `b` `udivmod64` leaves in the pair `res`. -/
theorem sim_divrem {inst : Instruction} {res : Fin 8 × Fin 8} {op : UInt64 → UInt64 → UInt64}
    (hgen : ∀ E ctl σs a, genInstr E ctl σs a inst = genDiv E ctl σs a res)
    (hfall : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals) (b a : UInt64)
      (vs : List Value), sl.values = .i64 b :: .i64 a :: vs → b ≠ 0 →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := .i64 (op a b) :: vs })
    (htrap : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals) (b a : UInt64)
      (vs : List Value), sl.values = .i64 b :: .i64 a :: vs → b = 0 →
      ∃ st' msg, execOne (f + 1) m st sl inst = .Trap st' msg)
    (hinvalid : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∀ b a vs, sl.values ≠ .i64 b :: .i64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg)
    (hres : ∀ (t : State) (a b : UInt64), t.r 0 = (a / b).toUInt32 →
      t.r 1 = ((a / b) >>> 32).toUInt32 → t.r 2 = (a % b).toUInt32 →
      t.r 3 = ((a % b) >>> 32).toUInt32 → SlotRel (.i64 (op a b)) (t.r res.1) (t.r res.2))
    (F : Nat) : InstrSim P σ code F inst := by
  intro E ctl σs a is fin hg hcode hev hdiv hb _ α m st sl ms hinv hsr hpc _ need D _ _ _
  rw [hgen] at hg
  obtain ⟨hb2, hlt, h0, h1, h2, h3, h4, h5, oq, ob, q1, q2, q3, q4, b1, b2, b3, b4, rfl, rfl⟩ :=
    gen_div hg
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      by_cases hshape : ∃ b a vs, sl.values = .i64 b :: .i64 a :: vs
      · obtain ⟨b, a', vs, hv⟩ := hshape
        by_cases hb0 : b = 0
        · obtain ⟨st', msg, he⟩ := htrap f m st sl b a' vs hv hb0
          rw [he]
          trivial
        rw [hfall f m st sl b a' vs hv hb0]
        obtain ⟨hvl, -, ha0, ha1, hbw0, hbw1⟩ := hinv.top2 hv
        obtain ⟨hk8, hklr, -⟩ := E.frame.opAt_bounds (k := σs.length - 2) (by omega)
        obtain ⟨hj8, hjlr, hlrs⟩ := E.frame.opAt_bounds hlt
        let L : List Instr := [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
          .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩,
          .ldrSp 3 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩, .orrReg 1 4 2 3]
        let S : List Instr := [.strSp res.1 ⟨E.frame.opAt (σs.length - 2), h4⟩,
          .strSp res.2 ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩]
        have hcode' : CodeAt code a (L ++ [Instr.bcondTo condEQ oq] ++ [Instr.blTo ob] ++ S) :=
          hcode
        obtain ⟨hc3, hcS⟩ := CodeAt.append.mp hcode'
        obtain ⟨hc2, hcBL⟩ := CodeAt.append.mp hc3
        obtain ⟨hcL, hcB⟩ := CodeAt.append.mp hc2
        have hok : SlotsOk P ms.sp L :=
          slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_nil _)))))
        rw [← hpc] at hcL
        obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok hcL
        have horr : ∀ w : State, (slotRun P σ [.orrReg 1 4 2 3] w).r 0 = w.r 0 ∧
            (slotRun P σ [.orrReg 1 4 2 3] w).r 1 = w.r 1 ∧
            (slotRun P σ [.orrReg 1 4 2 3] w).r 2 = w.r 2 ∧
            (slotRun P σ [.orrReg 1 4 2 3] w).r 3 = w.r 3 ∧
            (slotRun P σ [.orrReg 1 4 2 3] w).zFlag = (w.r 2 ||| w.r 3 == 0) ∧
            (slotRun P σ [.orrReg 1 4 2 3] w).mem = w.mem := by
          intro w
          simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try state_simp)
          rw [State.mem_withPc, State.mem_result]
        have hu : (slotRun P σ L ms).r 0 = a'.toUInt32 ∧
            (slotRun P σ L ms).r 1 = (a' >>> 32).toUInt32 ∧
            (slotRun P σ L ms).r 2 = b.toUInt32 ∧
            (slotRun P σ L ms).r 3 = (b >>> 32).toUInt32 ∧
            (slotRun P σ L ms).zFlag = (b.toUInt32 ||| (b >>> 32).toUInt32 == 0) ∧
            (slotRun P σ L ms).mem = ms.mem := by
          let w := slotRun P σ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
            .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
            .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩,
            .ldrSp 3 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ms
          have hw0 : w.r 0 = a'.toUInt32 := ha0
          have hw1 : w.r 1 = (a' >>> 32).toUInt32 := ha1
          have hw2 : w.r 2 = b.toUInt32 := hbw0
          have hw3 : w.r 3 = (b >>> 32).toUInt32 := hbw1
          have hwm : w.mem = ms.mem := rfl
          obtain ⟨o0, o1, o2, o3, oz, om⟩ := horr w
          exact ⟨o0.trans hw0, o1.trans hw1, o2.trans hw2, o3.trans hw3, oz.trans (by rw [hw2, hw3]),
            om.trans hwm⟩
        obtain ⟨hu0, hu1, hu2, hu3, huz, hum⟩ := hu
        have hz : (slotRun P σ L ms).zFlag = false := by
          rw [huz]; exact beq_false_of_ne (pair_ne_zero hb0)
        -- the test of the divisor
        have hcs1 : codeSize L = 20 := rfl
        have hcs2 : codeSize (L ++ [Instr.bcondTo condEQ oq]) = 24 := rfl
        have hcs3 : codeSize (L ++ [Instr.bcondTo condEQ oq] ++ [Instr.blTo ob]) = 28 := rfl
        have hBpc : (slotRun P σ L ms).pc = after a 5 := by
          rw [p1, hpc, show L.length = 5 from rfl]
          try addr_after
        rw [hcs1, show a + UInt32.ofNat 20 = (slotRun P σ L ms).pc by
          rw [hBpc]
          try addr_after] at hcB
        have rB := reach_bcondTo (P := P) (σ := σ) q1 q2 q3 hcB
        have hc0 : (slotRun P σ L ms).condHolds 0 = false := by rw [condHolds_eq, hz]
        rw [show condEQ = (0 : Fin 14) from rfl, hc0] at rB
        simp only [Bool.false_eq_true, ↓reduceIte] at rB
        -- the call of `udivmod64`
        obtain ⟨u1, hu1d⟩ : ∃ u1 : State,
            u1 = { slotRun P σ L ms with pc := (slotRun P σ L ms).pc + 4 } := ⟨_, rfl⟩
        have rB' : Reach P σ code (slotRun P σ L ms) u1 := by rw [hu1d]; exact rB
        have hp1 : u1.pc = after a 6 := by
          rw [hu1d, State.pc_withPc, hBpc]
          try addr_after
        have hr1 : ∀ i, u1.r i = (slotRun P σ L ms).r i := fun i => by rw [hu1d, State.r_withPc]
        rw [hcs2, show a + UInt32.ofNat 24 = u1.pc by
          rw [hp1]
          try addr_after] at hcBL
        obtain ⟨w, hwd⟩ : ∃ w : State,
            w = { u1 with lr := (u1.pc + 4) ||| 1, pc := u1.pc + 4 + UInt32.ofInt ob } :=
          ⟨_, rfl⟩
        have eBL : exec P σ (Instr.blTo ob) u1 = some w := by
          rw [hwd]; exact exec_blTo b1 b2 b3 u1
        have hwpc : w.pc = E.udivmod := by
          rw [hwd, State.pc_withLrPc, hp1]; exact b4
        have hwr : ∀ i, w.r i = u1.r i := fun i => by rw [hwd, State.r_withLrPc]
        obtain ⟨t, rt, tpc, t0, t1, t2, t3, kt⟩ := udivmod64_spec (P := P) (σ := σ) (s := w)
          (n := a') (d := b) hdiv hwpc (by rw [hwd, State.lr_withLrPc]; exact or1_odd _)
          (by rw [hwr, hr1]; exact hu0) (by rw [hwr, hr1]; exact hu1)
          (by rw [hwr, hr1]; exact hu2) (by rw [hwr, hr1]; exact hu3) hb0
        have htpc : t.pc = after a 7 := by
          rw [tpc, hwd, State.lr_withLrPc]
          have hev7 : (u1.pc + 4).toNat % 2 = 0 := by
            rw [hp1, show after a 6 + 4 = after a 7 by addr_after]
            exact even_after hev 7
          rw [or1_and _ hev7, hp1]
          try addr_after
        have hwsp : t.sp = ms.sp := by
          rw [kt.sp, hwd, State.sp_withLrPc, hu1d, State.sp_withPc]; exact sp1
        have hwmem : t.mem = ms.mem := by
          rw [kt.mem, hwd, State.mem_withLrPc, hu1d, State.mem_withPc]; exact hum
        have hwtr : t.trace = ms.trace := by
          rw [kt.trace, hwd, State.trace_withLrPc, hu1d, State.trace_withPc]; exact tr1
        have hwrd : t.reads = ms.reads := by
          rw [kt.reads, hwd, State.reads_withLrPc, hu1d, State.reads_withPc]; exact rd1
        -- the stores
        have hokS : SlotsOk P t.sp S := by
          rw [hwsp]
          exact slotsOk_st (hinv.frame.word (by omega) (by omega))
            (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))
        rw [hcs3, show a + UInt32.ofNat 28 = t.pc by
          rw [htpc]
          try addr_after] at hcS
        obtain ⟨rS, pS, spS, -, trS, rdS, -⟩ := run_slots (σ := σ) hokS hcS
        refine outcome_store hinv hsr
          (Reach.trans r1 (Reach.trans rB' (Reach.trans (reach_exec hcBL eBL rt) rS))) ?_
          (by rw [spS, hwsp]) (by rw [trS, hwtr]) (by rw [rdS, hwrd]) ?_
          (by omega) (by omega) hvl (fun h v hv' => ?_) (hres t a' b t0 t1 t2 t3)
          (Typed.cons trivial (by have := hinv.types.drop 2; rw [hv] at this; simpa using this))
        · rw [pS, htpc, show S.length = 2 from rfl]
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
          try addr_after
        · rw [slotRun_st2, hwmem, hwsp]
        · have hl := getElem?_reverse_lt hv'
          exact hinv.stack h v (by
            rw [hv, getElem?_reverse_cons (by simp; omega), getElem?_reverse_cons hl]; exact hv')
      · obtain ⟨msg, he⟩ := hinvalid f m st sl (fun b a vs h => hshape ⟨b, a, vs, h⟩)
        rw [he]
        trivial

theorem sim_divUI64 (F : Nat) : InstrSim P σ code F .divUI64 :=
  sim_divrem (inst := .divUI64) (res := (0, 1)) (op := fun a b => a / b) (fun _ _ _ _ => rfl)
    (fun f α m st sl b a vs hv hb => by simp only [execOne.eq_def, hv, hb, ↓reduceIte])
    (fun f α m st sl b a vs hv hb => ⟨st, "integer divide by zero", by
      simp only [execOne.eq_def, hv, hb, ↓reduceIte]⟩)
    (by invalid_tac)
    (fun t a b h0 h1 _ _ => ⟨h0, h1⟩) F

theorem sim_remUI64 (F : Nat) : InstrSim P σ code F .remUI64 :=
  sim_divrem (inst := .remUI64) (res := (2, 3)) (op := fun a b => a % b) (fun _ _ _ _ => rfl)
    (fun f α m st sl b a vs hv hb => by simp only [execOne.eq_def, hv, hb, ↓reduceIte])
    (fun f α m st sl b a vs hv hb => ⟨st, "integer divide by zero", by
      simp only [execOne.eq_def, hv, hb, ↓reduceIte]⟩)
    (by invalid_tac)
    (fun t a b _ _ h2 h3 => ⟨h2, h3⟩) F

end LeanExe.M7
