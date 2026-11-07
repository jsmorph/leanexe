import LeanExe.M7.Proof.Forms

/-!
The simulation of the multiplication, the comparisons for equality, the shifts, `eqzI64`, and
`extendUI32`.  Each lemma about words states that the register code leaves the words of Talos's
result, from the words of the operands in r0 to r3: `UMULL` and two `MLA`s give the product's low
word and the high word of its low 64 bits, `CLZ` and `LSR #5` give 1 for a zero word and 0
otherwise, and the shift sequences follow CompCert's `__compcert_i64_shl` and
`__compcert_i64_shr`.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

theorem ofNat_imm63 : UInt32.ofNat (63 : Fin 256).val = 63 := rfl

/-- Reads the registers of the state that placed register code leaves: it unfolds `slotRun`, the
steps, and the constructors from numbers, and applies `state_simp`. -/
macro "slot_regs" : tactic =>
  `(tactic| (
    simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some, Instr.lsrBy,
      Instr.lslBy, Instr.addLsl, Instr.movwOf, Instr.movtOf, List.cons_append, List.nil_append]
    state_simp))

/-! ## Words -/

theorem mod_mul_self_eq {S r W : Nat} (hr : r < W) : (S * W + r) % (W * W) = S % W * W + r := by
  have hW : 0 < W := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have h1 : S * W + r = (S % W * W + r) + W * W * (S / W) := by
    have hs := Nat.mod_add_div S W
    calc S * W + r = (S % W + W * (S / W)) * W + r := by rw [hs]
      _ = S % W * W + W * W * (S / W) + r := by rw [Nat.add_mul, Nat.mul_right_comm W]
      _ = _ := by rw [Nat.add_right_comm]
  rw [h1, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt S hW
  calc S % W * W + r < S % W * W + W := by omega
    _ = (S % W + 1) * W := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ W * W := Nat.mul_le_mul_right _ this

theorem mul_slot (a b : UInt64) :
    SlotRel (.i64 (a * b)) (UInt32.ofNat (a.toUInt32.toNat * b.toUInt32.toNat))
      (UInt32.ofNat (a.toUInt32.toNat * b.toUInt32.toNat / 4294967296) +
        a.toUInt32 * (b >>> 32).toUInt32 + (a >>> 32).toUInt32 * b.toUInt32) := by
  apply eq_of_pairNat
  have ha := pairNat_toUInt32 a
  have hb := pairNat_toUInt32 b
  unfold pairNat at ha hb ⊢
  rw [UInt64.toNat_mul, ← ha, ← hb, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_mul,
    UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  have h0 := toNat_lt32 a.toUInt32
  have h1 := toNat_lt32 (a >>> 32).toUInt32
  have h2 := toNat_lt32 b.toUInt32
  have h3 := toNat_lt32 (b >>> 32).toUInt32
  generalize a.toUInt32.toNat = A0 at *
  generalize (a >>> 32).toUInt32.toNat = A1 at *
  generalize b.toUInt32.toNat = B0 at *
  generalize (b >>> 32).toUInt32.toNat = B1 at *
  have expand : ∀ W : Nat, (A1 * W + A0) * (B1 * W + B0) =
      A1 * B1 * (W * W) + A1 * B0 * W + A0 * B1 * W + A0 * B0 := by
    intro W
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_mul_mul_comm, Nat.mul_right_comm A1 W B0,
      ← Nat.mul_assoc A0 B1 W]
    omega
  rw [expand 4294967296, show (2 : Nat) ^ 64 = 4294967296 * 4294967296 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl]
  generalize A1 * B1 = P11
  generalize A1 * B0 = P10
  generalize A0 * B1 = P01
  generalize A0 * B0 = P00
  have hhi : ((P00 / 4294967296 % 4294967296 + P01 % 4294967296) % 4294967296 +
      P10 % 4294967296) % 4294967296 = (P10 + P01 + P00 / 4294967296) % 4294967296 := by omega
  have hX : ∀ W : Nat, P11 * (W * W) + P10 * W + P01 * W + P00 =
      ((P10 + P01 + P00 / W) * W + P00 % W) + W * W * P11 := by
    intro W
    rw [Nat.add_mul, Nat.add_mul, Nat.add_assoc (P10 * W + P01 * W), Nat.div_add_mod',
      Nat.mul_comm P11 (W * W)]
    omega
  rw [hhi, hX 4294967296, Nat.add_mul_mod_self_left, mod_mul_self_eq (Nat.mod_lt _ (by decide))]

theorem words_eq_zero (a b : UInt64) :
    (a.toUInt32 ^^^ b.toUInt32 ||| (a >>> 32).toUInt32 ^^^ (b >>> 32).toUInt32) = 0 ↔ a = b := by
  rw [UInt32.or_eq_zero_iff, UInt32.xor_eq_zero_iff, UInt32.xor_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    apply UInt64.toNat_inj.mp
    rw [← pairNat_toUInt32 a, ← pairNat_toUInt32 b, h0, h1]
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem shr5_clz (x : UInt32) : shr (clz32 x) 5 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx
    decide
  · simp only [hx, ↓reduceIte]
    have := (clz32_bounds hx).1
    apply UInt32.toNat_inj.mp
    rw [toNat_shr]
    simp only [Nat.reducePow, show (0 : UInt32).toNat = 0 from rfl]
    omega

theorem eq_slot (a b : UInt64) :
    SlotRel (.i32 (if a = b then 1 else 0))
      (shr (clz32 (a.toUInt32 ^^^ b.toUInt32 ||| (a >>> 32).toUInt32 ^^^ (b >>> 32).toUInt32)) 5)
      0 := by
  refine ⟨?_, rfl⟩
  rw [shr5_clz]
  by_cases h : a = b
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((words_eq_zero a b).mpr h)),
      ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => h ((words_eq_zero a b).mp e)),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem ne_slot (a b : UInt64) :
    SlotRel (.i32 (if a ≠ b then 1 else 0))
      (shr (clz32 (a.toUInt32 ^^^ b.toUInt32 ||| (a >>> 32).toUInt32 ^^^ (b >>> 32).toUInt32)) 5
        ^^^ 1) 0 := by
  refine ⟨?_, rfl⟩
  rw [shr5_clz]
  by_cases h : a = b
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((words_eq_zero a b).mpr h)),
      ite_eq_right_of_eq_false _ _ (eq_false fun hne => hne h)]
    decide
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => h ((words_eq_zero a b).mp e)),
      ite_eq_left_of_eq_true _ _ (eq_true h)]
    decide

theorem eqz_slot (a : UInt64) :
    SlotRel (.i32 (if a = 0 then 1 else 0))
      (shr (clz32 (a.toUInt32 ||| (a >>> 32).toUInt32)) 5) 0 := by
  have h := words_eq_zero a 0
  rw [show (0 : UInt64).toUInt32 = 0 from rfl, show ((0 : UInt64) >>> 32).toUInt32 = 0 from rfl,
    UInt32.xor_zero, UInt32.xor_zero] at h
  refine ⟨?_, rfl⟩
  rw [shr5_clz]
  by_cases hz : a = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (h.mpr hz)), ite_eq_left_of_eq_true _ _ (eq_true hz)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => hz (h.mp e)),
      ite_eq_right_of_eq_false _ _ (eq_false hz)]

theorem toNat_and63 (b : UInt64) : (b.toUInt32 &&& 63).toNat = b.toNat % 64 := by
  rw [UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_toUInt32]
  simp only [Nat.reducePow]
  omega

theorem toNat_mod64 (b : UInt64) : (b % 64).toNat % 64 = b.toNat % 64 := by
  rw [UInt64.toNat_mod, show (64 : UInt64).toNat = 64 from rfl, Nat.mod_mod]

theorem shl_slot (a b : UInt64) :
    SlotRel (.i64 (a <<< (b % 64))) (shl a.toUInt32 ((b.toUInt32 &&& 63).toNat % 256))
      (shlHigh a.toUInt32 (a >>> 32).toUInt32 (b.toUInt32 &&& 63)) := by
  have hk := toNat_and63 b
  apply eq_of_pairNat
  rw [shl_pair _ _ _ (by rw [hk]; omega), pairNat_toUInt32, UInt64.toNat_shiftLeft, hk,
    toNat_mod64, Nat.shiftLeft_eq]

theorem shr_slot (a b : UInt64) :
    SlotRel (.i64 (a >>> (b % 64))) (shrLow a.toUInt32 (a >>> 32).toUInt32 (b.toUInt32 &&& 63))
      (shr (a >>> 32).toUInt32 ((b.toUInt32 &&& 63).toNat % 256)) := by
  have hk := toNat_and63 b
  apply eq_of_pairNat
  rw [shr_pair _ _ _ (by rw [hk]; omega), pairNat_toUInt32, UInt64.toNat_shiftRight, hk,
    toNat_mod64, Nat.shiftRight_eq_div_pow]

/-! ## The binary forms -/

theorem sim_mulI64 (F : Nat) : InstrSim P σ code F .mulI64 :=
  sim_binary (inst := .mulI64) (ops := [.umull 4 5 0 2 (by decide), .mla 5 0 3 5, .mla 5 1 2 5]) (res := (4, 5))
    (t := .i64) (op := fun a b => .i64 (a * b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      slot_regs
      rw [h0, h1, h2, h3]
      exact mul_slot a b)
    (fun _ _ => trivial) F

theorem sim_eqI64 (F : Nat) : InstrSim P σ code F .eqI64 :=
  sim_binary (inst := .eqI64) (ops := eqOps) (res := (0, 1)) (t := .i32)
    (op := fun a b => .i32 (if a = b then 1 else 0)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [eqOps]
      slot_regs
      rw [h0, h1, h2, h3, ofNat_imm0]
      exact eq_slot a b)
    (fun _ _ => trivial) F

theorem gen_neI64 (E : Env) (ctl : List Ctl) (σs : List ValueType) (a : UInt32) :
    genInstr E ctl σs a .neI64 = genBin E ctl σs (eqOps ++ [.eorImm 0 0 1]) (0, 1) .i32 := rfl

theorem exec_neI64 (f : Nat) {α : Type} (m : Module) (st : Store α) (sl : Locals) (b a : UInt64)
    (vs : List Value) (hv : sl.values = .i64 b :: .i64 a :: vs) :
    execOne (f + 1) m st sl .neI64 =
      .Fallthrough st { sl with values := .i32 (if a ≠ b then 1 else 0) :: vs } := by
  simp only [execOne.eq_def, hv]

theorem invalid_neI64 (f : Nat) {α : Type} (m : Module) (st : Store α) (sl : Locals)
    (hn : ∀ b a vs, sl.values ≠ .i64 b :: .i64 a :: vs) :
    ∃ msg, execOne (f + 1) m st sl .neI64 = .Invalid msg := by
  revert f α m st sl hn
  invalid_tac

theorem regs_neI64 (u : State) (a b : UInt64) (h0 : u.r 0 = a.toUInt32)
    (h1 : u.r 1 = (a >>> 32).toUInt32) (h2 : u.r 2 = b.toUInt32)
    (h3 : u.r 3 = (b >>> 32).toUInt32) :
    SlotRel (.i32 (if a ≠ b then 1 else 0)) ((slotRun P σ (eqOps ++ [.eorImm 0 0 1]) u).r 0)
      ((slotRun P σ (eqOps ++ [.eorImm 0 0 1]) u).r 1) := by
  simp only [eqOps]
  slot_regs
  rw [h0, h1, h2, h3, ofNat_imm0, ofNat_imm1]
  exact ne_slot a b

theorem regForm_neOps : (eqOps ++ [Instr.eorImm 0 0 1]).all Instr.regForm = true := rfl

theorem type_neI64 (a b : UInt64) : HasType .i32 (.i32 (if a ≠ b then 1 else 0)) := trivial

theorem sim_neI64 (F : Nat) : InstrSim P σ code F .neI64 :=
  sim_binary (inst := .neI64) (ops := eqOps ++ [Instr.eorImm 0 0 1]) (res := (0, 1)) (t := .i32)
    (op := fun a b => .i32 (if a ≠ b then 1 else 0)) gen_neI64 regForm_neOps exec_neI64
    invalid_neI64 regs_neI64 type_neI64 F

/-! ## Shifts -/

theorem gen_shift {E : Env} {ctl : List Ctl} {σs : List ValueType} {ops : List Instr}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genShift E ctl σs ops = .ok (is, fin)) :
    curBase ctl + 2 ≤ σs.length ∧ σs.length - 1 < E.frame.height ∧ ∃ h0 h1 h2 h4 h5,
      is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
        .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩] ++ ops ++
        [.strSp 0 ⟨E.frame.opAt (σs.length - 2), h4⟩,
          .strSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩] ∧
      fin = some (.i64 :: σs.drop 2) := by
  unfold genShift at hg
  by_cases hc : σs.length < curBase ctl + 2
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨x, hx, y, hy, l1, hl1, i, hi, l3, hl3, rfl, rfl⟩ := hg
    obtain ⟨-, rfl⟩ := Env.op_ok hx
    obtain ⟨hlt, rfl⟩ := Env.op_ok hy
    obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl1
    obtain ⟨h2, rfl⟩ := imm_ok hi
    obtain ⟨h4, h5, rfl⟩ := stPair_ok hl3
    exact ⟨by omega, hlt, h0, h1, h2, h4, h5, rfl, rfl⟩

/-- The simulation of a shift that the generator compiles with `genShift`: the loads of the value
below the top into r0:r1 and of the top's low word into r2, the register code `ops`, and the store
of r0:r1. -/
theorem sim_shift {inst : Instruction} {ops : List Instr} {op : UInt64 → UInt64 → Value}
    (hgen : ∀ E ctl σs a, genInstr E ctl σs a inst = genShift E ctl σs ops)
    (hops : ops.all Instr.regForm = true)
    (hfall : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals) (b a : UInt64)
      (vs : List Value), sl.values = .i64 b :: .i64 a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := op a b :: vs })
    (hinvalid : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∀ b a vs, sl.values ≠ .i64 b :: .i64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg)
    (hval : ∀ (u : State) (a b : UInt64), u.r 0 = a.toUInt32 → u.r 1 = (a >>> 32).toUInt32 →
      u.r 2 = b.toUInt32 → SlotRel (op a b) ((slotRun P σ ops u).r 0) ((slotRun P σ ops u).r 1))
    (htype : ∀ a b, HasType .i64 (op a b)) (F : Nat) : InstrSim P σ code F inst := by
  intro E ctl σs a is fin hg hcode _ hb α m st sl ms hinv hpc need D _ _ _
  rw [hgen] at hg
  obtain ⟨hb2, hlt, h0, h1, h2, h4, h5, rfl, rfl⟩ := gen_shift hg
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      by_cases hshape : ∃ b a vs, sl.values = .i64 b :: .i64 a :: vs
      · obtain ⟨b, a', vs, hv⟩ := hshape
        rw [hfall f m st sl b a' vs hv]
        obtain ⟨-, -, ha0, ha1, hb0, -⟩ := hinv.top2 hv
        obtain ⟨hk8, hklr, -⟩ := E.frame.opAt_bounds (k := σs.length - 2) (by omega)
        obtain ⟨hj8, hjlr, hlrs⟩ := E.frame.opAt_bounds hlt
        exact outcome_two hinv hpc hcode hb2 hlt
          (slotsOk_ld (P := P) (t := 0) (h := h0) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 1) (h := h1) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 2) (h := h2) (hinv.frame.word (by omega) (by omega))
          (slotsOk_nil _)))) rfl rfl hops hv
          (hval (slotRun P σ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
            .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
            .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩] ms) a' b ha0 ha1 hb0)
          (htype a' b)
      · obtain ⟨msg, he⟩ := hinvalid f m st sl (fun b a vs h => hshape ⟨b, a, vs, h⟩)
        rw [he]
        trivial

theorem sim_shlI64 (F : Nat) : InstrSim P σ code F .shlI64 :=
  sim_shift (inst := .shlI64) (ops := shlOps) (op := fun a b => .i64 (a <<< (b % 64))) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 => by
      simp only [shlOps]
      slot_regs
      rw [sub_addWithCarry, sub_addWithCarry, ofNat_imm32, ofNat_imm63, h0, h1, h2]
      exact shl_slot a b)
    (fun _ _ => trivial) F

theorem sim_shrUI64 (F : Nat) : InstrSim P σ code F .shrUI64 :=
  sim_shift (inst := .shrUI64) (ops := shrOps) (op := fun a b => .i64 (a >>> (b % 64))) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 => by
      simp only [shrOps]
      slot_regs
      rw [sub_addWithCarry, sub_addWithCarry, ofNat_imm32, ofNat_imm63, h0, h1, h2]
      exact shr_slot a b)
    (fun _ _ => trivial) F

/-! ## `eqzI64` and `extendUI32` -/

theorem gen_eqzI64 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a .eqzI64 = .ok (is, fin)) :
    curBase ctl + 1 ≤ σs.length ∧ σs.length - 1 < E.frame.height ∧ ∃ h0 h1 h2 h3,
      is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ++
        [.orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0] ++
        [.strSp 0 ⟨E.frame.opAt (σs.length - 1), h2⟩,
          .strSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ∧
      fin = some (.i32 :: σs.tail) := by
  unfold genInstr at hg
  by_cases hc : σs.length < curBase ctl + 1
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨x, hx, l1, hl1, l3, hl3, rfl, rfl⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok hx
    obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl1
    obtain ⟨h2, h3, rfl⟩ := stPair_ok hl3
    exact ⟨by omega, hlt, h0, h1, h2, h3, rfl, rfl⟩

theorem sim_eqzI64 (F : Nat) : InstrSim P σ code F .eqzI64 := by
  intro E ctl σs a is fin hgen hcode _ hb α m st sl ms hinv hpc need D _ _ _
  obtain ⟨hb1, hlt, h0, h1, h2, h3, rfl, rfl⟩ := gen_eqzI64 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hh := hinv.len
      by_cases hshape : ∃ x vs, sl.values = .i64 x :: vs
      · obtain ⟨x, vs, hv⟩ := hshape
        simp only [execOne.eq_def, hv]
        have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
        have htop := hinv.stack vs.length (.i64 x) (by
          rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
            Nat.sub_self, List.getElem?_cons_zero])
        rw [hvl] at htop
        obtain ⟨hx0, hx1⟩ := htop
        obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
        have hregs : ([Instr.orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0]).all
            Instr.regForm = true := rfl
        have hok := slotsOk_append (slotsOk_append
          (slotsOk_ld (P := P) (t := 0) (h := h0) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 1) (h := h1) (hinv.frame.word (by omega) (by omega))
          (slotsOk_nil _))) (slotsOk_reg hregs _))
          (slotsOk_st (P := P) (t := 0) (h := h2) (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (t := 1) (h := h3) (hinv.frame.word (by omega) (by omega))
          (slotsOk_nil _)))
        let u := slotRun P σ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩] ms
        obtain ⟨hm, hsp, -⟩ := slotRun_reg (P := P) (σ := σ) hregs u
        have hval : SlotRel (.i32 (if x = 0 then 1 else 0))
            ((slotRun P σ [.orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0] u).r 0)
            ((slotRun P σ [.orrReg 0 0 0 1, .clz 0 0, .lsrBy 0 0 5, .movImm 1 0] u).r 1) := by
          slot_regs
          rw [show u.r 0 = x.toUInt32 from hx0, show u.r 1 = (x >>> 32).toUInt32 from hx1,
            ofNat_imm0]
          exact eqz_slot x
        refine outcome_write hinv hpc hcode hok ?_ hlt (by omega) hvl
          (fun h v hv' => ?_) hval (Typed.cons trivial ?_)
        · rw [slotRun_append, slotRun_append, slotRun_st2, hm, hsp]
          rfl
        · have hl := getElem?_reverse_lt hv'
          exact hinv.stack h v (by rw [hv, getElem?_reverse_cons hl]; exact hv')
        · have := hinv.types.tail
          rw [hv] at this
          exact this
      · simp only [execOne.eq_def]
        split
        · rename_i x vs hv
          exact absurd ⟨x, vs, hv⟩ hshape
        · trivial

theorem extend_slot {x lo hi : UInt32} (h : SlotRel (.i32 x) lo hi) :
    SlotRel (.i64 (UInt64.ofNat x.toNat)) lo hi := by
  obtain ⟨rfl, rfl⟩ := h
  have hx := toNat_lt32 lo
  constructor <;> apply UInt32.toNat_inj.mp
  · rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  · rw [toNat_hi64, UInt64.toNat_ofNat']
    simp only [Nat.reducePow, show (0 : UInt32).toNat = 0 from rfl]
    omega

theorem gen_extendUI32 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a .extendUI32 = .ok (is, fin)) :
    curBase ctl + 1 ≤ σs.length ∧ is = [] ∧ fin = some (.i64 :: σs.tail) := by
  unfold genInstr at hg
  by_cases hc : σs.length < curBase ctl + 1 ∨ σs.head? ≠ some .i32
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    exact ⟨by omega, rfl, rfl⟩

theorem sim_extendUI32 (F : Nat) : InstrSim P σ code F .extendUI32 := by
  intro E ctl σs a is fin hgen hcode _ hb α m st sl ms hinv hpc need D _ _ _
  obtain ⟨hb1, rfl, rfl⟩ := gen_extendUI32 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hh := hinv.len
      by_cases hshape : ∃ x vs, sl.values = .i32 x :: vs
      · obtain ⟨x, vs, hv⟩ := hshape
        simp only [execOne.eq_def, hv]
        have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
        refine ⟨_, rfl, ms, .refl _, by rw [hpc, after_eq]; simp, rfl, rfl, rfl,
          BodyKeeps.refl _ _ _, Below.refl _ _ _,
          ⟨by have h := hinv.height; rw [hv] at h; simpa using h, fun h v hv' => ?_,
            hinv.count, hinv.locals, hinv.ltypes, hinv.frame, ?_⟩⟩
        · simp only [List.reverse_cons] at hv'
          by_cases hl : h < vs.length
          · rw [List.getElem?_append_left (by simpa using hl)] at hv'
            exact hinv.stack h v (by
              rw [hv, List.reverse_cons, List.getElem?_append_left (by simpa using hl)]
              exact hv')
          · rw [List.getElem?_append_right (by simp; omega)] at hv'
            simp only [List.length_reverse] at hv'
            by_cases he : h = vs.length
            · subst he
              simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv'
              subst hv'
              exact extend_slot (hinv.stack vs.length (.i32 x) (by
                rw [hv, List.reverse_cons, List.getElem?_append_right (by simp),
                  List.length_reverse, Nat.sub_self, List.getElem?_cons_zero]))
            · rw [List.getElem?_eq_none (by simp; omega)] at hv'
              cases hv'
        · have := hinv.types.tail
          rw [hv] at this
          exact Typed.cons trivial this
      · simp only [execOne.eq_def]
        split
        · rename_i x vs hv
          exact absurd ⟨x, vs, hv⟩ hshape
        · trivial

end LeanExe.M7
