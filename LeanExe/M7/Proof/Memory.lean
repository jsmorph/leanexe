import LeanExe.M7.Proof.Straight
import LeanExe.M7.Proof.Pair

/-!
Words of the model's memory and the code that loads and stores them relative to SP.  `Ram P a`
states that the byte at `a` is Normal memory and no device's, and a word load or store at an
address that is a multiple of 4 whose four bytes satisfy it reads or writes memory.
`load32_store32` reads back the word that a store wrote, and `load32_store32_far` states that a
store leaves every word whose distance from it, modulo 2^32, lies from 4 to 2^32 - 4.

Slot code is a list of register forms that fall through and of loads and stores relative to SP.
`slotRun` executes it without the checks of the loads and stores, and `run_slots` shows that the
model reaches that state from placed slot code whose loads and stores pass the checks.  The
tactic `slot_simp` reads the registers, the memory, SP, and the flags of the states that
`slotRun` builds.
-/

namespace LeanExe.M7

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Words of memory -/

/-- The byte at `a` is Normal memory and no device's. -/
def Ram (P : Platform) (a : UInt32) : Prop := P.normal a = true ∧ P.device a = false

/-- A word load or store at `a` reads or writes memory. -/
def WordOk (P : Platform) (a : UInt32) : Prop :=
  a % 4 = 0 ∧ P.device a = false ∧ P.mapped a 4 = true

theorem store32_far {m : UInt32 → UInt8} {a v b : UInt32} (h : ¬ b - a < 4) :
    store32 m a v b = m b := by
  simp only [store32, h, ↓reduceIte]

theorem toNat_sub_add32 (a b k : UInt32) :
    (b + k - a).toNat = ((b - a).toNat + k.toNat) % 4294967296 := by
  have := toNat_lt32 a
  have := toNat_lt32 b
  have := toNat_lt32 k
  rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_sub]
  simp only [Nat.reducePow]
  omega

/-- A word store at `a` leaves the word at `b` when the distance from `a` to `b`, modulo 2^32,
lies from 4 to 2^32 - 4. -/
theorem load32_store32_far {m : UInt32 → UInt8} {a v b : UInt32} (h1 : 4 ≤ (b - a).toNat)
    (h2 : (b - a).toNat ≤ 4294967292) : load32 (store32 m a v) b = load32 m b := by
  have hk : ∀ k : UInt32, k.toNat < 4 → ¬ b + k - a < 4 := fun k hk => by
    rw [UInt32.lt_iff_toNat_lt, toNat_sub_add32, show (4 : UInt32).toNat = 4 from rfl]
    omega
  have h0 : ¬ b - a < 4 := by
    rw [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl]
    omega
  unfold load32
  rw [store32_far h0, store32_far (hk 1 (by decide)), store32_far (hk 2 (by decide)),
    store32_far (hk 3 (by decide))]

/-- The four bytes of a word, each shifted to its place, combine to the word. -/
theorem bytes_combine (n : Nat) (hn : n < 4294967296) :
    n % 256 ||| n / 256 % 256 * 256 ||| n / 65536 % 256 * 65536 ||| n / 16777216 % 256 * 16777216
      = n := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, or_add_shift (by omega),
    show (65536 : Nat) = 2 ^ 16 from rfl, or_add_shift (by omega),
    show (16777216 : Nat) = 2 ^ 24 from rfl, or_add_shift (by omega)]
  omega

/-- Byte `k` of `v`, as `store32` writes it, as a number. -/
theorem toNat_byte (v c : UInt32) (k : Nat) (hc : c.toNat = k) (hk : k < 4) :
    ((v >>> (c * 8)).toUInt8.toUInt32).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_mul, hc,
    show (8 : UInt32).toNat = 8 from rfl, Nat.shiftRight_eq_div_pow,
    show k * 8 % 2 ^ 32 % 32 = 8 * k by omega]

theorem toNat_shiftLeft32 (x j : UInt32) (n : Nat) (hj : j.toNat = n) (hn : n < 32)
    (hx : x.toNat * 2 ^ n < 4294967296) : (x <<< j).toNat = x.toNat * 2 ^ n := by
  rw [UInt32.toNat_shiftLeft, hj, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt hx

/-- A load of the word that a store wrote reads it back. -/
theorem load32_store32 (m : UInt32 → UInt8) (a v : UInt32) : load32 (store32 m a v) a = v := by
  have e : ∀ k : UInt32, a + k - a = k := fun k => by
    rw [UInt32.add_comm, UInt32.add_sub_cancel]
  have hs : ∀ k : UInt32, k < 4 → store32 m a v (a + k) = (v >>> (k * 8)).toUInt8 := fun k hk => by
    simp only [store32, e, hk, ↓reduceIte]
  have h0 : store32 m a v a = (v >>> ((0 : UInt32) * 8)).toUInt8 := by
    simp only [store32, UInt32.sub_self, show (0 : UInt32) < 4 from by decide, ↓reduceIte]
  unfold load32
  rw [h0, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide)]
  apply UInt32.toNat_inj.mp
  have hv := toNat_lt32 v
  have b0 := toNat_byte v 0 0 rfl (by decide)
  have b1 := toNat_byte v 1 1 rfl (by decide)
  have b2 := toNat_byte v 2 2 rfl (by decide)
  have b3 := toNat_byte v 3 3 rfl (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.reducePow, Nat.reduceMul]
    at b0 b1 b2 b3
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    toNat_shiftLeft32 _ 8 8 rfl (by decide) (by rw [b1]; simp only [Nat.reducePow]; omega),
    toNat_shiftLeft32 _ 16 16 rfl (by decide) (by rw [b2]; simp only [Nat.reducePow]; omega),
    toNat_shiftLeft32 _ 24 24 rfl (by decide) (by rw [b3]; simp only [Nat.reducePow]; omega),
    b0, b1, b2, b3]
  exact bytes_combine _ hv

/-! ## Loads and stores relative to SP -/

theorem exec_ldrSp {s : State} {t : Fin 8} {o : Fin 4096} (h : WordOk P (s.sp + UInt32.ofNat o.val)) :
    exec P σ (.ldrSp t o) s =
      some { s.setR t (load32 s.mem (s.sp + UInt32.ofNat o.val)) with pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, loadWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

theorem exec_strSp {s : State} {t : Fin 8} {o : Fin 4096} (h : WordOk P (s.sp + UInt32.ofNat o.val)) :
    exec P σ (.strSp t o) s =
      some { s with mem := store32 s.mem (s.sp + UInt32.ofNat o.val) (s.r t), pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, storeWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

theorem exec_ldrLr {s : State} {o : Fin 4096} (h : WordOk P (s.sp + UInt32.ofNat o.val)) :
    exec P σ (.ldrLr o) s =
      some { s with lr := load32 s.mem (s.sp + UInt32.ofNat o.val), pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, loadWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

theorem exec_strLr {s : State} {o : Fin 4096} (h : WordOk P (s.sp + UInt32.ofNat o.val)) :
    exec P σ (.strLr o) s =
      some { s with mem := store32 s.mem (s.sp + UInt32.ofNat o.val) s.lr, pc := s.pc + 4 } := by
  obtain ⟨h4, hd, hm⟩ := h
  simp only [exec, storeWord, h4, hd, hm, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    Option.map_some]

/-- The word at `sp + o` of a region of `n` bytes of `Ram` from `sp`, with `sp` and `o` multiples
of 4 and `o + 4 ≤ n`, passes the checks of a load and a store. -/
theorem mod4_add {sp : UInt32} {o : Nat} (hsp : sp % 4 = 0) (ho : o % 4 = 0) :
    (sp + UInt32.ofNat o) % 4 = 0 := by
  have h : sp.toNat % 4 = 0 := by
    have := congrArg UInt32.toNat hsp
    simpa [UInt32.toNat_mod] using this
  have := toNat_lt32 sp
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_mod, UInt32.toNat_add, UInt32.toNat_ofNat',
    show (4 : UInt32).toNat = 4 from rfl, show (0 : UInt32).toNat = 0 from rfl, Nat.reducePow]
  omega

theorem wordOk_of_ram {sp : UInt32} {n o : Nat} (hram : ∀ j < n, Ram P (sp + UInt32.ofNat j))
    (hsp : sp % 4 = 0) (ho : o % 4 = 0) (hn : o + 4 ≤ n) : WordOk P (sp + UInt32.ofNat o) := by
  refine ⟨mod4_add hsp ho, (hram o (by omega)).2, ?_⟩
  unfold Platform.mapped
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  rw [add_ofNat_add]
  exact (hram (o + i) (by omega)).1

/-! ## The projections of the state updates

Each lemma is proved after `cases s`, so that `simp` uses it as an equation; see the lemmas of
`State` in `LeanExe/M7/Proof/Straight.lean`. -/

namespace State

theorem mem_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).mem = s.mem := by
  cases s; rfl
theorem sp_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).sp = s.sp := by
  cases s; rfl
theorem lr_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).lr = s.lr := by
  cases s; rfl
theorem trace_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).trace = s.trace := by
  cases s; rfl
theorem reads_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).reads = s.reads := by
  cases s; rfl
theorem pc_withPc (s : State) (p : UInt32) : ({ s with pc := p } : State).pc = p := by
  cases s; rfl

theorem mem_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).mem = s.mem := by
  cases s; rfl
theorem sp_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).sp = s.sp := by
  cases s; rfl
theorem lr_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).lr = s.lr := by
  cases s; rfl
theorem pc_setR (s : State) (d : Fin 8) (v : UInt32) : (s.setR d v).pc = s.pc := by
  cases s; rfl

theorem mem_setNZCV (s : State) (f : UInt32 × Bool × Bool) : (s.setNZCV f).mem = s.mem := by
  cases s; rfl
theorem sp_setNZCV (s : State) (f : UInt32 × Bool × Bool) : (s.setNZCV f).sp = s.sp := by
  cases s; rfl
theorem pc_setNZCV (s : State) (f : UInt32 × Bool × Bool) : (s.setNZCV f).pc = s.pc := by
  cases s; rfl

theorem mem_result (s : State) (sf : Fin 2) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result sf d f).mem = s.mem := by
  unfold result; split <;> (cases s; rfl)
theorem sp_result (s : State) (sf : Fin 2) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result sf d f).sp = s.sp := by
  unfold result; split <;> (cases s; rfl)
theorem pc_result (s : State) (sf : Fin 2) (d : Fin 8) (f : UInt32 × Bool × Bool) :
    (s.result sf d f).pc = s.pc := by
  unfold result; split <;> (cases s; rfl)

theorem r_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) (i : Fin 8) :
    ({ s with mem := m, pc := p } : State).r i = s.r i := by
  cases s; rfl
theorem mem_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).mem = m := by
  cases s; rfl
theorem sp_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).sp = s.sp := by
  cases s; rfl
theorem pc_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).pc = p := by
  cases s; rfl
theorem zFlag_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).zFlag = s.zFlag := by
  cases s; rfl
theorem cFlag_withMem (s : State) (m : UInt32 → UInt8) (p : UInt32) :
    ({ s with mem := m, pc := p } : State).cFlag = s.cFlag := by
  cases s; rfl

theorem r_withLrPc (s : State) (l p : UInt32) (i : Fin 8) :
    ({ s with lr := l, pc := p } : State).r i = s.r i := by
  cases s; rfl
theorem sp_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).sp = s.sp := by
  cases s; rfl
theorem mem_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).mem = s.mem := by
  cases s; rfl
theorem trace_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).trace = s.trace := by
  cases s; rfl
theorem reads_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).reads = s.reads := by
  cases s; rfl
theorem lr_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).lr = l := by
  cases s; rfl
theorem pc_withLrPc (s : State) (l p : UInt32) :
    ({ s with lr := l, pc := p } : State).pc = p := by
  cases s; rfl

end State

/-! ## Slot code -/

/-- The forms of slot code: the register forms that fall through, but `UDIV`, which stops the
model on a zero divisor, and the loads and stores of r0 to r7 relative to SP. -/
def Instr.slotForm : Instr → Bool
  | .ldrSp .. | .strSp .. => true
  | .udiv .. => false
  | i => i.regOnly && i.falls

/-- `i` is a load or a store of slot code at the offset `o` from SP. -/
def Instr.slotOffset : Instr → Option Nat
  | .ldrSp _ o | .strSp _ o => some o.val
  | _ => none

/-- The instructions `is` are slot code whose loads and stores address words that pass the
checks at `sp` plus their offsets. -/
def SlotsOk (P : Platform) (sp : UInt32) (is : List Instr) : Prop :=
  ∀ i ∈ is, i.slotForm = true ∧ ∀ o, i.slotOffset = some o → WordOk P (sp + UInt32.ofNat o)

/-- The state after the instruction `i` of slot code, with its load or store done without the
checks. -/
def slotStep (P : Platform) (σ : Nat → UInt32) (i : Instr) (s : State) : State :=
  match i with
  | .ldrSp t o => { s.setR t (load32 s.mem (s.sp + UInt32.ofNat o.val)) with pc := s.pc + 4 }
  | .strSp t o =>
      { s with mem := store32 s.mem (s.sp + UInt32.ofNat o.val) (s.r t), pc := s.pc + 4 }
  | i => (exec P σ i s).getD s

/-- The state after the slot code `is`, executed from `s` without the checks of its loads and
stores. -/
def slotRun (P : Platform) (σ : Nat → UInt32) (is : List Instr) (s : State) : State :=
  is.foldl (fun t i => slotStep P σ i t) s

theorem slotRun_nil (s : State) : slotRun P σ [] s = s := rfl

theorem slotRun_cons (i : Instr) (is : List Instr) (s : State) :
    slotRun P σ (i :: is) s = slotRun P σ is (slotStep P σ i s) := rfl

theorem slotRun_append (l1 l2 : List Instr) (s : State) :
    slotRun P σ (l1 ++ l2) s = slotRun P σ l2 (slotRun P σ l1 s) := by
  simp [slotRun, List.foldl_append]

theorem exec_slotStep_reg {i : Instr} {s : State} (hr : i.regOnly = true) (hfa : i.falls = true)
    (he : exec P σ i s = some (slotStep P σ i s)) :
    exec P σ i s = some (slotStep P σ i s) ∧ (slotStep P σ i s).sp = s.sp ∧
      (slotStep P σ i s).lr = s.lr ∧ (slotStep P σ i s).trace = s.trace ∧
      (slotStep P σ i s).reads = s.reads ∧ (slotStep P σ i s).pc = s.pc + 4 ∧
      ∀ j : Fin 13, 8 ≤ j.val → (slotStep P σ i s).regs j = s.regs j := by
  have k := exec_keeps hr he
  exact ⟨he, k.sp, k.lr, k.trace, k.reads, exec_falls_pc hfa he, k.high⟩

/-- A step of slot code whose load or store passes the checks is the model's execution of it, and
it keeps SP, LR, r8 to r12, the device trace, and the read count. -/
theorem exec_slotStep {i : Instr} {s : State} (hf : i.slotForm = true)
    (hw : ∀ o, i.slotOffset = some o → WordOk P (s.sp + UInt32.ofNat o)) :
    exec P σ i s = some (slotStep P σ i s) ∧ (slotStep P σ i s).sp = s.sp ∧
      (slotStep P σ i s).lr = s.lr ∧ (slotStep P σ i s).trace = s.trace ∧
      (slotStep P σ i s).reads = s.reads ∧ (slotStep P σ i s).pc = s.pc + 4 ∧
      ∀ j : Fin 13, 8 ≤ j.val → (slotStep P σ i s).regs j = s.regs j := by
  cases i
  case ldrSp t o =>
    have k := ((Keeps.refl s).setR t (load32 s.mem (s.sp + UInt32.ofNat o.val))).withPc (s.pc + 4)
    exact ⟨exec_ldrSp (hw o.val rfl), k.sp, k.lr, k.trace, k.reads, by cases s; rfl, k.high⟩
  case strSp t o =>
    exact ⟨exec_strSp (hw o.val rfl), by cases s; rfl, by cases s; rfl, by cases s; rfl,
      by cases s; rfl, by cases s; rfl, fun _ _ => by cases s; rfl⟩
  all_goals first
    | exact exec_slotStep_reg rfl rfl rfl
    | simp [Instr.slotForm, Instr.regOnly, Instr.falls] at hf

/-- Placed slot code whose loads and stores pass the checks takes the model to the state that
`slotRun` gives, at the address after the code, with SP, LR, r8 to r12, the device trace, and
the read count as they were. -/
theorem run_slots {is : List Instr} {s : State} (hok : SlotsOk P s.sp is)
    (hc : CodeAt code s.pc is) :
    Reach P σ code s (slotRun P σ is s) ∧
      (slotRun P σ is s).pc = s.pc + UInt32.ofNat (4 * is.length) ∧
      (slotRun P σ is s).sp = s.sp ∧ (slotRun P σ is s).lr = s.lr ∧
      (slotRun P σ is s).trace = s.trace ∧ (slotRun P σ is s).reads = s.reads ∧
      ∀ j : Fin 13, 8 ≤ j.val → (slotRun P σ is s).regs j = s.regs j := by
  induction is generalizing s with
  | nil => exact ⟨.refl _, by rw [slotRun_nil]; simp, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons i is ih =>
      obtain ⟨hf, hw⟩ := hok i List.mem_cons_self
      obtain ⟨he, hsp, hlr, htr, hrd, hpc, hhi⟩ := exec_slotStep (P := P) (σ := σ) hf hw
      have hok' : SlotsOk P (slotStep P σ i s).sp is := by
        rw [hsp]; exact fun j hj => hok j (List.mem_cons_of_mem _ hj)
      obtain ⟨hci, hcs⟩ := CodeAt.cons.mp hc
      have hsz : i.size = 4 := by
        cases i <;> first | rfl | simp [Instr.slotForm, Instr.falls] at hf
      rw [hsz, show s.pc + UInt32.ofNat 4 = (slotStep P σ i s).pc by rw [hpc]; rfl] at hcs
      obtain ⟨r, p, sp', lr', tr', rd', hi'⟩ := ih hok' hcs
      rw [slotRun_cons]
      refine ⟨reach_exec hci he r, ?_, by rw [sp', hsp], by rw [lr', hlr], by rw [tr', htr],
        by rw [rd', hrd], fun j hj => by rw [hi' j hj, hhi j hj]⟩
      rw [p, hpc, List.length_cons]
      addr_eq

end LeanExe.M7
