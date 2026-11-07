import LeanExe.M7.Isla.Walk

/-!
Theorems of `Agrees` for the word loads and stores of `LeanExe/M7/Machine.lean`: `LDR.W` and
`STR.W` at `Rn` plus an immediate in DTCM and in the device window, and at SP for a register of
r0 to r7 and for LR, from the traces of `tests/isla/m7` under the profile `sys` of
`LeanExe/M7/Isla/Profile.lean`.  Each theorem holds for every register of r0 to r7 in each field,
every immediate, every platform, and every sequence of device values, for every machine whose
program counter plus 4 is below 2^32 and whose access satisfies the reset constraint of
`tests/isla/m7-traces.sh`: an aligned word inside DTCM, 0x20000000 to 0x2001fffc, or inside the
device window, 0x40000000 to 0x4003fffc.  The SP forms state the alignment as SP and the immediate
being multiples of 4, the invariant under which the A-profile's R[13] and the M-profile's
`SP<31:2>:'00'` (B1.4.7) agree.  Each theorem assumes the descriptor that the walk reads from
`Mach.far`, `0x745` at 0x100000000 for the GiB of DTCM and `0x0060000040000441` at 0x100000008 for
the GiB of the device window.  `tests/isla/m7-theorems.sh` elaborates the module and prints the
axioms of its theorems.

The trace's memory event carries no memory type, and the semantics takes an access as a device
access from the platform's `device` predicate, so each theorem covers the device access and the
access to memory alike, by cases on `P.device` of the address, and `exec`'s `loadWord` and
`storeWord` take the same cases.  The walk of `LeanExe/M7/Isla/Walk.lean` rewrites the address of
the trace, the low word of the base register plus the immediate, into the model's address at once,
so that later events, the translation's masks among them, compute with it, and `ttbr_base` reduces
the table's address, which the walk computes from `_TTBR0_EL1` and `TTBR0_NS`, to 0x100000000.
`bytes_load32` and `setMem_store` state the trace's four bytes as the model's `load32` and
`store32`.  The backward direction gives the declared variables their values through `m7_auto`.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode Val Sys bytes writeBytes Opaque)

/-- The footprint of `LDR.W Rt, [Rn, #imm12]` in DTCM. -/
def ldrDtcmT : Footprint := isla_trace% "tests/isla/m7/ldr-dtcm"

/-- The fields of a load or store for the registers `t` and `n` and the immediate `imm`. -/
def memFields (t n : Fin 8) (imm : Fin 4096) : Fields :=
  [("Rn", n.val), ("Rt", t.val), ("imm12", imm.val)]

/-! The address translation. -/

/-- The table's address that the walk computes from `_TTBR0_EL1` and `TTBR0_NS`. -/
theorem ttbr_base (t : Nat) :
    (t / 18446744073709551616 % 18446744073709551616 * 18446744073709551616 + 4294967296) / 2 %
      140737488355328 * 2 % 72057594037927936 = 4294967296 := by
  generalize t / 18446744073709551616 % 18446744073709551616 = a
  omega

/-! The bytes of a word. -/

theorem or_shift {x y k : Nat} (hx : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

theorem toNat_load32 (mem : UInt32 → UInt8) (a : UInt32) :
    (load32 mem a).toNat = (mem a).toNat + (mem (a + 1)).toNat * 256 +
      (mem (a + 2)).toNat * 65536 + (mem (a + 3)).toNat * 16777216 := by
  have h0 := (mem a).toNat_lt
  have h1 := (mem (a + 1)).toNat_lt
  have h2 := (mem (a + 2)).toNat_lt
  have h3 := (mem (a + 3)).toNat_lt
  unfold load32
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt32.toNat_shiftLeft, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
    UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, show (8 : UInt32).toNat = 8 from rfl,
    show (16 : UInt32).toNat = 16 from rfl, show (24 : UInt32).toNat = 24 from rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod] at *
  rw [Nat.mod_eq_of_lt (show (mem (a + 1)).toNat * 256 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show (mem (a + 2)).toNat * 65536 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show (mem (a + 3)).toNat * 16777216 < 4294967296 by omega),
    show (256 : Nat) = 2 ^ 8 from rfl, or_shift (by omega),
    show (65536 : Nat) = 2 ^ 16 from rfl, or_shift (by omega),
    show (16777216 : Nat) = 2 ^ 24 from rfl, or_shift (by omega)]

/-- A byte of the machine's memory below 2^32 is the model's. -/
theorem mem_lo (m : Mach) (a c : UInt32) {i : Nat} (hc : c.toNat = i)
    (h : a.toNat + i < 4294967296) :
    m.mem (UInt64.ofNat (a.toNat + i)) = m.s.mem (a + c) := by
  unfold Mach.mem
  rw [ite_eq_left (by rw [UInt64.toNat_ofNat']; simp only [Nat.reducePow]; omega)]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat', UInt32.toNat_add, hc]
  simp only [Nat.reducePow]
  omega

theorem ofNat_succ64 (x : Nat) : UInt64.ofNat x + 1 = UInt64.ofNat (x + 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    show (1 : UInt64).toNat = 1 from rfl]
  simp only [Nat.reducePow]
  omega

/-- The four bytes of a word access below 2^32, as the trace reads them, are the model's word. -/
theorem bytes_load32 (m : Mach) (a : UInt32) (h : a.toNat + 4 ≤ 4294967296) :
    bytes m.mem (UInt64.ofNat a.toNat) 4 = (load32 m.s.mem a).toNat := by
  rw [toNat_load32]
  simp only [LeanExe.A64.Isla.bytes, ofNat_succ64, Nat.mul_zero, LeanExe.A64.Isla.nat_add_zero]
  rw [show UInt64.ofNat a.toNat = UInt64.ofNat (a.toNat + 0) from rfl,
    mem_lo m a 0 (i := 0) rfl (by omega), mem_lo m a 1 (i := 1) rfl (by omega),
    mem_lo m a 2 (i := 2) rfl (by omega), mem_lo m a 3 (i := 3) rfl (by omega), UInt32.add_zero]
  omega

/-- The bytes of a descriptor from 2^32 are those of `far`. -/
theorem bytes_far (m : Mach) {y : Nat} (h : 4294967296 ≤ y)
    (h2 : y + 8 ≤ 18446744073709551616) :
    bytes m.mem (UInt64.ofNat y) 8 = bytes m.far (UInt64.ofNat y) 8 := by
  apply LeanExe.A64.Isla.bytes_congr
  intro i hi
  unfold Mach.mem
  rw [ite_eq_right]
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-! The bytes of a word store. -/

/-- A byte of `writeBytes`: byte `c - a` of `x` inside the `k` bytes from `a`, and `f` elsewhere. -/
theorem writeBytes_apply : ∀ (k : Nat) (f : UInt64 → UInt8) (a : UInt64) (x : Nat) (c : UInt64),
    a.toNat + k < 18446744073709551616 →
    writeBytes f a x k c =
      if a.toNat ≤ c.toNat ∧ c.toNat < a.toNat + k then
        UInt8.ofNat (x / 256 ^ (c.toNat - a.toNat) % 256)
      else f c
  | 0, f, a, x, c, _ => by
    simp only [writeBytes, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | k + 1, f, a, x, c, h => by
    have ha : (a + 1).toNat = a.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      simp only [Nat.reducePow]
      omega
    simp only [writeBytes]
    rw [writeBytes_apply k _ (a + 1) (x / 256) c (by omega), ha]
    by_cases hc : c = a
    · subst hc
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by omega), Nat.sub_self, Nat.pow_zero, Nat.div_one]
    · have hne : c.toNat ≠ a.toNat := fun e => hc (UInt64.toNat_inj.mp e)
      by_cases hin : a.toNat + 1 ≤ c.toNat ∧ c.toNat < a.toNat + 1 + k
      · rw [ite_eq_left hin, ite_eq_left (by omega), Nat.div_div_eq_div_mul,
          show 256 * 256 ^ (c.toNat - (a.toNat + 1)) = 256 ^ (c.toNat - a.toNat) by
            rw [← Nat.pow_succ']
            congr 1
            omega]
      · rw [ite_eq_right hin, ite_eq_right hc, ite_eq_right (by omega)]

/-- A byte of `store32` inside the word. -/
theorem store32_apply (mem : UInt32 → UInt8) (a v b : UInt32) :
    store32 mem a v b =
      if (b - a).toNat < 4 then UInt8.ofNat (v.toNat / 256 ^ (b - a).toNat % 256) else mem b := by
  unfold store32
  by_cases h : (b - a).toNat < 4
  · rw [ite_eq_left (show b - a < 4 from UInt32.lt_iff_toNat_lt.mpr h), ite_eq_left h]
    apply UInt8.toNat_inj.mp
    rw [UInt32.toNat_toUInt8, UInt8.toNat_ofNat', UInt32.toNat_shiftRight, UInt32.toNat_mul,
      show (8 : UInt32).toNat = 8 from rfl, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]
    rw [show (b - a).toNat * 8 % 4294967296 % 32 = 8 * (b - a).toNat by omega, Nat.pow_mul]
    simp only [Nat.reducePow, Nat.mod_mod]
  · rw [ite_eq_right (fun e => h (UInt32.lt_iff_toNat_lt.mp e)), ite_eq_right h]

/-- The machine after the trace's store of the word `v` at an address of the model's memory is the
machine with the model's `store32`. -/
theorem setMem_store (m : Mach) (a v : UInt32) (h : a.toNat + 4 ≤ 4294967296) :
    m.setMem (writeBytes m.mem (UInt64.ofNat a.toNat) v.toNat 4) =
      { m with s := { m.s with mem := store32 m.s.mem a v } } := by
  have hA : (UInt64.ofNat a.toNat).toNat = a.toNat := by
    rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hs : (fun b : UInt32 => writeBytes m.mem (UInt64.ofNat a.toNat) v.toNat 4 b.toUInt64) =
      store32 m.s.mem a v := by
    funext b
    have hb := b.toNat_lt
    rw [writeBytes_apply 4 _ _ _ _ (by omega), hA, store32_apply, UInt32.toNat_toUInt64,
      UInt32.toNat_sub]
    simp only [Nat.reducePow]
    by_cases hin : a.toNat ≤ b.toNat ∧ b.toNat < a.toNat + 4
    · rw [ite_eq_left hin, show (4294967296 - a.toNat + b.toNat) % 4294967296 = b.toNat - a.toNat by
        omega, ite_eq_left (by omega)]
    · rw [ite_eq_right hin, ite_eq_right (show ¬ (4294967296 - a.toNat + b.toNat) % 4294967296 < 4 by omega)]
      unfold Mach.mem
      rw [ite_eq_left (by rw [UInt32.toNat_toUInt64]; omega)]
      congr 1
      apply UInt32.toNat_inj.mp
      rw [UInt64.toNat_toUInt32, UInt32.toNat_toUInt64]
      simp only [Nat.reducePow]
      omega
  have hf : (fun c : UInt64 => if c.toNat < 4294967296 then m.far c else
      writeBytes m.mem (UInt64.ofNat a.toNat) v.toNat 4 c) = m.far := by
    funext c
    split
    · rfl
    · rename_i hc
      rw [writeBytes_apply 4 _ _ _ _ (by omega), hA, ite_eq_right (by omega)]
      unfold Mach.mem
      rw [ite_eq_right hc]
  unfold Mach.setMem
  simp only [hs, hf]

/-! The model's side. -/

theorem loadWord_cases {P : Platform} {δ : Nat → UInt32} {s : State} {a : UInt32}
    {r : UInt32 × State} (h : loadWord P δ s a = some r) :
    (P.device a = true ∧
        r = (δ s.reads,
          { s with trace := s.trace ++ [.read a (δ s.reads)], reads := s.reads + 1 })) ∨
      (P.device a = false ∧ r = (load32 s.mem a, s)) := by
  unfold loadWord at h
  split at h
  · cases h
  · split at h
    · rename_i hd
      exact .inl ⟨hd, (Option.some.inj h).symm⟩
    · rename_i hd
      split at h
      · exact .inr ⟨by simpa using hd, (Option.some.inj h).symm⟩
      · cases h

theorem toNat_lt32 (a : UInt32) : a.toNat < 4294967296 := a.toNat_lt

/-- `device` of an address below 2^32 is the platform's. -/
theorem device_toNat (P : Platform) (a : UInt32) : device P a.toNat 4 = P.device a := by
  unfold device
  simp only [beq_self_eq_true, Bool.true_and, toNat_lt32, decide_true, ofNat_toNat32]

theorem devRead_pc (m : Mach) (a v : UInt32) : (devRead m a v).s.pc = m.s.pc := rfl

theorem devRead_x (m : Mach) (a v : UInt32) (i : Nat) : (devRead m a v).x i = m.x i := by
  cases m
  rfl

/-- The write of a register that keeps bits 63 to 32 after a device read, whose trace reads the
register's value from the machine before the read. -/
theorem setX_keep_dev (m : Mach) (a w : UInt32) {i : Nat} (h : i < 15) {v : Nat}
    (hv : v < 4294967296) :
    (devRead m a w).setX i (m.x i &&& 18446744069414584320 ||| v) =
      { devRead m a w with s := setLow (devRead m a w).s i (.ofNat v) } := by
  have := setX_keep (devRead m a w) h hv
  rwa [devRead_x] at this

/-- Proves that the outcome at the end of a path of a word load is `exec`'s. -/
macro "ld_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  rw [ite_eq_left]
  rotate_left
  · simp only [setX_pc, devRead_pc]
    omega
  simp only [Outcome.done.injEq, and_true]
  simp (disch := first | omega | exact toNat_lt32 _) only [setX_low, setX_keep]
  apply exists_mach
  · simp only [setLow_r]
    apply state_eq
    exact ofNat_toNat32 _
  · rfl
  · rfl))

/-- Two machines that differ only in their model states are equal when the states are. -/
theorem mach_with_s {m : Mach} {a b : State} (h : a = b) :
    ({ m with s := a } : Mach) = { m with s := b } := by
  rw [h]

/-- The backward counterpart of `ld_end`, for the path that keeps bits 63 to 32. -/
macro "ld_bwd_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  rw [ite_eq_left]
  rotate_left
  · simp only [setX_pc, devRead_pc]
    omega
  simp only [Outcome.done.injEq, and_true]
  simp (disch := first | omega | exact toNat_lt32 _) only [setX_keep, setX_keep_dev]
  apply mach_with_s
  simp only [setLow_r]
  apply Eq.symm
  apply state_eq
  exact ofNat_toNat32 _))

/-- Proves a side condition of a walk of a load or store. -/
macro "m7_side" : tactic => `(tactic| first
  | t32_side
  | exact toNat_lt32 _
  | exact BitVec.isLt _
  | (apply Nat.lt_of_lt_of_le (toNat_lt32 _); decide)
  | (apply Nat.lt_of_lt_of_le (BitVec.isLt _); decide))

/-! The walk of a load or store. -/

/-- The lemmas of the walk of a load or store, with the lemmas in brackets. -/
syntax "mem_walk_fwd " ident " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mem_walk_fwd $h with [$xs,*]) => `(tactic|
    m7_fwd $h using mem_omega with [Bool.and_eq_true, chain8_eq, device_eight,
      LeanExe.A64.Isla.sdiv_128, LeanExe.A64.Isla.and_ffffffff00000000, LeanExe.A64.Isla.and_hi64,
      LeanExe.A64.Isla.or_lo64, LeanExe.A64.Isla.and_c0_low, LeanExe.A64.Isla.and_c0,
      LeanExe.A64.Isla.and_3fffffff, LeanExe.A64.Isla.pa0_eq, LeanExe.A64.Isla.pa_eq,
      LeanExe.A64.Isla.or_40000000, LeanExe.A64.Isla.or_lt32, and_fffff000000000, ttbr_base,
      Nat.or_zero, ofNat_toNat32, $xs,*])

/-- The backward counterpart of `mem_walk_fwd`. -/
syntax "mem_walk_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mem_walk_bwd [$xs,*]) => `(tactic|
    m7_auto using mem_omega with [Bool.and_eq_true, chain8_eq, chain23_eq, devRead_x, device_eight,
      LeanExe.A64.Isla.sdiv_128, LeanExe.A64.Isla.and_ffffffff00000000, LeanExe.A64.Isla.and_hi64,
      LeanExe.A64.Isla.or_lo64, LeanExe.A64.Isla.and_c0_low, LeanExe.A64.Isla.and_c0,
      LeanExe.A64.Isla.and_3fffffff, LeanExe.A64.Isla.pa0_eq, LeanExe.A64.Isla.pa_eq,
      LeanExe.A64.Isla.or_40000000, LeanExe.A64.Isla.or_lt32, and_fffff000000000, ttbr_base,
      Nat.or_zero, ofNat_toNat32, $xs,*])

theorem storeWord_cases {P : Platform} {s : State} {a v : UInt32} {r : State}
    (h : storeWord P s a v = some r) :
    (P.device a = true ∧ r = { s with trace := s.trace ++ [.write a v] }) ∨
      (P.device a = false ∧ r = { s with mem := store32 s.mem a v }) := by
  unfold storeWord at h
  split at h
  · cases h
  · split at h
    · rename_i hd
      exact .inl ⟨hd, (Option.some.inj h).symm⟩
    · rename_i hd
      split at h
      · exact .inr ⟨by simpa using hd, (Option.some.inj h).symm⟩
      · cases h

theorem low_sp (s : State) : low s 13 = s.sp := by
  unfold low
  simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte]

theorem low_lr (s : State) : low s 14 = s.lr := by
  unfold low
  simp only [Nat.reduceLT, ↓reduceDIte, Nat.reduceEqDiff, ↓reduceIte]

theorem ofNat_four' : UInt32.ofNat 4 = 4 := rfl

/-- Proves that the outcome at the end of a path of `LDR.W LR` is `exec`'s. -/
macro "ldlr_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  rw [ite_eq_left]
  rotate_left
  · simp only [setX_pc, devRead_pc]
    omega
  simp only [Outcome.done.injEq, and_true]
  simp (disch := first | omega | exact toNat_lt32 _) only [setX_low, setX_keep]
  apply exists_mach
  · simp only [setLow, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ↓reduceDIte, ofNat_toNat32,
      ofNat_four', devRead]
  · rfl
  · rfl))

/-- The backward counterpart of `ldlr_end`. -/
macro "ldlr_bwd_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  rw [ite_eq_left]
  rotate_left
  · simp only [setX_pc, devRead_pc]
    omega
  simp only [Outcome.done.injEq, and_true]
  simp (disch := first | omega | exact toNat_lt32 _) only [setX_keep, setX_keep_dev]
  apply mach_with_s
  simp only [setLow, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, ↓reduceDIte, ofNat_toNat32,
    ofNat_four', devRead]))

/-- Proves that the outcome at the end of a path of a word store is `exec`'s. -/
macro "st_end" : tactic => `(tactic| (
  simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
  rw [ite_eq_left]
  rotate_left
  · first | omega | (simp only; omega)
  simp only [Outcome.done.injEq, and_true, ofNat_four']
  try (first | exact ⟨_, rfl⟩ | rfl)))

/-- The footprint of `LDR.W Rt, [Rn, #imm12]` with the access in the device window. -/
def ldrDevT : Footprint := isla_trace% "tests/isla/m7/ldr-dev"

/-- The footprint of `STR.W Rt, [Rn, #imm12]` in DTCM. -/
def strDtcmT : Footprint := isla_trace% "tests/isla/m7/str-dtcm"

/-- The footprint of `STR.W Rt, [Rn, #imm12]` with the access in the device window. -/
def strDevT : Footprint := isla_trace% "tests/isla/m7/str-dev"

/-- The footprint of `LDR.W Rt, [SP, #imm12]` in DTCM. -/
def ldrSpT : Footprint := isla_trace% "tests/isla/m7/ldr-sp"

/-- The footprint of `STR.W Rt, [SP, #imm12]` in DTCM. -/
def strSpT : Footprint := isla_trace% "tests/isla/m7/str-sp"

/-- The footprint of `LDR.W LR, [SP, #imm12]` in DTCM. -/
def ldrLrT : Footprint := isla_trace% "tests/isla/m7/ldr-lr"

/-- The footprint of `STR.W LR, [SP, #imm12]` in DTCM. -/
def strLrT : Footprint := isla_trace% "tests/isla/m7/str-lr"

/-- The fields of a load or store at SP for the register `t` and the immediate `imm`. -/
def spFields (t : Fin 8) (imm : Fin 4096) : Fields := [("Rt", t.val), ("imm12", imm.val)]

/-- The fields of a load or store of LR at SP for the immediate `imm`. -/
def lrFields (imm : Fin 4096) : Fields := [("imm12", imm.val)]

set_option Elab.async false

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `LDR.W Rt, [Rn, #imm12]` with the access in DTCM agrees with `exec`. -/
theorem ldrDtcm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t n : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.r n + UInt32.ofNat imm.val).toNat ∧
      (m.s.r n + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hal : (m.s.r n + UInt32.ofNat imm.val).toNat % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] ldrDtcmT (memFields t n imm)
      (.ldr t n imm) m := by
  have hr := (m.s.r n).toNat_lt
  have hA : (m.s.r n + UInt32.ofNat imm.val).toNat = (m.s.r n).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hX : m.x n.val % 4294967296 = (m.s.r n).toNat := by
    rw [x_mod m (k := n.val) (by omega), low_r]
  have haddr :
      ((m.s.r n).toNat + imm.val) % 4294967296 = (m.s.r n + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show ldrDtcmT.opcode =
          [.bits 13 0b1111100011010, .field "Rn" 3, .bits 1 0, .field "Rt" 3,
           .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, memFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8D0 + n.val) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [ldrDtcmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2963), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [ldrDtcmT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, haddr, hdev]
          all_goals ld_end
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.r n + UInt32.ofNat imm.val) (by omega)
          mem_walk_fwd h with [hσ, hX, haddr, hdev, hb]
          all_goals ld_end
      · unfold footRun
        simp only [ldrDtcmT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.r n + UInt32.ofNat imm.val) (by omega)
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hb, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `LDR.W Rt, [Rn, #imm12]` with the access in the device window agrees with
`exec`. -/
theorem ldrDev_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t n : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 1073741824 ≤ (m.s.r n + UInt32.ofNat imm.val).toNat ∧
      (m.s.r n + UInt32.ofNat imm.val).toNat ≤ 1074003964)
    (hal : (m.s.r n + UInt32.ofNat imm.val).toNat % 4 = 0)
    (hd : bytes m.far 4294967304 8 = 27021598837965889) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] ldrDevT (memFields t n imm)
      (.ldr t n imm) m := by
  have hr := (m.s.r n).toNat_lt
  have hA : (m.s.r n + UInt32.ofNat imm.val).toNat = (m.s.r n).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hX : m.x n.val % 4294967296 = (m.s.r n).toNat := by
    rw [x_mod m (k := n.val) (by omega), low_r]
  have haddr :
      ((m.s.r n).toNat + imm.val) % 4294967296 = (m.s.r n + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967304) 8 = 27021598837965889 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show ldrDevT.opcode =
          [.bits 13 0b1111100011010, .field "Rn" 3, .bits 1 0, .field "Rt" 3,
           .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, memFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8D0 + n.val) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [ldrDevT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2963), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [ldrDevT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, haddr, hdev]
          all_goals ld_end
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.r n + UInt32.ofNat imm.val) (by omega)
          mem_walk_fwd h with [hσ, hX, haddr, hdev, hb]
          all_goals ld_end
      · unfold footRun
        simp only [ldrDevT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.r n + UInt32.ofNat imm.val) (by omega)
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hb, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `STR.W Rt, [Rn, #imm12]` with the access in DTCM agrees with `exec`. -/
theorem strDtcm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t n : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.r n + UInt32.ofNat imm.val).toNat ∧
      (m.s.r n + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hal : (m.s.r n + UInt32.ofNat imm.val).toNat % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] strDtcmT (memFields t n imm)
      (.str t n imm) m := by
  have hr := (m.s.r n).toNat_lt
  have hA : (m.s.r n + UInt32.ofNat imm.val).toNat = (m.s.r n).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hX : m.x n.val % 4294967296 = (m.s.r n).toNat := by
    rw [x_mod m (k := n.val) (by omega), low_r]
  have hY : m.x t.val % 4294967296 = (m.s.r t).toNat := by
    rw [x_mod m (k := t.val) (by omega), low_r]
  have haddr :
      ((m.s.r n).toNat + imm.val) % 4294967296 = (m.s.r n + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show strDtcmT.opcode =
          [.bits 13 0b1111100011000, .field "Rn" 3, .bits 1 0, .field "Rt" 3,
           .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, memFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8C0 + n.val) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [strDtcmT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 3227), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [strDtcmT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, store]
          all_goals st_end
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.r n + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, hb, store]
          all_goals st_end
      · unfold footRun
        simp only [strDtcmT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, store, hdesc]
          all_goals first
            | st_end
            | m7_side
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.r n + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, hb, store, hdesc]
          all_goals first
            | st_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `STR.W Rt, [Rn, #imm12]` with the access in the device window agrees with
`exec`. -/
theorem strDev_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t n : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 1073741824 ≤ (m.s.r n + UInt32.ofNat imm.val).toNat ∧
      (m.s.r n + UInt32.ofNat imm.val).toNat ≤ 1074003964)
    (hal : (m.s.r n + UInt32.ofNat imm.val).toNat % 4 = 0)
    (hd : bytes m.far 4294967304 8 = 27021598837965889) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] strDevT (memFields t n imm)
      (.str t n imm) m := by
  have hr := (m.s.r n).toNat_lt
  have hA : (m.s.r n + UInt32.ofNat imm.val).toNat = (m.s.r n).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hX : m.x n.val % 4294967296 = (m.s.r n).toNat := by
    rw [x_mod m (k := n.val) (by omega), low_r]
  have hY : m.x t.val % 4294967296 = (m.s.r t).toNat := by
    rw [x_mod m (k := t.val) (by omega), low_r]
  have haddr :
      ((m.s.r n).toNat + imm.val) % 4294967296 = (m.s.r n + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967304) 8 = 27021598837965889 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show strDevT.opcode =
          [.bits 13 0b1111100011000, .field "Rn" 3, .bits 1 0, .field "Rt" 3,
           .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, memFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8C0 + n.val) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [strDevT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 3227), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [strDevT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, store]
          all_goals st_end
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.r n + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, hb, store]
          all_goals st_end
      · unfold footRun
        simp only [strDevT, LeanExe.A64.Isla.Footprint.vars, memFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, store, hdesc]
          all_goals first
            | st_end
            | m7_side
        · have hdev : device P (m.s.r n + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.r n + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, hb, store, hdesc]
          all_goals first
            | st_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `LDR.W Rt, [SP, #imm12]` agrees with `exec` for an access in DTCM. -/
theorem ldrSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.sp + UInt32.ofNat imm.val).toNat ∧
      (m.s.sp + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hsp : m.s.sp.toNat % 4 = 0) (himm : imm.val % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] ldrSpT (spFields t imm)
      (.ldrSp t imm) m := by
  have hr := (m.s.sp).toNat_lt
  have hA : (m.s.sp + UInt32.ofNat imm.val).toNat = (m.s.sp).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hal : (m.s.sp + UInt32.ofNat imm.val).toNat % 4 = 0 := by omega
  have hX : m.x 13 % 4294967296 = (m.s.sp).toNat := by
    rw [x_mod m (k := 13) (by omega), low_sp]
  have haddr :
      ((m.s.sp).toNat + imm.val) % 4294967296 = (m.s.sp + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show ldrSpT.opcode =
          [.bits 17 0b11111000110111010, .field "Rt" 3, .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, spFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8DD) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [ldrSpT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2963), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [ldrSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, haddr, hdev]
          all_goals ld_end
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.sp + UInt32.ofNat imm.val) (by omega)
          mem_walk_fwd h with [hσ, hX, haddr, hdev, hb]
          all_goals ld_end
      · unfold footRun
        simp only [ldrSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.sp + UInt32.ofNat imm.val) (by omega)
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hb, hdesc]
          all_goals first
            | ld_bwd_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `STR.W Rt, [SP, #imm12]` agrees with `exec` for an access in DTCM. -/
theorem strSp_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (t : Fin 8) (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.sp + UInt32.ofNat imm.val).toNat ∧
      (m.s.sp + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hsp : m.s.sp.toNat % 4 = 0) (himm : imm.val % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] strSpT (spFields t imm)
      (.strSp t imm) m := by
  have hr := (m.s.sp).toNat_lt
  have hA : (m.s.sp + UInt32.ofNat imm.val).toNat = (m.s.sp).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hal : (m.s.sp + UInt32.ofNat imm.val).toNat % 4 = 0 := by omega
  have hX : m.x 13 % 4294967296 = (m.s.sp).toNat := by
    rw [x_mod m (k := 13) (by omega), low_sp]
  have hY : m.x t.val % 4294967296 = (m.s.r t).toNat := by
    rw [x_mod m (k := t.val) (by omega), low_r]
  have haddr :
      ((m.s.sp).toNat + imm.val) % 4294967296 = (m.s.sp + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show strSpT.opcode =
          [.bits 17 0b11111000110011010, .field "Rt" 3, .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, spFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8CD) * 65536 + (t.val * 4096 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [strSpT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 3227), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [strSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, store]
          all_goals st_end
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.sp + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, hb, store]
          all_goals st_end
      · unfold footRun
        simp only [strSpT, LeanExe.A64.Isla.Footprint.vars, spFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, store, hdesc]
          all_goals first
            | st_end
            | m7_side
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.sp + UInt32.ofNat imm.val) (m.s.r t) (by omega)
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, hb, store, hdesc]
          all_goals first
            | st_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `LDR.W LR, [SP, #imm12]` agrees with `exec` for an access in DTCM. -/
theorem ldrLr_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.sp + UInt32.ofNat imm.val).toNat ∧
      (m.s.sp + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hsp : m.s.sp.toNat % 4 = 0) (himm : imm.val % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] ldrLrT (lrFields imm)
      (.ldrLr imm) m := by
  have hr := (m.s.sp).toNat_lt
  have hA : (m.s.sp + UInt32.ofNat imm.val).toNat = (m.s.sp).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hal : (m.s.sp + UInt32.ofNat imm.val).toNat % 4 = 0 := by omega
  have hX : m.x 13 % 4294967296 = (m.s.sp).toNat := by
    rw [x_mod m (k := 13) (by omega), low_sp]
  have haddr :
      ((m.s.sp).toNat + imm.val) % 4294967296 = (m.s.sp + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show ldrLrT.opcode =
          [.bits 20 0b11111000110111011110, .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lrFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8DD) * 65536 + (0xE000 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [ldrLrT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 2963), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [ldrLrT, LeanExe.A64.Isla.Footprint.vars, lrFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, haddr, hdev]
          all_goals ldlr_end
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.sp + UInt32.ofNat imm.val) (by omega)
          mem_walk_fwd h with [hσ, hX, haddr, hdev, hb]
          all_goals ldlr_end
      · unfold footRun
        simp only [ldrLrT, LeanExe.A64.Isla.Footprint.vars, lrFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases loadWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> simp only at hs <;>
          subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hdesc]
          all_goals first
            | ldlr_bwd_end
            | m7_side
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := bytes_load32 m (m.s.sp + UInt32.ofNat imm.val) (by omega)
          mem_walk_bwd [hσ, hX, haddr, hdev, devRead_x, hb, hdesc]
          all_goals first
            | ldlr_bwd_end
            | m7_side

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- The trace of `STR.W LR, [SP, #imm12]` agrees with `exec` for an access in DTCM. -/
theorem strLr_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown)
    (imm : Fin 4096) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296)
    (ha : 536870912 ≤ (m.s.sp + UInt32.ofNat imm.val).toNat ∧
      (m.s.sp + UInt32.ofNat imm.val).toNat ≤ 537001980)
    (hsp : m.s.sp.toNat % 4 = 0) (himm : imm.val % 4 = 0)
    (hd : bytes m.far 4294967296 8 = 1861) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] strLrT (lrFields imm)
      (.strLr imm) m := by
  have hr := (m.s.sp).toNat_lt
  have hA : (m.s.sp + UInt32.ofNat imm.val).toNat = (m.s.sp).toNat + imm.val := by
    have := ha.1
    rw [UInt32.toNat_add, UInt32.toNat_ofNat'] at this ⊢
    simp only [Nat.reducePow] at this ⊢
    omega
  have hal : (m.s.sp + UInt32.ofNat imm.val).toNat % 4 = 0 := by omega
  have hX : m.x 13 % 4294967296 = (m.s.sp).toNat := by
    rw [x_mod m (k := 13) (by omega), low_sp]
  have hY : m.x 14 % 4294967296 = (m.s.lr).toNat := by
    rw [x_mod m (k := 14) (by omega), low_lr]
  have haddr :
      ((m.s.sp).toNat + imm.val) % 4294967296 = (m.s.sp + UInt32.ofNat imm.val).toNat := by omega
  have hdesc : bytes m.mem (UInt64.ofNat 4294967296) 8 = 1861 := by
    rw [bytes_far m (by omega) (by omega)]
    exact hd
  have hT := u.ttbr0el1.isLt
  have hpc32 := m.s.pc.toNat_lt
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · rw [show strLrT.opcode =
          [.bits 20 0b11111000110011011110, .field "imm12" 12] from rfl]
      apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, lrFields, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      show _ = (0xF8CD) * 65536 + (0xE000 + imm.val)
      omega
    · simp only [exec, Option.map_eq_some_iff] at hs
      obtain ⟨r, hl, hs⟩ := hs
      t32_reads [strLrT, sys_get, sys] at hσ
      refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set
        "SEE" (.bits 128 3227), fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [strLrT, LeanExe.A64.Isla.Footprint.vars, lrFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv] at h
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, store]
          all_goals st_end
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.sp + UInt32.ofNat imm.val) (m.s.lr) (by omega)
          mem_walk_fwd h with [hσ, hX, hY, haddr, hdev, hb, store]
          all_goals st_end
      · unfold footRun
        simp only [strLrT, LeanExe.A64.Isla.Footprint.vars, lrFields, List.foldl,
          List.lookup, String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width,
          Nat.reduceAdd, Nat.reduceDiv]
        rcases storeWord_cases hl with ⟨hdv, rfl⟩ | ⟨hdv, rfl⟩ <;> subst hs
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = true := by
            rw [device_toNat, hdv]
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, store, hdesc]
          all_goals first
            | st_end
            | m7_side
        · have hdev : device P (m.s.sp + UInt32.ofNat imm.val).toNat 4 = false := by
            rw [device_toNat, hdv]
          have hb := setMem_store m (m.s.sp + UInt32.ofNat imm.val) (m.s.lr) (by omega)
          mem_walk_bwd [hσ, hX, hY, haddr, hdev, devRead_x, hb, store, hdesc]
          all_goals first
            | st_end
            | m7_side

#print axioms ldrDtcm_agrees
#print axioms ldrDev_agrees
#print axioms strDtcm_agrees
#print axioms strDev_agrees
#print axioms ldrSp_agrees
#print axioms strSp_agrees
#print axioms ldrLr_agrees
#print axioms strLr_agrees

end TestSupport.M7.Isla
