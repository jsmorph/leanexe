import LeanExe.A64.Isla.Float
import LeanExe.A64.Isla.Linux
import LeanExe.A64.Linux

/-!
Theorems of the traces of `SVC #0` of a Linux process at EL0, `tests/isla/linux-vhe/svc` under the
host's kernel at EL2 with FEAT_VHE and `tests/isla/linux-el1/svc` under a kernel at EL1 under KVM
on a host with VHE, which `tests/isla/linux-traces.sh` computes.  The program's decoder reads
`svcWord`, the word of `SVC #0`, as no instruction, and `pstep` of `LeanExe/A64/Linux.lean` runs it
by `Kernel.svc`, so the theorems state the exception's entry in place of `Agrees`.  `SvcAgrees`
states that the footprint's opcode is `svcWord` and that, for every `σ` that agrees with the
profile on the registers that the trace reads and holds the profile's `PSTATE`, the trace has a
path that ends, and every path ends in the model's state with the program counter at the vector
and registers `σ'` that `SvcEntry` describes and that differ from `σ` only at `W`.  `SvcEntry`
holds the return address `s.pc + 4` in `ELR_ELx`, the syndrome of `SVC #0` from AArch64,
0x56000000 (EC 0x15, IL 1, and ISS 0), in `ESR_ELx`, the flags of `s` in bits 31 to 28 of
`SPSR_ELx` and EL0 with `SP_EL0`, 0b00000, in its bits 4 to 0, and `PSTATE` at the kernel's level
with `SP_ELx` selected and D, A, I, and F set.  The model's state keeps every general register,
`SP_EL0`, the flags, the low 64 bits of each SIMD register, memory, and the output.

`svc_vhe` and `svc_el1` hold for every `u` with `u.Holds`, Linux's values of the bits that the
reset constraints fix, for every value of the bits that the traces test and no constraint fixes,
and for every `VBAR_ELx` whose bits 63 to 55 are set.  Linux 7.0 sets `VBAR_EL1` to `vectors` in
`__primary_switched` and `__secondary_switched` of `arch/arm64/kernel/head.S` and later to a copy
of the vectors that hardens the branch predictor (`arch/arm64/kernel/proton-pack.c` lines 1000 to
1015), `finalise_el2` moves the host's value into `VBAR_EL2` (`arch/arm64/kernel/hyp-stub.S` lines
117 to 118), and KVM restores it on each return to the host (`arch/arm64/kvm/hyp/vhe/switch.c`
lines 186 to 188).  Each of these tables lies in the kernel's image, at an address of the upper
half of the address space whose bits 63 to 55 are set.  The vector of a synchronous exception
from a lower level that uses AArch64 is `VBAR_ELx` with 0x400 in bits 10 to 0, `lowerSync`.
`AArch64.BranchAddr` sign-extends it from bit 55 when TBI1 of `TCR_ELx` is set and TBID1 clear,
which changes no bit under the premise, and the paths on which bit 55 of the vector is clear
contradict the premise.  Exception entry writes fields of `PSTATE`, and the
semantics writes a field by updating the struct that `σ` holds, so the theorems assume `σ`'s
`PSTATE` as a whole, the struct of `linux u`, beside the fields that the trace reads.

The traces leave `MaybeZeroSVEUppers` abstract with `--abstract`: each records one
`abstract-call` with the target level as argument and the unit result, and the theorems assume
that `A` gives the call the unit value, `.bits 0 0`, that is, that the call returns.  Isla records
the call in place of running the function, so the trace holds none of its reads, writes,
choices, assertions, and exceptions, and by reading 11 of `LeanExe/A64/Isla/Trace.lean` the
theorems cover them through the following reading of Arm's pseudocode, as the Sail model gives it
(`MaybeZeroSVEUppers`, `armv9p4.ir` lines 65005 to 65474, `v8_base.sail` lines 9423 to 9485).
The function computes the current vector lengths and returns without a write unless the target
level lies above `PSTATE.EL` and SVE is enabled at the target level.  Otherwise, when floating
point is enabled at EL0, the level that it tests under both kernels, a CONSTRAINED UNPREDICTABLE
choice for each of Z0 to Z31, P0 to P15, and FFR keeps the register or clears its bits from the
vector length upward, or from an eighth of it for P0 to P15 and FFR, where the vector length is
the current one when SVE is enabled at `PSTATE.EL` and 128 bits otherwise.  On a processor with
FEAT_SME and with `PSTATE.ZA` set, further choices clear rows of ZA.  The function reads system
registers, `PSTATE.EL` and `PSTATE.ZA`, and the registers that it may clear, and it writes no
other register.  Its assertions and those of the functions that it calls, among them that EL2 or
EL1 uses AArch64 and that each vector length lies between 128 and 2048 bits, hold under the
profile `kvm`, whose processor implements EL3, AArch32 at no level above EL0, and no RME, so the
call returns.  Every vector length is at least 128 bits, so the function changes no bit of Z0 to
Z31 below bit 128, and the model's state, which holds the low 64 bits of each, is exact.  On the
processor, the registers after the instruction are `σ'` except for the bits of Z0 to Z31 from bit
128 upward, which `σ` holds in `_Z`'s upper part, P0 to P15, and FFR, which the function may
clear.  The traces take the features of the KVM guest, which lack the host's FEAT_SPE, with which
exception entry also updates the sampling state of the Statistical Profiling Extension.

The proofs walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean`.  The forward lemma
takes every path to its end, and `svc_end` proves the parts of `SvcEntry` that the evaluation
leaves or refutes the path from its conditions and the premise on `VBAR_ELx`.  `nzcv_ao` and
`nzcv_a` follow the flags through the masks and ORs with which exception entry builds `SPSR_ELx`,
and `low_and` and `low_or` show its bits 4 to 0 clear.  The backward lemma builds one path after
a case split on the bits that the trace tests and the premise leaves open: `IESB` and `SPAN`,
bits 21 and 23 of `SCTLR_ELx`, TBI1 and TBID1, bits 38 and 52 of `TCR_ELx`, and, where `IESB` is
clear, `EA` and `NMEA`, bits 3 and 20 of `SCR_EL3`.  `tests/isla/theorems.sh` elaborates the
module and prints the axioms of its theorems.
-/

namespace TestSupport.A64.Isla

/- `LeanExe.A64.Linux`, which gives `svcWord`, imports the boot model, whose `Sys` would make the
name of the semantics' registers ambiguous. -/
open LeanExe.A64 hiding Sys
open LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's
walk. -/
set_option Elab.async false

attribute [local congr] run_congr runSome_congr

/-- The flags N, Z, C, and V of `s` as bits 3 to 0 of a number, in the form in which exception
entry builds them. -/
def nzcv (s : State) : Nat :=
  (if s.nFlag then 1 else 0) * 8 + ((if s.zFlag then 1 else 0) * 4 +
    ((if s.cFlag then 1 else 0) * 2 + if s.vFlag then 1 else 0))

theorem nzcv_lt (s : State) : nzcv s < 16 := by
  unfold nzcv
  split <;> split <;> split <;> split <;> omega

theorem nzcv_field (s : State) :
    nzcv s * 268435456 % 18446744073709551616 / 268435456 % 16 = nzcv s := by
  have := nzcv_lt s
  omega

/-- The address of the vector of a synchronous exception from a lower level that uses AArch64,
for the vector base `b`, whose bits 10 to 0 the architecture reserves. -/
def lowerSync (b : BitVec 64) : UInt64 := .ofNat (b.toNat / 2048 * 2048 + 1024)

/-- The registers `σ'` after `SVC #0` takes the exception from EL0 in the state `s` to the level
`el`, whose exception registers are `elr`, `esr`, and `spsr`: the return address `s.pc + 4`, the
syndrome of `SVC #0` from AArch64, the flags of `s` and EL0 with `SP_EL0` in the saved `PSTATE`,
and `PSTATE` at `el` with `SP_ELx` selected and D, A, I, and F set. -/
structure SvcEntry (el : Nat) (elr esr spsr : String) (s : State) (σ' : Sys) : Prop where
  elr : σ' elr = some (.bits 64 (s.pc + 4).toNat)
  esr : σ' esr = some (.struct [("bits", .bits 64 0x56000000)])
  spsr : ∃ m, σ' spsr = some (.struct [("bits", .bits 64 m)]) ∧
    m / 2 ^ 28 % 16 = nzcv s ∧ m % 32 = 0
  pstate : ∃ fs, σ' "PSTATE" = some (.struct fs) ∧ fs.lookup "EL" = some (.bits 2 el) ∧
    fs.lookup "SP" = some (.bits 1 1) ∧ fs.lookup "D" = some (.bits 1 1) ∧
    fs.lookup "A" = some (.bits 1 1) ∧ fs.lookup "I" = some (.bits 1 1) ∧
    fs.lookup "F" = some (.bits 1 1)

/-- The footprint `F` describes `SVC #0` from EL0 under the profile `π` and the meanings `A`: its
opcode is `svcWord`, and for every `σ` that agrees with `π` on the registers that the trace reads
and holds `π`'s `PSTATE`, the trace has a path that ends, and every path ends in the state `s` with
the program counter `v` and registers `σ'` that `SvcEntry el elr esr spsr` describes and that
differ from `σ` only at the registers `W`. -/
def SvcAgrees (P : Platform) (A : Abstract) (π : Sys) (W : List String) (F : Footprint)
    (el : Nat) (elr esr spsr : String) (v : UInt64) (s : State) : Prop :=
  F.opcode.word [] = svcWord.toNat ∧
  ∀ σ : Sys, (∀ q ∈ F.trace.reads .el0, σ.get q.1 q.2 = π.get q.1 q.2) →
    σ "PSTATE" = π "PSTATE" →
      (∃ o, F.Run P .el0 [] s σ o A) ∧
      ∀ o, F.Run P .el0 [] s σ o A → ∃ σ', o = .done { s with pc := v } σ' ∧
        SvcEntry el elr esr spsr s σ' ∧ ∀ r, r ∉ W → σ' r = σ r

/-- The vector's address as the walk computes it, under a vector base whose bits 63 to 55 are
set. -/
theorem lowerSync_eq {b : BitVec 64} (hb : b.toNat / 36028797018963968 = 511) :
    (b.toNat / 2048 % 9007199254740992 * 2048 + 1024) % 18446744073709551616 =
      b.toNat / 2048 * 2048 + 1024 := by
  have := b.isLt
  omega

/-- `AArch64.BranchAddr`'s sign extension from bit 55 keeps the vector's address under a vector
base whose bits 63 to 55 are set. -/
theorem lowerSync_tag {b : BitVec 64} (hb : b.toNat / 36028797018963968 = 511) :
    ashr 64 ((b.toNat / 2048 * 2048 + 1024 &&& 72057594037927935) * 256 %
      18446744073709551616) 8 = b.toNat / 2048 * 2048 + 1024 := by
  have := b.isLt
  rw [show (72057594037927935 : Nat) = 2 ^ 56 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold ashr lshr
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceLT, ↓reduceIte]
  split <;> omega

/-- Bits 4 to 0 of `x &&& m` are clear when those of `x` are. -/
theorem low_and {x m : Nat} (h : x % 32 = 0) : (x &&& m) % 32 = 0 := by
  have h' : x % 2 ^ 5 = 0 := h
  show (x &&& m) % 2 ^ 5 = 0
  apply Nat.eq_of_testBit_eq
  intro i
  have hx := congrArg (fun z => z.testBit i) h'
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.zero_testBit] at hx ⊢
  revert hx
  cases decide (i < 5) <;> cases x.testBit i <;> simp

/-- Bits 4 to 0 of `x ||| y` are clear when those of `x` and `y` are. -/
theorem low_or {x y : Nat} (hx : x % 32 = 0) (hy : y % 32 = 0) : (x ||| y) % 32 = 0 := by
  have hx' : x % 2 ^ 5 = 0 := hx
  have hy' : y % 2 ^ 5 = 0 := hy
  show (x ||| y) % 2 ^ 5 = 0
  apply Nat.eq_of_testBit_eq
  intro i
  have ex := congrArg (fun z => z.testBit i) hx'
  have ey := congrArg (fun z => z.testBit i) hy'
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.zero_testBit] at ex ey ⊢
  revert ex ey
  cases decide (i < 5) <;> cases x.testBit i <;> cases y.testBit i <;> simp

/-- Two numbers agree on bits `k` to `k + w - 1` when every one of those bits agrees. -/
theorem field_eq {a b k w : Nat} (h : ∀ i < w, a.testBit (i + k) = b.testBit (i + k)) :
    a / 2 ^ k % 2 ^ w = b / 2 ^ k % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · simp only [hi, decide_true, Bool.true_and]
    exact h i hi
  · simp only [hi, decide_false, Bool.false_and]

theorem testBit_of_field {m k w i : Nat} (hm : m / 2 ^ k % 2 ^ w = 2 ^ w - 1) (hi : i < w) :
    m.testBit (i + k) = true := by
  have := congrArg (fun z => z.testBit i) hm
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one, hi,
    decide_true, Bool.true_and] at this
  exact this

theorem testBit_of_field0 {y k w i : Nat} (hy : y / 2 ^ k % 2 ^ w = 0) (hi : i < w) :
    y.testBit (i + k) = false := by
  have := congrArg (fun z => z.testBit i) hy
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, hi,
    decide_true, Bool.true_and] at this
  exact this

/-- Bits `k` to `k + w - 1` of `x &&& m ||| y` are those of `x` when `m` has all of them set and
`y` none of them. -/
theorem field_and_or {x m y k w : Nat} (hm : m / 2 ^ k % 2 ^ w = 2 ^ w - 1)
    (hy : y / 2 ^ k % 2 ^ w = 0) : (x &&& m ||| y) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  apply field_eq
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_and, testBit_of_field hm hi, testBit_of_field0 hy hi,
    Bool.and_true, Bool.or_false]

/-- Bits `k` to `k + w - 1` of `x &&& m` are those of `x` when `m` has all of them set. -/
theorem field_and {x m k w : Nat} (hm : m / 2 ^ k % 2 ^ w = 2 ^ w - 1) :
    (x &&& m) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  apply field_eq
  intro i hi
  simp only [Nat.testBit_and, testBit_of_field hm hi, Bool.and_true]

/-- NZCV, bits 31 to 28 of a saved `PSTATE`, through a mask that keeps them and an OR that leaves
them clear, with the numerals that the walk leaves. -/
theorem nzcv_ao {x m y : Nat} (hm : m / 268435456 % 16 = 15) (hy : y / 268435456 % 16 = 0) :
    (x &&& m ||| y) / 268435456 % 16 = x / 268435456 % 16 :=
  field_and_or (k := 28) (w := 4) hm hy

/-- NZCV through a mask that keeps them. -/
theorem nzcv_a {x m : Nat} (hm : m / 268435456 % 16 = 15) :
    (x &&& m) / 268435456 % 16 = x / 268435456 % 16 :=
  field_and (k := 28) (w := 4) hm

/-- Proves the parts of `SvcEntry` that the evaluation of the path's registers leaves: the return
address, the flags and the mode of the saved `PSTATE`, and the program counter, or refutes a path
whose conditions contradict the premise on the vector base `hv`. -/
syntax "svc_end " term:max : tactic
macro_rules
  | `(tactic| svc_end $hv) => `(tactic| first
      | ((rw [UInt64.toNat_add]; rfl); done)
      | ((unfold lowerSync
          simp only [Nat.mul_zero, Nat.add_zero, lowerSync_tag $hv, lowerSync_eq $hv]); done)
      | ((simp (disch := omega) only [nzcv_ao, nzcv_a]; exact nzcv_field _); done)
      | ((repeat' (first | apply low_and | apply low_or | omega)); done)
      | (exfalso; omega))

/-- The registers outside the model that `SVC #0` writes under the host's kernel. -/
def svcVheW : List String :=
  ["SEE", "__BranchTaken", "Branchtypetaken", "ESR_EL2", "FAR_EL2", "HPFAR_EL2", "PSTATE",
    "SPSR_EL2", "ELR_EL2"]

set_option maxRecDepth 100000 in
/-- The footprint of `SVC #0` of a Linux process at EL0 under the host's kernel. -/
def svcVhe : Footprint := isla_trace% "tests/isla/linux-vhe/svc"

isla_nodes svcVhe

set_option maxRecDepth 100000 in
theorem svcVhe_n0 : svcVhe.trace = svcVhe.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx svcVhe .el0 linux [linux_get, linux]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `svcVhe` ends in the exception's entry at EL2. -/
theorem svcVhe_fwd {P : Platform} {A : Abstract} {u : LinuxUnknown} {s : State} {σ : Sys}
    {o : Outcome} (hA : A "MaybeZeroSVEUppers" [.bits 2 2] = some (.bits 0 0))
    (hσ : svcVhe.ctx σ u) (hps : σ "PSTATE" = linux u "PSTATE") (hu : u.Holds .vhe)
    (hv : u.vbar2.toNat / 2 ^ 55 = 511) (h : svcVhe.Run P .el0 [] s σ o A) :
    ∃ σ', o = .done { s with pc := lowerSync u.vbar2 } σ' ∧
      SvcEntry 2 "ELR_EL2" "ESR_EL2" "SPSR_EL2" s σ' ∧
      ∀ r, r ∉ svcVheW → σ' r = σ r := by
  obtain ⟨h1, h2, h3, h4⟩ := holds_vhe hu
  have h5 : u.mdcr.toNat / 256 % 2 = 0 := hu.tde
  have h6 : u.mdscr.toNat % 2 = 0 := hu.ss
  have h7 : u.hfgitr.toNat / 4503599627370496 % 2 = 0 := hu.svc
  have hv' : u.vbar2.toNat / 36028797018963968 = 511 := hv
  have hps' : σ "PSTATE" = some (.struct [("EL", .bits 2 0), ("SP", .bits 1 0),
      ("nRW", .bits 1 0), ("A", bv u.a), ("D", bv u.d), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao), ("PAN", bv u.pan)]) := by rw [hps]; rfl
  without_info
    unfold Footprint.Run at h
    rw [svcVhe_n0, show svcVhe.vars [] = fun _ => none from rfl] at h
    mem_fwd h using mem_omega with [Opaque.out hσ, hps', RVal.evalAll, hA, h1, h2, h3, h4, h5, h6,
      h7]
    all_goals
      simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte]
      refine ⟨_, done_eq ?_, ⟨?_, ?_, ?_, ?_⟩, by unfold svcVheW; frame_end⟩
    all_goals try simp only [List.lookup, String.reduceBEq, Option.some.injEq,
      Val.struct.injEq, Val.bits.injEq, List.cons.injEq, Prod.mk.injEq, exists_eq_left',
      Nat.reducePow, and_true, true_and, Sys.set_apply, String.reduceEq, ↓reduceIte]
    all_goals try (guard_target = And _ _; refine ⟨?_, ?_⟩)
    all_goals svc_end hv'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `svcVhe` has a path that ends. -/
theorem svcVhe_bwd {P : Platform} {A : Abstract} {u : LinuxUnknown} {s : State} {σ : Sys}
    (hA : A "MaybeZeroSVEUppers" [.bits 2 2] = some (.bits 0 0))
    (hσ : svcVhe.ctx σ u) (hps : σ "PSTATE" = linux u "PSTATE") (hu : u.Holds .vhe)
    (hv : u.vbar2.toNat / 2 ^ 55 = 511) :
    ∃ o, svcVhe.Run P .el0 [] s σ o A := by
  obtain ⟨h1, h2, h3, h4⟩ := holds_vhe hu
  have h5 : u.mdcr.toNat / 256 % 2 = 0 := hu.tde
  have h6 : u.mdscr.toNat % 2 = 0 := hu.ss
  have h7 : u.hfgitr.toNat / 4503599627370496 % 2 = 0 := hu.svc
  have hv' : u.vbar2.toNat / 36028797018963968 = 511 := hv
  have hps' : σ "PSTATE" = some (.struct [("EL", .bits 2 0), ("SP", .bits 1 0),
      ("nRW", .bits 1 0), ("A", bv u.a), ("D", bv u.d), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao), ("PAN", bv u.pan)]) := by rw [hps]; rfl
  without_info
    unfold Footprint.Run
    rw [svcVhe_n0, show svcVhe.vars [] = fun _ => none from rfl]
    by_cases b21 : u.sctlr2.toNat / 2097152 % 2 = 1
    all_goals first
      | (guard_hyp b21 : ¬u.sctlr2.toNat / 2097152 % 2 = 1
         by_cases bea : u.scr.toNat / 8 % 2 * 2 + u.scr.toNat / 1048576 % 2 = 3)
      | skip
    all_goals
      by_cases b23 : u.sctlr2.toNat / 8388608 % 2 = 0 <;>
      by_cases b38 : u.tcr2.toNat / 274877906944 % 2 = 1 <;>
      by_cases b52 : u.tcr2.toNat / 4503599627370496 % 2 = 0
    all_goals
      apply Exists.intro
      mem_bwd using mem_omega with [Opaque.out hσ, hps', RVal.evalAll, hA, h1, h2, h3, h4, h5,
        h6, h7]
    all_goals try rfl
    all_goals try (mem_side hσ [hps', RVal.evalAll, hA, h1, h2, h3, h4, h5, h6, h7])

/-- The trace of `SVC #0` at EL0 under the host's kernel takes the exception to EL2 from every
state, where `A` gives `MaybeZeroSVEUppers` the unit result, for every `u` with Linux's values
of the bits that the reset constraints fix and whose `VBAR_EL2` has bits 63 to 55 set. -/
theorem svc_vhe (P : Platform) (A : Abstract)
    (hA : A "MaybeZeroSVEUppers" [.bits 2 2] = some (.bits 0 0)) (u : LinuxUnknown)
    (hu : u.Holds .vhe) (hv : u.vbar2.toNat / 2 ^ 55 = 511) (s : State) :
    SvcAgrees P A (linux u) svcVheW svcVhe 2 "ELR_EL2" "ESR_EL2" "SPSR_EL2"
      (lowerSync u.vbar2) s := by
  refine ⟨by decide, fun σ hσ hps => ?_⟩
  have hc := svcVhe.ctx_of σ u hσ
  exact ⟨svcVhe_bwd hA hc hps hu hv, fun o h => svcVhe_fwd hA hc hps hu hv h⟩

/-- The registers outside the model that `SVC #0` writes under a kernel at EL1. -/
def svcEl1W : List String :=
  ["SEE", "__BranchTaken", "Branchtypetaken", "ESR_EL1", "FAR_EL1", "PSTATE",
    "SPSR_EL1", "ELR_EL1"]

set_option maxRecDepth 100000 in
/-- The footprint of `SVC #0` of a Linux process at EL0 under a kernel at EL1. -/
def svcEl1 : Footprint := isla_trace% "tests/isla/linux-el1/svc"

isla_nodes svcEl1

set_option maxRecDepth 100000 in
theorem svcEl1_n0 : svcEl1.trace = svcEl1.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx svcEl1 .el0 linux [linux_get, linux]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `svcEl1` ends in the exception's entry at EL1. -/
theorem svcEl1_fwd {P : Platform} {A : Abstract} {u : LinuxUnknown} {s : State} {σ : Sys}
    {o : Outcome} (hA : A "MaybeZeroSVEUppers" [.bits 2 1] = some (.bits 0 0))
    (hσ : svcEl1.ctx σ u) (hps : σ "PSTATE" = linux u "PSTATE") (hu : u.Holds .el1)
    (hv : u.vbar1.toNat / 2 ^ 55 = 511) (h : svcEl1.Run P .el0 [] s σ o A) :
    ∃ σ', o = .done { s with pc := lowerSync u.vbar1 } σ' ∧
      SvcEntry 1 "ELR_EL1" "ESR_EL1" "SPSR_EL1" s σ' ∧
      ∀ r, r ∉ svcEl1W → σ' r = σ r := by
  obtain ⟨h1, h2, h3, h4⟩ := holds_el1 hu
  have h5 : u.mdcr.toNat / 256 % 2 = 0 := hu.tde
  have h6 : u.mdscr.toNat % 2 = 0 := hu.ss
  have h7 : u.hfgitr.toNat / 4503599627370496 % 2 = 0 := hu.svc
  have h8 : u.hcr.toNat / 2147483648 % 2 = 1 := hu.hcrRw
  have hv' : u.vbar1.toNat / 36028797018963968 = 511 := hv
  have hps' : σ "PSTATE" = some (.struct [("EL", .bits 2 0), ("SP", .bits 1 0),
      ("nRW", .bits 1 0), ("A", bv u.a), ("D", bv u.d), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao), ("PAN", bv u.pan)]) := by rw [hps]; rfl
  without_info
    unfold Footprint.Run at h
    rw [svcEl1_n0, show svcEl1.vars [] = fun _ => none from rfl] at h
    mem_fwd h using mem_omega with [Opaque.out hσ, hps', RVal.evalAll, hA, h1, h2, h3, h4, h5, h6,
      h7, h8]
    all_goals
      simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte]
      refine ⟨_, done_eq ?_, ⟨?_, ?_, ?_, ?_⟩, by unfold svcEl1W; frame_end⟩
    all_goals try simp only [List.lookup, String.reduceBEq, Option.some.injEq,
      Val.struct.injEq, Val.bits.injEq, List.cons.injEq, Prod.mk.injEq, exists_eq_left',
      Nat.reducePow, and_true, true_and, Sys.set_apply, String.reduceEq, ↓reduceIte]
    all_goals try (guard_target = And _ _; refine ⟨?_, ?_⟩)
    all_goals svc_end hv'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `svcEl1` has a path that ends. -/
theorem svcEl1_bwd {P : Platform} {A : Abstract} {u : LinuxUnknown} {s : State} {σ : Sys}
    (hA : A "MaybeZeroSVEUppers" [.bits 2 1] = some (.bits 0 0))
    (hσ : svcEl1.ctx σ u) (hps : σ "PSTATE" = linux u "PSTATE") (hu : u.Holds .el1)
    (hv : u.vbar1.toNat / 2 ^ 55 = 511) :
    ∃ o, svcEl1.Run P .el0 [] s σ o A := by
  obtain ⟨h1, h2, h3, h4⟩ := holds_el1 hu
  have h5 : u.mdcr.toNat / 256 % 2 = 0 := hu.tde
  have h6 : u.mdscr.toNat % 2 = 0 := hu.ss
  have h7 : u.hfgitr.toNat / 4503599627370496 % 2 = 0 := hu.svc
  have h8 : u.hcr.toNat / 2147483648 % 2 = 1 := hu.hcrRw
  have hv' : u.vbar1.toNat / 36028797018963968 = 511 := hv
  have hps' : σ "PSTATE" = some (.struct [("EL", .bits 2 0), ("SP", .bits 1 0),
      ("nRW", .bits 1 0), ("A", bv u.a), ("D", bv u.d), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao), ("PAN", bv u.pan)]) := by rw [hps]; rfl
  without_info
    unfold Footprint.Run
    rw [svcEl1_n0, show svcEl1.vars [] = fun _ => none from rfl]
    by_cases b21 : u.sctlr1.toNat / 2097152 % 2 = 1
    all_goals first
      | (guard_hyp b21 : ¬u.sctlr1.toNat / 2097152 % 2 = 1
         by_cases bea : u.scr.toNat / 8 % 2 * 2 + u.scr.toNat / 1048576 % 2 = 3)
      | skip
    all_goals
      by_cases b23 : u.sctlr1.toNat / 8388608 % 2 = 0 <;>
      by_cases b38 : u.tcr1.toNat / 274877906944 % 2 = 1 <;>
      by_cases b52 : u.tcr1.toNat / 4503599627370496 % 2 = 0
    all_goals
      apply Exists.intro
      mem_bwd using mem_omega with [Opaque.out hσ, hps', RVal.evalAll, hA, h1, h2, h3, h4, h5,
        h6, h7, h8]
    all_goals try rfl
    all_goals try (mem_side hσ [hps', RVal.evalAll, hA, h1, h2, h3, h4, h5, h6, h7, h8])

/-- The trace of `SVC #0` at EL0 under a kernel at EL1 takes the exception to EL1 from every
state, where `A` gives `MaybeZeroSVEUppers` the unit result, for every `u` with Linux's values
of the bits that the reset constraints fix and whose `VBAR_EL1` has bits 63 to 55 set. -/
theorem svc_el1 (P : Platform) (A : Abstract)
    (hA : A "MaybeZeroSVEUppers" [.bits 2 1] = some (.bits 0 0)) (u : LinuxUnknown)
    (hu : u.Holds .el1) (hv : u.vbar1.toNat / 2 ^ 55 = 511) (s : State) :
    SvcAgrees P A (linux u) svcEl1W svcEl1 1 "ELR_EL1" "ESR_EL1" "SPSR_EL1"
      (lowerSync u.vbar1) s := by
  refine ⟨by decide, fun σ hσ hps => ?_⟩
  have hc := svcEl1.ctx_of σ u hσ
  exact ⟨svcEl1_bwd hA hc hps hu hv, fun o h => svcEl1_fwd hA hc hps hu hv h⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.svc_vhe
#print axioms TestSupport.A64.Isla.svc_el1
