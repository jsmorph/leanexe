import LeanExe.A64.Isla.Trace

/-!
Checks of the model's `exec` against Isla's traces of the Armv9.4-A Sail model for three
instructions: `ADD X3, X4, X5`, `SUBS X3, X4, X5`, and `LDR X3, [X4, #24]`, whose traces
`tests/isla/traces.sh` produced with symbolic register values and memory.  `config` gives the
registers outside the model under the traces' configuration, with the values that it leaves
UNKNOWN as the fields of `Unknown`.  `Agrees` states that a trace describes an instruction from a
state: the instruction's word decodes to it, every path of the trace ends without failure in one
state, some path ends there, and `exec` gives that state with the program counter advanced by 4,
an increment that the traces omit.  The load's theorem holds for addresses that are multiples of
8 in `0x40000000`-`0x7FFFFFFF`, the constraint under which Isla traced it, and that the platform
maps as Normal memory.

`isla_fwd` takes a hypothesis that a path ends in an outcome through the trace, and `isla_bwd`
builds one path from the values of the declared variables.  Both evaluate each event with
`isla_simp`, and the arithmetic that remains is linear arithmetic on natural numbers for `omega`.
-/

namespace LeanExe.A64.Isla

/-- The values that the configuration of the traces leaves UNKNOWN: six system registers and the
last element of `FeatureImpl`, which names no feature. -/
structure Unknown where
  mair : UInt64
  mair2 : UInt64
  pir : UInt64
  pire0 : UInt64
  sctlr2 : UInt64
  s2pir : UInt64
  feature : Bool

/-- A system register whose one field `bits` holds `n`. -/
def sysreg (w n : Nat) : Val := .struct [("bits", .bits w n)]

/-- `FeatureImpl` but its last element, one character per feature, `1` for an implemented one. -/
def features : String :=
  "10001111111111111110111111111111111110111111111111111111111111111111111101110000011111" ++
  "10011111100110111111111110111111111110111111111001111111111111111111111111111101111111" ++
  "11111011111111111111111111111111111111111111011011111110110100111011111111111111111111"

/-- The registers outside the model under the configuration of `tests/isla/traces.sh`: Isla's
`armv9p4.toml`, `PSTATE` at EL1 with SP_EL1 and debug exceptions masked, the debug registers that
Islaris fixed, and `SCTLR_EL1` `0x04000208`, with the MMU off and SA set.  `SEE` is the decoder's
integer -1, and the load writes `InGuardedPage`. -/
def config (u : Unknown) : Sys
  | "__isla_vector_gpr" => some (.bool false)
  | "__monomorphize_reads" => some (.bool false)
  | "SPESampleInFlight" => some (.bool false)
  | "InGuardedPage" => some (.bool false)
  | "__supported_pa_size" => some (.bits 128 52)
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "PSTATE" =>
    some (.struct [("EL", .bits 2 1), ("SP", .bits 1 1), ("D", .bits 1 1), ("nRW", .bits 1 0)])
  | "SCTLR_EL1" => some (sysreg 64 0x04000208)
  | "TCR_EL1" => some (sysreg 64 0)
  | "MDSCR_EL1" => some (sysreg 64 0)
  | "HCR_EL2" => some (sysreg 64 0x80000000)
  | "MDCR_EL2" => some (sysreg 32 0)
  | "SCR_EL3" => some (sysreg 64 0x401)
  | "VTCR_EL2" => some (sysreg 64 0)
  | "_EDSCR" => some (sysreg 32 2)
  | "MDCCSR_EL0" => some (sysreg 64 0)
  | "OSLSR_EL1" => some (sysreg 64 0)
  | "OSDLR_EL1" => some (sysreg 64 0)
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" =>
    some (.vec (features.toList.map (fun c => .bool (c == '1')) ++ [.bool u.feature]))
  | "MAIR_EL1" => some (sysreg 64 u.mair.toNat)
  | "MAIR2_EL1" => some (sysreg 64 u.mair2.toNat)
  | "PIR_EL1" => some (sysreg 64 u.pir.toNat)
  | "PIRE0_EL1" => some (sysreg 64 u.pire0.toNat)
  | "SCTLR_EL2" => some (sysreg 64 u.sctlr2.toNat)
  | "S2PIR_EL2" => some (sysreg 64 u.s2pir.toNat)
  | _ => none

/-- The trace `t` describes the instruction `i`, whose word is `w`, from the state `s` and the
registers `σ`: `w` decodes to `i`, the outcomes of `t` are exactly one state `s'`, and `exec`
gives `s'` with the program counter advanced by 4. -/
def Agrees (P : Platform) (w : UInt32) (i : Instr) (t : Trace) (σ : Sys) (s : State) : Prop :=
  decode w = some i ∧
  ∃ s', (∀ o, t.Run (fun _ => none) s σ o ↔ o = .done s') ∧
    exec P i s = some { s' with pc := s'.pc + 4 }

theorem Vars.set_apply (ρ : Vars) (x : Nat) (v : Val) (y : Nat) :
    ρ.set x v y = if y = x then some v else ρ y := rfl

theorem Sys.set_apply (σ : Sys) (r : String) (v : Val) (q : String) :
    σ.set r v q = if q = r then some v else σ q := rfl

/-- Evaluates the expressions, values, and register accesses of a trace's events: string, natural
number, and constructor comparisons of literals, lookups of variables and registers, and the
operators on the bit vectors that result. -/
syntax "isla_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| isla_simp $(loc)?) => `(tactic| simp only [Exp.eval, Base.eval, RVal.eval,
      Base.evalAll, Base.evalFields, Unop.apply, Binop.apply, Binop.arith, regGet, regSet, part,
      gpr, gprs, partGet, partPut, bit, acc, upd, Vars.set_apply, Sys.set_apply, config, sysreg,
      features, List.lookup, Option.bind, Option.map, Val.bits.injEq, Val.bool.injEq,
      Val.enum.injEq, Val.struct.injEq, Val.vec.injEq, Option.some.injEq, Prod.mk.injEq,
      List.cons.injEq, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Outcome.done.injEq, eq_self_iff_true, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true', Bool.not_not, Bool.not_true, Bool.not_false, and_true, true_and,
      and_self, ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false, or_false,
      false_or, Nat.pow_zero, Nat.div_one, Nat.mod_mod, Nat.add_zero, Nat.zero_add, ↓reduceIte,
      ↓reduceDIte, reduceCtorEq, String.reduceEq, String.reduceNe, String.reduceBEq,
      String.reduceAppend, String.reduceToList, Char.reduceBEq, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq] $(loc)?)

/-- Takes the hypothesis `h`, that a path of a trace ends in an outcome, through the trace: it
unfolds and evaluates one event at a time, takes apart the existentials of `declare-const` and
the conjunctions of reads and asserts, substitutes each variable by the value that a read gives,
and proves the condition of each `assume` with the tactic after `using`.  It stops when `h`
names the outcome. -/
syntax "isla_fwd " ident " using " tacticSeq : tactic
macro_rules
  | `(tactic| isla_fwd $h using $d) => `(tactic| repeat (first
      | (rw [Trace.Run] at $h:ident; try isla_simp at $h:ident)
      | subst $h:ident
      | (obtain ⟨x, $h:ident⟩ := $h:ident; try subst x)
      | rw [ite_eq_left (by $d)] at $h:ident))

/-- Builds a path of a trace up to its next `declare-const` or its end: it unfolds and evaluates
one event at a time, leaves the condition of each read or assert as a later goal, and proves the
condition of each `assume` with the tactic after `using`. -/
syntax "isla_walk " "using " tacticSeq : tactic
macro_rules
  | `(tactic| isla_walk using $d) => `(tactic| repeat (first
      | (rw [Trace.Run]; try isla_simp)
      | (apply And.intro; rotate_left)
      | rw [ite_eq_left (by $d)]))

/-- Builds a path of a trace with `isla_walk`, giving the declared variables the values of the
list in order. -/
syntax "isla_bwd " "[" term,* "]" " using " tacticSeq : tactic
macro_rules
  | `(tactic| isla_bwd [] using $d) => `(tactic| (isla_walk using ($d)))
  | `(tactic| isla_bwd [$w] using $d) =>
    `(tactic| ((isla_walk using ($d)); refine ⟨$w, ?_⟩; (isla_walk using ($d))))
  | `(tactic| isla_bwd [$w, $ws,*] using $d) =>
    `(tactic| ((isla_walk using ($d)); refine ⟨$w, ?_⟩; (isla_bwd [$ws,*] using ($d))))

/-- The model's write of a general register, as `partPut` writes it. -/
theorem setX_eq {s : State} {d : Fin 32} {i : Fin 31} (h : d.val = i.val) (v : UInt64) :
    s.setX d v = { s with regs := fun j => if j = i then v else s.regs j } := by
  unfold State.setX
  rw [ite_eq_left (by omega)]
  congr 1
  funext j
  simp only [Fin.ext_iff, h]

/-- The model's read of a general register. -/
theorem x_eq {s : State} {d : Fin 32} {i : Fin 31} (h : d.val = i.val) : s.x d = s.regs i := by
  unfold State.x
  rw [dite_eq_left (by omega)]
  exact congrArg s.regs (Fin.ext h)

theorem toNat_lt (a : UInt64) : a.toNat < 2 ^ 64 := a.toNat_lt_size

/-- The test of signed overflow, `(a ^^^ b) &&& (a ^^^ r)`, on top bits. -/
theorem bit_xor_and {x y z : Nat} (hx : x < 2) (hy : y < 2) (hz : z < 2) :
    (x ^^^ y) &&& (x ^^^ z) = 1 ↔ x ≠ y ∧ x ≠ z := by
  rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;>
    rcases (by omega : z = 0 ∨ z = 1) with rfl | rfl <;> decide

/-! The flags of `State.subs` as conditions on natural numbers. -/

theorem nflag (r : UInt64) : (r >>> 63 == 1) = decide (r.toNat / 2 ^ 63 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]

theorem zflag (r : UInt64) : (r == 0) = decide (r.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]

theorem cflag (a b : UInt64) : decide (b ≤ a) = decide (b.toNat ≤ a.toNat) := by
  rw [decide_eq_decide]
  exact UInt64.le_iff_toNat_le

theorem vflag (a b r : UInt64) : (((a ^^^ b) &&& (a ^^^ r)) >>> 63 == 1) =
    decide (a.toNat / 2 ^ 63 ≠ b.toNat / 2 ^ 63 ∧ a.toNat / 2 ^ 63 ≠ r.toNat / 2 ^ 63) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight,
    UInt64.toNat_and, UInt64.toNat_xor, UInt64.toNat_ofNat, Nat.shiftRight_and_distrib,
    Nat.shiftRight_xor_distrib, Nat.reducePow, Nat.reduceMod]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := toNat_lt a
  have := toNat_lt b
  have := toNat_lt r
  exact bit_xor_and (by omega) (by omega) (by omega)

/-! The bits of the word `NZCV` that the trace of `SUBS` builds with `concat`. -/

theorem word_n {n z c v : Nat} (hn : n < 2) (hz : z < 2) (hc : c < 2) (hv : v < 2) :
    (((n * 2 + z) * 2 + c) * 2 + v) / 8 % 2 = n := by omega

theorem word_z {n z c v : Nat} (hz : z < 2) (hc : c < 2) (hv : v < 2) :
    (((n * 2 + z) * 2 + c) * 2 + v) / 4 % 2 = z := by omega

theorem word_c {n z c v : Nat} (hc : c < 2) (hv : v < 2) :
    (((n * 2 + z) * 2 + c) * 2 + v) / 2 % 2 = c := by omega

theorem word_v {n z c v : Nat} (hv : v < 2) : (((n * 2 + z) * 2 + c) * 2 + v) % 2 = v := by
  omega

/-- The OR of a number below `2 ^ k` and a number shifted left by `k` within 64 bits is their
sum. -/
theorem or_shl {x b k : Nat} (hx : x < 2 ^ k) (hb : b * 2 ^ k < 18446744073709551616) :
    x ||| b <<< k % 18446744073709551616 = x + b * 2 ^ k := by
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

/-- The model's `load64` is the semantics' `bytes` of eight bytes. -/
theorem load64_toNat (m : UInt64 → UInt8) (a : UInt64) : (load64 m a).toNat = bytes m a 8 := by
  simp only [load64, bytes, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    UInt64.toNat_ofNat, UInt64.add_assoc, UInt64.reduceAdd, Nat.reducePow, Nat.reduceMod]
  have := UInt8.toNat_lt (m a)
  have := UInt8.toNat_lt (m (a + 1))
  have := UInt8.toNat_lt (m (a + 2))
  have := UInt8.toNat_lt (m (a + 3))
  have := UInt8.toNat_lt (m (a + 4))
  have := UInt8.toNat_lt (m (a + 5))
  have := UInt8.toNat_lt (m (a + 6))
  have := UInt8.toNat_lt (m (a + 7))
  rw [or_shl (k := 8) ?_ ?_, or_shl (k := 16) ?_ ?_, or_shl (k := 24) ?_ ?_,
    or_shl (k := 32) ?_ ?_, or_shl (k := 40) ?_ ?_, or_shl (k := 48) ?_ ?_,
    or_shl (k := 56) ?_ ?_]
  all_goals omega

theorem load64_eq (m : UInt64 → UInt8) (a : UInt64) : load64 m a = .ofNat (bytes m a 8) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', ← load64_toNat, Nat.mod_eq_of_lt (toNat_lt _)]

/-- An address `a` with `a &&& 0xFFFFFFFFC0000007 = 0x40000000`, the constraint of the load's
trace, is a multiple of 8 in `0x40000000`-`0x7FFFFFFF` whose bits 52 to 63 are clear. -/
theorem ram {a : Nat} (h : a &&& 18446744072635809799 = 1073741824) (ha : a < 2 ^ 64) :
    a % 8 = 0 ∧ a / 2 ^ 30 = 1 ∧ a &&& 18442240474082181120 = 0 := by
  have and_eq : ∀ m, m &&& 18446744072635809799 = m → a &&& m = 1073741824 &&& m := by
    intro m hm
    calc a &&& m = a &&& (18446744072635809799 &&& m) := by
          rw [Nat.and_comm 18446744072635809799, hm]
      _ = 1073741824 &&& m := by rw [← Nat.and_assoc, h]
  have h7 : a &&& 7 = 0 := (and_eq 7 (by decide)).trans (by decide)
  have h8 : a % 8 = a &&& 7 := (Nat.and_two_pow_sub_one_eq_mod a 3).symm
  have hs : a >>> 30 &&& 17179869183 = 1 := by
    have := congrArg (· >>> 30) h
    simpa only [Nat.shiftRight_and_distrib, Nat.reduceShiftRight] using this
  have hm : a >>> 30 &&& 17179869183 = a >>> 30 % 2 ^ 34 := Nat.and_two_pow_sub_one_eq_mod _ 34
  rw [hm, Nat.shiftRight_eq_div_pow] at hs
  exact ⟨by omega, by omega, (and_eq _ (by decide)).trans (by decide)⟩

/-- The trace of `ADD X3, X4, X5`. -/
def addTrace : Trace := isla_trace% "tests/isla/add.trace"

/-- The trace of `SUBS X3, X4, X5`. -/
def subsTrace : Trace := isla_trace% "tests/isla/subs.trace"

/-- The trace of `LDR X3, [X4, #24]`. -/
def ldrTrace : Trace := isla_trace% "tests/isla/ldr.trace"

/-- Reduces an equation between two functions that update register 3 of the same registers to
the equation between the values written. -/
macro "regs_end" : tactic => `(tactic| (
  funext j
  by_cases hj : j = 3 <;> simp only [hj, eq_self_iff_true, ↓reduceIte]))

/-- Proves that the state at the end of the trace of `ADD` is `exec`'s. -/
macro "add_end" : tactic => `(tactic| (
  simp only [Outcome.done.injEq, setX_eq (d := 3) (i := 3) rfl, x_eq (d := 4) (i := 4) rfl,
    x_eq (d := 5) (i := 5) rfl, State.mk.injEq, eq_self_iff_true, and_true]
  regs_end
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add]
  omega))

/-- The trace of `ADD X3, X4, X5` agrees with `exec` from every state. -/
theorem add (P : Platform) (u : Unknown) (s : State) :
    Agrees P 0x8B050083 (.addReg 3 4 5) addTrace (config u) s := by
  have := toNat_lt (s.regs 4)
  have := toNat_lt (s.regs 5)
  refine ⟨by decide, s.setX 3 (s.x 4 + s.x 5), fun o => ⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · unfold addTrace at h
    isla_fwd h using omega
    add_end
  · subst h
    unfold addTrace
    isla_bwd [s.pc.toNat, (s.regs 4).toNat, (s.regs 5).toNat] using omega
    · exact (Outcome.done.inj (by add_end)).symm
    all_goals exact toNat_lt _

/-- Proves that the state at the end of the trace of `SUBS` from the state `s` is `exec`'s.  The
flags of the trace are the bits of a word of 4 bits, and its V flag compares the sign-extended
result with the sum of the sign-extended operands, which `omega` decides once the signs of the
operands and the result and the carry are known. -/
syntax "subs_end " term : tactic
macro_rules
  | `(tactic| subs_end $s) => `(tactic| (
    simp only [Outcome.done.injEq, State.subs, setX_eq (d := 3) (i := 3) rfl,
      x_eq (d := 4) (i := 4) rfl, x_eq (d := 5) (i := 5) rfl, vflag]
    simp only [nflag, zflag, cflag, UInt64.toNat_sub, State.mk.injEq, eq_self_iff_true,
      true_and, and_true]
    simp (disch := first | omega | (split <;> omega)) only [word_n, word_z, word_c, word_v]
    simp (disch := omega) only [Nat.mod_eq_of_lt, decide_eq_decide]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · regs_end
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_ofNat', UInt64.toNat_sub]
      omega
    · (repeat' split) <;> omega
    · (repeat' split) <;> omega
    · (repeat' split) <;> omega
    · rcases Nat.lt_or_ge (State.regs $s 4).toNat (2 ^ 63) with _ | _ <;>
        rcases Nat.lt_or_ge (State.regs $s 5).toNat (2 ^ 63) with _ | _ <;>
        rcases Nat.lt_or_ge ((State.regs $s 4).toNat + (2 ^ 64 - (State.regs $s 5).toNat))
          (2 ^ 64) with _ | _ <;>
        rcases Nat.lt_or_ge (((State.regs $s 4).toNat + (2 ^ 64 - (State.regs $s 5).toNat)) %
          2 ^ 64) (2 ^ 63) with _ | _ <;>
        (repeat' split) <;> omega))

set_option maxHeartbeats 1000000 in
/-- The trace of `SUBS X3, X4, X5` agrees with `exec` from every state.  The proof of the V flag
takes 32 cases of `omega`, beyond the default budget of heartbeats. -/
theorem subs (P : Platform) (u : Unknown) (s : State) :
    Agrees P 0xEB050083 (.subsReg 3 4 5) subsTrace (config u) s := by
  have := toNat_lt (s.regs 4)
  have := toNat_lt (s.regs 5)
  refine ⟨by decide, s.subs 3 (s.x 4) (s.x 5), fun o => ⟨fun h => ?_, fun h => ?_⟩, rfl⟩
  · unfold subsTrace at h
    isla_fwd h using omega
    subs_end s
  · subst h
    unfold subsTrace
    isla_bwd [s.pc.toNat, (s.regs 4).toNat, (s.regs 5).toNat] using omega
    · exact (Outcome.done.inj (by subs_end s)).symm
    all_goals exact toNat_lt _

/-- Proves that the state at the end of the trace of `LDR` is `exec`'s: the trace writes to X3
the eight bytes at an address that the constraint on `X4 + 24` makes equal to it. -/
macro "ldr_end" : tactic => `(tactic| (
  simp only [Outcome.done.injEq, setX_eq (d := 3) (i := 3) rfl, load64_eq, State.mk.injEq,
    eq_self_iff_true, and_true]
  all_goals
    regs_end
    refine congrArg (fun a => UInt64.ofNat (bytes _ a 8)) ?_
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    omega))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The trace of `LDR X3, [X4, #24]` agrees with `exec` from every state whose address `X4 + 24` is
a multiple of 8 in `0x40000000`-`0x7FFFFFFF`, as the trace's constraint states, and lies in
memory that the platform maps as Normal.  The comparison of `FeatureImpl`, a vector of 259
Booleans, recurses deeper than the default limit, and the trace's 98 events take more than the
default budget of heartbeats. -/
theorem ldr (P : Platform) (u : Unknown) (s : State)
    (ha : (s.regs 4 + 24) &&& 0xFFFFFFFFC0000007 = 0x40000000)
    (hm : P.mapped (s.regs 4 + 24) 8 = true) :
    Agrees P 0xF9400C83 (.ldr 3 4 3) ldrTrace (config u) s := by
  have h4 := toNat_lt (s.regs 4)
  have hA : ((s.regs 4).toNat + 24) % 18446744073709551616 &&& 18446744072635809799 =
      1073741824 := by
    have := congrArg UInt64.toNat ha
    simpa [UInt64.toNat_and, UInt64.toNat_add] using this
  obtain ⟨h8, h30, hh⟩ := ram hA (Nat.mod_lt _ (by decide))
  have h4' : (s.regs 4).toNat % 18446744073709551616 = (s.regs 4).toNat := Nat.mod_eq_of_lt h4
  refine ⟨by decide, s.setX 3 (load64 s.mem (s.regs 4 + 24)),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · unfold ldrTrace at h
    isla_fwd h using exact hA
    ldr_end
  · subst h
    unfold ldrTrace
    isla_bwd [u.feature, (s.regs 4).toNat, s.pc.toNat, u.mair.toNat, u.mair2.toNat, u.pir.toNat,
      u.pire0.toNat, u.sctlr2.toNat, u.s2pir.toNat, bytes s.mem (s.regs 4 + 24) 8] using exact hA
    · exact (Outcome.done.inj (by ldr_end)).symm
    all_goals first
      | exact toNat_lt _
      | exact hA
      | (rw [← load64_toNat]; exact toNat_lt _)
      | (simp only [h4'] at *; first | exact hh | omega)
      | (simp only [sint, sdiv, udiv, neg]; (repeat' split) <;> omega)
      | (refine congrArg (fun a => bytes _ a 8) ?_
         apply UInt64.toNat_inj.mp
         simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
           Nat.reduceMod]
         omega)
  · have hx : s.xsp 4 + UInt64.ofNat (8 * (3 : Fin 4096).val) = s.regs 4 + 24 := rfl
    simp only [exec, hx, hm]
    rfl

end LeanExe.A64.Isla
