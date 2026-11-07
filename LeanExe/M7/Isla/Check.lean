import LeanExe.M7.Isla.Trace
import LeanExe.M7.Encode
import LeanExe.M7.Isla.Profile

/-!
Checks of the model's `exec` against Isla's traces of the A-profile Sail model in AArch32 Thumb
state.  `Agrees` states what the footprint of one instruction form establishes for one value of the
form's fields and one machine, and the theorem of a form quantifies over both.

The footprint's opcode, which `isla_trace%` reads from the trace's opcode file, must have the
fields of the footprint's header and 16 or 32 bits, and its halfwords for the fields' values must
decode to the instruction, with the opcode's length.  For every `σ` that agrees with the profile
`π` on the registers outside the model that the trace reads, whenever `exec` gives a state `s'`,
every outcome of the trace from the machine `m` is the machine with `s'` as its model state and
some high words of X0 to X14, with registers `σ'` that differ from `σ` only at the registers
`W`, and one outcome is that machine with `m`'s high words.  The traces write a register of
AArch32 either with zeros in bits 63 to 32 or with those bits kept, a choice that the Sail model
leaves to a fresh Boolean (`v8_base.sail` 13989-13993), so a write gives two outcomes that agree
on the model's state.  X15 to X30 and the memory above 2^32 keep their values.  The statement
covers the instruction's decode and execution: the model's registers, flags, program counter,
memory, and device accesses, and the registers outside the model that they change.  `σ'` leaves
out the effects of `__InstructionExecute` around the decode and execution, as in
`LeanExe/A64/Isla/Check.lean`.  A trace's `assume` events, which Isla records for the
configuration's constraints, end a path in `fail` when false, so the theorem of such a trace
carries the constraint as a premise.

`t32_simp`, `t32_fwd`, `t32_walk`, `t32_bwd`, and `t32_gprs` are the tactics `isla_simp`,
`isla_fwd`, `isla_walk`, `isla_bwd`, and `isla_gprs` of the A64 check with this semantics'
functions.  A read at a symbolic index evaluates Isla's chain of 30 `ite` expressions over the
values of `R0` to `R30`, and `chain_eq` folds the chain over the machine's registers into the
indexed register.  `x_mod` and `low_r` turn the low word of an X register into the model's
register, and `setX_low`, `setX_keep`, and `setLow_r` turn the trace's two writes of an X register
into `State.setR`.  `t32_reg_end` and `t32_reg_bwd` compare the outcome of a path with `exec`'s
for a form that writes one register.
-/

namespace LeanExe.M7.Isla

open LeanExe.A64.Isla (Footprint Fields Opcode Val Vars Sys acc upd)

/-- The footprint `F` describes the instruction `i` for the fields `f` from the machine `m`: the
header names the fields of `F`'s opcode, the opcode has 16 or 32 bits, its halfwords decode to `i`
with its length, and for every `σ` that agrees with the profile `π` on the registers that the
trace reads, if `exec` gives `s'`, every outcome of the trace is the machine with `s'` and some
high words of X0 to X14, with registers `σ'` that differ from `σ` only at the registers `W`, and
one outcome keeps `m`'s high words. -/
def Agrees (P : Platform) (δ : Nat → UInt32) (π : Sys) (W : List String) (F : Footprint)
    (f : Fields) (i : Instr) (m : Mach) : Prop :=
  F.segments.map (fun g => (g.name, g.width)) = F.opcode.fields ∧
  (F.opcode.width = 16 ∨ F.opcode.width = 32) ∧
  decode (halves F.opcode f) = some (i, F.opcode.width / 16) ∧
  ∀ σ : Sys, (∀ q ∈ reads F.trace, σ.get q.1 q.2 = π.get q.1 q.2) →
    ∀ s', exec P δ i m.s = some s' →
      ∃ σ', (∀ o, footRun P δ F f m σ o →
          ∃ hi, o = .done { m with s := s', hi := hi } σ') ∧
        footRun P δ F f m σ (.done { m with s := s' } σ') ∧ ∀ r, r ∉ W → σ' r = σ r

/-! The opcode's halfwords. -/

theorem ofNat16_add (a b : Nat) : UInt16.ofNat (a * 65536 + b) = UInt16.ofNat b := by
  apply UInt16.toNat_inj.mp
  simp only [UInt16.toNat_ofNat', Nat.reducePow]
  omega

/-- The halfwords of a 32-bit opcode whose word is `e1 * 65536 + e2` are the encoding's. -/
theorem halves_32 {p : Opcode} {f : Fields} {e1 e2 : Nat} (hw : p.width = 32)
    (h : p.word f = e1 * 65536 + e2) (h2 : e2 < 65536) :
    halves p f = [UInt16.ofNat e1, UInt16.ofNat e2] := by
  simp only [halves, hw, h, ofNat16_add, Nat.reduceEqDiff, ↓reduceIte, List.cons.injEq, and_true]
  congr 1
  omega

/-- The decoder reads the halfwords of a 32-bit form's opcode as the form when the opcode's word is
the form's encoding. -/
theorem decode_halves {p : Opcode} {f : Fields} {i : Instr} (hw : p.width = 32)
    (hi : i ≠ .bxLr) (h : p.word f = (encodeNat i).1 * 65536 + (encodeNat i).2) :
    decode (halves p f) = some (i, p.width / 16) := by
  rw [halves_32 hw h (encodeNat_lt i).2, hw]
  have := decode_encode i []
  simp only [encode, (wide_encodeNat i).mpr hi, ↓reduceIte, List.append_nil, List.length_cons,
    List.length_nil] at this
  exact this

/-! Reads and writes of the X registers. -/

theorem Vars.set_apply (ρ : Vars) (x : Nat) (v : Val) (y : Nat) :
    ρ.set x v y = if y = x then some v else ρ y := rfl

theorem Sys.set_apply (σ : Sys) (r : String) (v : Val) (q : String) :
    σ.set r v q = if q = r then some v else σ q := rfl

theorem Sys.get_set (σ : Sys) (r : String) (v : Val) (q : String) (al : List String) :
    (σ.set r v).get q al = if q = r then acc al v else σ.get q al := by
  unfold LeanExe.A64.Isla.Sys.get LeanExe.A64.Isla.Sys.set
  split <;> rfl

/-- `cond (decide (k = 30)) (m.x 30) (... (m.x 0))`, the chain of a read at the index `k` from the
X registers of the machine `m`, as `t32_simp` writes it. -/
syntax "chain32% " term:max term:max : term
macro_rules
  | `(chain32% $m $k) => do
    let mut t ← `(Mach.x $m 0)
    for j in [1:31] do
      let lit := Lean.Syntax.mkNumLit (toString j)
      t ← `(cond (decide ($k = $lit)) (Mach.x $m $lit) $t)
    return t

/-- `cond (decide (k = j)) (f j) (... (cond (decide (k = 1)) (f 1) (f 0)))`, the value of the
chain that Isla builds for a read at the symbolic index `k`. -/
def pick (k : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | j + 1 => cond (decide (k = j + 1)) (f (j + 1)) (pick k f j)

theorem pick_eq (k : Nat) (f : Nat → Nat) : ∀ j, k ≤ j → pick k f j = f k
  | 0, h => by
    obtain rfl := Nat.le_zero.mp h
    rfl
  | j + 1, h => by
    unfold pick
    by_cases hk : k = j + 1
    · rw [decide_eq_true hk, Bool.cond_true, hk]
    · rw [decide_eq_false hk, Bool.cond_false]
      exact pick_eq k f j (by omega)

/-- The chain of a read at the index `k` below 31 is X register `k`. -/
theorem chain_eq {m : Mach} {k : Nat} (hk : k < 31) : chain32% m k = m.x k :=
  pick_eq k (Mach.x m) 30 (by omega)

/-- A flag as a number, divided by a number of at least 2. -/
theorem bit_div (b : Bool) {k : Nat} (h : 2 ≤ k) : (if b = true then 1 else 0) / k = 0 := by
  split <;> exact Nat.div_eq_of_lt (by omega)

/-- A flag as a number, modulo a number of at least 2. -/
theorem bit_mod (b : Bool) {k : Nat} (h : 2 ≤ k) :
    (if b = true then 1 else 0) % k = (if b = true then 1 else 0) := by
  split <;> exact Nat.mod_eq_of_lt (by omega)

/-- `x + 0 = x` by `omega`.  `simp` applies `Nat.add_zero`, an `rfl` theorem, without a proof
step, and the kernel then checks the equation by unfolding, which takes minutes on the large terms
of a trace's addresses. -/
theorem nat_add_zero (x : Nat) : x + 0 = x := by omega

theorem fin_mod {k : Nat} (n : Fin k) {m : Nat} (h : k ≤ m) : n.val % m = n.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le n.isLt h)

theorem fin_div {k : Nat} (n : Fin k) {m : Nat} (h : k ≤ m) : n.val / m = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le n.isLt h)

theorem regAt_lt {m : Mach} {k : Nat} (h : k < 31) : regAt m k = m.x k := ite_eq_left h

theorem setRegAt_lt {m : Mach} {k : Nat} (h : k < 31) (n : Nat) :
    setRegAt m k n = m.setX k n := ite_eq_left h

theorem x_lt (m : Mach) {k : Nat} (h : k < 15) :
    m.x k = (m.hi ⟨k, h⟩).toNat * 4294967296 + (low m.s k).toNat := dite_eq_left h

theorem x_lt_pow (m : Mach) (k : Nat) : m.x k < 18446744073709551616 := by
  unfold Mach.x
  split
  · rename_i h
    have : (m.hi ⟨k, h⟩).toNat < 4294967296 := (m.hi ⟨k, h⟩).toNat_lt
    have : (low m.s k).toNat < 4294967296 := (low m.s k).toNat_lt
    omega
  · split
    · exact (m.xs _).toNat_lt
    · omega

/-- The low word of an X register below 15. -/
theorem x_mod (m : Mach) {k : Nat} (h : k < 15) : m.x k % 4294967296 = (low m.s k).toNat := by
  rw [x_lt m h]
  have : (low m.s k).toNat < 4294967296 := (low m.s k).toNat_lt
  omega

/-- The high word of an X register below 15. -/
theorem x_div (m : Mach) {k : Nat} (h : k < 15) : m.x k / 4294967296 = (m.hi ⟨k, h⟩).toNat := by
  rw [x_lt m h]
  have : (low m.s k).toNat < 4294967296 := (low m.s k).toNat_lt
  omega

/-- The low word of X register `r` for `r` among r0 to r7 is the model's register. -/
theorem low_r (s : State) (r : Fin 8) : low s r.val = s.r r := by
  unfold low State.r
  rw [dite_eq_left (by omega)]

/-- The write of X register `d` among r0 to r7 sets the model's register to the low word. -/
theorem setLow_r (s : State) (d : Fin 8) (v : UInt32) : setLow s d.val v = s.setR d v := by
  unfold setLow State.setR
  rw [ite_eq_left (by omega)]

/-- Evaluates the expressions, values, and register accesses of a trace's events: string, natural
number, and constructor comparisons of literals, lookups of variables and registers, the operators
on the bit vectors that result, the reduction of `a % b` to `a` and of `a / b` to 0 for the value
`a` of a field below `b`, and the chain of a read from the machine's registers.  `omega` proves
the side conditions of these rules.  The lemmas in brackets join the set, among them the equations
of the premise on the registers outside the model. -/
syntax "t32_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| t32_simp [$xs,*] $(loc)?) => `(tactic| simp -failIfUnchanged (disch := omega) only [
      eval, LeanExe.A64.Isla.Base.eval, LeanExe.A64.Isla.RVal.eval,
      LeanExe.A64.Isla.Base.evalAll, LeanExe.A64.Isla.Base.evalFields,
      LeanExe.A64.Isla.Unop.apply, LeanExe.A64.Isla.Binop.apply, LeanExe.A64.Isla.Binop.arith,
      LeanExe.A64.Isla.lshr, regGet, regSet, part, gprs, partGet, partPut, LeanExe.A64.Isla.bit,
      LeanExe.A64.Isla.acc, LeanExe.A64.Isla.upd, gprVals, runSome, Vars.set_apply,
      Sys.set_apply, Sys.get_set, List.lookup,
      Option.bind, Option.map, Option.getD, LeanExe.A64.Isla.Val.bits.injEq,
      LeanExe.A64.Isla.Val.bool.injEq, LeanExe.A64.Isla.Val.enum.injEq,
      LeanExe.A64.Isla.Val.struct.injEq, LeanExe.A64.Isla.Val.vec.injEq, Option.some.injEq,
      Prod.mk.injEq, List.cons.injEq, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, eq_self_iff_true, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true', Bool.not_not, Bool.not_true, Bool.not_false, Bool.and_true,
      Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false,
      Bool.false_or, and_true, true_and, and_self, ne_eq, not_true_eq_false, not_false_eq_true,
      false_and, and_false, or_false, false_or, Nat.pow_zero, Nat.div_one, Nat.mod_mod,
      Nat.zero_add, nat_add_zero, Nat.zero_mul, bit_div, bit_mod, fin_mod, fin_div, regAt_lt,
      setRegAt_lt, Fin.is_lt, ↓reduceIte,
      ↓reduceDIte, reduceCtorEq, String.reduceEq, String.reduceNe, String.reduceBEq,
      String.reduceAppend, String.reduceToList, Char.reduceBEq, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq, Bool.cond_true,
      Bool.cond_false, decide_true, decide_false, chain_eq, $xs,*] $(loc)?)

/-- Turns a statement over the registers that a footprint's trace reads, such as the premise of
`Agrees` on `σ`, into one statement per read: the lemmas in brackets unfold the footprint and
evaluate the profile. -/
syntax "t32_reads " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| t32_reads [$xs,*] $(loc)?) => `(tactic| simp only [
      LeanExe.A64.Isla.Footprint.trace, reads,
      readsAll, eventReads, LeanExe.A64.Isla.Exp.regs, List.filter, part, gprs, List.lookup,
      Option.map, Option.isNone, Option.bind, LeanExe.A64.Isla.acc, String.reduceEq,
      String.reduceBEq,
      ↓reduceIte, Bool.false_eq_true, reduceCtorEq, List.nil_append, List.cons_append,
      List.append_nil, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      forall_const, and_true, LeanExe.A64.Isla.sysreg, LeanExe.A64.Isla.bv, $xs,*] $(loc)?)

/-- Takes the hypothesis `h`, that a path of a trace ends in an outcome, through the trace, as the
tactic of the same name in `LeanExe/A64/Isla/Check.lean` does: it unfolds and evaluates one event
at a time, splits the disjunctions of `cases`, takes apart the existentials of `declare-const` and
the conjunctions of reads and asserts, substitutes each variable by the value that a read gives,
rewrites with the equation of `read_register_from_vector` between Isla's chain and the indexed
register, and proves the condition of each `assume` with the tactic after `using`. -/
syntax "t32_fwd " ident " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| t32_fwd $h using $d with [$xs,*]) => `(tactic| repeat' (first
      | (rw [run] at $h:ident; t32_simp [$xs,*] at $h:ident)
      | (guard_hyp $h : False; exact False.elim $h)
      | (guard_hyp $h : Or _ _; rcases $h:ident with $h:ident | $h:ident)
      | (guard_hyp $h : Exists _; obtain ⟨x, $h:ident⟩ := $h:ident)
      | (guard_hyp $h : And _ _
         obtain ⟨x, $h:ident⟩ := $h:ident
         first
           | subst x
           | (guard_hyp x : _ = Mach.x _ _
              rw [x] at $h:ident
              t32_simp [$xs,*] at $h:ident)
           | skip)
      | (guard_hyp $h : @Eq Outcome _ _; subst $h:ident)
      | focus (rw [ite_eq_left] at $h:ident; rotate_left; ($d))))

/-- Builds a path of a trace up to its next `declare-const` of a free variable or its end, as the
tactic of the same name in `LeanExe/A64/Isla/Check.lean` does. -/
syntax "t32_walk " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_walk using $d with [$xs,*]) => `(tactic| repeat (first
      | (rw [run]; t32_simp [$xs,*])
      | (guard_target = And _ _; apply And.intro; rotate_left)
      | focus (rw [ite_eq_left]; rotate_left; ($d))))

/-- Builds a path of a trace with `t32_walk`, giving the declared variables the values of the
list in order. -/
syntax "t32_bwd " "[" term,* "]" " using " tacticSeq " with "
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_bwd [] using $d with [$xs,*]) => `(tactic| (t32_walk using ($d) with [$xs,*]))
  | `(tactic| t32_bwd [$w] using $d with [$xs,*]) => `(tactic| (
      t32_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      t32_walk using ($d) with [$xs,*]))
  | `(tactic| t32_bwd [$w, $ws,*] using $d with [$xs,*]) => `(tactic| (
      t32_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      t32_bwd [$ws,*] using ($d) with [$xs,*]))

/-- Builds a path of a trace with `t32_bwd`, giving the 31 declared variables that hold Isla's
values of `R0` to `R30` the values of the X registers of the machine `m`. -/
syntax "t32_gprs " term " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| t32_gprs $m using $d with [$xs,*]) => `(tactic| t32_bwd [
      Mach.x $m 0, Mach.x $m 1, Mach.x $m 2, Mach.x $m 3, Mach.x $m 4, Mach.x $m 5, Mach.x $m 6,
      Mach.x $m 7, Mach.x $m 8, Mach.x $m 9, Mach.x $m 10, Mach.x $m 11, Mach.x $m 12,
      Mach.x $m 13, Mach.x $m 14, Mach.x $m 15, Mach.x $m 16, Mach.x $m 17, Mach.x $m 18,
      Mach.x $m 19, Mach.x $m 20, Mach.x $m 21, Mach.x $m 22, Mach.x $m 23, Mach.x $m 24,
      Mach.x $m 25, Mach.x $m 26, Mach.x $m 27, Mach.x $m 28, Mach.x $m 29, Mach.x $m 30]
      using $d with [$xs,*])

/-! The outcome at the end of a path. -/

theorem setX_s (m : Mach) {i : Nat} (h : i < 15) (n : Nat) :
    (m.setX i n).s = setLow m.s i (.ofNat n) := by
  unfold Mach.setX
  rw [ite_eq_left h]

theorem setX_hi (m : Mach) {i : Nat} (h : i < 15) (n : Nat) :
    (m.setX i n).hi = fun j => if j.val = i then .ofNat (n / 4294967296) else m.hi j := by
  unfold Mach.setX
  rw [ite_eq_left h]

theorem setX_xs (m : Mach) {i : Nat} (h : i < 15) (n : Nat) : (m.setX i n).xs = m.xs := by
  unfold Mach.setX
  rw [ite_eq_left h]

theorem setX_far (m : Mach) (i n : Nat) : (m.setX i n).far = m.far := by
  unfold Mach.setX
  split <;> rfl

/-- A machine whose model state is `s'` and whose X15 to X30 and upper memory are `m`'s is `m` with
`s'` and some high words. -/
theorem exists_mach {m m' : Mach} {s' : State} (h : m'.s = s') (hx : m'.xs = m.xs)
    (hf : m'.far = m.far) : ∃ hi, m' = { m with s := s', hi := hi } := by
  refine ⟨m'.hi, ?_⟩
  cases m'
  cases m
  simp only at h hx hf
  subst h hx hf
  rfl

/-- The low word of a write that keeps bits 63 to 32 of `x` and puts `v` below them. -/
theorem keep_low {x v : Nat} (hv : v < 4294967296) :
    (x &&& 18446744069414584320 ||| v) % 4294967296 = v := by
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.or_mod_two_pow, Nat.and_mod_two_pow,
    show (18446744069414584320 : Nat) % 2 ^ 32 = 0 from rfl, Nat.and_zero, Nat.zero_or,
    Nat.mod_eq_of_lt hv]

/-- The high word of a write that keeps bits 63 to 32 of `x` and puts `v` below them. -/
theorem keep_high {x v : Nat} (hx : x < 18446744073709551616) (hv : v < 4294967296) :
    (x &&& 18446744069414584320 ||| v) / 4294967296 = x / 4294967296 := by
  rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← Nat.shiftRight_eq_div_pow,
    ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib, Nat.shiftRight_and_distrib,
    show (18446744069414584320 : Nat) >>> 32 = 4294967295 from rfl,
    Nat.shiftRight_eq_div_pow v, Nat.div_eq_of_lt (by omega), Nat.or_zero]
  have : x >>> 32 < 2 ^ 32 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt this]

theorem ofNat_toNat32 (a : UInt32) : UInt32.ofNat a.toNat = a := UInt32.ofNat_toNat

theorem ofNat_mod32 (n : Nat) : UInt32.ofNat (n % 4294967296) = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', Nat.reducePow]
  omega

theorem ofNat_and32 (a b : UInt32) : UInt32.ofNat (a.toNat &&& b.toNat) = a &&& b := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_and, Nat.reducePow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right b.toNat_lt)

theorem ofNat_or32 (a b : UInt32) : UInt32.ofNat (a.toNat ||| b.toNat) = a ||| b := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_or, Nat.reducePow]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow a.toNat_lt b.toNat_lt)

theorem ofNat_xor32 (a b : UInt32) : UInt32.ofNat (a.toNat ^^^ b.toNat) = a ^^^ b := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_xor, Nat.reducePow]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.toNat_lt b.toNat_lt)

/-- The sum of `ADC` without flags, as the trace computes it in 32 bits. -/
theorem ofNat_adc32 (a b : UInt32) (c : Bool) :
    UInt32.ofNat (((a.toNat + b.toNat) % 4294967296 + (if c = true then 1 else 0)) % 4294967296) =
      (addWithCarry a b c).1 := by
  simp only [addWithCarry]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', Nat.reducePow]
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem lt32_and {a b : Nat} (hb : b < 4294967296) : a &&& b < 4294967296 :=
  Nat.lt_of_le_of_lt Nat.and_le_right hb

theorem lt32_or {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    a ||| b < 4294967296 :=
  Nat.or_lt_two_pow (n := 32) ha hb

theorem lt32_xor {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) :
    a ^^^ b < 4294967296 :=
  Nat.xor_lt_two_pow (n := 32) ha hb

/-- Proves that a value that a trace writes to the low word of a register is below 2^32: a
remainder modulo 2^32, or the bitwise AND, OR, or exclusive OR of such values. -/
macro "t32_lt" : tactic => `(tactic| first
  | omega
  | (apply lt32_and; omega)
  | (apply lt32_or <;> omega)
  | (apply lt32_xor <;> omega))

/-- A write of an X register below 15 with a value below 2^32, as the trace's write that clears
bits 63 to 32 gives it: the model's register takes the value, and the high word becomes 0. -/
theorem setX_low (m : Mach) {i : Nat} (h : i < 15) {v : Nat} (hv : v < 4294967296) :
    m.setX i v =
      { m with s := setLow m.s i (.ofNat v), hi := fun j => if j.val = i then 0 else m.hi j } := by
  unfold Mach.setX
  rw [ite_eq_left h, Nat.div_eq_of_lt hv]
  rfl

/-- A write of an X register below 15 that keeps bits 63 to 32 and puts `v` below them: the model's
register takes the value, and the high words do not change. -/
theorem setX_keep (m : Mach) {i : Nat} (h : i < 15) {v : Nat} (hv : v < 4294967296) :
    m.setX i (m.x i &&& 18446744069414584320 ||| v) =
      { m with s := setLow m.s i (.ofNat v) } := by
  unfold Mach.setX
  rw [ite_eq_left h, ← ofNat_mod32, keep_low hv, keep_high (x_lt_pow m i) hv, x_div m h]
  congr 1
  funext j
  split
  · rename_i hj
    rw [ofNat_toNat32]
    exact congrArg m.hi (Fin.ext hj.symm)
  · rfl

/-- The model's state after a form that writes register `d` with `a`, as the trace's outcome gives
it, is `exec`'s. -/
theorem state_eq {s : State} {d : Fin 8} {a b : UInt32} (h : a = b) :
    { s.setR d a with pc := (s.setR d a).pc + UInt32.ofNat 4 } =
      { s.setR d b with pc := s.pc + 4 } := by
  subst h
  rfl

/-- Proves that the outcome at the end of a path of the trace of a form that writes one register of
r0 to r7, the low word of the result being a value of `t32_lt`, is `exec`'s, with the lemmas in
brackets that turn the written value into the model's. -/
syntax "t32_reg_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_reg_end [$xs,*]) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
      true_and]
    simp (disch := first | omega | t32_lt) only [setX_low, setX_keep]
    apply exists_mach
    · simp only [setLow_r]
      apply state_eq
      simp (disch := omega) only [x_mod, low_r, $xs,*]
    · rfl
    · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path of the trace that
keeps bits 63 to 32 of the written register, as `t32_reg_end` does. -/
syntax "t32_reg_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_reg_bwd [$xs,*]) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
      true_and]
    simp (disch := first | omega | t32_lt) only [setX_keep]
    simp only [setLow_r]
    congr 1
    apply Eq.symm
    apply state_eq
    simp (disch := omega) only [x_mod, low_r, $xs,*]))

/-- The harness's test for the pattern of B T3 fails on an opcode whose bits 31 to 27 are not
11110. -/
theorem mask_top {w : Nat} (hw : w < 4294967296) (h : w / 134217728 ≠ 30) :
    ¬(w &&& 4160802816 = 4026564608) := by
  intro heq
  have h1 := congrArg (· >>> 27) heq
  simp only [Nat.shiftRight_and_distrib] at h1
  rw [show (4160802816 : Nat) >>> 27 = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (4026564608 : Nat) >>> 27 = 30 from rfl, Nat.shiftRight_eq_div_pow] at h1
  omega

/-- Proves a side condition of a path of a trace: a bound of a value that a declaration chose, a
condition on the fields, a comparison of signed numbers, the harness's test of the opcode, or the
equation of `FeatureImpl` with the profile's. -/
macro "t32_side" : tactic => `(tactic| first
  | omega
  | (simp only [LeanExe.A64.Isla.sint]; omega)
  | exact x_lt_pow _ _
  | exact Nat.lt_trans (UInt32.toNat_lt _) (by decide)
  | (split <;> omega)
  | (apply mask_top <;> omega)
  | rfl)

theorem ofNat_four : UInt32.ofNat 4 = 4 := rfl

theorem ofNat_zero32 : UInt32.ofNat 0 = 0 := rfl

/-- The N flag of a result, as the trace computes it from bit 31. -/
theorem nflag32 (r : UInt32) : (r >>> 31 == 1) = decide (r.toNat / 2147483648 % 2 = 1) := by
  have h : (r >>> 31).toNat = r.toNat / 2147483648 := by
    rw [UInt32.toNat_shiftRight, show (31 : UInt32).toNat % 32 = 31 from rfl,
      Nat.shiftRight_eq_div_pow]
  have hr : r.toNat < 4294967296 := r.toNat_lt
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj, h,
    show (1 : UInt32).toNat = 1 from rfl]
  omega

/-- The Z flag of a result. -/
theorem zflag32 (r : UInt32) : (r == 0) = decide (r.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj,
    show (0 : UInt32).toNat = 0 from rfl]

theorem toNat_zero_iff (a : UInt32) : a.toNat = 0 ↔ a = 0 := by
  rw [← UInt32.toNat_inj, show (0 : UInt32).toNat = 0 from rfl]

/-- A flag read as a bit and written back. -/
theorem bit_eq_one (b : Bool) : decide ((if b = true then 1 else 0) = 1) = b := by
  cases b <;> rfl

/-- Proves that the outcome at the end of a path of the trace of a form that writes one register
of r0 to r7 and, when its S bit is set, the flags N and Z from the result and C and V from the
model, is `exec`'s.  The lemmas in brackets state the trace's value of the result on the low words
of the registers as the `toNat` of the model's result. -/
syntax "t32_nz_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_nz_end [$xs,*]) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
      true_and]
    simp (disch := first | omega | t32_lt) only [setX_low, setX_keep]
    apply exists_mach
    · simp (disch := omega) only [setLow_r, x_mod, low_r, $xs,*] at *
      simp -failIfUnchanged only [toNat_zero_iff] at *
      simp -failIfUnchanged only [State.result, State.setNZCV, State.setR, ↓reduceIte,
        State.mk.injEq, nflag32, zflag32, toNat_zero_iff, bit_eq_one, ofNat_toNat32, ofNat_four,
        ofNat_zero32, UInt32.toNat_zero, Nat.zero_div, Nat.zero_mod, Nat.reduceEqDiff, decide_true,
        decide_false, true_and, and_true, *]
    · rfl
    · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path of the trace that
keeps bits 63 to 32 of the written register, as `t32_nz_end` does. -/
syntax "t32_nz_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| t32_nz_bwd [$xs,*]) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
      true_and]
    simp (disch := first | omega | t32_lt) only [setX_keep]
    congr 1
    simp (disch := omega) only [setLow_r, x_mod, low_r, $xs,*] at *
    simp -failIfUnchanged only [toNat_zero_iff] at *
    simp -failIfUnchanged only [State.result, State.setNZCV, State.setR, ↓reduceIte,
      State.mk.injEq, nflag32, zflag32, toNat_zero_iff, bit_eq_one, ofNat_toNat32, ofNat_four,
      ofNat_zero32, UInt32.toNat_zero, Nat.zero_div, Nat.zero_mod, Nat.reduceEqDiff, decide_true,
      decide_false, true_and, and_true, *]))

/-- Proves that registers `σ'` that set the registers of the list `W` in `σ` agree with `σ`
outside `W`. -/
macro "t32_frame" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [Sys.set_apply, hr, ↓reduceIte]))

open Lean Elab Tactic in
/-- Runs the tactics without recording info trees, as `Register.lean` of the A64 check does. -/
elab "t32_quiet " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

end LeanExe.M7.Isla
