import LeanExe.A64.Isla.Trace
import LeanExe.A64.Encode

/-!
Checks of the model's `exec` against Isla's traces of the Armv9.4-A Sail model.  `Agrees` states
what the footprint of one instruction form establishes for one value of the form's fields and one
state of the model, and the theorem of a form quantifies over both.

The footprint's opcode, the fixed bits and the named fields that `isla-footprint -i` took, which
`isla_trace%` reads from the trace's opcode file, must have 32 bits and the fields of the
footprint's header, and the word that it gives for the fields' values must decode to the
instruction.  For every `σ` that agrees with the profile `π` on the registers outside the model
that the trace reads, at the accessor paths at which it reads them, whenever `exec` gives a state
`s'`, the outcomes of the trace from the state and `σ` are exactly `s'` with some `σ'` that
differs from `σ` only at the registers `W`.  The statement covers the whole effect of the
instruction's decode and execution: the model's state, with the program counter, memory, and
output, and the registers outside the model that they change.  `σ'` leaves out the effects of
`__InstructionExecute` around the decode and execution, which reading 4 of `Trace.lean` lists,
among them those on `_EDSCR`, `MDCCSR_EL0`, `InGuardedPage`, and `PSTATE.BTYPE`.  The trace's
`assume` events, which Isla records for the configuration's constraints, end a path in `fail` when
false, so the theorem of such a trace carries the constraint as a premise.  A path that Isla
dropped leaves the states that would take it without an outcome, which makes `Agrees` false for
them whenever `exec` succeeds there.

The same statement serves every form.  A form whose `exec` never fails, such as `ADD`, gets the
equivalence for every state.  For a load or a store, `exec` fails outside Normal memory, at the
UART other than by a byte store, and on a misaligned stack pointer, and the trace's paths of those
states, such as the exception entry of the alignment fault, need no counterpart.  A branch writes
`_PC` and sets `__BranchTaken`, and the program-counter rule of `finish` keeps the written value,
so the outcome holds `exec`'s target.  The premise on `σ` names accessor paths, so a theorem fixes
only the fields of a register that its trace reads, such as `PSTATE.EL`.

The profiles `tcg` and `kvm` of `Profile.lean` hold the registers outside the model of the traces
of `tests/isla/traces.sh`.  `Agrees.of_reads` carries a theorem to any profile that agrees with
its profile on the registers that the trace reads, so a form whose two traces are equal needs one
proof of the trace's paths.  `isla_reads` evaluates the registers that a trace reads under the
profiles, for the premise of `Agrees` and for the condition of `Agrees.of_reads`.

`isla_fwd` takes a hypothesis that a path ends in an outcome through the trace, and `isla_bwd`
builds one path from the values of the declared variables.  Both evaluate each event with
`isla_simp`, and the arithmetic that remains is linear arithmetic on natural numbers for `omega`.
A read at a symbolic index evaluates Isla's chain of 30 `ite` expressions to the nested `cond`
that `pick` describes.  The read's rule equates the chain with the indexed register, an equation
with which the forward direction rewrites, and `chain_eq`, a rule of `isla_simp`, folds the chain
over the state's registers into the indexed register in the backward direction.
-/

namespace LeanExe.A64.Isla

/-- The footprint `F` describes the instruction `i` for the fields `f` from the state `s`: the
header names the fields of `F`'s opcode, the opcode has 32 bits, its word decodes to `i`, and for
every `σ` that agrees with the profile `π` on the registers that the trace reads, if `exec` gives
`s'`, the outcomes of the trace are exactly `s'` with registers `σ'` that differ from `σ` only at
the registers `W`. -/
def Agrees (P : Platform) (π : Sys) (W : List String) (F : Footprint) (f : Fields) (i : Instr)
    (s : State) : Prop :=
  F.segments.map (fun g => (g.name, g.width)) = F.opcode.fields ∧
  F.opcode.width = 32 ∧
  decode (.ofNat (F.opcode.word f)) = some i ∧
  ∀ σ : Sys, (∀ q ∈ F.trace.reads, σ.get q.1 q.2 = π.get q.1 q.2) →
    ∀ s', exec P i s = some s' →
      ∃ σ', (∀ o, F.Run P f s σ o ↔ o = .done s' σ') ∧ ∀ r, r ∉ W → σ' r = σ r

/-- `Agrees` under the profile `π` holds under a profile `π'` that agrees with `π` on the registers
that the trace reads. -/
theorem Agrees.of_reads {P : Platform} {π π' : Sys} {W : List String} {F : Footprint}
    {f : Fields} {i : Instr} {s : State}
    (h : ∀ q ∈ F.trace.reads, π'.get q.1 q.2 = π.get q.1 q.2) (a : Agrees P π W F f i s) :
    Agrees P π' W F f i s :=
  ⟨a.1, a.2.1, a.2.2.1, fun σ hσ => a.2.2.2 σ fun q hq => (hσ q hq).trans (h q hq)⟩

theorem Vars.set_apply (ρ : Vars) (x : Nat) (v : Val) (y : Nat) :
    ρ.set x v y = if y = x then some v else ρ y := rfl

theorem Sys.set_apply (σ : Sys) (r : String) (v : Val) (q : String) :
    σ.set r v q = if q = r then some v else σ q := rfl

theorem Sys.get_set (σ : Sys) (r : String) (v : Val) (q : String) (al : List String) :
    (σ.set r v).get q al = if q = r then acc al v else σ.get q al := by
  unfold Sys.get Sys.set
  split <;> rfl

theorem toNat_lt (a : UInt64) : a.toNat < 2 ^ 64 := a.toNat_lt_size

theorem toNat_mod (a : UInt64) : a.toNat % 18446744073709551616 = a.toNat :=
  Nat.mod_eq_of_lt a.toNat_lt_size

theorem toNat_mod128 (a : UInt64) :
    a.toNat % 340282366920938463463374607431768211456 = a.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans (toNat_lt a) (by decide))

/-- `Nat.add_zero` with a proof that is not definitional.  `simp` applies `Nat.add_zero`, a `rfl`
theorem, without a proof step, so the kernel checks `x + 0 = x` by unfolding.  For the table's
address in the walk of a store at the UART, a remainder of a 128-bit term, that check ran for more
than nine minutes and took 8 GiB. -/
theorem nat_add_zero (n : Nat) : n + 0 = n := by omega

/-- SMT-LIB's `bvsdiv` of 128 bits on operands below the sign bit. -/
theorem sdiv_128 {a b : Nat} (ha : a < 170141183460469231731687303715884105728)
    (hb : b < 170141183460469231731687303715884105728) (hb0 : 0 < b) : sdiv 128 a b = a / b := by
  have h : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
  unfold sdiv udiv
  rw [h, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A flag or other Boolean as the bit that a trace reads is below 2. -/
theorem bit_lt (b : Bool) : (if b = true then 1 else 0) < 2 := by
  cases b <;> decide

/-- The word of a footprint's opcode decodes to the instruction whose encoding it equals. -/
theorem decode_word {F : Footprint} {f : Fields} {i : Instr} (h : F.opcode.word f = encodeNat i) :
    decode (.ofNat (F.opcode.word f)) = some i := by
  rw [h]
  exact decode_encode i

open Lean Elab Tactic in
/-- Runs the tactics without recording info trees.  The command-line driver keeps the info tree of
every command of a file until it ends, and the info tree of each step of a walk holds its goals and
metavariable contexts.  Without it, the elaboration of the register forms' theorems takes 9.5
GiB. -/
elab "without_info " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

theorem fin_mod {k : Nat} (n : Fin k) {m : Nat} (h : k ≤ m) : n.val % m = n.val :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le n.isLt h)

theorem fin_div {k : Nat} (n : Fin k) {m : Nat} (h : k ≤ m) : n.val / m = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le n.isLt h)

/-- `cond (decide (k = j)) (f j) (... (cond (decide (k = 1)) (f 1) (f 0)))`, the value of the
chain that Isla builds for a read at the symbolic index `k`, as `isla_simp` evaluates it. -/
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

/-- The chain of a read at the index `k` below 31 is register `k`. -/
theorem chain_regs {s : State} {k : Nat} (hk : k < 31) :
    pick k (fun j => (regAt s j).toNat) 30 = (regAt s k).toNat := pick_eq _ _ _ (by omega)

/-- `cond (decide (k = 30)) (s.regs 30).toNat (... (s.regs 0).toNat)`, the chain of a read at
the index `k` from the registers of the state `s`, as `isla_simp` writes it. -/
syntax "chain% " term:max term:max : term
macro_rules
  | `(chain% $s $k) => do
    let mut t ← `(UInt64.toNat (State.regs $s 0))
    for j in [1:31] do
      let lit := Lean.Syntax.mkNumLit (toString j)
      t ← `(cond (decide ($k = $lit)) (UInt64.toNat (State.regs $s $lit)) $t)
    return t

/-- The chain of a read at the index `k` below 31 from the registers of `s` is register `k`, in
the form in which `isla_simp` rewrites it. -/
theorem chain_eq {s : State} {k : Nat} (hk : k < 31) : chain% s k = (regAt s k).toNat :=
  chain_regs hk

/-- Evaluates the expressions, values, and register accesses of a trace's events: string, natural
number, and constructor comparisons of literals, lookups of variables and registers, the operators
on the bit vectors that result, the reduction of `a % b` to `a` and of `a / b` to 0 for the value
`a` of a field or a register below `b`, and the chain of a read from the state's registers.
`omega` proves the side conditions of these rules.  The lemmas in brackets join the set, among
them the equations of the premise on the registers outside the model. -/
syntax "isla_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| isla_simp [$xs,*] $(loc)?) => `(tactic| simp -failIfUnchanged (disch := omega) only [
      Exp.eval, Base.eval, RVal.eval, Base.evalAll, Base.evalFields, Unop.apply, Binop.apply,
      Binop.arith, lshr, regGet, regSet, part, gpr, gprs, partGet, partPut, bit, acc, upd, gprVals,
      Trace.RunSome, Vars.set_apply, Sys.set_apply, Sys.get_set, List.lookup, Option.bind,
      Option.map, Option.getD, Val.bits.injEq, Val.bool.injEq, Val.enum.injEq, Val.struct.injEq,
      Val.vec.injEq, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, eq_self_iff_true, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_not, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or,
      Bool.or_false, Bool.false_or, and_true, true_and, and_self, ne_eq, not_true_eq_false,
      not_false_eq_true, false_and, and_false, or_false, false_or, Nat.pow_zero, Nat.div_one,
      Nat.mod_mod, Nat.add_zero, Nat.zero_add, Nat.zero_mul, fin_mod, fin_div, toNat_mod,
      Fin.is_lt, ↓reduceIte, ↓reduceDIte, reduceCtorEq, String.reduceEq,
      String.reduceNe, String.reduceBEq, String.reduceAppend, String.reduceToList, Char.reduceBEq,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
      Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq,
      Bool.cond_true, Bool.cond_false, decide_true, decide_false, chain_eq, $xs,*] $(loc)?)

/-- Turns a statement over the registers that a footprint's trace reads, such as the premise of
`Agrees` on `σ` or the condition of `Agrees.of_reads`, into one statement per read: the lemmas in
brackets unfold the footprint and evaluate the profiles. -/
syntax "isla_reads " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| isla_reads [$xs,*] $(loc)?) => `(tactic| simp only [Footprint.trace, Trace.reads,
      Trace.readsAll, Event.reads, Exp.regs, List.filter, part, gpr, gprs, List.lookup,
      Option.map, Option.isNone, Option.bind, acc, String.reduceEq, String.reduceBEq,
      ↓reduceIte, Bool.false_eq_true, reduceCtorEq, List.nil_append, List.cons_append,
      List.append_nil, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      forall_const, and_true, $xs,*] $(loc)?)

/-- Takes the hypothesis `h`, that a path of a trace ends in an outcome, through the trace: it
unfolds and evaluates one event at a time with `isla_simp` and the lemmas in brackets, splits the
disjunctions of `cases`, takes apart the existentials of `declare-const` and the conjunctions of
reads and asserts, substitutes each variable by the value that a read gives, rewrites with the
equation of `read_register_from_vector` between Isla's chain and the indexed register, and proves
the condition of each `assume` with the tactic after `using`.  It stops when `h` names the
outcome. -/
syntax "isla_fwd " ident " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| isla_fwd $h using $d with [$xs,*]) => `(tactic| repeat' (first
      | (rw [Trace.Run] at $h:ident; isla_simp [$xs,*] at $h:ident)
      | (guard_hyp $h : False; exact False.elim $h)
      | (guard_hyp $h : Or _ _; rcases $h:ident with $h:ident | $h:ident)
      | (guard_hyp $h : Exists _; obtain ⟨x, $h:ident⟩ := $h:ident)
      | (guard_hyp $h : And _ _
         obtain ⟨x, $h:ident⟩ := $h:ident
         first
           | subst x
           | (guard_hyp x : _ = UInt64.toNat (regAt _ _)
              rw [x] at $h:ident
              isla_simp [$xs,*] at $h:ident)
           | skip)
      | (guard_hyp $h : @Eq Outcome _ _; subst $h:ident)
      | focus (rw [ite_eq_left] at $h:ident; rotate_left; ($d))))

/-- Builds a path of a trace up to its next `declare-const` of a free variable or its end: it
unfolds and evaluates one event at a time with `isla_simp` and the lemmas in brackets, which
include the facts that choose the branch of each `cases`, leaves the condition of each read or
assert as a later goal, and proves the condition of each `assume` with the tactic after
`using`. -/
syntax "isla_walk " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| isla_walk using $d with [$xs,*]) => `(tactic| repeat (first
      | (rw [Trace.Run]; isla_simp [$xs,*])
      | (guard_target = And _ _; apply And.intro; rotate_left)
      | focus (rw [ite_eq_left]; rotate_left; ($d))))

/-- Builds a path of a trace with `isla_walk`, giving the declared variables the values of the
list in order. -/
syntax "isla_bwd " "[" term,* "]" " using " tacticSeq " with "
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| isla_bwd [] using $d with [$xs,*]) => `(tactic| (isla_walk using ($d) with [$xs,*]))
  | `(tactic| isla_bwd [$w] using $d with [$xs,*]) => `(tactic| (
      isla_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      isla_walk using ($d) with [$xs,*]))
  | `(tactic| isla_bwd [$w, $ws,*] using $d with [$xs,*]) => `(tactic| (
      isla_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      isla_bwd [$ws,*] using ($d) with [$xs,*]))

/-- Builds a path of a trace with `isla_bwd`, giving the 31 declared variables that hold Isla's
values of `R0` to `R30` the values of the registers of the state `s`. -/
syntax "isla_gprs " term " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| isla_gprs $s using $d with [$xs,*]) => `(tactic| isla_bwd [
      (State.regs $s 0).toNat, (State.regs $s 1).toNat, (State.regs $s 2).toNat,
      (State.regs $s 3).toNat, (State.regs $s 4).toNat, (State.regs $s 5).toNat,
      (State.regs $s 6).toNat, (State.regs $s 7).toNat, (State.regs $s 8).toNat,
      (State.regs $s 9).toNat, (State.regs $s 10).toNat, (State.regs $s 11).toNat,
      (State.regs $s 12).toNat, (State.regs $s 13).toNat, (State.regs $s 14).toNat,
      (State.regs $s 15).toNat, (State.regs $s 16).toNat, (State.regs $s 17).toNat,
      (State.regs $s 18).toNat, (State.regs $s 19).toNat, (State.regs $s 20).toNat,
      (State.regs $s 21).toNat, (State.regs $s 22).toNat, (State.regs $s 23).toNat,
      (State.regs $s 24).toNat, (State.regs $s 25).toNat, (State.regs $s 26).toNat,
      (State.regs $s 27).toNat, (State.regs $s 28).toNat, (State.regs $s 29).toNat,
      (State.regs $s 30).toNat] using $d with [$xs,*])

theorem setRegAt_pc (s : State) (i : Nat) (v : UInt64) : (setRegAt s i v).pc = s.pc := by
  unfold setRegAt
  split <;> rfl

theorem setRegAt_lt {s : State} {i : Nat} (h : i < 31) (v : UInt64) :
    setRegAt s i v = { s with regs := fun j => if j.val = i then v else s.regs j } :=
  ite_eq_left h

theorem setRegAt_31 {s : State} {i : Nat} (h : i = 31) (v : UInt64) : setRegAt s i v = s :=
  ite_eq_right (by omega)

theorem setX_eq_setRegAt (s : State) (d : Fin 32) (v : UInt64) :
    s.setX d v = setRegAt s d.val v := rfl

theorem x_lt {s : State} {n : Fin 32} (h : n.val < 31) : s.x n = regAt s n.val := by
  unfold State.x regAt
  rw [dite_eq_left h, dite_eq_left h]

theorem x_31 {s : State} {n : Fin 32} (h : n.val = 31) : s.x n = 0 := by
  unfold State.x
  rw [dite_eq_right (by omega)]

/-- The model's read of a register below 31, where register 31 is the stack pointer, as the
vector primitive reads it. -/
theorem xsp_lt {s : State} {n : Fin 32} (h : n.val < 31) : s.xsp n = regAt s n.val := by
  unfold State.xsp regAt
  rw [dite_eq_left h, dite_eq_left h]

/-- The model's read of register 31 as the stack pointer. -/
theorem xsp_31 {s : State} {n : Fin 32} (h : n.val = 31) : s.xsp n = s.sp := by
  unfold State.xsp
  rw [dite_eq_right (by omega)]

/-- Proves that the outcome at the end of a path of the trace of a form that writes one general
register, `ADD (register)` among them, is `exec`'s: it reads `__BranchTaken`, reduces the reads
and writes of registers at an index with the path's facts on the fields, and compares the written
values as natural numbers. -/
macro "gpr_end" : tactic => `(tactic| (
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
    true_and]
  simp (disch := omega) only [x_lt, x_31, setX_eq_setRegAt, setRegAt_lt, setRegAt_31,
    State.mk.injEq, and_true, true_and]
  try (funext j; split <;> (try rfl))
  try (apply UInt64.toNat_inj.mp
       simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_zero, toNat_mod,
         Nat.zero_add, Nat.add_zero, Nat.reducePow, Nat.mod_mod] <;> omega)))

/-- Proves that registers `σ'` that set the registers of the list `W` in `σ` agree with `σ`
outside `W`. -/
macro "frame_end" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [Sys.set_apply, hr, ↓reduceIte]))

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

/-- Reads `__BranchTaken` at the end of a path and reduces the equation of two outcomes to the
equation of their states. -/
macro "done_end" : tactic => `(tactic|
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
    true_and])

end LeanExe.A64.Isla
