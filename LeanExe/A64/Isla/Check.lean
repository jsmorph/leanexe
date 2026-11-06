import LeanExe.A64.Isla.Trace
import LeanExe.A64.Encode

/-!
Checks of the model's `exec` against Isla's traces of the Armv9.4-A Sail model.  `Agrees` states
what the footprint of one instruction form establishes for one value of the form's fields and one
state of the model, and the theorem of a form quantifies over both.

The opcode, the fixed bits and the named fields that `isla-footprint -i` took, is written here as
an `Opcode`, whose fields must be those of the footprint's header, and the word that the opcode
gives for the fields' values must decode to the instruction.  For every `σ` that agrees with the
profile `π` on the registers outside the model that the trace reads, at the accessor paths at
which it reads them, whenever `exec` gives a state `s'`, the outcomes of the trace from the state
and `σ` are exactly `s'` with some `σ'` that differs from `σ` only at the registers `W`.  The
statement covers the instruction's whole effect: the model's state, with the program counter,
memory, and output, and the registers outside the model that the instruction changes.  The trace's
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

`profile` gives the registers of the startup's configuration, the arguments of
`tests/isla/dev/add.sh`, that the traces read: Isla's flag for vector reads of the general
registers and the decoder's `SEE`.  `config` gives those of the configuration of
`tests/isla/traces.sh`, under which the traces of `ADD X3, X4, X5`, `SUBS X3, X4, X5`, and
`LDR X3, [X4, #24]` ran with concrete opcodes, with the values that it leaves UNKNOWN as the
fields of `Unknown`.

`isla_fwd` takes a hypothesis that a path ends in an outcome through the trace, and `isla_bwd`
builds one path from the values of the declared variables.  Both evaluate each event with
`isla_simp`, and the arithmetic that remains is linear arithmetic on natural numbers for `omega`.
A read at a symbolic index evaluates Isla's chain of 30 `ite` expressions to the nested `cond`
that `pick` describes.  The read's rule equates the chain with the indexed register, an equation
with which the forward direction rewrites, and `chain_eq`, a rule of `isla_simp`, folds the chain
over the state's registers into the indexed register in the backward direction.
-/

namespace LeanExe.A64.Isla

/-- A piece of an opcode as `isla-footprint -i` takes it: `w` fixed bits of value `n`, or the
field `name` of `w` bits. -/
inductive Piece where
  | bits (w n : Nat)
  | field (name : String) (w : Nat)

/-- An opcode, its pieces from the most significant. -/
abbrev Opcode := List Piece

/-- The names and widths of the fields of an opcode, in order. -/
def Opcode.fields : Opcode → List (String × Nat)
  | [] => []
  | .bits _ _ :: p => Opcode.fields p
  | .field name w :: p => (name, w) :: Opcode.fields p

/-- The value of the word of the opcode `p` for the fields `f`, after the bits `acc`. -/
def Opcode.wordFrom (f : Fields) (acc : Nat) : Opcode → Nat
  | [] => acc
  | .bits w n :: p => Opcode.wordFrom f (acc * 2 ^ w + n) p
  | .field name w :: p => Opcode.wordFrom f (acc * 2 ^ w + (f.lookup name).getD 0) p

/-- The value of the word of the opcode `p` for the fields `f`. -/
def Opcode.word (p : Opcode) (f : Fields) : Nat := Opcode.wordFrom f 0 p

/-- The footprint `F` of the opcode `p` describes the instruction `i` for the fields `f` from the
state `s`: the header names the opcode's fields, the opcode's word decodes to `i`, and for every
`σ` that agrees with the profile `π` on the registers that the trace reads, if `exec` gives `s'`,
the outcomes of the trace are exactly `s'` with registers `σ'` that differ from `σ` only at the
registers `W`. -/
def Agrees (P : Platform) (π : Sys) (W : List String) (p : Opcode) (F : Footprint) (f : Fields)
    (i : Instr) (s : State) : Prop :=
  F.segments.map (fun g => (g.name, g.width)) = p.fields ∧
  decode (.ofNat (p.word f)) = some i ∧
  ∀ σ : Sys, (∀ q ∈ F.trace.reads, σ.get q.1 q.2 = π.get q.1 q.2) →
    ∀ s', exec P i s = some s' →
      ∃ σ', (∀ o, F.Run P f s σ o ↔ o = .done s' σ') ∧ ∀ r, r ∉ W → σ' r = σ r

/-- The registers outside the model that the startup's configuration fixes and the traces read:
`__isla_vector_gpr`, which `-I` sets, and `SEE`, the decoder's integer -1. -/
def profile : Sys
  | "__isla_vector_gpr" => some (.bool true)
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | _ => none

/-- The values that the configuration of `tests/isla/traces.sh` leaves UNKNOWN: six system
registers and the last element of `FeatureImpl`, which names no feature. -/
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
integer -1. -/
def config (u : Unknown) : Sys
  | "__isla_vector_gpr" => some (.bool false)
  | "__monomorphize_reads" => some (.bool false)
  | "SPESampleInFlight" => some (.bool false)
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

theorem Vars.set_apply (ρ : Vars) (x : Nat) (v : Val) (y : Nat) :
    ρ.set x v y = if y = x then some v else ρ y := rfl

theorem Sys.set_apply (σ : Sys) (r : String) (v : Val) (q : String) :
    σ.set r v q = if q = r then some v else σ q := rfl

theorem Sys.get_set (σ : Sys) (r : String) (v : Val) (q : String) (al : List String) :
    (σ.set r v).get q al = if q = r then acc al v else σ.get q al := by
  unfold Sys.get Sys.set
  split <;> rfl

theorem profile_get (r : String) (al : List String) :
    profile.get r al = (profile r).bind (acc al) := rfl

theorem config_get (u : Unknown) (r : String) (al : List String) :
    (config u).get r al = (config u r).bind (acc al) := rfl

theorem toNat_lt (a : UInt64) : a.toNat < 2 ^ 64 := a.toNat_lt_size

theorem toNat_mod (a : UInt64) : a.toNat % 18446744073709551616 = a.toNat :=
  Nat.mod_eq_of_lt a.toNat_lt_size

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

/-- Turns the premise `h` of `Agrees` on the registers that the trace of the footprint reads
into equations, one per read, whose right sides are the profile's values: the lemmas in brackets
unfold the footprint and evaluate the profile. -/
syntax "isla_premise " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| isla_premise $h [$xs,*]) => `(tactic| simp only [Footprint.trace, Trace.reads,
      Trace.readsAll, Event.reads, Exp.regs, List.filter, part, gpr, gprs, List.lookup,
      Option.map, Option.isNone, Option.bind, acc, String.reduceEq, String.reduceBEq,
      ↓reduceIte, Bool.false_eq_true, reduceCtorEq, List.nil_append, List.cons_append,
      List.append_nil, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      forall_const, and_true, $xs,*] at $h:ident)

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

/-- The footprint of `ADD Xd, Xn, Xm` with Rd, Rn, and Rm symbolic, from `tests/isla/dev/add.sh`
in the startup's configuration. -/
def addFp : Footprint := isla_trace% "tests/isla/dev/add.trace"

/-- `10001011000 Rm:5 000000 Rn:5 Rd:5`, the opcode of `tests/isla/dev/add.sh`. -/
def addOpcode : Opcode :=
  [.bits 11 0b10001011000, .field "Rm" 5, .bits 6 0, .field "Rn" 5, .field "Rd" 5]

/-- The fields of `ADD Xd, Xn, Xm` for the registers `d`, `n`, and `m`. -/
def addFields (d n m : Fin 32) : Fields := [("Rd", d.val), ("Rn", n.val), ("Rm", m.val)]

/-- Proves that registers `σ'` that set the registers of the list `W` in `σ` agree with `σ`
outside `W`. -/
macro "frame_end" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [Sys.set_apply, hr, ↓reduceIte]))

set_option maxHeartbeats 4000000 in
/-- The footprint of `ADD Xd, Xn, Xm` agrees with `exec` for every register number, with register
31 the zero register, and every state.  The backward direction builds the path of each of the 8
cases of register 31 among `d`, `n`, and `m`, and the 706 events that the two directions evaluate
take more than the default budget of heartbeats. -/
theorem addReg (P : Platform) (d n m : Fin 32) (s : State) :
    Agrees P profile ["SEE", "__BranchTaken"] addOpcode addFp (addFields d n m) (.addReg d n m)
      s := by
  refine ⟨by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : addOpcode.word (addFields d n m) = encodeNat (.addReg d n m) := by
      simp only [Opcode.word, Opcode.wordFrom, addOpcode, addFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_premise hσ [addFp, profile_get, profile]
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 14),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [addFp, Footprint.vars, addFields, List.foldl, List.lookup, String.reduceBEq,
        Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals gpr_end
    · subst h
      unfold Footprint.Run
      simp only [addFp, Footprint.vars, addFields, List.foldl, List.lookup, String.reduceBEq,
        Option.getD]
      by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
        try isla_gprs s using omega with [hσ, hn, hm, hd]
      all_goals first
        | exact toNat_lt _
        | gpr_end
        | (simp only [sint]; omega)
        | omega

/-! The traces of `tests/isla/traces.sh`, of one encoding each, in the configuration `config`. -/

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

/-- The footprint of `ADD X3, X4, X5`. -/
def add1Fp : Footprint := isla_trace% "tests/isla/add.trace"

/-- The footprint of `SUBS X3, X4, X5`. -/
def subsFp : Footprint := isla_trace% "tests/isla/subs.trace"

/-- The footprint of `LDR X3, [X4, #24]`. -/
def ldrFp : Footprint := isla_trace% "tests/isla/ldr.trace"

/-- Reads `__BranchTaken` at the end of a path and reduces the equation of two outcomes to the
equation of their states. -/
macro "done_end" : tactic => `(tactic|
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
    true_and])

/-- Reduces an equation between two functions that update register 3 of the same registers to
the equation between the values written. -/
macro "regs_end" : tactic => `(tactic| (
  funext j
  by_cases hj : j = 3 <;> simp only [hj, eq_self_iff_true, ↓reduceIte]))

/-- Proves that the state at the end of the trace of `ADD X3, X4, X5` is `exec`'s. -/
macro "add_end" : tactic => `(tactic| (
  done_end
  simp only [setX_eq (d := 3) (i := 3) rfl, x_eq (d := 4) (i := 4) rfl,
    x_eq (d := 5) (i := 5) rfl, State.mk.injEq, eq_self_iff_true, and_true]
  regs_end
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add]
  omega))

/-- The trace of `ADD X3, X4, X5` agrees with `exec` from every state. -/
theorem add (P : Platform) (u : Unknown) (s : State) :
    Agrees P (config u) ["SEE", "__BranchTaken"] [.bits 32 0x8B050083] add1Fp []
      (.addReg 3 4 5) s := by
  refine ⟨rfl, by decide, fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_premise hσ [add1Fp, config_get, config]
  have := toNat_lt (s.regs 4)
  have := toNat_lt (s.regs 5)
  refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 14),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [add1Fp, Footprint.vars, List.foldl] at h
    isla_fwd h using omega with [hσ]
    add_end
  · subst h
    unfold Footprint.Run
    simp only [add1Fp, Footprint.vars, List.foldl]
    isla_bwd [s.pc.toNat, (s.regs 4).toNat, (s.regs 5).toNat] using omega with [hσ]
    all_goals first
      | exact toNat_lt _
      | (apply Eq.symm; add_end)

/-- Proves that the state at the end of the trace of `SUBS` from the state `s` is `exec`'s.  The
flags of the trace are the bits of a word of 4 bits, and its V flag compares the sign-extended
result with the sum of the sign-extended operands, which `omega` decides once the signs of the
operands and the result and the carry are known. -/
syntax "subs_end " term : tactic
macro_rules
  | `(tactic| subs_end $s) => `(tactic| (
    done_end
    simp only [Bool.cond_eq_ite, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    simp only [State.subs, setX_eq (d := 3) (i := 3) rfl, x_eq (d := 4) (i := 4) rfl,
      x_eq (d := 5) (i := 5) rfl, vflag]
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
    Agrees P (config u) ["SEE", "__BranchTaken"] [.bits 32 0xEB050083] subsFp []
      (.subsReg 3 4 5) s := by
  refine ⟨rfl, by decide, fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_premise hσ [subsFp, config_get, config]
  have := toNat_lt (s.regs 4)
  have := toNat_lt (s.regs 5)
  refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 17),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [subsFp, Footprint.vars, List.foldl] at h
    isla_fwd h using omega with [hσ]
    subs_end s
  · subst h
    unfold Footprint.Run
    simp only [subsFp, Footprint.vars, List.foldl]
    isla_bwd [s.pc.toNat, (s.regs 4).toNat, (s.regs 5).toNat] using omega with [hσ]
    all_goals first
      | exact toNat_lt _
      | (apply Eq.symm; subs_end s)

/-- Proves that the state at the end of the trace of `LDR` is `exec`'s: the trace writes to X3
the eight bytes at an address that the constraint on `X4 + 24` makes equal to it. -/
macro "ldr_end" : tactic => `(tactic| (
  done_end
  simp only [setX_eq (d := 3) (i := 3) rfl, load64_eq, State.mk.injEq, eq_self_iff_true,
    and_true]
  all_goals
    regs_end
    refine congrArg (fun a => UInt64.ofNat (bytes _ a 8)) ?_
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    omega))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The trace of `LDR X3, [X4, #24]` agrees with `exec` from every state whose address `X4 + 24`
is a multiple of 8 in `0x40000000`-`0x7FFFFFFF`, as the trace's constraint states.  The
comparison of `FeatureImpl`, a vector of 259 Booleans, recurses deeper than the default limit,
and the trace's 98 events take more than the default budget of heartbeats. -/
theorem ldr (P : Platform) (u : Unknown) (s : State)
    (ha : (s.regs 4 + 24) &&& 0xFFFFFFFFC0000007 = 0x40000000) :
    Agrees P (config u) ["SEE", "__BranchTaken", "InGuardedPage"] [.bits 32 0xF9400C83] ldrFp []
      (.ldr 3 4 3) s := by
  have h4 := toNat_lt (s.regs 4)
  have hA : ((s.regs 4).toNat + 24) % 18446744073709551616 &&& 18446744072635809799 =
      1073741824 := by
    have := congrArg UInt64.toNat ha
    simpa [UInt64.toNat_and, UInt64.toNat_add] using this
  obtain ⟨h8, h30, hh⟩ := ram hA (Nat.mod_lt _ (by decide))
  have h4' : (s.regs 4).toNat % 18446744073709551616 = (s.regs 4).toNat := Nat.mod_eq_of_lt h4
  have hx : s.xsp 4 + UInt64.ofNat (8 * (3 : Fin 4096).val) = s.regs 4 + 24 := rfl
  refine ⟨rfl, by decide, fun σ hσ s' hs => ?_⟩
  simp only [exec, hx] at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    isla_premise hσ [ldrFp, config_get, config]
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)).set
      "InGuardedPage" (.bool false), fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [ldrFp, Footprint.vars, List.foldl] at h
      isla_fwd h using exact hA with [hσ, features, sysreg]
      ldr_end
    · subst h
      unfold Footprint.Run
      simp only [ldrFp, Footprint.vars, List.foldl]
      isla_bwd [u.feature, (s.regs 4).toNat, s.pc.toNat, u.mair.toNat, u.mair2.toNat,
        u.pir.toNat, u.pire0.toNat, u.sctlr2.toNat, u.s2pir.toNat,
        bytes s.mem (s.regs 4 + 24) 8] using exact hA
        with [hσ, features, sysreg]
      all_goals first
        | exact toNat_lt _
        | exact hA
        | (apply Eq.symm; ldr_end)
        | (rw [← load64_toNat]; exact toNat_lt _)
        | (simp only [h4'] at *; first | exact hh | omega)
        | (simp only [sint, sdiv, udiv, neg]; (repeat' split) <;> omega)
        | (refine congrArg (fun a => bytes _ a 8) ?_
           apply UInt64.toNat_inj.mp
           simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
             Nat.reduceMod]
           omega)
  · cases hs

end LeanExe.A64.Isla
