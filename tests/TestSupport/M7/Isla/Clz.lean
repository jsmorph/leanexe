import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile
import LeanExe.A64.Isla.Walk

/-!
The theorem of `Agrees` for `CLZ Rd, Rm` of `LeanExe/M7/Machine.lean`, from the trace of
`tests/isla/m7/clz` under the profile `sys` of `LeanExe/M7/Isla/Profile.lean`.  The theorem holds
for every register of r0 to r7 in each field, every machine whose program counter plus 4 is below
2^32, every platform, and every sequence of device values.  `tests/isla/m7-theorems.sh` elaborates
the module and prints the axioms of its theorems.

`CountLeadingZeroBits` of the Sail model tests the bits of Rm from bit 31 down and writes 31 less
the position of the first set bit, or 32 when no bit is set, so the trace nests 33 tests, each
followed by the fork of the register write, 66 paths in all, in 384 KB.  A step of a walk over the
trace's literal costs the size of the remaining trace, as the documentation of
`LeanExe/A64/Isla/Walk.lean` states, so the module gives each node of the trace a definition with
`isla_nodes`, `t32_unfold` replaces a path's node by its definition one step at a time, and
`run_congr` and `runSome_congr` keep `simp` out of the trace and the variables of a path.

The walks state each test as `bitAt X c`, a Boolean that `omega` does not read, so that the tests
that a path accumulates do not enter the arithmetic of the walk's side conditions.  At the end of a
path, `lt_of_bit0` turns the cleared bits from bit 31 down into a bound on Rm, one bit at a time,
and `clz32_of` turns that bound and the set bit into the model's `clz32`.  The backward direction
stops at each test, takes the case of the bit, builds the path of a set bit to its end, and
continues on the path of a cleared bit with the tighter bound.  `clz_fwd_paths` and `clz_bwd_path`
state the two directions, which elaborate in parallel, and `clz_agrees` joins them.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode Vars Sys)

/-- The fields of `CLZ Rd, Rm`, whose encoding repeats Rm. -/
def clzFields (d m : Fin 8) : Fields := [("Rm", m.val), ("Rd", d.val), ("Rm2", m.val)]

set_option maxRecDepth 100000 in
/-- The footprint of `CLZ Rd, Rm`. -/
def clzT : Footprint := isla_trace% "tests/isla/m7/clz"

set_option maxRecDepth 100000 in
isla_nodes clzT

set_option maxRecDepth 100000 in
theorem clzT_n0 : clzT.trace = clzT.n0 := rfl

/-- With `attribute [local congr]`, `simp` enters neither the trace of a path nor its variables,
which a walk extends with values that `simp` already evaluated. -/
theorem run_congr {P : Platform} {δ : Nat → UInt32} {len : Nat} {t : LeanExe.A64.Isla.Trace}
    {ρ : Vars} {m m' : Mach} {σ σ' : Sys} {o o' : Outcome} (h2 : m = m') (h3 : σ = σ')
    (h4 : o = o') : run P δ len t ρ m σ o = run P δ len t ρ m' σ' o' := by
  subst h2 h3 h4
  rfl

theorem runSome_congr {P : Platform} {δ : Nat → UInt32} {len : Nat}
    {ts : List LeanExe.A64.Isla.Trace} {ρ : Vars} {m m' : Mach} {σ σ' : Sys} {o o' : Outcome}
    (h2 : m = m') (h3 : σ = σ') (h4 : o = o') :
    runSome P δ len ts ρ m σ o = runSome P δ len ts ρ m' σ' o' := by
  subst h2 h3 h4
  rfl

attribute [local congr] run_congr runSome_congr

open Lean Meta in
/-- The path that `e` states, with its node constant replaced by the node's definition. -/
def unfoldRun (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  unless e.isAppOfArity ``LeanExe.M7.Isla.run 8 do throwError "t32_unfold: not a path"
  let args := e.getAppArgs
  let .const c _ := args[3]! | throwError "t32_unfold: not a node"
  let some v := (← getConstInfo c).value? | throwError "t32_unfold: {c} has no value"
  return mkAppN e.getAppFn (args.set! 3 v)

/-- Replaces the node constant of the path that the goal, or the hypothesis `h`, states by the
node's definition. -/
syntax "t32_unfold" (" at " ident)? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| t32_unfold) => withMainContext do
    let g ← getMainGoal
    let ty ← unfoldRun (← instantiateMVars (← g.getType))
    replaceMainGoal [← g.replaceTargetDefEq ty]
  | `(tactic| t32_unfold at $h:ident) => withMainContext do
    let g ← getMainGoal
    let decl ← getLocalDeclFromUserName h.getId
    let ty ← unfoldRun (← instantiateMVars decl.type)
    replaceMainGoal [← g.replaceLocalDeclDefEq decl.fvarId ty]

/-- Bit `c` of `x`, for `c` a power of 2, as the trace tests it. -/
def bitAt (x c : Nat) : Bool := x / c % 2 == 1

/-- The trace's test of a bit of a word, shifted right by the bit's position. -/
theorem bit_iff (x c : Nat) :
    (x % 4294967296 / c % 2 = 1) = (bitAt (x % 4294967296) c = true) := by
  rw [bitAt, beq_iff_eq]

/-- The trace's test of bit 0 of a word, which the shift by 0 leaves unshifted. -/
theorem bit0_iff (x : Nat) : (x % 4294967296 % 2 = 1) = (bitAt (x % 4294967296) 1 = true) := by
  rw [bitAt, beq_iff_eq, Nat.div_one]

/-- A cleared bit `c` of a value below `2 * c` bounds it by `c`. -/
theorem lt_of_bit0 (c : Nat) {x : Nat} (h : x < 2 * c) (hb : ¬bitAt x c = true) : x < c := by
  apply Nat.lt_of_not_le
  intro hc
  apply hb
  have : x / c = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [bitAt, this]

/-- A set bit `c` of a value bounds it below by `c`. -/
theorem le_of_bit1 {x c : Nat} (h : bitAt x c = true) : c ≤ x := by
  apply Nat.le_of_not_lt
  intro hc
  simp [bitAt, Nat.div_eq_of_lt hc] at h

/-- `clz32` of a word whose highest set bit is bit `31 - v`. -/
theorem clz32_of {x : UInt32} {X v : Nat} (hX : X = x.toNat) (hv : v < 32)
    (h1 : 2 ^ (31 - v) ≤ X) (h2 : X < 2 ^ (32 - v)) : UInt32.ofNat v = clz32 x := by
  subst hX
  have hp : 0 < 2 ^ (31 - v) := Nat.two_pow_pos _
  have hn : x.toNat ≠ 0 := by omega
  have hx : x ≠ 0 := fun h => hn ((toNat_zero_iff x).mpr h)
  have hlog : x.toNat.log2 = 31 - v := by
    apply Nat.le_antisymm
    · have h2' : x.toNat < 2 ^ (31 - v + 1) := by
        rw [show 31 - v + 1 = 32 - v by omega]
        exact h2
      exact Nat.le_of_lt_succ ((Nat.log2_lt hn).mpr h2')
    · exact (Nat.le_log2 hn).mpr h1
  simp only [clz32, hx, ↓reduceIte, hlog, show 31 - (31 - v) = v by omega]

/-- `clz32` of the zero word. -/
theorem clz32_zero {x : UInt32} {X : Nat} (hX : X = x.toNat) (h : X < 1) :
    UInt32.ofNat 32 = clz32 x := by
  have : x = 0 := (toNat_zero_iff x).mp (by omega)
  subst this
  rfl

/-- A write of an X register below 15 that keeps bits 63 to 32 and clears the rest, the trace's
write of 0 that keeps the high word. -/
theorem setX_keep0 (m : Mach) {i : Nat} (h : i < 15) :
    m.setX i (m.x i &&& 18446744069414584320) = { m with s := setLow m.s i (.ofNat 0) } := by
  rw [← Nat.or_zero (m.x i &&& 18446744069414584320), setX_keep m h (by decide)]

/-- Takes the hypothesis `h`, that a path of the trace ends in an outcome, through the trace, as
`t32_fwd` does, unfolding the node of each step and proving the condition of each `assume` with
`omega`. -/
syntax "clz_fwd " ident " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| clz_fwd $h with [$xs,*]) => `(tactic| repeat' (first
      | (t32_unfold at $h:ident
         rw [LeanExe.M7.Isla.run] at $h:ident
         t32_simp [$xs,*] at $h:ident)
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
      | focus (rw [ite_eq_left] at $h:ident; rotate_left; omega)))

theorem or_of_not_left {a b : Prop} (_ : ¬a) (hb : b) : a ∨ b := Or.inr hb

/-- Builds a path of the trace as `t32_walk` does, unfolding the node of each step.  At a fork it
takes the second path when the first event of the first, an assert, is false under the lemmas in
brackets, and it stops at a fork that they do not decide or at a declaration. -/
syntax "clz_walk " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| clz_walk [$xs,*]) => `(tactic| repeat (first
      | (t32_unfold; rw [LeanExe.M7.Isla.run]; t32_simp [$xs,*])
      | (guard_target = Or _ _
         refine or_of_not_left ?_ ?_
         · intro h
           t32_unfold at h
           rw [LeanExe.M7.Isla.run] at h
           t32_simp [$xs,*] at h)
      | (guard_target = And _ _; apply And.intro; rotate_left)
      | focus (rw [ite_eq_left]; rotate_left; omega)))

/-- Builds a path of the trace with `clz_walk`, giving the declared variables the values of the
list in order. -/
syntax "clz_bwd " "[" term,* "]" " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| clz_bwd [] with [$xs,*]) => `(tactic| clz_walk [$xs,*])
  | `(tactic| clz_bwd [$w] with [$xs,*]) => `(tactic| (
      clz_walk [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      clz_walk [$xs,*]))
  | `(tactic| clz_bwd [$w, $ws,*] with [$xs,*]) => `(tactic| (
      clz_walk [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      clz_bwd [$ws,*] with [$xs,*]))

/-- Builds the path through the reads of `R0` to `R30` with the values of the X registers of the
machine `m`, as `t32_gprs` does. -/
syntax "clz_gprs " term:max " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| clz_gprs $m with [$xs,*]) => `(tactic| clz_bwd [
      Mach.x $m 0, Mach.x $m 1, Mach.x $m 2, Mach.x $m 3, Mach.x $m 4, Mach.x $m 5, Mach.x $m 6,
      Mach.x $m 7, Mach.x $m 8, Mach.x $m 9, Mach.x $m 10, Mach.x $m 11, Mach.x $m 12,
      Mach.x $m 13, Mach.x $m 14, Mach.x $m 15, Mach.x $m 16, Mach.x $m 17, Mach.x $m 18,
      Mach.x $m 19, Mach.x $m 20, Mach.x $m 21, Mach.x $m 22, Mach.x $m 23, Mach.x $m 24,
      Mach.x $m 25, Mach.x $m 26, Mach.x $m 27, Mach.x $m 28, Mach.x $m 29, Mach.x $m 30]
      with [$xs,*])

/-- Takes the bound `hlt : X < 2 ^ 32` down through the cleared bits from bit 31, one bit at a time,
as far as the hypotheses of the path give them. -/
syntax "clz_chain " term:max ident : tactic
macro_rules
  | `(tactic| clz_chain $X $hlt) => do
    let mut t ← `(tactic| skip)
    for j in [0:32] do
      let c := Lean.Syntax.mkNumLit (toString (2 ^ (31 - j)))
      t ← `(tactic| ($t:tactic; try have $hlt : $X < $c := lt_of_bit0 $c $hlt (by assumption)))
    return t

/-- Proves that the model's `clz32` of Rm is the value that the path writes, from the path's set
bit and the bound `hlt` below it, or from the bound 1 on the path that finds no set bit.  `hX`
states the trace's word `X` as the model's register. -/
syntax "clz_close " term:max ident : tactic
macro_rules
  | `(tactic| clz_close $hX $hlt) => `(tactic| first
      | exact clz32_zero $hX $hlt
      | (apply clz32_of $hX
         · decide
         · simp only [Nat.reduceSub, Nat.reducePow]
           exact le_of_bit1 (by assumption)
         · simp only [Nat.reduceSub, Nat.reducePow]
           exact $hlt))

/-- Proves that the outcome at the end of a path of the trace is `exec`'s, as `t32_reg_end` does,
with `clz_chain` and `clz_close` for the written value. -/
syntax "clz_end " term:max term:max : tactic
macro_rules
  | `(tactic| clz_end $X $hX) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | t32_lt) only [setX_low, setX_keep, setX_keep0]
    apply exists_mach
    · simp only [setLow_r]
      apply state_eq
      have hlt : $X < 4294967296 := Nat.mod_lt _ (by decide)
      clz_chain $X hlt
      clz_close $hX hlt
    · rfl
    · rfl))

/-- Proves that the outcome of `exec` equals the outcome at the end of the path that keeps bits 63
to 32 of Rd, with the bound `hlt` that the backward direction carries. -/
syntax "clz_bwd_end " term:max ident : tactic
macro_rules
  | `(tactic| clz_bwd_end $hX $hlt) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | t32_lt) only [setX_keep, setX_keep0]
    simp only [setLow_r]
    congr 1
    apply Eq.symm
    apply state_eq
    clz_close $hX $hlt))

/-- Builds the backward direction from the first test of a bit of the word `X` on, with the bound
`hlt : X < 2 ^ 32` and the premise `hσ` on the registers outside the model: at the test of bit
`c`, the case of a set bit builds its path to the end, and the case of a cleared bit lowers the
bound to `c` and walks to the next test.  The path that finds no set bit remains. -/
syntax "clz_forks " term:max term:max ident ident : tactic
macro_rules
  | `(tactic| clz_forks $X $hX $hlt $hσ) => do
    let mut t ← `(tactic| skip)
    for j in [0:32] do
      let c := Lean.Syntax.mkNumLit (toString (2 ^ (31 - j)))
      t ← `(tactic| (
        $t:tactic
        by_cases hb : bitAt $X $c = true
        · refine Or.inl ?_
          clz_bwd [false] with [$hσ:ident, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars, hb]
          all_goals first
            | clz_bwd_end $hX $hlt
            | t32_side
        refine Or.inr ?_
        have $hlt : $X < $c := lt_of_bit0 $c $hlt hb
        clz_walk [$hσ:ident, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars, hb]))
    return t

/-- Unfolds `footRun` of CLZ's footprint for the fields of `d` and `k` into a path from the node
`clzT.n0` with the header's variables bound, at the hypothesis `h` or in the goal. -/
syntax "clz_run " term:max term:max (" at " ident)? : tactic
macro_rules
  | `(tactic| clz_run $d $k at $h) => `(tactic| (
    unfold footRun at $h:ident
    rw [clzT_n0, show clzT.vars (clzFields $d $k) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 3 (Fin.val $k))) 1
        (.bits 3 (Fin.val $d))) 2 (.bits 3 (Fin.val $k)) from rfl,
      show clzT.opcode.width / 8 = 4 from rfl] at $h:ident))
  | `(tactic| clz_run $d $k) => `(tactic| (
    unfold footRun
    rw [clzT_n0, show clzT.vars (clzFields $d $k) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 3 (Fin.val $k))) 1
        (.bits 3 (Fin.val $d))) 2 (.bits 3 (Fin.val $k)) from rfl,
      show clzT.opcode.width / 8 = 4 from rfl]))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of CLZ's trace ends in `exec`'s state, with some high words of X0 to X14. -/
theorem clz_fwd_paths (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d k : Fin 8) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) (σ : Sys)
    (hσ : ∀ q ∈ reads clzT.trace, σ.get q.1 q.2 = (sys u).get q.1 q.2) (o : Outcome)
    (h : footRun P δ clzT (clzFields d k) m σ o) :
    ∃ hi, o = .done
      { m with s := { m.s.setR d (clz32 (m.s.r k)) with pc := m.s.pc + 4 }, hi := hi }
      (((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2882)) := by
  without_info
    have hX : m.x k.val % 4294967296 = (m.s.r k).toNat := by
      rw [x_mod m (by omega), low_r]
    t32_reads [clzT, sys_get, sys] at hσ
    clz_run d k at h
    clz_fwd h with [hσ, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars]
    all_goals clz_end (m.x k.val % 4294967296) hX

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- CLZ's trace has a path to `exec`'s state that keeps the high words of X0 to X14. -/
theorem clz_bwd_path (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d k : Fin 8) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) (σ : Sys)
    (hσ : ∀ q ∈ reads clzT.trace, σ.get q.1 q.2 = (sys u).get q.1 q.2) :
    footRun P δ clzT (clzFields d k) m σ
      (.done { m with s := { m.s.setR d (clz32 (m.s.r k)) with pc := m.s.pc + 4 } }
        (((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
          (.bits 128 2882))) := by
  without_info
    have hX : m.x k.val % 4294967296 = (m.s.r k).toNat := by
      rw [x_mod m (by omega), low_r]
    t32_reads [clzT, sys_get, sys] at hσ
    clz_run d k
    have hlt : m.x k.val % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
    clz_bwd [u.feature, m.s.pc.toNat] with [hσ, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars]
    clz_gprs m with [hσ, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars]
    clz_forks (m.x k.val % 4294967296) hX hlt hσ
    clz_bwd [false] with [hσ, bit_iff, bit0_iff, LeanExe.A64.Isla.reduceVars]
    all_goals first
      | clz_bwd_end hX hlt
      | t32_side

set_option maxRecDepth 100000 in
/-- The trace of `CLZ Rd, Rm` agrees with `exec` for every register of r0 to r7 in each field and
every machine whose program counter plus 4 is below 2^32.  The encoding repeats Rm, and the trace
assumes the configuration's constraint that the two fields are equal, which `clzFields` gives. -/
theorem clz_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d k : Fin 8) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] clzT (clzFields d k)
      (.clz d k) m := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · apply decode_halves (by decide) (by intro h; cases h)
    rw [show clzT.opcode = [.bits 13 0x1F56, .field "Rm" 3, .bits 5 0x1E, .field "Rd" 3,
      .bits 5 0x10, .field "Rm2" 3] from rfl]
    simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, clzFields, encodeNat, List.lookup,
      String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    exact ⟨_, fun o h => clz_fwd_paths P δ u d k m hpc σ hσ o h,
      clz_bwd_path P δ u d k m hpc σ hσ, by t32_frame⟩

#print axioms clz_fwd_paths
#print axioms clz_bwd_path
#print axioms clz_agrees

end TestSupport.M7.Isla
