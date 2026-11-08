import LeanExe.M7.Proof.Bounds
import LeanExe.ProofKit.Exec

/-!
The simulation of the branches `br`, `br_if`, and `return`, as `LeanExe/A64/Proof/Control.lean`
states it for the AArch64 back end.  A branch to a construct that carries a value copies the top
slot into the slot of the construct's base height through r0 and r1 and then branches with `B.W`
to the construct's target, so the model reaches the target with the carried value where the code
after the target expects it, and with the slots below the base, the slots of the locals, the slot
of LR, and the bytes outside the frame unchanged.  `br_if` loads the condition's low word, compares
it with 0, and either branches or falls through, by `BNE` to the target for a construct that
carries nothing, and by `BEQ` past the copy and the branch for one that carries a value.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## The relation with the memory unchanged -/

theorem ValAt.of_mem {s t : State} {o : Nat} {v : Value} (h : ValAt s o v) (hsp : t.sp = s.sp)
    (hmem : t.mem = s.mem) : ValAt t o v :=
  h.congr hsp ⟨by rw [hmem], by rw [hmem]⟩

theorem Below.of_mem {fr : Frame} {b : Nat} {s t : State} (hmem : t.mem = s.mem) :
    Below fr b s t :=
  fun _ _ => ⟨by rw [hmem], by rw [hmem]⟩

/-- The relation after the pop of the top `v` of the stack `v :: vs`, at a state with the SP and
the memory of `ms`. -/
theorem Inv.pop {E : Env} {σs : List ValueType} {sl : Locals} {ms ms1 : State} {v : Value}
    {vs : List Value} (hinv : Inv P E σs sl ms) (hv : sl.values = v :: vs) (hsp : ms1.sp = ms.sp)
    (hmem : ms1.mem = ms.mem) : Inv P E σs.tail { sl with values := vs } ms1 := by
  have hh := hinv.height
  rw [hv] at hh
  refine ⟨by simp at hh ⊢; omega, fun h v' hv' => ?_, hinv.count,
    fun i v' o h1 h2 => (hinv.locals i v' o h1 h2).of_mem hsp hmem, hinv.ltypes,
    hinv.frame.congr hsp, ?_⟩
  · have hl : h < vs.length := getElem?_reverse_lt hv'
    exact (hinv.stack h v' (by rw [hv, getElem?_reverse_cons hl]; exact hv')).of_mem hsp hmem
  · have h1 := hinv.types
    rw [hv] at h1
    exact h1.tail

/-- The slots of the locals after the store of two words into the operand slot of height `k`. -/
theorem LocalsOk.write_op {E : Env} {σs : List ValueType} {sl : Locals} {ms t : State} {k : Nat}
    {w0 w1 : UInt32} (hinv : Inv P E σs sl ms) (hsp : t.sp = ms.sp)
    (hmem : t.mem = store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
      (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) : LocalsOk E (sl.params ++ sl.locals) t := by
  have hf := hinv.frame.fits
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hk
  refine ⟨hinv.count, fun i v o hv ho => ?_, hinv.ltypes⟩
  obtain ⟨ho8, hob, -, hop⟩ := Frame.localOff_bounds ho
  exact (hinv.locals i v o hv ho).congr hsp (slotSame_store2 hmem (by omega) (by omega)
    (hop k hk))

/-! ## Branches to a construct -/

theorem gen_branchTo {E : Env} {t : Ctl} {σs : List ValueType} {a : UInt32} {is : List Instr}
    (hg : branchTo E t σs a = .ok is) :
    t.base + t.arity ≤ σs.length ∧ t.arity ≤ 1 ∧ σs.take t.arity = t.types ∧
      ∃ moves ob, ((t.arity = 0 ∧ moves = []) ∨
        (t.arity = 1 ∧ σs.length - 1 < E.frame.height ∧ t.base < E.frame.height ∧
          ∃ h0 h1 h2 h3, moves = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
            .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩,
            .strSp 0 ⟨E.frame.opAt t.base, h2⟩, .strSp 1 ⟨E.frame.opAt t.base + 4, h3⟩])) ∧
        ob % 2 = 0 ∧ -16777216 ≤ ob ∧ ob < 16777216 ∧
        after a moves.length + 4 + UInt32.ofInt ob = t.target ∧ is = moves ++ [.bTo ob] := by
  unfold branchTo at hg
  by_cases hc : σs.length < t.base + t.arity ∨ t.arity > 1 ∨ σs.take t.arity ≠ t.types
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  have hc' := hc
  simp only [not_or, Nat.not_lt, gt_iff_lt, Ne, Decidable.not_not] at hc'
  obtain ⟨hle, ha1, htake⟩ := hc'
  simp only [hc, ↓reduceIte] at hg
  refine ⟨hle, by omega, htake, ?_⟩
  by_cases h1 : t.arity = 1
  · simp only [ite_eq_left h1, except_bind_ok, except_pure_ok] at hg
    obtain ⟨x, hx, y, hy, moves, hm, i, hi, rfl⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok hx
    obtain ⟨hlb, rfl⟩ := Env.op_ok hy
    obtain ⟨c0, c1, c2, c3, rfl⟩ := copySlot_ok hm
    obtain ⟨ob, rfl, b1, b2, b3, b4⟩ := bAt_ok hi
    exact ⟨_, ob, .inr ⟨h1, hlt, hlb, c0, c1, c2, c3, rfl⟩, b1, b2, b3, b4, rfl⟩
  · simp only [ite_eq_right h1, except_bind_ok, except_pure_ok] at hg
    obtain ⟨moves, rfl, i, hi, rfl⟩ := hg
    obtain ⟨ob, rfl, b1, b2, b3, b4⟩ := bAt_ok hi
    exact ⟨[], ob, .inl ⟨by omega, rfl⟩, b1, b2, b3, b4, rfl⟩

/-- The run of a branch to `t` from a related state: the model reaches `t.target` with the value
that the branch carries in the slot of `t.base`, and with SP, the device trace, the read count,
the slot of LR, the bytes from the end of the parameters up, the slots below `t.base`, the slots of
the locals, and the bytes below the stack's limit unchanged. -/
theorem run_branchTo {E : Env} {t : Ctl} {σs : List ValueType} {a : UInt32} {is : List Instr}
    {sl : Locals} {ms : State} (hg : branchTo E t σs a = .ok is) (hcode : CodeAt code a is)
    (hpc : ms.pc = a) (hinv : Inv P E σs sl ms) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = t.target ∧ ms'.sp = ms.sp ∧
      ms'.trace = ms.trace ∧ ms'.reads = ms.reads ∧ BodyKeeps E.frame ms.sp ms ms' ∧
      Below E.frame t.base ms ms' ∧ LocalsOk E (sl.params ++ sl.locals) ms' ∧
      Kept E.frame t sl.values ms' ∧ KeepsBelow E.limit ms ms' := by
  obtain ⟨hle, ha1, htake, moves, ob, hmv, b1, b2, b3, b4, rfl⟩ := gen_branchTo hg
  have hh := hinv.len
  have hhe := hinv.height
  have hkt : Typed t.types (sl.values.take t.arity) := by
    rw [← htake]; exact hinv.types.take t.arity
  rcases hmv with ⟨h0, rfl⟩ | ⟨h1, hlt, hlb, c0, c1, c2, c3, rfl⟩
  · rw [List.nil_append, ← hpc] at hcode
    have hA : after a ([] : List Instr).length = a := by rw [after_eq]; simp
    rw [hA] at b4
    refine ⟨_, reach_exec hcode (exec_bTo b1 b2 b3 ms) (.refl _), ?_, State.sp_withPc _ _,
      State.trace_withPc _ _, State.reads_withPc _ _, BodyKeeps.of_mem (State.mem_withPc _ _),
      Below.of_mem (State.mem_withPc _ _), ⟨hinv.count, fun i v o h1 h2 =>
        (hinv.locals i v o h1 h2).of_mem (State.sp_withPc _ _) (State.mem_withPc _ _),
        hinv.ltypes⟩, ⟨by omega, by omega, fun j hj => absurd hj (by omega), hkt⟩,
      KeepsBelow.of_mem (State.mem_withPc _ _)⟩
    rw [State.pc_withPc, hpc, b4]
  · have hfit := hinv.frame.fits
    obtain ⟨ht8, htlr, hlrs⟩ := E.frame.opAt_bounds hlt
    obtain ⟨hb8, hblr, -⟩ := E.frame.opAt_bounds hlb
    let L : List Instr := [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), c0⟩,
      .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, c1⟩, .strSp 0 ⟨E.frame.opAt t.base, c2⟩,
      .strSp 1 ⟨E.frame.opAt t.base + 4, c3⟩]
    have hc' : CodeAt code a (L ++ [.bTo ob]) := hcode
    obtain ⟨hcL, hcB⟩ := hc'.split_wide (rfl : L.all Instr.wide = true)
    have hok : SlotsOk P ms.sp L :=
      slotsOk_ld (hinv.frame.word (by omega) (by omega))
        (slotsOk_ld (hinv.frame.word (by omega) (by omega))
        (slotsOk_st (hinv.frame.word (by omega) (by omega))
        (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))))
    rw [← hpc] at hcL
    obtain ⟨r1, p1, sp1, -, tr1, rd1, -⟩ := run_slots (σ := σ) hok hcL
    have hu : (slotRun P σ L ms).pc = after a L.length := by rw [p1, hpc, after_eq]
    rw [← hu] at hcB
    have hmem : ({ slotRun P σ L ms with
        pc := (slotRun P σ L ms).pc + 4 + UInt32.ofInt ob } : State).mem =
        store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt t.base))
          (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1)))))
          (ms.sp + UInt32.ofNat (E.frame.opAt t.base + 4))
          (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4))) := rfl
    have hsp : ({ slotRun P σ L ms with
        pc := (slotRun P σ L ms).pc + 4 + UInt32.ofInt ob } : State).sp = ms.sp := by
      rw [State.sp_withPc]; exact sp1
    obtain ⟨v, vs, hv⟩ : ∃ v vs, sl.values = v :: vs := by
      cases hvs : sl.values with
      | nil => rw [hvs, List.length_nil] at hh; omega
      | cons v vs => exact ⟨v, vs, rfl⟩
    have hvl : vs.length = σs.length - 1 := by
      rw [hv, List.length_cons] at hh; omega
    have htop := hinv.stack vs.length v (by
      rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
        Nat.sub_self, List.getElem?_cons_zero])
    rw [hvl] at htop
    refine ⟨_, r1.trans (reach_exec hcB (exec_bTo b1 b2 b3 _) (.refl _)), ?_, hsp,
      by rw [State.trace_withPc]; exact tr1, by rw [State.reads_withPc]; exact rd1,
      keeps_write_op hinv.frame hmem hlb, below_write_op hinv.frame hmem hlb (Nat.le_refl _),
      LocalsOk.write_op hinv hsp hmem hlb, ⟨by omega, by omega, fun j hj => ?_, hkt⟩,
      keepsBelow_write_op hinv.frame hmem hlb⟩
    · rw [State.pc_withPc, hu]
      exact b4
    · have hj0 : j = 0 := by omega
      subst hj0
      have e : ∀ p, sl.values[t.arity - 1 - 0]'p = v := fun p => by simp [hv, h1]
      rw [e, Nat.add_zero]
      exact valAt_store2 hsp hmem (by omega) htop

/-! ## `br` and `return` -/

theorem gen_br {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {n : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.br n) = .ok (is, fin)) :
    ∃ t, ctl[n]? = some t ∧ branchTo E t σs a = .ok is ∧ fin = none := by
  cases ht : ctl[n]? with
  | none => simp [genInstr, ht, throw, throwThe, MonadExceptOf.throw] at hg
  | some t =>
      cases hb : branchTo E t σs a with
      | error e => simp [genInstr, ht, hb, bind, Except.bind] at hg
      | ok bs =>
          simp [genInstr, ht, hb, bind, Except.bind, pure, Except.pure] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨t, rfl, hb, rfl⟩

theorem gen_ret {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genInstr E ctl σs a .ret = .ok (is, fin)) :
    ∃ t, ctl.getLast? = some t ∧ branchTo E t σs a = .ok is ∧ fin = none := by
  cases ht : ctl.getLast? with
  | none => simp [genInstr, ht, throw, throwThe, MonadExceptOf.throw] at hg
  | some t =>
      cases hb : branchTo E t σs a with
      | error e => simp [genInstr, ht, hb, bind, Except.bind] at hg
      | ok bs =>
          simp [genInstr, ht, hb, bind, Except.bind, pure, Except.pure] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨t, rfl, hb, rfl⟩

theorem sim_br (F n : Nat) : InstrSim P σ code F (.br n) := by
  intro E ctl σs a is fin hgen hcode _ _ _ _ α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨t, ht, hbr, rfl⟩ := gen_br hgen
  cases F with
  | zero => rw [ProofKit.execOne_zero]; trivial
  | succ f =>
      have hex : execOne (f + 1) m st sl (.br n) = .Break n st sl := by
        simp only [execOne.eq_def]
      rw [hex]
      obtain ⟨ms', hr, hp, hsp, htr, hrd, hk, hb, hl, hkt, hkb⟩ := run_branchTo hbr hcode hpc hinv
      exact ⟨t, ht, ms', hr, hp, hsp, htr, hrd, hk, hb, hl, hkt, hsr.congr hkb⟩

theorem sim_ret (F : Nat) : InstrSim P σ code F .ret := by
  intro E ctl σs a is fin hgen hcode _ _ _ _ α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨t, ht, hbr, rfl⟩ := gen_ret hgen
  cases F with
  | zero => rw [ProofKit.execOne_zero]; trivial
  | succ f =>
      have hex : execOne (f + 1) m st sl .ret = .Return st sl.values := by
        simp only [execOne.eq_def]
      rw [hex]
      obtain ⟨ms', hr, hp, hsp, htr, hrd, hk, -, -, hkt, hkb⟩ := run_branchTo hbr hcode hpc hinv
      exact ⟨t, ht, ms', hr, hp, hsp, htr, hrd, hk, hkt, hsr.congr hkb⟩

/-! ## `br_if` -/

theorem gen_br_if {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {n : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.br_if n) = .ok (is, fin)) :
    curBase ctl + 1 ≤ σs.length ∧ σs.head? = some .i32 ∧ σs.length - 1 < E.frame.height ∧
      fin = some σs.tail ∧ ∃ t hc, ctl[n]? = some t ∧
        ((t.arity = 0 ∧ ∃ oq, oq % 2 = 0 ∧ -1048576 ≤ oq ∧ oq < 1048576 ∧
            after a 2 + 4 + UInt32.ofInt oq = t.target ∧
            is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, .cmpImm 0 0,
              .bcondTo condNE oq]) ∨
          (t.arity ≠ 0 ∧ ∃ oq bs, oq % 2 = 0 ∧ -1048576 ≤ oq ∧ oq < 1048576 ∧
            after a 2 + 4 + UInt32.ofInt oq = after a (4 * t.arity + 4) ∧
            branchTo E t σs.tail (after a 3) = .ok bs ∧
            is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, .cmpImm 0 0,
              .bcondTo condEQ oq] ++ bs)) := by
  unfold genInstr at hg
  by_cases hc : σs.length < curBase ctl + 1 ∨ σs.head? ≠ some .i32
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  have hc' := hc
  simp only [not_or, Nat.not_lt, Ne, Decidable.not_not] at hc'
  simp only [hc, ↓reduceIte] at hg
  split at hg
  · rename_i t ht
    simp only [except_bind_ok] at hg
    obtain ⟨o, ho, c, hcimm, hg⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok ho
    obtain ⟨hcc, rfl⟩ := imm_ok hcimm
    by_cases h0 : t.arity = 0
    · simp only [ite_eq_left h0, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
      obtain ⟨i, hi, rfl, rfl⟩ := hg
      obtain ⟨oq, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi
      exact ⟨by omega, hc'.2, hlt, rfl, t, hcc, ht, .inl ⟨h0, oq, q1, q2, q3, q4, rfl⟩⟩
    · simp only [ite_eq_right h0, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
      obtain ⟨i, hi, bs, hbs, rfl, rfl⟩ := hg
      obtain ⟨oq, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi
      exact ⟨by omega, hc'.2, hlt, rfl, t, hcc, ht, .inr ⟨h0, oq, bs, q1, q2, q3, q4, hbs, rfl⟩⟩
  · exact absurd hg except_throw_ok

/-- `LDR` of the low word of the `i32` `c` on top and `CMP` with 0: the model reaches the next
instruction with Z set exactly when `c` is 0, and with SP, the memory, the device trace, and the
read count unchanged. -/
theorem run_cmp {E : Env} {σs : List ValueType} {sl : Locals} {ms : State} {c : UInt32}
    {vs : List Value} {hc : E.frame.opAt (σs.length - 1) < 4096} {rest : List Instr}
    (hinv : Inv P E σs sl ms) (hv : sl.values = .i32 c :: vs)
    (hlt : σs.length - 1 < E.frame.height)
    (hcode : CodeAt code ms.pc
      ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, Instr.cmpImm 0 0] ++ rest)) :
    ∃ u, Reach P σ code ms u ∧ u.pc = after ms.pc 2 ∧ u.sp = ms.sp ∧ u.mem = ms.mem ∧
      u.trace = ms.trace ∧ u.reads = ms.reads ∧ u.zFlag = (c == 0) ∧ CodeAt code u.pc rest := by
  have hh := hinv.len
  have hvl : vs.length = σs.length - 1 := by rw [hv, List.length_cons] at hh; omega
  have htop : ValAt ms (E.frame.opAt (σs.length - 1)) (.i32 c) := by
    have := hinv.stack vs.length (.i32 c) (by
      rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
        Nat.sub_self, List.getElem?_cons_zero])
    rwa [hvl] at this
  have hc32 : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) = c := htop.1
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
  let L : List Instr := [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, Instr.cmpImm 0 0]
  have hc' : CodeAt code ms.pc (L ++ rest) := hcode
  obtain ⟨hcL, hcR⟩ := hc'.split_wide (rfl : L.all Instr.wide = true)
  have hok : SlotsOk P ms.sp L :=
    slotsOk_ld (hinv.frame.word (by omega) (by omega))
      (slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_nil _))
  obtain ⟨r1, p1, sp1, -, tr1, rd1, -⟩ := run_slots (σ := σ) hok hcL
  have hz : (slotRun P σ L ms).zFlag = (c == 0) := by
    simp only [L, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    first | rw [cmp_imm0] | rw [cmp_zero]
    exact congrArg (· == 0) hc32
  have hpc' : (slotRun P σ L ms).pc = after ms.pc 2 := by rw [p1, after_eq]; rfl
  exact ⟨_, r1, hpc', sp1, rfl, tr1, rd1, hz, by rw [hpc']; exact hcR⟩

theorem sim_br_if (F n : Nat) : InstrSim P σ code F (.br_if n) := by
  intro E ctl σs a is fin hgen hcode _ _ hb hctl α m st sl ms hinv hsr hpc _ need D _ _ _
  obtain ⟨hb1, hhead, hlt, rfl, t, hc, ht, hcase⟩ := gen_br_if hgen
  cases F with
  | zero => rw [ProofKit.execOne_zero]; trivial
  | succ f =>
      obtain ⟨c, vs, hv⟩ := hinv.types.i32_head hhead
      have hh := hinv.len
      have hhe := hinv.height
      have hbase : t.base ≤ curBase ctl := hctl.bases t (List.mem_of_getElem? ht)
      have hloc := hinv.localsOk
      rw [← hpc] at hcode
      -- the fall-through when `c` is 0, at `after a k` with `k` the code's length
      have fall : c = 0 → ∀ u : State, Reach P σ code ms u → u.pc = after a is.length →
          u.sp = ms.sp → u.mem = ms.mem → u.trace = ms.trace → u.reads = ms.reads →
          Outcome P σ code E ctl (some σs.tail) (after a is.length)
            (execOne (f + 1) m st sl (.br_if n)) ms := by
        intro hc0 u hr hp hsp hmem htr hrd
        subst hc0
        have hex : execOne (f + 1) m st sl (.br_if n) =
            .Fallthrough st { sl with values := vs } := by
          simp only [execOne.eq_def, hv]
        rw [hex]
        exact ⟨σs.tail, rfl, u, hr, hp, hsp, htr, hrd, BodyKeeps.of_mem hmem, Below.of_mem hmem,
          Inv.pop hinv hv hsp hmem, hsr.congr (KeepsBelow.of_mem hmem)⟩
      have hex1 : c ≠ 0 → execOne (f + 1) m st sl (.br_if n) =
          .Break n st { sl with values := vs } := fun hc0 => by
        simp only [execOne.eq_def, hv]
      rcases hcase with ⟨h0, oq, q1, q2, q3, q4, rfl⟩ | ⟨h0, oq, bs, q1, q2, q3, q4, hbt, rfl⟩
      · -- `BNE` to the target of a construct that carries nothing
        obtain ⟨u, ru, pu, spu, mu, tru, rdu, zu, hcu⟩ :=
          run_cmp (rest := [.bcondTo condNE oq]) hinv hv hlt hcode
        have rB := reach_bcondTo (P := P) (σ := σ) q1 q2 q3 hcu
        have hcnd : u.condHolds condNE = !(c == 0) := by
          rw [show condNE = (1 : Fin 14) from rfl, condHolds_ne, zu]
        rw [hcnd] at rB
        have hu1sp (p : UInt32) : ({ u with pc := p } : State).sp = ms.sp := by
          rw [State.sp_withPc, spu]
        have hu1m (p : UInt32) : ({ u with pc := p } : State).mem = ms.mem := by
          rw [State.mem_withPc, mu]
        have hu1tr (p : UInt32) : ({ u with pc := p } : State).trace = ms.trace := by
          rw [State.trace_withPc, tru]
        have hu1rd (p : UInt32) : ({ u with pc := p } : State).reads = ms.reads := by
          rw [State.reads_withPc, rdu]
        by_cases hc0 : c = 0
        · rw [show (!(c == 0)) = false by simp [hc0], ite_eq_right Bool.false_ne_true] at rB
          exact fall hc0 _ (ru.trans rB)
            (by rw [State.pc_withPc, pu, hpc]; show after a 2 + 4 = after a 3; addr_after)
            (hu1sp _) (hu1m _) (hu1tr _) (hu1rd _)
        · rw [show (!(c == 0)) = true by simp [hc0], ite_eq_left rfl] at rB
          rw [hex1 hc0]
          refine ⟨t, ht, _, ru.trans rB, by rw [State.pc_withPc, pu, hpc]; exact q4, hu1sp _,
            hu1tr _, hu1rd _, BodyKeeps.of_mem (hu1m _), Below.of_mem (hu1m _),
            ⟨hloc.count, fun i v o h1 h2 => (hloc.vals i v o h1 h2).of_mem (hu1sp _) (hu1m _),
              hloc.types⟩,
            ⟨by omega, by omega, fun j hj => absurd hj (by omega), ?_⟩,
            hsr.congr (KeepsBelow.of_mem (hu1m _))⟩
          rw [show t.types = [] from List.eq_nil_of_length_eq_zero h0, h0]
          trivial
      · -- `BEQ` past the copy and the branch of a construct that carries a value
        have ha1 := (gen_branchTo hbt).2.1
        have h1 : t.arity = 1 := by omega
        have hbl : bs.length = 5 := by
          obtain ⟨_, _, _, moves, ob, hmv, _, _, _, _, hbs⟩ := gen_branchTo hbt
          rw [hbs]
          rcases hmv with ⟨h0', _⟩ | ⟨_, _, _, _, _, _, _, rfl⟩
          · omega
          · rfl
        have hil : ([Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, Instr.cmpImm 0 0,
            Instr.bcondTo condEQ oq] ++ bs).length = 4 * t.arity + 4 := by
          rw [List.length_append, hbl, h1]; try rfl
        obtain ⟨u, ru, pu, spu, mu, tru, rdu, zu, hcu⟩ :=
          run_cmp (rest := .bcondTo condEQ oq :: bs) hinv hv hlt hcode
        obtain ⟨hcQ, hcB⟩ := CodeAt.cons.mp hcu
        have rB := reach_bcondTo (P := P) (σ := σ) q1 q2 q3 hcQ
        have hcnd : u.condHolds condEQ = (c == 0) := by
          rw [show condEQ = (0 : Fin 14) from rfl, condHolds_eq, zu]
        rw [hcnd] at rB
        have hu1sp (p : UInt32) : ({ u with pc := p } : State).sp = ms.sp := by
          rw [State.sp_withPc, spu]
        have hu1m (p : UInt32) : ({ u with pc := p } : State).mem = ms.mem := by
          rw [State.mem_withPc, mu]
        have hu1tr (p : UInt32) : ({ u with pc := p } : State).trace = ms.trace := by
          rw [State.trace_withPc, tru]
        have hu1rd (p : UInt32) : ({ u with pc := p } : State).reads = ms.reads := by
          rw [State.reads_withPc, rdu]
        by_cases hc0 : c = 0
        · rw [show (c == 0) = true by simp [hc0], ite_eq_left rfl] at rB
          exact fall hc0 _ (ru.trans rB) (by rw [State.pc_withPc, hil, pu, hpc]; exact q4)
            (hu1sp _) (hu1m _) (hu1tr _) (hu1rd _)
        · rw [show (c == 0) = false by simp [hc0], ite_eq_right Bool.false_ne_true] at rB
          rw [hex1 hc0]
          have hcB' : CodeAt code (after a 3) bs := by
            rw [pu, hpc, show (Instr.bcondTo condEQ oq).size = 4 from rfl] at hcB
            exact hcB.at_eq (by addr_after)
          obtain ⟨ms', hr, hp, hsp, htr, hrd, hk, hbw, hl, hkt, hkb⟩ :=
            run_branchTo hbt hcB' (by rw [State.pc_withPc, pu, hpc]; addr_after)
              (Inv.pop hinv hv (hu1sp (u.pc + 4)) (hu1m (u.pc + 4)))
          have hk' : BodyKeeps E.frame ms.sp ({ u with pc := u.pc + 4 } : State) ms' := by
            rw [← hu1sp (u.pc + 4)]; exact hk
          refine ⟨t, ht, ms', ru.trans (rB.trans hr), hp, hsp.trans (hu1sp _),
            htr.trans (hu1tr _), hrd.trans (hu1rd _), (BodyKeeps.of_mem (hu1m _)).trans hk',
            (Below.of_mem (hu1m _)).trans hbw (hu1sp _), hl, hkt,
            hsr.congr ((KeepsBelow.of_mem (hu1m _)).trans hkb)⟩

end LeanExe.M7
