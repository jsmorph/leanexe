import LeanExe.A64.Proof.Arith

/-!
The simulation of a call.  The caller stores the operand registers below the arguments into its
frame's spill slots, moves the arguments into X0 upward, and branches with `BL` to the callee's
entry.  `CallsOk` supplies the callee's outcome at one less fuel, as Talos runs the callee's body:
the callee returns with SP and X18 unchanged and changes no memory from its caller's SP upward,
so the caller's locals and spill slots keep their words.  The caller moves the result from X0
into the register of its height and reloads the spilled registers.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Accesses to the frame -/

theorem sub_aligned {a : UInt64} {k : Nat} (ha : a % 16 = 0) (hk : k % 16 = 0) :
    (a - UInt64.ofNat k) % 16 = 0 := by
  have h1 : a.toNat % 16 = 0 := by
    have := congrArg UInt64.toNat ha
    simpa [UInt64.toNat_mod] using this
  have := a.toNat_lt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h16, h0]
  omega

theorem mapped_of {s : State} {i : Nat}
    (h : ∀ j < 8, P.normal (s.sp + UInt64.ofNat (8 * i + j)) = true) :
    P.mapped (s.sp + UInt64.ofNat (8 * i)) 8 = true := by
  unfold Platform.mapped
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have := h j hj
  rwa [UInt64.ofNat_add, ← UInt64.add_assoc] at this

theorem exec_str_sp {s : State} {r : Fin 32} {i : Nat} (hs : i < 4096) (hal : s.sp % 16 = 0)
    (hmap : ∀ j < 8, P.normal (s.sp + UInt64.ofNat (8 * i + j)) = true) :
    LeanExe.A64.exec P (.str r 31 ⟨i, hs⟩) s =
      some { s with mem := store64 s.mem (slotAddr s.sp i) (s.x r), pc := s.pc + 4 } := by
  simp only [exec, State.xsp_31, State.spAligned, mapped_of P hmap, Bool.and_true, hal]
  simp [slotAddr]

theorem exec_ldr_sp {s : State} {r : Fin 32} {i : Nat} (hs : i < 4096) (hal : s.sp % 16 = 0)
    (hmap : ∀ j < 8, P.normal (s.sp + UInt64.ofNat (8 * i + j)) = true) :
    LeanExe.A64.exec P (.ldr r 31 ⟨i, hs⟩) s =
      some { s.setX r (load64 s.mem (slotAddr s.sp i)) with pc := s.pc + 4 } := by
  simp only [exec, State.xsp_31, State.spAligned, mapped_of P hmap, Bool.and_true, hal]
  simp [slotAddr]

/-- An address at least `k` bytes above `sp`, for `k ≤ k'`, when it is at least `k'` above. -/
theorem not_lt_mono {a sp : UInt64} {k k' : Nat} (hk : k ≤ k') (hk' : k' < 2 ^ 64)
    (h : ¬ a - sp < UInt64.ofNat k') : ¬ a - sp < UInt64.ofNat k := by
  intro hc
  apply h
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hc ⊢
  omega

/-! ## The generator's call -/

theorem gen_call {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {k : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.call k) = .ok (is, fin)) :
    ∃ target ps rs, E.callee k = some (target, ps, rs) ∧ σ.take ps.length = ps.reverse ∧
      fin = some (rs.reverse ++ σ.drop ps.length) ∧
      ∃ h p r, σ.length = h ∧ ps.length = p ∧ rs.length = r ∧ curBase ctl + p ≤ h ∧ h ≤ 26 ∧
      h - p + r ≤ 26 ∧ E.locals + spillSlots < 4096 ∧
      ∃ spills moves res reloads g,
        is = spills ++ moves ++ [Instr.bl g] ++ res ++ reloads ∧
        spills.length = h - p ∧
        (∀ j (hj : j < spills.length), ∃ hs,
          spills[j] = .str (regOf j) 31 ⟨E.locals + j, hs⟩) ∧
        moves.length = p ∧
        (∀ i (hi : i < moves.length), moves[i] = mov (regOf i) (regOf (h - p + i))) ∧
        res.length = r ∧
        (∀ k (hk : k < res.length),
          res[k] = mov (regOf (h - p + (r - 1 - k))) (regOf (r - 1 - k))) ∧
        reloads.length = h - p ∧
        (∀ j (hj : j < reloads.length), ∃ hs,
          reloads[j] = .ldr (regOf j) 31 ⟨E.locals + j, hs⟩) ∧
        bField (after a (h - p + p)) target = .ok g := by
  simp only [genInstr] at hg
  cases hk : E.callee k with
  | none => simp [hk, throw, throwThe, MonadExceptOf.throw] at hg
  | some c =>
      obtain ⟨target, ps, rs⟩ := c
      rw [hk] at hg
      by_cases hc : σ.length < curBase ctl + ps.length ∨ 26 < σ.length ∨
          26 < σ.length - ps.length + rs.length ∨
          4096 ≤ E.locals + spillSlots ∨ σ.take ps.length ≠ ps.reverse
      · simp [hc, throw, throwThe, MonadExceptOf.throw] at hg
      · have hs : spillSlots = 26 := rfl
        have hc' := hc
        simp only [not_or, Ne, Decidable.not_not] at hc'
        obtain ⟨c1, c2, c3, c6, htake⟩ := hc'
        cases hb : bField (after a (σ.length - ps.length + ps.length)) target with
        | error e => simp [hc, hb, bind, Except.bind] at hg
        | ok g =>
            simp [hc, hb, bind, Except.bind, pure, Except.pure] at hg
            obtain ⟨rfl, rfl⟩ := hg
            refine ⟨target, ps, rs, rfl, htake, rfl, σ.length, ps.length, rs.length, rfl, rfl, rfl,
              by omega, by omega, by omega, by omega,
              List.ofFn fun j : Fin (σ.length - ps.length) =>
                Instr.str (regOf j) 31 ⟨E.locals + j, by omega⟩,
              List.ofFn fun i : Fin ps.length =>
                mov (regOf i) (regOf (σ.length - ps.length + i)),
              List.ofFn fun k : Fin rs.length =>
                mov (regOf (σ.length - ps.length + (rs.length - 1 - k)))
                  (regOf (rs.length - 1 - k)),
              List.ofFn fun j : Fin (σ.length - ps.length) =>
                Instr.ldr (regOf j) 31 ⟨E.locals + j, by omega⟩,
              g, by simp [List.append_assoc], by simp,
              fun j hj => ⟨by simp at hj; omega, by simp⟩, by simp,
              fun i hi => by simp, by simp, fun k hk => by simp, by simp,
              fun j hj => ⟨by simp at hj; omega, by simp⟩, hb⟩

/-! ## Registers -/

theorem regOf_ge : ∀ k < 26, k ≤ (regOf k).val := by decide

theorem regOf_ne_30 : ∀ k < 26, regOf k ≠ 30 := by decide

theorem x31 (s : State) : s.x 31 = 0 := by
  unfold State.x; rw [dite_eq_right (by decide)]

/-! ## Runs of the call's parts -/

/-- The run of stores of the registers `src j` into the slots `o + j` of the frame at SP. -/
theorem run_strs {o d : Nat} {src : Nat → Fin 32} {stores : List Instr}
    (hlen : stores.length = d)
    (hst : ∀ j (hj : j < d), ∃ hs, stores[j]'(by omega) = .str (src j) 31 ⟨o + j, hs⟩)
    (hb : o + d ≤ 512) {a : UInt64} {ms : State} (hcode : CodeAt code a stores)
    (hpc : ms.pc = a) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < 8 * (o + d), P.normal (ms.sp + UInt64.ofNat j) = true) :
    ∃ s, Reach P code ms s ∧ s.pc = after a d ∧ s.sp = ms.sp ∧ (∀ q, s.x q = ms.x q) ∧
      s.out = ms.out ∧ (∀ j < d, load64 s.mem (slotAddr ms.sp (o + j)) = ms.x (src j)) ∧
      (∀ b, (∀ j < d, ¬ b - slotAddr ms.sp (o + j) < 8) → s.mem b = ms.mem b) := by
  have key : ∀ k ≤ d, ∃ M, Reach P code ms { ms with mem := M, pc := after a k } ∧
      (∀ j < k, load64 M (slotAddr ms.sp (o + j)) = ms.x (src j)) ∧
      (∀ b, (∀ j < k, ¬ b - slotAddr ms.sp (o + j) < 8) → M b = ms.mem b) := by
    intro k
    induction k with
    | zero =>
        refine fun _ => ⟨ms.mem, ?_, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
        rw [after_zero, ← hpc]
        exact .refl _
    | succ k ih =>
        intro hk
        obtain ⟨M, hr, hload, hout⟩ := ih (by omega)
        obtain ⟨hs, hsk⟩ := hst k (by omega)
        have ck : code (after a k) = some (encode (.str (src k) 31 ⟨o + k, hs⟩)) := by
          have := hcode k (by omega)
          rwa [hsk] at this
        let t : State := { ms with mem := M, pc := after a k }
        have et := exec_str_sp P (s := t) (r := src k) hs hal
          (fun j hj => hmap (8 * (o + k) + j) (by omega))
        refine ⟨store64 M (slotAddr ms.sp (o + k)) (ms.x (src k)),
          hr.trans (reach_exec P code ck et ?_), ?_, ?_⟩
        · rw [after_succ]
          exact .refl _
        · intro j hj
          by_cases hjk : j = k
          · subst hjk
            exact load64_store64_same _ _ _
          · rw [load64_store64_other _ _ _ _ (slot_apart (by omega) (by omega) (by omega))]
            exact hload j (by omega)
        · intro b hb'
          rw [store64_other _ _ _ _ (hb' k (by omega))]
          exact hout b fun j hj => hb' j (by omega)
  obtain ⟨M, hr, hload, hout⟩ := key d (Nat.le_refl _)
  exact ⟨_, hr, rfl, rfl, fun _ => rfl, rfl, hload, hout⟩

/-- The run of loads of the slots `o + j` of the frame at SP into the registers `dst j`. -/
theorem run_ldrs {o d : Nat} {dst : Nat → Fin 32} {loads : List Instr}
    (hlen : loads.length = d)
    (hld : ∀ j (hj : j < d), ∃ hs, loads[j]'(by omega) = .ldr (dst j) 31 ⟨o + j, hs⟩)
    (hdst : ∀ j < d, (dst j).val < 31) (hinj : ∀ i < d, ∀ j < d, dst i = dst j → i = j)
    (hb : o + d ≤ 512) {a : UInt64} {ms : State} (hcode : CodeAt code a loads)
    (hpc : ms.pc = a) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < 8 * (o + d), P.normal (ms.sp + UInt64.ofNat j) = true) :
    ∃ s, Reach P code ms s ∧ s.pc = after a d ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧
      s.out = ms.out ∧ (∀ j < d, s.x (dst j) = load64 ms.mem (slotAddr ms.sp (o + j))) ∧
      (∀ q, (∀ j < d, q ≠ dst j) → s.x q = ms.x q) := by
  have key : ∀ k ≤ d, ∃ s, Reach P code ms s ∧ s.pc = after a k ∧ s.sp = ms.sp ∧
      s.mem = ms.mem ∧ s.out = ms.out ∧
      (∀ j < k, s.x (dst j) = load64 ms.mem (slotAddr ms.sp (o + j))) ∧
      (∀ q, (∀ j < k, q ≠ dst j) → s.x q = ms.x q) := by
    intro k
    induction k with
    | zero =>
        exact fun _ => ⟨ms, .refl _, by rw [after_zero, hpc], rfl, rfl, rfl,
          fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨s, hr, hp, hsp, hmem, hout, hx, hq⟩ := ih (by omega)
        obtain ⟨hs, hsk⟩ := hld k (by omega)
        have ck : code s.pc = some (encode (.ldr (dst k) 31 ⟨o + k, hs⟩)) := by
          have := hcode k (by omega)
          rw [hsk] at this
          rw [hp]
          exact this
        have es := exec_ldr_sp P (s := s) (r := dst k) hs (by rw [hsp]; exact hal)
          (fun j hj => by rw [hsp]; exact hmap (8 * (o + k) + j) (by omega))
        let w := load64 s.mem (slotAddr s.sp (o + k))
        refine ⟨{ s.setX (dst k) w with pc := s.pc + 4 }, hr.trans (reach_exec P code ck es
          (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show s.pc + 4 = _
          rw [hp, after_succ]
        · show (s.setX (dst k) w).sp = _
          rw [State.setX_sp, hsp]
        · show (s.setX (dst k) w).mem = _
          rw [State.setX_mem, hmem]
        · show (s.setX (dst k) w).out = _
          rw [State.setX_out, hout]
        · intro j hj
          rw [State.x_withPc]
          by_cases hjk : j = k
          · subst hjk
            rw [State.x_setX_same (hdst j (by omega))]
            show load64 s.mem (slotAddr s.sp (o + j)) = _
            rw [hmem, hsp]
          · rw [State.x_setX_ne (fun e => hjk (hinj k (by omega) j (by omega) e).symm)]
            exact hx j (by omega)
        · intro q hq'
          rw [State.x_withPc, State.x_setX_ne (fun e => hq' k (by omega) e.symm)]
          exact hq q fun j hj => hq' j (by omega)
  obtain ⟨s, hr, hp, hsp, hmem, hout, hx, hq⟩ := key d (Nat.le_refl _)
  exact ⟨s, hr, hp, hsp, hmem, hout, hx, hq⟩

/-- The run of the moves of register `src i` into register `dst i`, in order, where no move
overwrites the source of a later one. -/
theorem run_movs {n : Nat} {dst src : Nat → Fin 32} {moves : List Instr} (hlen : moves.length = n)
    (hmv : ∀ i (hi : i < n), moves[i]'(by omega) = mov (dst i) (src i))
    (hdst : ∀ i < n, (dst i).val < 31) (hinj : ∀ i < n, ∀ j < n, dst i = dst j → i = j)
    (hsafe : ∀ i < n, ∀ j < i, src i ≠ dst j)
    {a : UInt64} {ms : State} (hcode : CodeAt code a moves) (hpc : ms.pc = a) :
    ∃ s, Reach P code ms s ∧ s.pc = after a n ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧
      s.out = ms.out ∧ (∀ i (hi : i < n), s.x (dst i) = ms.x (src i)) ∧
      (∀ q : Fin 32, (∀ i < n, q ≠ dst i) → s.x q = ms.x q) := by
  have key : ∀ k ≤ n, ∃ s, Reach P code ms s ∧ s.pc = after a k ∧ s.sp = ms.sp ∧
      s.mem = ms.mem ∧ s.out = ms.out ∧ (∀ i (hi : i < k), s.x (dst i) = ms.x (src i)) ∧
      (∀ q : Fin 32, (∀ i < k, q ≠ dst i) → s.x q = ms.x q) := by
    intro k
    induction k with
    | zero =>
        exact fun _ => ⟨ms, .refl _, by rw [after_zero, hpc], rfl, rfl, rfl,
          fun i hi => absurd hi (by omega), fun _ _ => rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨s, hr, hpk, hsp, hmem, hout, hx, hq⟩ := ih (by omega)
        have ck : code s.pc = some (encode (mov (dst k) (src k))) := by
          have := hcode k (by omega)
          rw [hmv k (by omega)] at this
          rw [hpk]
          exact this
        let w := s.x 31 ||| s.x (src k)
        have es : LeanExe.A64.exec P (mov (dst k) (src k)) s =
            some { s.setX (dst k) w with pc := s.pc + 4 } := rfl
        have hw : w = ms.x (src k) := by
          show s.x 31 ||| s.x (src k) = _
          rw [x31, UInt64.zero_or, hq _ fun j hj => hsafe k (by omega) j hj]
        refine ⟨{ s.setX (dst k) w with pc := s.pc + 4 }, hr.trans (reach_exec P code ck es
          (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show s.pc + 4 = _
          rw [hpk, after_succ]
        · show (s.setX _ w).sp = _
          rw [State.setX_sp, hsp]
        · show (s.setX _ w).mem = _
          rw [State.setX_mem, hmem]
        · show (s.setX _ w).out = _
          rw [State.setX_out, hout]
        · intro i hi
          rw [State.x_withPc]
          by_cases hik : i = k
          · subst hik
            rw [State.x_setX_same (hdst i (by omega)), hw]
          · rw [State.x_setX_ne (fun e => hik (hinj k (by omega) i (by omega) e).symm)]
            exact hx i (by omega)
        · intro q hq'
          rw [State.x_withPc, State.x_setX_ne (fun e => hq' k (by omega) e.symm)]
          exact hq q fun j hj => hq' j (by omega)
  obtain ⟨s, hr, hpk, hsp, hmem, hout, hx, hq⟩ := key n (Nat.le_refl _)
  exact ⟨s, hr, hpk, hsp, hmem, hout, hx, hq⟩

/-- Element `i` of the first `p` values of `l`, deepest first, is element `l.length - p + i` of
`l`, deepest first. -/
theorem take_reverse_getElem {β : Type} {l : List β} {p i : Nat} (hp : p ≤ l.length)
    (hi : i < p) :
    (l.take p).reverse[i]'(by simp; omega) = l.reverse[l.length - p + i]'(by simp; omega) := by
  rw [List.getElem_reverse, List.getElem_reverse, List.getElem_take]
  congr 1
  simp only [List.length_take]
  omega

/-- The operand stack after a call: the values below the call's results are those below its
arguments. -/
theorem getElem_reverse_call {vs vs' : List Value} {p r d kk : Nat} (hlen : vs.length = d + p)
    (hlen' : vs'.length = r + d) (hdrop : vs'.drop r = vs.drop p) (hk : kk < d) :
    vs'.reverse[kk]'(by simp; omega) = vs.reverse[kk]'(by simp; omega) := by
  rw [List.getElem_reverse, List.getElem_reverse]
  have h1 : vs'[vs'.length - 1 - kk]'(by omega) =
      (vs'.drop r)[d - 1 - kk]'(by simp; omega) := by
    rw [List.getElem_drop]
    congr 1
    omega
  have h2 : vs[vs.length - 1 - kk]'(by omega) = (vs.drop p)[d - 1 - kk]'(by simp; omega) := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [h1, h2]
  exact List.getElem_of_eq hdrop _

/-! ## The call -/

theorem sim_call (f k : Nat) : InstrSim P code (f + 1) (.call k) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc hcl
  obtain ⟨target, ps, rs, hk, htk, hfin, h, p, r, hσl, hpl, hrl0, hpb, hh26, hhr, hlocs,
    spills, moves, res, reloads, g, his, hsl, hsv, hml, hmv, hresl, hresv, hrl, hrv, hbf⟩ :=
    gen_call hgen
  subst his hfin
  have hh : sl.values.length = h := by rw [hinv.len, hσl]
  have hEl : E.locals = E.localTypes.length := rfl
  have hty := hinv.types
  rw [hσl] at hb
  have hbound := hinv.frame.bound
  obtain ⟨hl1, hl2, hl3⟩ := hinv.frame.limit
  have hs26 : spillSlots = 26 := rfl
  generalize hd : h - p = d at *
  have hhd : h = d + p := by omega
  have c1 := (CodeAt.append (code := code)).mp hcode
  have c2 := (CodeAt.append (code := code)).mp c1.1
  have c3 := (CodeAt.append (code := code)).mp c2.1
  have c4 := (CodeAt.append (code := code)).mp c3.1
  have cM : CodeAt code (after a d) moves := by
    have := c4.2
    rwa [hsl] at this
  have cB : code (after a (d + p)) = some (encode (.bl g)) := by
    have := (CodeAt.cons.mp c3.2).1
    rwa [List.length_append, hsl, hml] at this
  have cR : CodeAt code (after a (d + p + 1)) res := by
    have := c2.2
    simp only [List.length_append, List.length_singleton, hsl, hml] at this
    exact this
  have cL : CodeAt code (after a (d + p + 1 + r)) reloads := by
    have := c1.2
    simp only [List.length_append, List.length_singleton, hsl, hml, hresl] at this
    exact this
  have hlenis : (spills ++ moves ++ [Instr.bl g] ++ res ++ reloads).length =
      d + p + 1 + r + d := by
    simp only [List.length_append, List.length_singleton, hsl, hml, hresl, hrl]
  -- the spills and the moves of the arguments
  obtain ⟨s1, r1, p1, sp1, x1, out1, ld1, mem1⟩ := run_strs P code (o := E.locals)
    (src := regOf) hsl (fun j hj => hsv j (by omega)) (by omega) c4.1 hpc hinv.aligned
    (fun j hj => hinv.frame.mapped j (by omega))
  obtain ⟨s2, r2, p2, sp2, mem2, out2, x2a, x2b⟩ := run_movs P code (n := p) (dst := regOf)
    (src := fun i => regOf (d + i)) hml (fun i hi => hmv i (by omega))
    (fun i hi => regOf_lt_31 i (by omega))
    (fun i hi j hj e => regOf_inj i (by omega) j (by omega) e)
    (fun i hi j hj e => absurd (regOf_inj (d + i) (by omega) j (by omega) e) (by omega)) cM p1
  -- the branch to the callee
  let t : State := { s2.setX 30 (s2.pc + 4) with pc := s2.pc + sext 26 g.val * 4 }
  have et : LeanExe.A64.exec P (.bl g) s2 = some t := rfl
  have pB : s2.pc = after a (d + p) := by rw [p2, after_after]
  have pt : t.pc = target := by
    show s2.pc + sext 26 g.val * 4 = _
    rw [pB]
    exact bField_target hbf
  have tx : ∀ q : Fin 32, q ≠ 30 → t.x q = s2.x q := fun q hq => by
    show (s2.setX 30 (s2.pc + 4)).x q = _
    exact State.x_setX_ne (Ne.symm hq)
  have t30 : t.x 30 = after a (d + p + 1) := by
    show (s2.setX 30 (s2.pc + 4)).x 30 = _
    rw [State.x_setX_same (by decide), pB, ← after_succ]
  have tsp : t.sp = ms.sp := by
    show (s2.setX 30 (s2.pc + 4)).sp = _
    rw [State.setX_sp, sp2, sp1]
  have tmem : t.mem = s1.mem := by
    show (s2.setX 30 (s2.pc + 4)).mem = _
    rw [State.setX_mem, mem2]
  have tout : t.out = ms.out := by
    show (s2.setX 30 (s2.pc + 4)).out = _
    rw [State.setX_out, out2, out1]
  have t18 : t.x 18 = ms.x 18 := by
    rw [tx 18 (by decide), x2b 18 (fun i hi => (regOf_ne_18 i (by omega)).symm), x1]
  have t17 : t.x 17 = ms.x 17 := by
    rw [tx 17 (by decide), x2b 17 (fun i hi => (regOf_ne_17 i (by omega)).symm), x1]
  have hsrt : StoreRel P E.cap E.globalTypes st t := hsr.congr t17 t18 fun b hb => by
    rw [tmem]
    exact mem1 b fun j hj => below_slot hl2 hl3 (by omega) hb
  have rt : Reach P code ms t :=
    r1.trans (r2.trans (reach_exec P code (by rw [pB]; exact cB) et (.refl _)))
  -- the callee
  have hvl : sl.values.length = d + p := by omega
  have hargs : StackRel t (sl.values.take ps.length) := by
    rw [hpl]
    refine ⟨by simp; omega, fun i hi => ?_⟩
    simp only [List.length_take] at hi
    have hi' : i < p := by omega
    have e := take_reverse_getElem (l := sl.values) (by omega) hi'
    rw [e, tx _ (regOf_ne_30 i (by omega)), x2a i hi', x1]
    have := hinv.stack.2 (d + i) (by omega)
    simp only [show sl.values.length - p + i = d + i by omega]
    exact this
  have htargs : Typed ps.reverse (sl.values.take ps.length) := by
    rw [← htk]; exact hty.take ps.length
  have hfs : CallOutcome P code E.toShared ps rs sl.values (Wasm.run f m k st sl.values) t :=
    hcl k (target, ps, rs) hk f (by omega) st sl.values t
      (show ps.length ≤ sl.values.length by omega) htargs pt
      (hinv.frame.stack.congr tsp t18) hsrt hargs
  simp only [execOne.eq_def]
  rcases hfs with hov | hfs
  · obtain ⟨ms', hr', hp', hout'⟩ := hov
    exact .inl ⟨⟨k, _, hk⟩, ms', rt.trans hr', hp', by rw [hout', tout]⟩
  refine .inr ?_
  revert hfs
  cases Wasm.run f m k st sl.values with
  | Success vs' st' =>
      intro hfs
      obtain ⟨ms', hr', hp', hsp', h18', hout', hmf', hlen', hdrop', hres', htres', hsr'⟩ :=
        hfs
      have htres : Typed (rs.reverse ++ σ.drop ps.length) vs' := by
        rw [← List.take_append_drop rs.length vs', hdrop']
        exact htres'.append (hty.drop ps.length)
      rw [hpl, hrl0] at hlen'
      rw [hpl, hrl0] at hdrop'
      rw [hrl0] at hres'
      rw [t30] at hp'
      rw [tsp] at hsp'
      rw [t18] at h18'
      rw [tout] at hout'
      -- the results
      obtain ⟨s3, r3, p3, sp3, mem3, out3, x3a, x3b⟩ := run_movs P code (n := r)
        (dst := fun k => regOf (d + (r - 1 - k))) (src := fun k => regOf (r - 1 - k)) hresl
        (fun k hk => hresv k (by omega)) (fun k hk => regOf_lt_31 _ (by omega))
        (fun i hi j hj e => by have := regOf_inj _ (by omega) _ (by omega) e; omega)
        (fun i hi j hj e => by have := regOf_inj _ (by omega) _ (by omega) e; omega) cR hp'
      -- the reloads
      obtain ⟨s4, r4, p4, sp4, mem4, out4, x4a, x4b⟩ := run_ldrs P code (o := E.locals)
        (dst := regOf) hrl (fun j hj => hrv j (by omega)) (fun j hj => regOf_lt_31 j (by omega))
        (fun i hi j hj e => regOf_inj i (by omega) j (by omega) e) (by omega) cL
        (by rw [p3, after_after])
        (by rw [sp3, hsp']; exact hinv.aligned)
        (fun j hj => by rw [sp3, hsp']; exact hinv.frame.mapped j (by omega))
      have hcal : ∀ i < 512, load64 ms'.mem (slotAddr ms.sp i) =
          load64 s1.mem (slotAddr ms.sp i) := by
        intro i hi
        apply load64_congr
        intro kk hkk
        rw [hmf' _ (by rw [tsp]; exact le_slot hkk hl3 hi (Nat.zero_le _)), tmem]
      have hrest : ∀ j < d, s4.x (regOf j) = ms.x (regOf j) := by
        intro j hj
        rw [x4a j hj, mem3, sp3, hsp', hcal _ (by omega), ld1 j hj]
      have hloc' : LocalsRel s4 (sl.params ++ sl.locals) := by
        intro i hi
        have hi' : i < E.locals := by rw [hEl, ← hinv.count]; exact hi
        rw [sp4, sp3, hsp', mem4, mem3, hcal _ (by omega)]
        rw [load64_congr (m' := ms.mem) fun kk hkk =>
          mem1 _ fun j hj => slot_apart (by omega) (by omega) (by omega) kk hkk]
        exact hinv.locals i hi
      have hmf4 : MemFrame ms.sp (E.locals + spillSlots) ms s4 := by
        intro b hb'
        rw [mem4, mem3, hmf' b (by rw [tsp]; omega), tmem]
        exact mem1 b fun j hj => slot_inside (n := E.locals + spillSlots) (by omega) (by omega)
          (hinv.frame.outside (m := E.locals + spillSlots) (Nat.le_refl _) hb')
      have hvl' : vs'.length = d + r := by rw [hlen', hvl]; omega
      have h184 : s4.x 18 = ms.x 18 := by
        rw [x4b 18 (fun j hj => (regOf_ne_18 j (by omega)).symm),
          x3b 18 (fun k hk => (regOf_ne_18 _ (by omega)).symm), h18']
      have hstack' : StackRel s4 vs' := by
        refine ⟨by omega, fun kk hk => ?_⟩
        by_cases hkd : kk < d
        · rw [getElem_reverse_call hvl (by omega) hdrop' hkd, hrest kk hkd]
          exact hinv.stack.2 kk (by omega)
        · have hx : s4.x (regOf kk) = ms'.x (regOf (kk - d)) := by
            rw [x4b _ (fun j hj e => absurd (regOf_inj kk (by omega) j (by omega) e) (by omega))]
            have := x3a (r - 1 - (kk - d)) (by omega)
            rwa [show d + (r - 1 - (r - 1 - (kk - d))) = kk by omega,
              show r - 1 - (r - 1 - (kk - d)) = kk - d by omega] at this
          have e : vs'.reverse[kk]'(by simp; omega) =
              (vs'.take r).reverse[kk - d]'(by simp; omega) := by
            rw [List.getElem_reverse, List.getElem_reverse, List.getElem_take]
            congr 1
            simp only [List.length_take]
            omega
          rw [hx, e]
          exact hres'.2 (kk - d) (by simp; omega)
      have h174 : s4.x 17 = ms'.x 17 := by
        rw [x4b 17 (fun j hj => (regOf_ne_17 j (by omega)).symm),
          x3b 17 (fun k hk => (regOf_ne_17 _ (by omega)).symm)]
      refine ⟨_, rfl, s4, rt.trans (hr'.trans (r3.trans r4)), ?_, ?_, ?_, h184, hmf4,
        ⟨hstack', hloc', hinv.count, hinv.frame.congr (by rw [sp4, sp3, hsp']) h184, htres,
          hinv.ltypes⟩, fun kk hk => hrest kk (by omega),
        hsr'.regs h174 (by rw [h184, h18']) (by rw [mem4, mem3])⟩
      · rw [p4, after_after, hlenis]
      · rw [sp4, sp3, hsp']
      · rw [out4, out3, hout']
  | Trap st' msg =>
      intro hfs
      obtain ⟨ms', hr', hout', hpc'⟩ := hfs
      exact ⟨ms', rt.trans hr', by rw [hout', tout], hpc'⟩
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | Thrown _ _ _ => intro hfs; exact (hfs : False).elim

end LeanExe.A64
