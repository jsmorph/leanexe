import LeanExe.A64.Proof.Call

/-!
The simulation of the instructions that read and write the module's store in the area at X17:
`globalGet` and `globalSet`, an `LDR` or `STR` at `X17 + 8 (i + 1)`; `memorySize`, which loads
the memory's size less 8 from X17 and computes the page count; `load64` and `store64`, which
compare the address with the size less `off + 8`, branch to the stub of an access outside the
memory above it, and access the byte `X17 + 4096 + a + off`; and `memoryGrow`, which computes the
old and the new page counts in X16 and X29, stores the new size less 8 when the new count lies
within the cap, and leaves the old count or `0xFFFFFFFF` in the result's register.  Every store
lies below the stack's limit, so the frames keep their bytes.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Accesses with a base other than SP -/

theorem State.setXsp_eq_setX {s : State} {r : Fin 32} {v : UInt64} (h : r.val < 31) :
    s.setXsp r v = s.setX r v := by
  simp [State.setXsp, State.setX, h]

theorem mapped_base {s : State} {n : Fin 32} {i : Nat}
    (h : ∀ k < 8, P.normal (s.x n + UInt64.ofNat (8 * i + k)) = true) :
    P.mapped (s.x n + UInt64.ofNat (8 * i)) 8 = true := by
  unfold Platform.mapped
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have := h j hj
  rwa [UInt64.ofNat_add, ← UInt64.add_assoc] at this

theorem exec_ldr_base {s : State} {t n : Fin 32} {i : Nat} (hs : i < 4096) (hn : n.val < 31)
    (hmap : ∀ k < 8, P.normal (s.x n + UInt64.ofNat (8 * i + k)) = true) :
    LeanExe.A64.exec P (.ldr t n ⟨i, hs⟩) s =
      some { s.setX t (load64 s.mem (s.x n + UInt64.ofNat (8 * i))) with pc := s.pc + 4 } := by
  have h31 : (n.val != 31) = true := by simp; omega
  simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, mapped_base P hmap,
    Bool.and_self, ↓reduceIte]

theorem exec_str_base {s : State} {t n : Fin 32} {i : Nat} (hs : i < 4096) (hn : n.val < 31)
    (hmap : ∀ k < 8, P.normal (s.x n + UInt64.ofNat (8 * i + k)) = true) :
    LeanExe.A64.exec P (.str t n ⟨i, hs⟩) s =
      some { s with
        mem := store64 s.mem (s.x n + UInt64.ofNat (8 * i)) (s.x t), pc := s.pc + 4 } := by
  have h31 : (n.val != 31) = true := by simp; omega
  simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, mapped_base P hmap,
    Bool.and_self, ↓reduceIte]

/-- Two addresses of the area at `g`, `x` bytes and `y` bytes above it, where `x` lies outside the
8 bytes from `y`, lie at least 8 bytes apart in the order of `store64`. -/
theorem area_off {g : UInt64} {x y : Nat} (hxy : ¬ (y ≤ x ∧ x < y + 8))
    (hx : g.toNat + x < 2 ^ 64) (hy : g.toNat + y + 8 ≤ 2 ^ 64) :
    ¬ g + UInt64.ofNat x - (g + UInt64.ofNat y) < 8 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_add,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  simp only [Nat.reducePow] at *
  omega

/-- Byte `j` of the area, for `j` up to its size, lies `j` bytes above X17 without a wrap. -/
theorem StoreRel.toNat_addr {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α}
    {s : State} (h : StoreRel P cap gts st s) {j : Nat} (hj : j ≤ areaSize cap) :
    (s.x 17 + UInt64.ofNat j).toNat = (s.x 17).toNat + j := by
  have := h.below
  have := (s.x 18).toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- A store below the stack's limit keeps the relation of the frame. -/
theorem Inv.store_below {lts σ : List ValueType} {sl : Locals} {s : State}
    (hinv : Inv P lts σ sl s) {b w p : UInt64} (hb : b.toNat + 8 ≤ (s.x 18).toNat) :
    Inv P lts σ sl { s with mem := store64 s.mem b w, pc := p } := by
  obtain ⟨hl1, hl2, hl3⟩ := hinv.frame.limit
  have hbound := hinv.bound
  refine ⟨hinv.stack.congr fun _ _ => rfl, fun i hi => ?_, hinv.count,
    hinv.frame.congr rfl rfl, hinv.types, hinv.ltypes⟩
  show ValRel _ (load64 (store64 s.mem b w) (slotAddr s.sp i))
  rw [load64_store64_other _ _ _ _ fun k hk => ?_]
  · exact hinv.locals i hi
  · have hi' : i < lts.length := by rw [← hinv.count]; exact hi
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, toNat_slot,
      UInt64.toNat_ofNat']
    have : (8 : UInt64).toNat = 8 := rfl
    rw [this]
    have := b.toNat_lt
    simp only [Nat.reducePow] at *
    omega

/-- A store below the stack's limit keeps the bytes from the end of a frame up. -/
theorem memFrame_store_below {s : State} {n : Nat} {b w p : UInt64}
    (hb : b.toNat + 8 ≤ (s.x 18).toNat) (hl : (s.x 18).toNat ≤ s.sp.toNat) :
    MemFrame s.sp n s { s with mem := store64 s.mem b w, pc := p } := by
  intro c hc
  show store64 s.mem b w c = s.mem c
  refine store64_other _ _ _ _ ?_
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub]
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  have := b.toNat_lt
  have := c.toNat_lt
  simp only [Nat.reducePow] at *
  omega

/-! ## Globals -/

theorem gen_globalGet {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.globalGet i) = .ok (is, fin)) :
    ∃ (hi : i < E.globalTypes.length) (h : i + 1 < 4096), σ.length < 26 ∧
      is = [.ldr (regOf σ.length) 17 ⟨i + 1, h⟩] ∧ fin = some (E.globalTypes[i] :: σ) := by
  unfold genInstr at hg
  by_cases hi : i < E.globalTypes.length
  · rw [List.getElem?_eq_getElem hi] at hg
    by_cases h : i + 1 < 4096
    · by_cases hlt : σ.length < 26
      · simp [h, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg
        exact ⟨hi, h, hlt, hg.1.symm, hg.2.symm⟩
      · obtain ⟨e, he⟩ := opReg_error hlt
        simp [h, he, bind, Except.bind] at hg
    · simp [h, throw, throwThe, MonadExceptOf.throw] at hg
  · rw [List.getElem?_eq_none (by omega)] at hg
    simp [throw, throwThe, MonadExceptOf.throw] at hg

theorem sim_globalGet (F i : Nat) : InstrSim P code F (.globalGet i) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨hi, h, hlt, rfl, rfl⟩ := gen_globalGet hgen
  have hh := hinv.len
  have hgl := hsr.glen
  have hi' : i < st.globals.globals.length := by rw [← hsr.types.length]; exact hi
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      simp only [execOne.eq_def, List.getElem?_eq_getElem hi']
      have hc : code ms.pc = some (encode (.ldr (regOf σ.length) 17 ⟨i + 1, h⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hex := exec_ldr_base P (s := ms) (t := regOf σ.length) h (n := 17) (by decide)
        (fun k hk => hsr.mapped _ (by unfold areaSize; omega))
      have hd := regOf_lt_31 _ hlt
      refine res_outcome P code (hsr.globals i hi') (hsr.types.getElem hi) hinv.types hinv hsr
        (by omega) (by omega) hinv.stack (Reach.single (by rw [step_at hc]; exact hex))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [hpc, after]
      · rw [State.x_withPc, hh, State.x_setX_same hd]
      · intro k hk
        rw [State.x_withPc, State.x_setX_ne (fun e => absurd
          (regOf_inj _ hlt k (by omega) e) (by omega))]
      · rw [State.x_withPc, State.x_setX_ne (regOf_ne_18 _ hlt)]
      · rw [State.x_withPc, State.x_setX_ne (regOf_ne_17 _ hlt)]
      · exact State.setX_sp
      · exact State.setX_mem
      · exact State.setX_out

theorem gen_globalSet {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.globalSet i) = .ok (is, fin)) :
    ∃ (h : i + 1 < 4096), curBase ctl + 1 ≤ σ.length ∧ σ.head? = E.globalTypes[i]? ∧
      σ.length - 1 < 26 ∧ is = [.str (regOf (σ.length - 1)) 17 ⟨i + 1, h⟩] ∧
      fin = some σ.tail := by
  unfold genInstr at hg
  by_cases hc : σ.length < curBase ctl + 1 ∨ σ.head? ≠ E.globalTypes[i]?
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hc' := hc
  simp only [not_or, Ne, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2⟩ := hc'
  by_cases h : i + 1 < 4096
  · by_cases hlt : σ.length - 1 < 26
    · simp [hc, h, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg
      exact ⟨h, by omega, hc2, hlt, hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [hc, h, he, bind, Except.bind] at hg
  · simp [hc, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

/-- The store relation after a store of the word `w` of a value `v` of global `i`'s type into
global `i`'s word. -/
theorem StoreRel.setGlobal {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s : State} (h : StoreRel P cap gts st s) {i : Nat} (hi : i < gts.length) {v : Value}
    {w p : UInt64} (hv : ValRel v w) (ht : HasType gts[i] v) :
    StoreRel P cap gts { st with globals := { globals := st.globals.globals.set i v } }
      { s with mem := store64 s.mem (s.x 17 + UInt64.ofNat (8 * (i + 1))) w, pc := p } := by
  have hgl := h.glen
  have hlen := h.types.length
  have hlt := h.lt_limit (j := 0) (by unfold areaSize; omega)
  have h17 := (s.x 18).toNat_lt
  have hbelow := h.below
  unfold areaSize at hbelow
  have hg : (s.x 17).toNat + 4096 + cap * 65536 < 2 ^ 64 := by omega
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types.set hi ht, ?_, ?_, h.mapped, h.below⟩
  · show load64 (store64 s.mem (s.x 17 + UInt64.ofNat (8 * (i + 1))) w) (s.x 17) = _
    rw [load64_store64_other _ _ _ _ fun k hk => ?_]
    · exact h.size
    · have e : s.x 17 + UInt64.ofNat k = s.x 17 + UInt64.ofNat (0 + k) := by rw [Nat.zero_add]
      rw [e]
      exact area_off (by omega) (by omega) (by omega)
  · intro j hj
    simp only [List.length_set] at hj
    show ValRel _ (load64 (store64 s.mem (s.x 17 + UInt64.ofNat (8 * (i + 1))) w)
      (s.x 17 + UInt64.ofNat (8 * (j + 1))))
    by_cases hji : j = i
    · subst hji
      rw [List.getElem_set_self, load64_store64_same]
      exact hv
    · rw [List.getElem_set_ne (Ne.symm hji), load64_store64_other _ _ _ _ fun k hk => ?_]
      · exact h.globals j hj
      · rw [add_ofNat_add]
        exact area_off (by omega) (by omega) (by omega)
  · intro j hj
    show store64 s.mem (s.x 17 + UInt64.ofNat (8 * (i + 1))) w
      (s.x 17 + UInt64.ofNat (4096 + j)) = _
    rw [store64_other _ _ _ _ (area_off (by omega) (by omega) (by omega))]
    exact h.bytes j hj

theorem sim_globalSet (F i : Nat) : InstrSim P code F (.globalSet i) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨h, hc1, hhead, hlt, rfl, rfl⟩ := gen_globalSet hgen
  have hh := hinv.len
  have hgl := hsr.glen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t, σ0, rfl⟩ : ∃ t σ0, σ = t :: σ0 := by
        cases σ with
        | nil => simp at hc1
        | cons t σ0 => exact ⟨t, σ0, rfl⟩
      have hi : i < E.globalTypes.length := lt_of_getElem?_eq_some (by rw [← hhead]; rfl)
      have hti : t = E.globalTypes[i] := by
        rw [List.getElem?_eq_getElem hi] at hhead
        simpa using hhead
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hi' : i < st.globals.globals.length := by rw [← hsr.types.length]; exact hi
      simp only [execOne.eq_def, hvs, List.getElem?_eq_getElem hi']
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢
      have hc : code ms.pc = some (encode (.str (regOf σ0.length) 17 ⟨i + 1, h⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hex := exec_str_base P (s := ms) (t := regOf σ0.length) h (n := 17) (by decide)
        (fun k hk => hsr.mapped _ (by unfold areaSize; omega))
      have hb8 : (ms.x 17 + UInt64.ofNat (8 * (i + 1))).toNat + 8 ≤ (ms.x 18).toNat := by
        rw [hsr.toNat_addr (j := 8 * (i + 1)) (by unfold areaSize; omega)]
        have := hsr.below
        unfold areaSize at this
        omega
      refine .inr ⟨_, rfl, { ms with
          mem := store64 ms.mem (ms.x 17 + UInt64.ofNat (8 * (i + 1))) (ms.x (regOf σ0.length)),
          pc := ms.pc + 4 }, Reach.single (by rw [step_at hc]; exact hex), ?_, rfl, rfl, rfl,
        memFrame_store_below hb8 hinv.frame.limit.2.1, ?_, fun _ _ => rfl, ?_⟩
      · simp [hpc, after]
      · have := Inv.store_below P (hinv := hinv) (p := ms.pc + 4)
          (w := ms.x (regOf σ0.length)) hb8
        exact ⟨hstack.pop.congr fun _ _ => rfl, this.locals, this.count, this.frame, hty.2,
          this.ltypes⟩
      · have hv : ValRel v (ms.x (regOf σ0.length)) := by
          have := hstack.top
          rwa [hvl] at this
        exact hsr.setGlobal P hi hv (by rw [← hti]; exact hty.1)

/-! ## `memory.size` -/

theorem gen_memorySize {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a .memorySize = .ok (is, fin)) :
    σ.length < 26 ∧ is = [.ldr (regOf σ.length) 17 0, .addImm (regOf σ.length) (regOf σ.length) 8,
      .lsrImm (regOf σ.length) (regOf σ.length) 16] ∧ fin = some (.i32 :: σ) := by
  unfold genInstr at hg
  by_cases hlt : σ.length < 26
  · simp [opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg
    exact ⟨hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [he, bind, Except.bind] at hg

/-- The page count from the memory's size less 8. -/
theorem pages_of_size {pages : Nat} (h1 : 1 ≤ pages) (h2 : pages < 4096) :
    (UInt64.ofNat (pages * 65536 - 8) + UInt64.ofNat 8) >>> UInt64.ofNat 16 =
      UInt64.ofNat pages := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
  omega

theorem toUInt64_ofNat_small {p : Nat} (h : p < 2 ^ 32) :
    (UInt32.ofNat p).toUInt64 = UInt64.ofNat p := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- The run of `LDR`, `ADD`, and `LSR` that computes the page count in register `d` from the
memory's size less 8 at X17.  The other registers, SP, the memory, and the UART's output keep
their values. -/
theorem run_size {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {ms : State}
    {a : UInt64} {d : Fin 32} (hd : d.val < 31)
    (hcode : CodeAt code a [.ldr d 17 0, .addImm d d 8, .lsrImm d d 16]) (hpc : ms.pc = a)
    (hsr : StoreRel P cap gts st ms) :
    ∃ s, Reach P code ms s ∧ s.pc = after a 3 ∧ s.x d = UInt64.ofNat st.mem.pages ∧
      (∀ q, q ≠ d → s.x q = ms.x q) ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.out = ms.out := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  have hex := exec_ldr_base P (s := ms) (t := d) (i := 0) (by decide) (n := 17) (by decide)
    (fun k hk => hsr.mapped _ (by unfold areaSize; omega))
  simp only [Nat.mul_zero, add_ofNat_zero] at hex
  let s1 : State := { ms.setX d (load64 ms.mem (ms.x 17)) with pc := ms.pc + 4 }
  let s2 : State := { s1.setX d (s1.x d + UInt64.ofNat 8) with pc := s1.pc + 4 }
  let s3 : State := { s2.setX d (s2.x d >>> UInt64.ofNat 16) with pc := s2.pc + 4 }
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have e2 : LeanExe.A64.exec P (.addImm d d 8) s1 = some s2 := by
    simp only [exec, State.xsp_eq_x hd, State.setXsp_eq_setX hd]
    rfl
  have e3 : LeanExe.A64.exec P (.lsrImm d d 16) s2 = some s3 := rfl
  have hx1 : s1.x d = UInt64.ofNat (st.mem.pages * 65536 - 8) := by
    show (ms.setX d (load64 ms.mem (ms.x 17))).x d = _
    rw [State.x_setX_same hd, hsr.size]
  have hx2 : s2.x d = UInt64.ofNat (st.mem.pages * 65536 - 8) + UInt64.ofNat 8 := by
    show (s1.setX d (s1.x d + UInt64.ofNat 8)).x d = _
    rw [State.x_setX_same hd, hx1]
  refine ⟨s3, reach_exec P code (by rw [hpc]; exact c0) hex
      (reach_exec P code (by rw [p1]; exact c1) e2
        (reach_exec P code (by rw [p2]; exact c2) e3 (.refl _))), ?_, ?_, fun q hq => ?_, ?_,
    ?_, ?_⟩
  · show s2.pc + 4 = _
    rw [p2, ← after_succ]
  · show (s2.setX d (s2.x d >>> UInt64.ofNat 16)).x d = _
    rw [State.x_setX_same hd, hx2]
    exact pages_of_size hsr.pages.1 (by have := hsr.pages.2; have := hsr.cap_lt; omega)
  · show (s2.setX d (s2.x d >>> UInt64.ofNat 16)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s1.setX d (s1.x d + UInt64.ofNat 8)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (ms.setX d (load64 ms.mem (ms.x 17))).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
  · show (s2.setX d (s2.x d >>> UInt64.ofNat 16)).sp = _
    rw [State.setX_sp]
    show (s1.setX d (s1.x d + UInt64.ofNat 8)).sp = _
    rw [State.setX_sp]
    show (ms.setX d (load64 ms.mem (ms.x 17))).sp = _
    rw [State.setX_sp]
  · show (s2.setX d (s2.x d >>> UInt64.ofNat 16)).mem = _
    rw [State.setX_mem]
    show (s1.setX d (s1.x d + UInt64.ofNat 8)).mem = _
    rw [State.setX_mem]
    show (ms.setX d (load64 ms.mem (ms.x 17))).mem = _
    rw [State.setX_mem]
  · show (s2.setX d (s2.x d >>> UInt64.ofNat 16)).out = _
    rw [State.setX_out]
    show (s1.setX d (s1.x d + UInt64.ofNat 8)).out = _
    rw [State.setX_out]
    show (ms.setX d (load64 ms.mem (ms.x 17))).out = _
    rw [State.setX_out]

theorem sim_memorySize (F : Nat) : InstrSim P code F .memorySize := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨hlt, rfl, rfl⟩ := gen_memorySize hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      simp only [execOne.eq_def, h64, sizeValue_false]
      obtain ⟨s, hrs, hps, hxs, hks, hsps, hmems, houts⟩ :=
        run_size P code (regOf_lt_31 _ hlt) hcode hpc hsr
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      refine res_outcome P code (v := .i32 (UInt32.ofNat st.mem.pages)) (t := .i32)
        (vs := sl.values) (w := UInt64.ofNat st.mem.pages)
        (toUInt64_ofNat_small (p := st.mem.pages) (by omega)).symm trivial hinv.types hinv hsr
        (by omega) (by omega)
        hinv.stack hrs hps (by rw [hh]; exact hxs) ?_ (hks 18 (Ne.symm (regOf_ne_18 _ hlt)))
        (hks 17 (Ne.symm (regOf_ne_17 _ hlt))) hsps hmems houts
      intro k hk
      exact hks _ (fun e => absurd (regOf_inj k (by omega) _ hlt e) (by omega))

/-! ## The bounds check -/

/-- The run of the check of an access at offset `off` to the address in register `r`: the
machine loads the memory's size less 8, subtracts `off`, compares the address with it, and
branches to `tB` when the address lies above it, which is when the access would end beyond the
memory's size.  Otherwise it reaches the access at `after a 4`.  X16 and the flags change. -/
theorem run_bounds {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {ms : State}
    {a tB : UInt64} {r : Fin 32} {off : Nat} (hoff : off < 4096) {g : Fin 524288}
    (hr : r.val < 31) (hr16 : r ≠ 16)
    (hcode : CodeAt code a [.ldr 16 17 0, .subImm 16 16 ⟨off, hoff⟩, .subsReg 31 r 16,
      .bcond 8 g])
    (hg : cbField (after a 3) tB = .ok g) (hpc : ms.pc = a)
    (hsr : StoreRel P cap gts st ms) :
    ∃ s, Reach P code ms s ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.out = ms.out ∧
      (∀ q, q ≠ 16 → s.x q = ms.x q) ∧
      s.pc = if (ms.x r).toNat + off + 8 ≤ st.mem.pages * 65536 then after a 4 else tB := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  have hex := exec_ldr_base P (s := ms) (t := 16) (i := 0) (by decide) (n := 17) (by decide)
    (fun k hk => hsr.mapped _ (by unfold areaSize; omega))
  simp only [Nat.mul_zero, add_ofNat_zero] at hex
  let S := load64 ms.mem (ms.x 17)
  let s1 : State := { ms.setX 16 S with pc := ms.pc + 4 }
  let s2 : State := { s1.setX 16 (s1.x 16 - UInt64.ofNat off) with pc := s1.pc + 4 }
  let s3 : State := { s2.subs 31 (s2.x r) (s2.x 16) with pc := s2.pc + 4 }
  let s4 : State :=
    { s3 with pc := if s3.condHolds 8 then s3.pc + sext 19 g.val * 4 else s3.pc + 4 }
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have p3 : s3.pc = after a 3 := by
    show s2.pc + 4 = _
    rw [p2, ← after_succ]
  have e1 : LeanExe.A64.exec P (.subImm 16 16 ⟨off, hoff⟩) s1 = some s2 := by
    simp only [exec, State.xsp_eq_x (show (16 : Fin 32).val < 31 by decide),
      State.setXsp_eq_setX (show (16 : Fin 32).val < 31 by decide)]
    rfl
  have e2 : LeanExe.A64.exec P (.subsReg 31 r 16) s2 = some s3 := rfl
  have e3 : LeanExe.A64.exec P (.bcond 8 g) s3 = some s4 := rfl
  have hreach : Reach P code ms s4 :=
    reach_exec P code (by rw [hpc]; exact c0) hex
      (reach_exec P code (by rw [p1]; exact c1) e1
        (reach_exec P code (by rw [p2]; exact c2) e2
          (reach_exec P code (by rw [p3]; exact c3) e3 (.refl _))))
  have hx1 : ∀ q, q ≠ 16 → s1.x q = ms.x q := fun q hq => by
    show (ms.setX 16 S).x q = _
    exact State.x_setX_ne (Ne.symm hq)
  have hx2 : ∀ q, q ≠ 16 → s2.x q = ms.x q := fun q hq => by
    show (s1.setX 16 _).x q = _
    rw [State.x_setX_ne (Ne.symm hq), hx1 q hq]
  have hx3 : ∀ q, s3.x q = s2.x q := fun q => by
    show (s2.setX 31 (s2.x r - s2.x 16)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have h16 : s2.x 16 = UInt64.ofNat (st.mem.pages * 65536 - 8 - off) := by
    show (s1.setX 16 (s1.x 16 - UInt64.ofNat off)).x 16 = _
    rw [State.x_setX_same (by decide)]
    have hs1 : s1.x 16 = S := by
      show (ms.setX 16 S).x 16 = _
      exact State.x_setX_same (by decide)
    rw [hs1]
    show load64 ms.mem (ms.x 17) - _ = _
    rw [hsr.size]
    have := hsr.pages
    have := hsr.cap_lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  have hxr : s2.x r = ms.x r := hx2 r hr16
  have hcond : s3.condHolds 8 = !decide ((ms.x r).toNat + off + 8 ≤ st.mem.pages * 65536) := by
    rw [condHolds_8]
    show (decide (s2.x 16 ≤ s2.x r) && !(s2.x r - s2.x 16 == 0)) = _
    rw [hxr, h16]
    have := hsr.pages
    have := hsr.cap_lt
    have hlt := (ms.x r).toNat_lt
    by_cases hc : (ms.x r).toNat + off + 8 ≤ st.mem.pages * 65536
    · have h1 : ¬ (UInt64.ofNat (st.mem.pages * 65536 - 8 - off) ≤ ms.x r ∧
          ms.x r ≠ UInt64.ofNat (st.mem.pages * 65536 - 8 - off)) := by
        rw [UInt64.le_iff_toNat_le, Ne, ← UInt64.toNat_inj, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_true hc]
      by_cases h2 : UInt64.ofNat (st.mem.pages * 65536 - 8 - off) ≤ ms.x r
      · have h3 : ms.x r = UInt64.ofNat (st.mem.pages * 65536 - 8 - off) := by
          exact Classical.byContradiction fun hne => h1 ⟨h2, hne⟩
        rw [h3]
        simp
      · simp [h2]
    · have h1 : UInt64.ofNat (st.mem.pages * 65536 - 8 - off) < ms.x r := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_false hc]
      have h2 : ms.x r - UInt64.ofNat (st.mem.pages * 65536 - 8 - off) ≠ 0 := fun e =>
        absurd ((sub_eq_zero_iff' _ _).mp e) (fun e' => by
          rw [e', UInt64.lt_iff_toNat_lt] at h1
          omega)
      simp [UInt64.le_of_lt h1, h2]
  refine ⟨s4, hreach, ?_, ?_, ?_, fun q hq => ?_, ?_⟩
  · show (s2.setX 31 (s2.x r - s2.x 16)).sp = _
    rw [State.setX_sp]
    show (s1.setX 16 (s1.x 16 - UInt64.ofNat off)).sp = _
    rw [State.setX_sp]
    show (ms.setX 16 S).sp = _
    exact State.setX_sp
  · show (s2.setX 31 (s2.x r - s2.x 16)).mem = _
    rw [State.setX_mem]
    show (s1.setX 16 (s1.x 16 - UInt64.ofNat off)).mem = _
    rw [State.setX_mem]
    show (ms.setX 16 S).mem = _
    exact State.setX_mem
  · show (s2.setX 31 (s2.x r - s2.x 16)).out = _
    rw [State.setX_out]
    show (s1.setX 16 (s1.x 16 - UInt64.ofNat off)).out = _
    rw [State.setX_out]
    show (ms.setX 16 S).out = _
    exact State.setX_out
  · show s3.x q = _
    rw [hx3, hx2 q hq]
  · show (if s3.condHolds 8 then s3.pc + sext 19 g.val * 4 else s3.pc + 4) = _
    rw [hcond, p3]
    by_cases hc : (ms.x r).toNat + off + 8 ≤ st.mem.pages * 65536
    · rw [if_pos hc]
      simp only [decide_eq_true hc, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (after_succ a 3).symm
    · rw [if_neg hc]
      simp only [decide_eq_false hc, Bool.not_false, ite_true]
      exact cbField_target hg

/-! ## `i64.load` -/

theorem gen_load64 {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.load64 off) = .ok (is, fin)) :
    ∃ (h : off.toNat % 8 = 0 ∧ off.toNat < 4096) (g : Fin 524288), curBase ctl + 1 ≤ σ.length ∧
      (σ.head? = some .i32 ∨ σ.head? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, .subImm 16 16 ⟨off.toNat, h.2⟩, .subsReg 31 (regOf (σ.length - 1)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 1)),
        .ldr (regOf (σ.length - 1)) 16 ⟨512 + off.toNat / 8, by have := h.2; omega⟩] ∧
      fin = some (.i64 :: σ.tail) := by
  unfold genInstr at hg
  by_cases hc : σ.length < curBase ctl + 1 ∨ ¬ (σ.head? = some .i32 ∨ σ.head? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2⟩ := hc'
  by_cases h : off.toNat % 8 = 0 ∧ off.toNat < 4096
  · by_cases hlt : σ.length - 1 < 26
    · cases hcb : cbField (after a 3) E.trapBounds with
      | error e => simp [h, opReg_ok hlt, hcb, bind, Except.bind] at hg
      | ok g =>
          simp [h, opReg_ok hlt, hcb, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨h, g, by omega, Classical.byContradiction fun hn =>
            hc2 ⟨fun h => hn (.inl h), fun h => hn (.inr h)⟩, hlt, rfl,
            hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [h, he, bind, Except.bind] at hg
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

/-- A `load64` of 8 bytes that hold those of Talos's memory from `x` reads Talos's `read64`. -/
theorem load64_read64 {mem : UInt64 → UInt8} {b : UInt64} {m : Mem} {x : UInt32}
    (h : ∀ k < 8, mem (b + UInt64.ofNat k) = m.bytes (x.toNat + k)) :
    load64 mem b = m.read64 x := by
  have e0 := h 0 (by decide)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  simp only [load64, Mem.read64]
  rw [e0, show b + 1 = b + UInt64.ofNat 1 from rfl, show b + 2 = b + UInt64.ofNat 2 from rfl,
    show b + 3 = b + UInt64.ofNat 3 from rfl, show b + 4 = b + UInt64.ofNat 4 from rfl,
    show b + 5 = b + UInt64.ofNat 5 from rfl, show b + 6 = b + UInt64.ofNat 6 from rfl,
    show b + 7 = b + UInt64.ofNat 7 from rfl, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- The address of the access at offset `off` to the address `w`: `X17 + w + 4096 + off`, the
byte `w + off` of the memory. -/
theorem access_addr {g w : UInt64} {off k : Nat} (h8 : off % 8 = 0) (hoff : off < 4096) :
    g + w + UInt64.ofNat (8 * (512 + off / 8)) + UInt64.ofNat k =
      g + UInt64.ofNat (4096 + (w.toNat + off + k)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
  have := w.toNat_lt
  simp only [Nat.reducePow] at *
  omega

theorem access_addr' {g w : UInt64} {off k : Nat} (h8 : off % 8 = 0) (hoff : off < 4096) :
    g + w + UInt64.ofNat (8 * (512 + off / 8) + k) =
      g + UInt64.ofNat (4096 + (w.toNat + off + k)) := by
  rw [UInt64.ofNat_add, ← UInt64.add_assoc]
  exact access_addr h8 hoff

/-- The first four instructions of an access: its bounds check. -/
theorem CodeAt.take4 {a : UInt64} {i0 i1 i2 i3 i4 i5 : Instr}
    (h : CodeAt code a [i0, i1, i2, i3, i4, i5]) : CodeAt code a [i0, i1, i2, i3] := by
  intro i hi
  have := h i (by simp at hi ⊢; omega)
  simp at hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> exact this

/-- The value of an address of type `i32` or `i64` on top of a typed stack. -/
theorem addr_cases {t : ValueType} {v : Value} (ht : HasType t v)
    (h : t = .i32 ∨ t = .i64) : (∃ x, v = .i32 x) ∨ (∃ x, v = .i64 x) := by
  rcases h with rfl | rfl <;> cases v <;>
    first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩ | exact ht.elim

theorem sim_load64 (F : Nat) (off : UInt32) : InstrSim P code F (.load64 off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨h, g, hc1, hty0, hlt, hg, rfl, rfl⟩ := gen_load64 hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t, σ0, rfl⟩ : ∃ t σ0, σ = t :: σ0 := by
        cases σ with
        | nil => simp at hc1
        | cons t σ0 => exact ⟨t, σ0, rfl⟩
      simp only [List.length_cons, Nat.add_sub_cancel, List.tail_cons] at hlt hcode hc1 ⊢
      simp only [List.head?_cons, Option.some.injEq] at hty0
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      have htop : ValRel v (ms.x (regOf σ0.length)) := by
        have := hstack.top
        rwa [hvl] at this
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      generalize hn : (ms.x (regOf σ0.length)).toNat = n
      suffices key : ∀ y : UInt32, (n + off.toNat + 8 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl (some (.i64 :: σ0)) (after a 6)
            (if n + off.toNat + 8 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough st { sl with values := .i64 (st.mem.read64 y) :: vs }) ms by
        rcases addr_cases hty.1 hty0 with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · have hx : n = x.toNat := by rw [← hn, htop]; simp
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x + off) fun hin => ?_
          rw [UInt32.toNat_add, ← hx]
          simp only [Nat.reducePow] at *
          omega
        · have hx : n = x.toNat := by rw [← hn, htop]
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x.toUInt32 + off) fun hin => ?_
          rw [UInt32.toNat_add, UInt64.toNat_toUInt32, ← hx]
          simp only [Nat.reducePow] at *
          omega
      intro y hy
      have hr := regOf_lt_31 _ hlt
      have hr16 : regOf σ0.length ≠ 16 := regOf_ne_scratch _ hlt
      obtain ⟨s, hrs, hsps, hmems, houts, hxs, hpcs⟩ :=
        run_bounds P code (r := regOf σ0.length) h.2 hr hr16 (CodeAt.take4 code hcode) hg hpc hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 8 ≤ st.mem.pages * 65536
      · rw [if_neg (by omega)]
        rw [if_pos hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5
        let s5 : State := { s.setX 16 (s.x 17 + s.x (regOf σ0.length)) with pc := s.pc + 4 }
        have e5 : LeanExe.A64.exec P (.addReg 16 17 (regOf σ0.length)) s = some s5 := rfl
        have p5 : s5.pc = after a 5 := by
          show s.pc + 4 = _
          rw [hpcs, ← after_succ]
        have h16 : s5.x 16 = ms.x 17 + ms.x (regOf σ0.length) := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x 16 = _
          rw [State.x_setX_same (by decide), hxs 17 (by decide), hxs _ hr16]
        have hbound : n + off.toNat + 8 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hb : ∀ k < 8, s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8) + k) =
            ms.x 17 + UInt64.ofNat (4096 + (n + off.toNat + k)) := fun k hk => by
          rw [h16, access_addr' h.1 h.2, hn]
        have hex6 := exec_ldr_base P (s := s5) (t := regOf σ0.length)
          (i := 512 + off.toNat / 8) (by have := h.2; omega)
          (n := 16) (by decide) (fun k hk => by
            rw [hb k hk]
            exact hsr.mapped _ (by unfold areaSize; omega))
        have hmem5 : s5.mem = ms.mem := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hval : load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))) =
            st.mem.read64 y := by
          rw [hmem5]
          apply load64_read64
          intro k hk
          rw [UInt64.add_assoc, ← UInt64.ofNat_add, hb k hk, hsr.bytes _ (by omega), hy hin]
        let s6 : State := { s5.setX (regOf σ0.length)
          (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8)))) with
          pc := s5.pc + 4 }
        have hr6 : Reach P code ms s6 :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) hex6 (.refl _)))
        have hk6 : ∀ q, q ≠ regOf σ0.length → q ≠ 16 → s6.x q = ms.x q := fun q hq hq16 => by
          show (s5.setX (regOf σ0.length)
            (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))))).x q = _
          rw [State.x_setX_ne (Ne.symm hq)]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x q = _
          rw [State.x_setX_ne (Ne.symm hq16), hxs q hq16]
        refine res_outcome P code (v := .i64 (st.mem.read64 y)) (t := .i64) (vs := vs)
          (w := s6.x (regOf σ0.length)) ?_ (show HasType .i64 (.i64 (st.mem.read64 y)) from ⟨⟩)
          hty.2 hinv hsr (by omega) (by omega)
          hstack.pop hr6 ?_ (by rw [hvl]) ?_ (hk6 18 (Ne.symm (regOf_ne_18 _ hlt)) (by decide))
          (hk6 17 (Ne.symm (regOf_ne_17 _ hlt)) (by decide)) ?_ ?_ ?_
        · show (s5.setX (regOf σ0.length)
            (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))))).x
              (regOf σ0.length) = _
          rw [State.x_setX_same hr, hval]
        · show s5.pc + 4 = after a 6
          rw [p5, ← after_succ]
        · intro k hk
          exact hk6 _ (fun e => absurd (regOf_inj k (by omega) _ hlt e) (by omega))
            (regOf_ne_scratch k (by omega))
        · show (s5.setX (regOf σ0.length)
            (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))))).sp = _
          rw [State.setX_sp]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        · show (s5.setX (regOf σ0.length)
            (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))))).mem = _
          rw [State.setX_mem, hmem5]
        · show (s5.setX (regOf σ0.length)
            (load64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8))))).out = _
          rw [State.setX_out]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).out = _
          rw [State.setX_out, houts]
      · rw [if_pos (by omega)]
        rw [if_neg hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

/-! ## `i64.store` -/

theorem and255 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

/-- Byte `k` of the 8 bytes that Talos's `write64` writes from `y`. -/
theorem write64_byte_toNat (m : Mem) (y : UInt32) (v : UInt64) {k : Nat} (hk : k < 8) :
    ((m.write64 y v).bytes (y.toNat + k)).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [Mem.write64, UInt64.toNat_and, and255, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow] <;> omega

/-- The machine's store of `v` at byte `y` of the memory in the area at `g` leaves byte `j` of
the memory as Talos's `write64` does. -/
theorem write64_byte {mem : UInt64 → UInt8} {g : UInt64} {m : Mem} {y : UInt32} {v : UInt64}
    {j : Nat} (hy : g.toNat + 4096 + y.toNat + 8 ≤ 2 ^ 64) (hj : g.toNat + 4096 + j < 2 ^ 64)
    (hmem : mem (g + UInt64.ofNat (4096 + j)) = m.bytes j) :
    store64 mem (g + UInt64.ofNat (4096 + y.toNat)) v (g + UInt64.ofNat (4096 + j)) =
      (m.write64 y v).bytes j := by
  by_cases hin : y.toNat ≤ j ∧ j < y.toNat + 8
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ j = y.toNat + k := ⟨j - y.toNat, by omega, by omega⟩
    have e : g + UInt64.ofNat (4096 + (y.toNat + k)) =
        g + UInt64.ofNat (4096 + y.toNat) + UInt64.ofNat k := by
      rw [add_ofNat_add, Nat.add_assoc]
    apply UInt8.toNat_inj.1
    rw [e, store64_at _ _ _ k hk, write64_byte_toNat _ _ _ hk]
  · rw [store64_other _ _ _ _ (area_off (by omega) (by omega) (by omega))]
    have h0 : j ≠ y.toNat := by omega
    have h1 : j ≠ y.toNat + 1 := by omega
    have h2 : j ≠ y.toNat + 2 := by omega
    have h3 : j ≠ y.toNat + 3 := by omega
    have h4 : j ≠ y.toNat + 4 := by omega
    have h5 : j ≠ y.toNat + 5 := by omega
    have h6 : j ≠ y.toNat + 6 := by omega
    have h7 : j ≠ y.toNat + 7 := by omega
    simp only [Mem.write64, h0, h1, h2, h3, h4, h5, h6, h7, ite_false]
    exact hmem

/-- The store relation after a store of `v` at byte `y` of the memory, within its size. -/
theorem StoreRel.write {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s s' : State} (h : StoreRel P cap gts st s) {y : UInt32} {v : UInt64}
    (hy : y.toNat + 8 ≤ st.mem.pages * 65536) (h17 : s'.x 17 = s.x 17) (h18 : s'.x 18 = s.x 18)
    (hmem : s'.mem = store64 s.mem (s.x 17 + UInt64.ofNat (4096 + y.toNat)) v) :
    StoreRel P cap gts { st with mem := st.mem.write64 y v } s' := by
  have hgl := h.glen
  have hlen := h.types.length
  have hbelow := h.below
  have hx18 := (s.x 18).toNat_lt
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ h.pages.2
  unfold areaSize at hbelow
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [hmem, h17, load64_store64_other _ _ _ _ fun k hk =>
      area_off (by omega) (by omega) (by omega)]
    exact h.size
  · intro i hi
    have hi' : i < st.globals.globals.length := hi
    rw [hmem, h17, load64_store64_other _ _ _ _ fun k hk => by
      rw [add_ofNat_add]
      exact area_off (by omega) (by omega) (by omega)]
    exact h.globals i hi
  · intro j hj
    rw [hmem, h17]
    exact write64_byte (by omega) (by omega) (h.bytes j hj)
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

/-- A store below the stack's limit keeps the locals of a frame. -/
theorem LocalsRel.store_below {lts σ : List ValueType} {sl : Locals} {s s' : State}
    (hinv : Inv P lts σ sl s) {b w : UInt64} (hb : b.toNat + 8 ≤ (s.x 18).toNat)
    (hmem : s'.mem = store64 s.mem b w) (hsp : s'.sp = s.sp) :
    LocalsRel s' (sl.params ++ sl.locals) := by
  have := Inv.store_below P hinv (p := s.pc) (w := w) hb
  intro i hi
  rw [hmem, hsp]
  exact this.locals i hi

theorem gen_store64 {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.store64 off) = .ok (is, fin)) :
    ∃ (h : off.toNat % 8 = 0 ∧ off.toNat < 4096) (g : Fin 524288), curBase ctl + 2 ≤ σ.length ∧
      σ.head? = some .i64 ∧ (σ[1]? = some .i32 ∨ σ[1]? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, .subImm 16 16 ⟨off.toNat, h.2⟩, .subsReg 31 (regOf (σ.length - 2)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 2)),
        .str (regOf (σ.length - 1)) 16 ⟨512 + off.toNat / 8, by have := h.2; omega⟩] ∧
      fin = some (σ.drop 2) := by
  unfold genInstr at hg
  by_cases hc : σ.length < curBase ctl + 2 ∨ σ.head? ≠ some .i64 ∨
      ¬ (σ[1]? = some .i32 ∨ σ[1]? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Ne, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2, hc3⟩ := hc'
  by_cases h : off.toNat % 8 = 0 ∧ off.toNat < 4096
  · by_cases hlt : σ.length - 1 < 26
    · have hlt2 : σ.length - 2 < 26 := by omega
      cases hcb : cbField (after a 3) E.trapBounds with
      | error e => simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind] at hg
      | ok g =>
          simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨h, g, by omega, hc2, Classical.byContradiction fun hn =>
            hc3 ⟨fun h => hn (.inl h), fun h => hn (.inr h)⟩, hlt, rfl, hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [h, he, bind, Except.bind] at hg
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

theorem access_addr0 {g w : UInt64} {off : Nat} (h8 : off % 8 = 0) (hoff : off < 4096) :
    g + w + UInt64.ofNat (8 * (512 + off / 8)) = g + UInt64.ofNat (4096 + (w.toNat + off)) := by
  have := access_addr (g := g) (w := w) (k := 0) h8 hoff
  rwa [add_ofNat_zero, Nat.add_zero] at this

theorem sim_store64 (F : Nat) (off : UInt32) : InstrSim P code F (.store64 off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨h, g, hc1, hty0, hty1, hlt, hg, rfl, rfl⟩ := gen_store64 hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t1, t2, σ0, rfl⟩ : ∃ t1 t2 σ0, σ = t1 :: t2 :: σ0 := by
        match σ, hc1 with
        | t1 :: t2 :: σ0, _ => exact ⟨t1, t2, σ0, rfl⟩
      simp only [List.length_cons, Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero,
        show σ0.length + 1 + 1 - 2 = σ0.length by omega] at hlt hcode hc1 ⊢
      simp only [List.head?_cons, Option.some.injEq, List.getElem?_cons_succ,
        List.getElem?_cons_zero] at hty0 hty1
      subst hty0
      obtain ⟨v1, v2, vs, hvs⟩ : ∃ v1 v2 vs, sl.values = v1 :: v2 :: vs := by
        match hv : sl.values with
        | v1 :: v2 :: vs => exact ⟨v1, v2, vs, rfl⟩
        | [] => rw [hv] at hh; simp at hh
        | [_] => rw [hv] at hh; simp at hh
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      have hlt0 : σ0.length < 26 := by omega
      have htop : ValRel v1 (ms.x (regOf (σ0.length + 1))) := by
        have := hstack.top
        rwa [List.length_cons, hvl] at this
      have hadr : ValRel v2 (ms.x (regOf σ0.length)) := by
        have := hstack.pop.top
        rwa [hvl] at this
      obtain ⟨vv, rfl⟩ : ∃ vv, v1 = .i64 vv := by
        cases v1 <;> first | exact ⟨_, rfl⟩ | exact hty.1.elim
      have hvv : ms.x (regOf (σ0.length + 1)) = vv := htop
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      generalize hn : (ms.x (regOf σ0.length)).toNat = n
      suffices key : ∀ y : UInt32, (n + off.toNat + 8 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl (some σ0) (after a 6)
            (if n + off.toNat + 8 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough { st with mem := st.mem.write64 y vv } { sl with values := vs })
            ms by
        rcases addr_cases hty.2.1 hty1 with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · have hx : n = x.toNat := by rw [← hn, hadr]; simp
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x + off) fun hin => ?_
          rw [UInt32.toNat_add, ← hx]
          simp only [Nat.reducePow] at *
          omega
        · have hx : n = x.toNat := by rw [← hn, hadr]
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x.toUInt32 + off) fun hin => ?_
          rw [UInt32.toNat_add, UInt64.toNat_toUInt32, ← hx]
          simp only [Nat.reducePow] at *
          omega
      intro y hy
      have hr := regOf_lt_31 _ hlt0
      have hr16 : regOf σ0.length ≠ 16 := regOf_ne_scratch _ hlt0
      obtain ⟨s, hrs, hsps, hmems, houts, hxs, hpcs⟩ :=
        run_bounds P code (r := regOf σ0.length) h.2 hr hr16 (CodeAt.take4 code hcode) hg hpc hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 8 ≤ st.mem.pages * 65536
      · rw [if_neg (by omega)]
        rw [if_pos hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5
        let s5 : State := { s.setX 16 (s.x 17 + s.x (regOf σ0.length)) with pc := s.pc + 4 }
        have e5 : LeanExe.A64.exec P (.addReg 16 17 (regOf σ0.length)) s = some s5 := rfl
        have p5 : s5.pc = after a 5 := by
          show s.pc + 4 = _
          rw [hpcs, ← after_succ]
        have h16 : s5.x 16 = ms.x 17 + ms.x (regOf σ0.length) := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x 16 = _
          rw [State.x_setX_same (by decide), hxs 17 (by decide), hxs _ hr16]
        have hk5 : ∀ q, q ≠ 16 → s5.x q = ms.x q := fun q hq => by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x q = _
          rw [State.x_setX_ne (Ne.symm hq), hxs q hq]
        have hbound : n + off.toNat + 8 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hb : ∀ k < 8, s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8) + k) =
            ms.x 17 + UInt64.ofNat (4096 + (n + off.toNat + k)) := fun k hk => by
          rw [h16, access_addr' h.1 h.2, hn]
        have hex6 := exec_str_base P (s := s5) (t := regOf (σ0.length + 1))
          (i := 512 + off.toNat / 8) (by have := h.2; omega) (n := 16) (by decide)
          (fun k hk => by
            rw [hb k hk]
            exact hsr.mapped _ (by unfold areaSize; omega))
        have haddr : s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8)) =
            ms.x 17 + UInt64.ofNat (4096 + y.toNat) := by
          rw [h16, access_addr0 h.1 h.2, hn, hy hin]
        have hmem5 : s5.mem = ms.mem := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hv5 : s5.x (regOf (σ0.length + 1)) = vv := by
          rw [hk5 _ (regOf_ne_scratch _ hlt), hvv]
        let s6 : State := { s5 with
          mem := store64 s5.mem (s5.x 16 + UInt64.ofNat (8 * (512 + off.toNat / 8)))
            (s5.x (regOf (σ0.length + 1))), pc := s5.pc + 4 }
        have hr6 : Reach P code ms s6 :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) hex6 (.refl _)))
        have hmem6 : s6.mem = store64 ms.mem (ms.x 17 + UInt64.ofNat (4096 + y.toNat)) vv := by
          show store64 s5.mem _ _ = _
          rw [hmem5, haddr, hv5]
        have hsp6 : s6.sp = ms.sp := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        have h186 : s6.x 18 = ms.x 18 := hk5 18 (by decide)
        have h176 : s6.x 17 = ms.x 17 := hk5 17 (by decide)
        have hb8 : (ms.x 17 + UInt64.ofNat (4096 + y.toNat)).toNat + 8 ≤ (ms.x 18).toNat := by
          rw [hsr.toNat_addr (j := 4096 + y.toNat) (by unfold areaSize; omega)]
          have := hsr.below
          unfold areaSize at this
          omega
        refine .inr ⟨_, rfl, s6, hr6, ?_, hsp6, ?_, h186, fun c hc => ?_, ?_,
          fun k hk => ?_, hsr.write P (hy := by rw [hy hin]; exact hin) h176 h186 hmem6⟩
        · show s5.pc + 4 = after a 6
          rw [p5, ← after_succ]
        · show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).out = _
          rw [State.setX_out, houts]
        · rw [hmem6]
          refine store64_other _ _ _ _ ?_
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub]
          have : (8 : UInt64).toNat = 8 := rfl
          rw [this]
          have := c.toNat_lt
          have := hinv.frame.limit.2.1
          simp only [Nat.reducePow] at *
          omega
        · refine ⟨hstack.pop.pop.congr fun k hk => hk5 _ (regOf_ne_scratch k (by omega)),
            LocalsRel.store_below P (sl := sl) hinv hb8 hmem6 hsp6, hinv.count,
            hinv.frame.congr hsp6 h186, hty.2.2, hinv.ltypes⟩
        · exact hk5 _ (regOf_ne_scratch k (by omega))
      · rw [if_pos (by omega)]
        rw [if_neg hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

/-! ## `memory.grow` -/

theorem gen_memoryGrow {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a .memoryGrow = .ok (is, fin)) :
    ∃ (hc : E.cap < 4096) (gf : Fin 524288) (gd : Fin 67108864), curBase ctl + 1 ≤ σ.length ∧
      σ.head? = some .i32 ∧ σ.length - 1 < 26 ∧ cbField (after a 5) (after a 12) = .ok gf ∧
      bField (after a 11) (after a 16) = .ok gd ∧
      is = [.ldr 16 17 0, .addImm 16 16 8, .lsrImm 16 16 16,
        .addReg 29 16 (regOf (σ.length - 1)), .subsImm 31 29 ⟨E.cap, hc⟩, .bcond 8 gf,
        .movz (regOf (σ.length - 1)) 16 0, .lslv 29 29 (regOf (σ.length - 1)), .subImm 29 29 8,
        .str 29 17 0, mov (regOf (σ.length - 1)) 16, .b gd] ++
        movImm (regOf (σ.length - 1)) 0xFFFFFFFF ∧ fin = some σ := by
  unfold genInstr at hg
  by_cases hc0 : σ.length < curBase ctl + 1 ∨ σ.head? ≠ some .i32
  · simp only [hc0, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc0, ite_false] at hg
  have hc' := hc0
  simp only [not_or, Ne, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2⟩ := hc'
  by_cases hc : E.cap < 4096
  · by_cases hlt : σ.length - 1 < 26
    · cases hf : cbField (after a 5) (after a 12) with
      | error e => simp [hc, opReg_ok hlt, hf, bind, Except.bind] at hg
      | ok gf =>
          cases hd : bField (after a 11) (after a 16) with
          | error e => simp [hc, opReg_ok hlt, hf, hd, bind, Except.bind] at hg
          | ok gd =>
              simp [hc, opReg_ok hlt, hf, hd, bind, Except.bind, pure, Except.pure] at hg
              exact ⟨hc, gf, gd, by omega, hc2, hlt, rfl, rfl, hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [hc, he, bind, Except.bind] at hg
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

theorem CodeAt.drop_take {a : UInt64} {l : List Instr} (h : CodeAt code a l) (k n : Nat)
    (hk : k + n ≤ l.length) : CodeAt code (after a k) ((l.drop k).take n) := by
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [after_after, List.getElem_take, List.getElem_drop]
  exact h (k + i) (by omega)

theorem area_off0 {g : UInt64} {x : Nat} (h8 : 8 ≤ x) (hx : x < 2 ^ 64) :
    ¬ g + UInt64.ofNat x - g < 8 := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  simp only [Nat.reducePow] at *
  omega

theorem cond_hi (x y : UInt64) : (decide (y ≤ x) && !(x - y == 0)) = decide (y < x) := by
  have e : (x - y == 0) = decide (x = y) := by
    by_cases hxy : x = y
    · subst hxy
      simp
    · have : x - y ≠ 0 := fun e => hxy ((sub_eq_zero_iff' x y).mp e)
      simp [hxy, this]
  rw [e]
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  by_cases h : y.toNat < x.toNat
  · simp [h, Nat.le_of_lt h, Nat.ne_of_gt h]
  · simp [h]
    omega

/-- The store relation after a growth of the memory to `new` pages within the cap, whose size
less 8 the machine stores at X17. -/
theorem StoreRel.grow {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s s' : State} (h : StoreRel P cap gts st s) {new : Nat} (h1 : st.mem.pages ≤ new)
    (h2 : new ≤ cap) (h17 : s'.x 17 = s.x 17) (h18 : s'.x 18 = s.x 18)
    (hmem : s'.mem = store64 s.mem (s.x 17) (UInt64.ofNat (new * 65536 - 8))) :
    StoreRel P cap gts { st with mem := { st.mem with pages := new } } s' := by
  have hgl := h.glen
  have hlen := h.types.length
  have hbelow := h.below
  have hx18 := (s.x 18).toNat_lt
  have hpg := h.pages
  unfold areaSize at hbelow
  refine ⟨h.caps, h.cap_lt, h.glen, ⟨by show 1 ≤ new; omega, h2⟩, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [hmem, h17, load64_store64_same]
  · intro i hi
    have hi' : i < st.globals.globals.length := hi
    rw [hmem, h17, load64_store64_other _ _ _ _ fun k hk => by
      rw [add_ofNat_add]
      exact area_off0 (by omega) (by omega)]
    exact h.globals i hi
  · intro j hj
    rw [hmem, h17, store64_other _ _ _ _ (area_off0 (by omega) (by omega))]
    exact h.bytes j hj
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

theorem shl16_sub8 {N : Nat} (h1 : 1 ≤ N) (h2 : N < 2 ^ 33) :
    UInt64.ofNat N <<< ((16 : UInt64) % 64) - UInt64.ofNat 8 = UInt64.ofNat (N * 65536 - 8) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    UInt64.toNat_ofNat']
  show (2 ^ 64 - 8 % 2 ^ 64 + (N % 2 ^ 64) <<< (16 % 64 % 64) % 2 ^ 64) % 2 ^ 64 = _
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow, Nat.reduceMod] at *
  omega

/-- The run of `memory.grow`'s first six instructions from `ms` at `a`, for a delta in register
`r`: the old page count in X16, the new one, `N`, in X29, and a branch to `after a 12` when `N`
exceeds the cap, or else on to `after a 6`. -/
theorem run_grow_head {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {ms : State}
    {a : UInt64} {r : Fin 32} {delta : UInt32} {gf : Fin 524288} (hc : cap < 4096)
    (hr : r.val < 31) (hr16 : r ≠ 16) (hr29 : r ≠ 29)
    (hcode : ∀ i (hi : i < 6), code (after a i) = some (encode
      ([.ldr 16 17 0, .addImm 16 16 8, .lsrImm 16 16 16, .addReg 29 16 r,
        .subsImm 31 29 ⟨cap, hc⟩, .bcond 8 gf] : List Instr)[i]))
    (hgf : cbField (after a 5) (after a 12) = .ok gf) (hpc : ms.pc = a)
    (hsr : StoreRel P cap gts st ms) (hdel : ms.x r = delta.toUInt64) :
    ∃ s, Reach P code ms s ∧
      s.pc = (if st.mem.pages + delta.toNat ≤ cap then after a 6 else after a 12) ∧
      s.x 29 = UInt64.ofNat (st.mem.pages + delta.toNat) ∧
      s.x 16 = UInt64.ofNat st.mem.pages ∧ (∀ q, q ≠ 29 → q ≠ 16 → s.x q = ms.x q) ∧
      s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.out = ms.out := by
  have hS : CodeAt code a [.ldr 16 17 0, .addImm 16 16 8, .lsrImm 16 16 16] := by
    intro i hi
    have := hcode i (by simp at hi; omega)
    simp at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> exact this
  obtain ⟨s3, hr3, hp3, hx16, hk3, hsp3, hmem3, hout3⟩ :=
    run_size P code (d := 16) (by decide) hS hpc hsr
  have hpg := hsr.pages
  let s4 : State := { s3.setX 29 (s3.x 16 + s3.x r) with pc := s3.pc + 4 }
  have e4 : LeanExe.A64.exec P (.addReg 29 16 r) s3 = some s4 := rfl
  let s5 : State := { s4.subs 31 (s4.xsp 29) (UInt64.ofNat cap) with pc := s4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.subsImm 31 29 ⟨cap, hc⟩) s4 = some s5 := rfl
  let s6 : State :=
    { s5 with pc := if s5.condHolds 8 then s5.pc + sext 19 gf.val * 4 else s5.pc + 4 }
  have e6 : LeanExe.A64.exec P (.bcond 8 gf) s5 = some s6 := rfl
  have p4 : s4.pc = after a 4 := by
    show s3.pc + 4 = _
    rw [hp3, ← after_succ]
  have p5 : s5.pc = after a 5 := by
    show s4.pc + 4 = _
    rw [p4, ← after_succ]
  have hx29 : s4.x 29 = UInt64.ofNat (st.mem.pages + delta.toNat) := by
    show (s3.setX 29 (s3.x 16 + s3.x r)).x 29 = _
    rw [State.x_setX_same (by decide), hx16, hk3 _ hr16, hdel]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, UInt64.toNat_ofNat']
    have := delta.toNat_lt
    have := hsr.cap_lt
    simp only [Nat.reducePow] at *
    omega
  have hk5 : ∀ q, s5.x q = s4.x q := fun q => by
    show (s4.setX 31 (s4.xsp 29 - UInt64.ofNat cap)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s5.condHolds 8 = decide (cap < st.mem.pages + delta.toNat) := by
    rw [condHolds_8]
    show (decide (UInt64.ofNat cap ≤ s4.xsp 29) && !(s4.xsp 29 - UInt64.ofNat cap == 0)) = _
    rw [cond_hi, State.xsp_eq_x (by decide), hx29]
    have := delta.toNat_lt
    have := hsr.cap_lt
    apply decide_eq_decide.mpr
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  refine ⟨s6, hr3.trans (reach_exec P code (by rw [hp3]; exact hcode 3 (by decide)) e4
      (reach_exec P code (by rw [p4]; exact hcode 4 (by decide)) e5
        (reach_exec P code (by rw [p5]; exact hcode 5 (by decide)) e6 (.refl _)))),
    ?_, by show s5.x 29 = _; rw [hk5, hx29], ?_, fun q hq hq16 => ?_, ?_, ?_, ?_⟩
  · show (if s5.condHolds 8 then s5.pc + sext 19 gf.val * 4 else s5.pc + 4) = _
    rw [hcond, p5]
    by_cases hN : st.mem.pages + delta.toNat ≤ cap
    · rw [if_pos hN, decide_eq_false (by omega)]
      exact (after_succ a 5).symm
    · rw [if_neg hN, decide_eq_true (by omega)]
      exact cbField_target hgf
  · show s5.x 16 = _
    rw [hk5]
    show (s3.setX 29 (s3.x 16 + s3.x r)).x 16 = _
    rw [State.x_setX_ne (by decide), hx16]
  · show s5.x q = _
    rw [hk5]
    show (s3.setX 29 (s3.x 16 + s3.x r)).x q = _
    rw [State.x_setX_ne (Ne.symm hq), hk3 q hq16]
  · show (s4.setX 31 (s4.xsp 29 - UInt64.ofNat cap)).sp = _
    rw [State.setX_sp]
    show (s3.setX 29 (s3.x 16 + s3.x r)).sp = _
    rw [State.setX_sp, hsp3]
  · show (s4.setX 31 (s4.xsp 29 - UInt64.ofNat cap)).mem = _
    rw [State.setX_mem]
    show (s3.setX 29 (s3.x 16 + s3.x r)).mem = _
    rw [State.setX_mem, hmem3]
  · show (s4.setX 31 (s4.xsp 29 - UInt64.ofNat cap)).out = _
    rw [State.setX_out]
    show (s3.setX 29 (s3.x 16 + s3.x r)).out = _
    rw [State.setX_out, hout3]

/-- The run of a successful growth from `s` at `after a 6`, with the new page count `N` in X29
and the old one in X16: the new size less 8 stored at X17, the old count in register `r`, and a
branch to `after a 16`. -/
theorem run_grow_ok {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {s : State}
    {a : UInt64} {r : Fin 32} {gd : Fin 67108864} {N : Nat}
    (hr : r.val < 31) (hr16 : r ≠ 16) (hr17 : r ≠ 17) (hr29 : r ≠ 29)
    (hcode : ∀ i (hi : i < 6), code (after a (6 + i)) = some (encode
      ([.movz r 16 0, .lslv 29 29 r, .subImm 29 29 8, .str 29 17 0, mov r 16, .b gd] :
        List Instr)[i]))
    (hgd : bField (after a 11) (after a 16) = .ok gd) (hpc : s.pc = after a 6)
    (hsr : StoreRel P cap gts st s) (hN1 : 1 ≤ N) (hN2 : N < 2 ^ 33)
    (h29 : s.x 29 = UInt64.ofNat N) :
    ∃ t, Reach P code s t ∧ t.pc = after a 16 ∧ t.x r = s.x 16 ∧
      (∀ q, q ≠ 29 → q ≠ r → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.out = s.out ∧
      t.mem = store64 s.mem (s.x 17) (UInt64.ofNat (N * 65536 - 8)) := by
  let s7 : State := { s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0) with pc := s.pc + 4 }
  have e7 : LeanExe.A64.exec P (.movz r 16 0) s = some s7 := rfl
  let s8 : State := { s7.setX 29 (s7.x 29 <<< (s7.x r % 64)) with pc := s7.pc + 4 }
  have e8 : LeanExe.A64.exec P (.lslv 29 29 r) s7 = some s8 := rfl
  let s9 : State := { s8.setX 29 (s8.x 29 - UInt64.ofNat 8) with pc := s8.pc + 4 }
  have e9 : LeanExe.A64.exec P (.subImm 29 29 8) s8 = some s9 := by
    simp only [exec, State.xsp_eq_x (show (29 : Fin 32).val < 31 by decide),
      State.setXsp_eq_setX (show (29 : Fin 32).val < 31 by decide)]
    rfl
  have hk9 : ∀ q, q ≠ 29 → q ≠ r → s9.x q = s.x q := fun q hq hqr => by
    show (s8.setX 29 (s8.x 29 - UInt64.ofNat 8)).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s7.setX 29 (s7.x 29 <<< (s7.x r % 64))).x q = _
    rw [State.x_setX_ne (Ne.symm hq)]
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).x q = _
    rw [State.x_setX_ne (Ne.symm hqr)]
  have hex10 := exec_str_base P (s := s9) (t := 29) (i := 0) (by decide) (n := 17)
    (by decide) (fun k hk => by
      rw [hk9 17 (by decide) (Ne.symm hr17)]
      exact hsr.mapped _ (by unfold areaSize; omega))
  simp only [Nat.mul_zero, add_ofNat_zero] at hex10
  let s10 : State := { s9 with mem := store64 s9.mem (s9.x 17) (s9.x 29), pc := s9.pc + 4 }
  let s11 : State := { s10.setX r (s10.x 31 ||| s10.x 16) with pc := s10.pc + 4 }
  have e11 : LeanExe.A64.exec P (mov r 16) s10 = some s11 := rfl
  let s12 : State := { s11 with pc := s11.pc + sext 26 gd.val * 4 }
  have e12 : LeanExe.A64.exec P (.b gd) s11 = some s12 := rfl
  have p7 : s7.pc = after a 7 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have p8 : s8.pc = after a 8 := by
    show s7.pc + 4 = _
    rw [p7, ← after_succ]
  have p9 : s9.pc = after a 9 := by
    show s8.pc + 4 = _
    rw [p8, ← after_succ]
  have p10 : s10.pc = after a 10 := by
    show s9.pc + 4 = _
    rw [p9, ← after_succ]
  have p11 : s11.pc = after a 11 := by
    show s10.pc + 4 = _
    rw [p10, ← after_succ]
  have hx7 : s7.x r = 16 := by
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).x r = _
    rw [State.x_setX_same hr]
    decide
  have hx29_7 : s7.x 29 = UInt64.ofNat N := by
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).x 29 = _
    rw [State.x_setX_ne hr29, h29]
  have hx29_9 : s9.x 29 = UInt64.ofNat (N * 65536 - 8) := by
    show (s8.setX 29 (s8.x 29 - UInt64.ofNat 8)).x 29 = _
    rw [State.x_setX_same (by decide)]
    show (s7.setX 29 (s7.x 29 <<< (s7.x r % 64))).x 29 - UInt64.ofNat 8 = _
    rw [State.x_setX_same (by decide), hx29_7, hx7]
    exact shl16_sub8 hN1 hN2
  have hmem9 : s9.mem = s.mem := by
    show (s8.setX 29 (s8.x 29 - UInt64.ofNat 8)).mem = _
    rw [State.setX_mem]
    show (s7.setX 29 (s7.x 29 <<< (s7.x r % 64))).mem = _
    rw [State.setX_mem]
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).mem = _
    rw [State.setX_mem]
  have c i (hi : i < 6) := hcode i hi
  refine ⟨s12, reach_exec P code (by rw [hpc]; exact c 0 (by decide)) e7
      (reach_exec P code (by rw [p7]; exact c 1 (by decide)) e8
        (reach_exec P code (by rw [p8]; exact c 2 (by decide)) e9
          (reach_exec P code (by rw [p9]; exact c 3 (by decide)) hex10
            (reach_exec P code (by rw [p10]; exact c 4 (by decide)) e11
              (reach_exec P code (by rw [p11]; exact c 5 (by decide)) e12 (.refl _)))))),
    ?_, ?_, fun q hq hqr => ?_, ?_, ?_, ?_⟩
  · show s11.pc + sext 26 gd.val * 4 = _
    rw [p11, bField_target hgd]
  · show (s10.setX r (s10.x 31 ||| s10.x 16)).x r = _
    rw [State.x_setX_same hr]
    have h31 : s10.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
    show s10.x 31 ||| s9.x 16 = _
    rw [h31, UInt64.zero_or, hk9 16 (by decide) (Ne.symm hr16)]
  · show (s10.setX r (s10.x 31 ||| s10.x 16)).x q = _
    rw [State.x_setX_ne (Ne.symm hqr)]
    exact hk9 q hq hqr
  · show (s10.setX r (s10.x 31 ||| s10.x 16)).sp = _
    rw [State.setX_sp]
    show (s8.setX 29 (s8.x 29 - UInt64.ofNat 8)).sp = _
    rw [State.setX_sp]
    show (s7.setX 29 (s7.x 29 <<< (s7.x r % 64))).sp = _
    rw [State.setX_sp]
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).sp = _
    rw [State.setX_sp]
  · show (s10.setX r (s10.x 31 ||| s10.x 16)).out = _
    rw [State.setX_out]
    show (s8.setX 29 (s8.x 29 - UInt64.ofNat 8)).out = _
    rw [State.setX_out]
    show (s7.setX 29 (s7.x 29 <<< (s7.x r % 64))).out = _
    rw [State.setX_out]
    show (s.setX r (UInt64.ofNat 16 <<< UInt64.ofNat 0)).out = _
    rw [State.setX_out]
  · show (s10.setX r (s10.x 31 ||| s10.x 16)).mem = _
    rw [State.setX_mem]
    show store64 s9.mem (s9.x 17) (s9.x 29) = _
    rw [hmem9, hk9 17 (by decide) (Ne.symm hr17), hx29_9]

theorem sim_memoryGrow (F : Nat) : InstrSim P code F .memoryGrow := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _
  obtain ⟨hc, gf, gd, hc1, hhead, hlt, hgf, hgd, rfl, rfl⟩ := gen_memoryGrow hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t, σ0, rfl⟩ : ∃ t σ0, σ = t :: σ0 := by
        cases σ with
        | nil => simp at hc1
        | cons t σ0 => exact ⟨t, σ0, rfl⟩
      simp only [List.length_cons, Nat.add_sub_cancel] at hlt hcode hc1 ⊢
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      obtain ⟨delta, rfl⟩ : ∃ delta, v = .i32 delta := by
        cases v <;> first | exact ⟨_, rfl⟩ | exact hty.1.elim
      have hdel : ms.x (regOf σ0.length) = delta.toUInt64 := by
        have := hstack.top
        rwa [hvl] at this
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      have hgrow : st.mem.grow delta (st.memoryCap m 0) =
          if st.mem.pages + delta.toNat ≤ E.cap then
            some ({ st.mem with pages := st.mem.pages + delta.toNat }, st.mem.pages)
          else none := by
        simp [Mem.grow, Store.memoryCap, hsr.caps]
      simp only [execOne.eq_def, hvs, hgrow]
      have hr := regOf_lt_31 _ hlt
      have hr16 : (regOf σ0.length) ≠ 16 := regOf_ne_scratch _ hlt
      have hr17 : (regOf σ0.length) ≠ 17 := regOf_ne_17 _ hlt
      have hr18 : (regOf σ0.length) ≠ 18 := regOf_ne_18 _ hlt
      have hr29 : (regOf σ0.length) ≠ 29 := regOf_ne_29 _ hlt
      have cfg : ∀ i (hi : i < 12), code (after a i) = some (encode
          ([.ldr 16 17 0, .addImm 16 16 8, .lsrImm 16 16 16, .addReg 29 16 (regOf σ0.length),
            .subsImm 31 29 ⟨E.cap, hc⟩, .bcond 8 gf, .movz (regOf σ0.length) 16 0,
            .lslv 29 29 (regOf σ0.length),
            .subImm 29 29 8, .str 29 17 0, mov (regOf σ0.length) 16, .b gd] : List Instr)[i]) := by
        intro i hi
        have := hcode i (by simp [movImm]; omega)
        rwa [List.getElem_append_left (by simpa using hi)] at this
      obtain ⟨s6, hr6, hp6, hx29, hx16, hk6, hsp6, hmem6, hout6⟩ :=
        run_grow_head P code (r := (regOf σ0.length)) (delta := delta) hc hr hr16 hr29
          (fun i hi => by
            have := cfg i (by omega)
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
              rfl | rfl | rfl | rfl | rfl | rfl <;> exact this)
          hgf hpc hsr hdel
      have hkk : ∀ (u : State), (∀ q, q ≠ 29 → q ≠ 16 → q ≠ (regOf σ0.length) → u.x q = ms.x q) →
          ∀ k < vs.length, u.x (regOf k) = ms.x (regOf k) := fun u hu k hk =>
        hu _ (regOf_ne_29 k (by omega)) (regOf_ne_scratch k (by omega))
          (fun e => absurd (regOf_inj k (by omega) _ hlt e) (by omega))
      by_cases hN : st.mem.pages + delta.toNat ≤ E.cap
      · rw [if_pos hN]
        rw [if_pos hN] at hp6
        have hsr6 : StoreRel P E.cap E.globalTypes st s6 :=
          hsr.regs (hk6 17 (by decide) (by decide)) (hk6 18 (by decide) (by decide)) hmem6
        obtain ⟨s12, hr12, hp12, hx12, hk12, hsp12, hout12, hmem12⟩ :=
          run_grow_ok P code (r := (regOf σ0.length)) (gd := gd)
            (N := st.mem.pages + delta.toNat) hr hr16
            hr17 hr29 (fun i hi => by
              have := cfg (6 + i) (by omega)
              rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
                rfl | rfl | rfl | rfl | rfl | rfl <;> exact this)
            hgd hp6 hsr6 (by omega) (by have := delta.toNat_lt; omega) hx29
        have hk : ∀ q, q ≠ 29 → q ≠ 16 → q ≠ (regOf σ0.length) → s12.x q = ms.x q :=
          fun q hq hq16 hqr => by
            rw [hk12 q hq hqr, hk6 q hq hq16]
        have h1812 : s12.x 18 = ms.x 18 := hk 18 (by decide) (by decide) (Ne.symm hr18)
        have h1712 : s12.x 17 = ms.x 17 := hk 17 (by decide) (by decide) (Ne.symm hr17)
        have hsp : s12.sp = ms.sp := by rw [hsp12, hsp6]
        have hmem : s12.mem = store64 ms.mem (ms.x 17)
            (UInt64.ofNat ((st.mem.pages + delta.toNat) * 65536 - 8)) := by
          rw [hmem12, hmem6, hk6 17 (by decide) (by decide)]
        have hb8 : (ms.x 17).toNat + 8 ≤ (ms.x 18).toNat := by
          have := hsr.below
          unfold areaSize at this
          omega
        refine .inr ⟨_, rfl, s12, hr6.trans hr12, ?_, hsp, by rw [hout12, hout6], h1812,
          fun c hc => ?_, ?_, fun k hk' => hkk s12 hk k (by omega),
          hsr.grow P (by omega) hN h1712 h1812 hmem⟩
        · rw [hp12]
          simp [movImm]
        · rw [hmem]
          refine store64_other _ _ _ _ ?_
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub]
          have : (8 : UInt64).toNat = 8 := rfl
          rw [this]
          have := c.toNat_lt
          have := hinv.frame.limit.2.1
          simp only [Nat.reducePow] at *
          omega
        · refine ⟨StackRel.push hstack.pop (by omega) ?_ (hkk s12 hk),
            LocalsRel.store_below P (sl := sl) hinv hb8 hmem hsp, hinv.count,
            hinv.frame.congr hsp h1812, Typed.cons trivial hty.2, hinv.ltypes⟩
          rw [hvl, hx12, hx16]
          exact (toUInt64_ofNat_small (by omega)).symm
      · rw [if_neg hN]
        rw [if_neg hN] at hp6
        have cM : CodeAt code (after a 12) (movImm (regOf σ0.length) 0xFFFFFFFF) := by
          simpa [movImm] using CodeAt.drop_take code hcode 12 4 (by simp [movImm])
        obtain ⟨s7, hr7, hp7, hx7, hk7, hsp7, hmem7, hout7⟩ :=
          run_movImm P code (d := (regOf σ0.length)) (v := 0xFFFFFFFF) hr cM hp6
        have hk : ∀ q, q ≠ 29 → q ≠ 16 → q ≠ (regOf σ0.length) → s7.x q = ms.x q :=
          fun q hq hq16 hqr => by
            rw [hk7 q hqr, hk6 q hq hq16]
        refine res_outcome P code (v := .i32 0xFFFFFFFF) (t := .i32) (vs := vs)
          (w := 0xFFFFFFFF) rfl trivial hty.2 hinv hsr (by omega) (by omega) hstack.pop
          (hr6.trans hr7) ?_ (by rw [hvl]; exact hx7) (hkk s7 hk)
          (hk 18 (by decide) (by decide) (Ne.symm hr18))
          (hk 17 (by decide) (by decide) (Ne.symm hr17)) (by rw [hsp7, hsp6])
          (by rw [hmem7, hmem6]) (by rw [hout7, hout6])
        rw [hp7, after_after]
        simp [movImm]

end LeanExe.A64
