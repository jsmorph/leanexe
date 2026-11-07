import LeanExe.M7.Proof.Constructs

/-!
The simulation of a function, as `LeanExe/A64/Proof/Function.lean` states it for the AArch64 back
end.  The prologue sets r4 to SP less the frame's size and compares it with the stack's limit,
which `StackOk` places at least `need k` bytes, and so at least the frame's size, below SP; the
branch to the stub of the stack therefore falls through.  The prologue then lowers SP, stores LR
in its slot, and clears the slots of the named declared locals.  The parameters stay in the
caller's outgoing area, where the frame's offsets of the parameters reach them, so Talos's locals
on entry and the state after the prologue satisfy `Inv`.  The body's outcome under the function's
construct reaches the epilogue, which copies the results from the bottom operand slots to the
caller's outgoing area, reloads LR from its slot, which `BodyKeeps` keeps, raises SP, and
returns.  `calls_ok` proves `CallsOk` at every fuel for a table of functions whose code the
generator placed, by strong induction on the fuel.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Immediates, flags, and addresses -/

theorem imm12_field {v : Nat} (hv : v < 4096) :
    imm12 (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v) = UInt32.ofNat v := by
  simp only [imm12, field]
  congr 1
  omega

theorem and_align {x : UInt32} (h : x.toNat % 4 = 0) : x &&& 0xFFFFFFFC = x := by
  apply UInt32.toNat_inj.mp
  have hx := toNat_lt32 x
  have hq : x.toNat / 4 < 2 ^ 30 := by simp only [Nat.reducePow]; omega
  have e1 : x.toNat = (x.toNat / 4) <<< 2 := by
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 2 = 4 from rfl]
    omega
  rw [UInt32.toNat_and, show (0xFFFFFFFC : UInt32).toNat = (2 ^ 30 - 1) <<< 2 from rfl, e1,
    ← Nat.shiftLeft_and_distrib, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hq]

theorem toNat_mod4 {x : UInt32} (h : x % 4 = 0) : x.toNat % 4 = 0 := by
  have := congrArg UInt32.toNat h
  simpa [UInt32.toNat_mod] using this

theorem mod4_of_toNat {x : UInt32} (h : x.toNat % 4 = 0) : x % 4 = 0 :=
  UInt32.toNat_inj.mp (by rw [UInt32.toNat_mod]; exact h)

theorem toNat_sub_frame {sp : UInt32} {F : Nat} (h : F ≤ sp.toNat) :
    (sp - UInt32.ofNat F).toNat = sp.toNat - F := by
  have := toNat_lt32 sp
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- An offset from SP less the frame's size at or above the frame's size, as an offset from SP. -/
theorem sub_frame_above {sp : UInt32} {F j : Nat} (h : F ≤ sp.toNat) (hj : F ≤ j) :
    sp - UInt32.ofNat F + UInt32.ofNat j = sp + UInt32.ofNat (j - F) := by
  apply UInt32.toNat_inj.mp
  have := toNat_lt32 sp
  rw [UInt32.toNat_add, UInt32.toNat_add, toNat_sub_frame h, UInt32.toNat_ofNat',
    UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- An offset from SP less the frame's size, as an offset from the stack's limit `lim`. -/
theorem sub_frame_below {sp lim : UInt32} {F : Nat} (j : Nat) (h : lim.toNat + F ≤ sp.toNat) :
    sp - UInt32.ofNat F + UInt32.ofNat j = lim + UInt32.ofNat (sp.toNat - lim.toNat - F + j) := by
  apply UInt32.toNat_inj.mp
  have := toNat_lt32 sp
  have := toNat_lt32 lim
  rw [UInt32.toNat_add, UInt32.toNat_add, toNat_sub_frame (by omega), UInt32.toNat_ofNat',
    UInt32.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

/-- A word whose bytes all keep their values from `lo` up keeps its value. -/
theorem load32_above {m m' : UInt32 → UInt8} {lo a : UInt32}
    (h : ∀ b : UInt32, lo.toNat ≤ b.toNat → m' b = m b) (ha : lo.toNat ≤ a.toNat)
    (ha4 : a.toNat + 4 ≤ 4294967296) : load32 m' a = load32 m a :=
  load32_congr fun k hk => h _ (by rw [toNat_add_ofNat (by omega)]; omega)

theorem load32_zero {m : UInt32 → UInt8} {a : UInt32} (h : ∀ k < 4, m (a + UInt32.ofNat k) = 0) :
    load32 m a = 0 := by
  rw [load32_congr (m' := m) (m := fun _ => 0) h]
  simp [load32]

/-! ## The clearing of the named locals -/

/-- `c` stores r0 into the two words of the slot at the offset `x` from SP. -/
def ZeroCode (c : List Instr) (x : Nat) : Prop :=
  ∃ h0 h1, c = [.strSp 0 ⟨x, h0⟩, .strSp 0 ⟨x + 4, h1⟩]

theorem ZeroCode.unique {c : List Instr} {x y : Nat} (hx : ZeroCode c x) (hy : ZeroCode c y) :
    x = y := by
  obtain ⟨_, _, rfl⟩ := hx
  obtain ⟨_, _, e⟩ := hy
  simp at e
  omega

theorem store2_zero {m : UInt32 → UInt8} {sp b : UInt32} {x : Nat} (h : ¬ Outside sp x b) :
    store32 (store32 m (sp + UInt32.ofNat x) 0) (sp + UInt32.ofNat (x + 4)) 0 b = 0 := by
  unfold Outside at h
  have hb := toNat_lt32 b
  have hs := toNat_lt32 sp
  have e1 : (b - (sp + UInt32.ofNat x)).toNat =
      (b.toNat + 4294967296 - (sp.toNat + x % 4294967296) % 4294967296) % 4294967296 := by
    rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have e2 : (b - (sp + UInt32.ofNat (x + 4))).toNat =
      (b.toNat + 4294967296 - (sp.toNat + (x + 4) % 4294967296) % 4294967296) % 4294967296 := by
    rw [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  simp only [store32]
  by_cases h2 : b - (sp + UInt32.ofNat (x + 4)) < 4
  · rw [ite_eq_left h2, UInt32.zero_shiftRight]
    rfl
  · by_cases h1 : b - (sp + UInt32.ofNat x) < 4
    · rw [ite_eq_right h2, ite_eq_left h1, UInt32.zero_shiftRight]
      rfl
    · exfalso
      rw [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl] at h1 h2
      omega

theorem length_zeros : ∀ {codes : List (List Instr)},
    (∀ j (hj : j < codes.length), ∃ o, ZeroCode codes[j] o) →
    codes.flatten.length = 2 * codes.length
  | [], _ => rfl
  | c :: cs, h => by
      obtain ⟨o, h0, h1, rfl⟩ := h 0 (by simp)
      rw [List.flatten_cons, List.length_append,
        length_zeros (codes := cs) fun j hj => h (j + 1) (by simp; omega)]
      simp only [List.length_cons, List.length_nil]
      omega

theorem wide_zeros : ∀ {codes : List (List Instr)},
    (∀ j (hj : j < codes.length), ∃ o, ZeroCode codes[j] o) →
    codes.flatten.all Instr.wide = true
  | [], _ => rfl
  | c :: cs, h => by
      obtain ⟨o, h0, h1, rfl⟩ := h 0 (by simp)
      rw [List.flatten_cons, List.all_append,
        wide_zeros (codes := cs) fun j hj => h (j + 1) (by simp; omega)]
      rfl

/-- Placed stores of r0, which holds 0, into slots whose words pass the checks: every byte of
each slot holds 0, and every byte outside the slots keeps its value. -/
theorem run_zeros {s : State} (h0 : s.r 0 = 0) :
    ∀ {codes : List (List Instr)},
      (∀ j (hj : j < codes.length), ∃ o, ZeroCode codes[j] o ∧
        WordOk P (s.sp + UInt32.ofNat o) ∧ WordOk P (s.sp + UInt32.ofNat (o + 4))) →
      CodeAt code s.pc codes.flatten →
      ∃ t, Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat (8 * codes.length) ∧ t.sp = s.sp ∧
        t.lr = s.lr ∧ t.trace = s.trace ∧ t.reads = s.reads ∧
        (∀ j (hj : j < codes.length) o, ZeroCode codes[j] o → ∀ b, ¬ Outside s.sp o b →
          t.mem b = 0) ∧
        ∀ b, (∀ j (hj : j < codes.length) o, ZeroCode codes[j] o → Outside s.sp o b) →
          t.mem b = s.mem b
  | [], _, _ => ⟨s, .refl _, by simp, rfl, rfl, rfl, rfl, fun j hj => absurd hj (by simp),
      fun _ _ => rfl⟩
  | c :: cs, hz, hc => by
      obtain ⟨o0, ⟨q0, q1, hc0⟩, w0, w1⟩ := hz 0 (by simp)
      simp only [List.getElem_cons_zero] at hc0
      subst hc0
      have hok : SlotsOk P s.sp [.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩] :=
        slotsOk_st w0 (slotsOk_st w1 (slotsOk_nil _))
      rw [List.flatten_cons] at hc
      obtain ⟨hc1, hc2⟩ := CodeAt.append.mp hc
      obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok hc1
      have hm1 : (slotRun P σ [.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩] s).mem =
          store32 (store32 s.mem (s.sp + UInt32.ofNat o0) (s.r 0))
            (s.sp + UInt32.ofNat (o0 + 4)) (s.r 0) := rfl
      rw [h0] at hm1
      have hr0 : (slotRun P σ [.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩] s).r 0 = 0 := h0
      rw [show s.pc + UInt32.ofNat (codeSize [Instr.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩]) =
          (slotRun P σ [.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩] s).pc by rw [p1]; rfl] at hc2
      generalize slotRun P σ [.strSp 0 ⟨o0, q0⟩, .strSp 0 ⟨o0 + 4, q1⟩] s = s1
        at r1 p1 sp1 lr1 tr1 rd1 hm1 hr0 hc2
      obtain ⟨t, rt, pt, spt, lrt, trt, rdt, hzt, hmt⟩ :=
        run_zeros (s := s1) hr0 (codes := cs) (fun j hj => by
          obtain ⟨o, hzo, wa, wb⟩ := hz (j + 1) (by simp; omega)
          exact ⟨o, hzo, by rw [sp1]; exact wa, by rw [sp1]; exact wb⟩) hc2
      refine ⟨t, r1.trans rt, ?_, spt.trans sp1, lrt.trans lr1, trt.trans tr1, rdt.trans rd1,
        fun j hj o hzo b hb => ?_, fun b hb => ?_⟩
      · rw [pt, p1]
        simp only [List.length_cons, List.length_nil]
        addr_eq
      · cases j with
        | zero =>
            have eo : o = o0 := ZeroCode.unique hzo ⟨q0, q1, rfl⟩
            subst eo
            by_cases hin : ∃ j, ∃ hj : j < cs.length, ∃ o', ZeroCode cs[j] o' ∧
                ¬ Outside s1.sp o' b
            · obtain ⟨j, hj, o', hz', hno⟩ := hin
              exact hzt j hj o' hz' b hno
            · rw [hmt b fun j hj o' hz' => Classical.byContradiction fun hno =>
                hin ⟨j, hj, o', hz', hno⟩, hm1]
              exact store2_zero hb
        | succ j =>
            exact hzt j (by simp at hj; omega) o hzo b (by rw [sp1]; exact hb)
      · rw [hmt b fun j hj o hzo => by rw [sp1]; exact hb (j + 1) (by simp; omega) o hzo, hm1]
        exact store2_outside (hb 0 (by simp) o0 ⟨q0, q1, rfl⟩)

/-- The clearing of the named declared locals of the frame `fr` that the generator emits. -/
def ClearCode (fr : Frame) (clear : List Instr) : Prop :=
  (fr.named = [] ∧ clear = []) ∨
    ∃ codes : List (List Instr), codes.length = fr.named.length ∧
      (∀ j (hj : j < codes.length), ∃ i o, fr.named[j]? = some i ∧ fr.localOff i = some o ∧
        ZeroCode codes[j] o) ∧ clear = Instr.movImm 0 0 :: codes.flatten

theorem ClearCode.wide {fr : Frame} {clear : List Instr} (h : ClearCode fr clear) :
    clear.all Instr.wide = true := by
  rcases h with ⟨-, rfl⟩ | ⟨codes, -, hz, rfl⟩
  · rfl
  · rw [List.all_cons, wide_zeros fun j hj => by
      obtain ⟨i, o, -, -, h⟩ := hz j hj
      exact ⟨o, h⟩]
    rfl

/-- The offset of a named local's slot. -/
theorem Frame.localOff_named {fr : Frame} {i o : Nat} (hp : fr.params ≤ i)
    (h : fr.localOff i = some o) :
    ∃ j, j < fr.named.length ∧ fr.named[j]? = some i ∧ o = 8 * (fr.out + j) := by
  rcases Frame.localOff_eq h with ⟨hi, -⟩ | hj
  · omega
  · exact hj

/-- The clearing of the named locals of the frame `fr`, whose names lie at or above its
parameters: every byte of the slot of a named local holds 0, and every byte outside the slots of
the named locals keeps its value. -/
theorem run_clearing {fr : Frame} {clear : List Instr} (hcc : ClearCode fr clear)
    (hge : ∀ i ∈ fr.named, fr.params ≤ i) {s : State}
    (hw : ∀ j < fr.named.length, WordOk P (s.sp + UInt32.ofNat (8 * (fr.out + j))) ∧
      WordOk P (s.sp + UInt32.ofNat (8 * (fr.out + j) + 4)))
    (hc : CodeAt code s.pc clear) :
    ∃ t, Reach P σ code s t ∧ t.pc = after s.pc clear.length ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      t.trace = s.trace ∧ t.reads = s.reads ∧
      (∀ i o, fr.params ≤ i → fr.localOff i = some o → ∀ b, ¬ Outside s.sp o b →
        t.mem b = 0) ∧
      ∀ b, (∀ j < fr.named.length, Outside s.sp (8 * (fr.out + j)) b) → t.mem b = s.mem b := by
  rcases hcc with ⟨hn, rfl⟩ | ⟨codes, hcl, hz, rfl⟩
  · refine ⟨s, .refl _, by rw [after_eq]; simp, rfl, rfl, rfl, rfl, fun i o hi ho => ?_,
      fun _ _ => rfl⟩
    obtain ⟨j, hj, -⟩ := Frame.localOff_named hi ho
    rw [hn] at hj
    exact absurd hj (by simp)
  -- the offsets of the stores
  have hzo : ∀ j (hj : j < codes.length), ∃ o, ZeroCode codes[j] o ∧
      ∃ j', j' < fr.named.length ∧ o = 8 * (fr.out + j') := fun j hj => by
    obtain ⟨i, o, hi, ho, hzc⟩ := hz j hj
    have hpi := hge i (List.mem_of_getElem? hi)
    obtain ⟨j', hj', -, rfl⟩ := Frame.localOff_named hpi ho
    exact ⟨_, hzc, j', hj', rfl⟩
  -- `MOV r0, #0`
  have hok : SlotsOk P s.sp [Instr.movImm 0 0] :=
    slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_nil _)
  have hc' : CodeAt code s.pc ([Instr.movImm 0 0] ++ codes.flatten) := hc
  obtain ⟨hc1, hc2⟩ := hc'.split_wide rfl
  obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok hc1
  have hr0 : (slotRun P σ [Instr.movImm 0 0] s).r 0 = 0 := by
    simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    try rfl
  have hm1 : (slotRun P σ [Instr.movImm 0 0] s).mem = s.mem := rfl
  rw [show after s.pc [Instr.movImm 0 0].length = (slotRun P σ [Instr.movImm 0 0] s).pc by
    rw [p1, after_eq] <;> rfl] at hc2
  generalize slotRun P σ [Instr.movImm 0 0] s = s1 at r1 p1 sp1 lr1 tr1 rd1 hr0 hm1 hc2
  obtain ⟨t, rt, pt, spt, lrt, trt, rdt, hzt, hmt⟩ := run_zeros (s := s1) hr0 (codes := codes)
    (fun j hj => by
      obtain ⟨o, hzc, j', hj', rfl⟩ := hzo j hj
      exact ⟨_, hzc, by rw [sp1]; exact (hw j' hj').1, by rw [sp1]; exact (hw j' hj').2⟩) hc2
  have hlen := length_zeros fun j hj => (hzo j hj).imp fun _ h => h.1
  refine ⟨t, r1.trans rt, ?_, spt.trans sp1, lrt.trans lr1, trt.trans tr1, rdt.trans rd1,
    fun i o hi ho b hb => ?_, fun b hb => ?_⟩
  · rw [pt, p1]
    simp only [List.length_cons, List.length_nil, hlen, after_eq]
    addr_eq
  · obtain ⟨j, hj, hji, rfl⟩ := Frame.localOff_named hi ho
    obtain ⟨i', o', hi', ho', hzc⟩ := hz j (by omega)
    rw [hji] at hi'
    cases hi'
    rw [ho] at ho'
    cases ho'
    exact hzt j (by omega) _ hzc b (by rw [sp1]; exact hb)
  · rw [hmt b fun j hj o hzc => by
      obtain ⟨o', hzc', j', hj', rfl⟩ := hzo j hj
      rw [ZeroCode.unique hzc hzc', sp1]
      exact hb j' hj', hm1]

/-! ## The generator's function -/

theorem frameOf_named_ge {sig : Nat → Option (Nat × Nat)} {f : Function} {i : Nat}
    (h : i ∈ (frameOf sig f).named) : f.params.length ≤ i := by
  simp only [frameOf, List.mem_filterMap, List.mem_range] at h
  obtain ⟨j, -, hj⟩ := h
  split at hj
  · simp at hj
    omega
  · cases hj

/-- What the generator's code `is` of the function `f`, with the frame `fr`, placed at `entry`,
consists of: the prologue, the clearing of the named locals, the body, the copies of the
results, and the epilogue, with the checks that the generator made. -/
def FunctionCode (callee : Table) (S : Shared) (entry : UInt32) (f : Function) (fr : Frame)
    (is : List Instr) : Prop :=
  (f.params ++ f.results).all intType = true ∧
    (∀ i ∈ fr.named, ∃ t, (f.params ++ f.locals)[i]? = some t ∧ intType t = true) ∧
    fr.size < 4096 ∧ fr.size + 8 * max f.params.length f.results.length ≤ 4096 ∧
    ∃ (hlr : fr.lrOff < 4096) (oq : Int) (clear body : List Instr)
      (fin : Option (List ValueType)) (results : List (List Instr)),
      oq % 2 = 0 ∧ -1048576 ≤ oq ∧ oq < 1048576 ∧
      after entry 4 + 4 + UInt32.ofInt oq = S.trapStack ∧ ClearCode fr clear ∧
      genList { toShared := S, frame := fr, localTypes := f.params ++ f.locals, callee }
        [⟨after (after entry (prologueSize + clear.length))
            (listSize (sigOf callee) [f.results.length] 0 f.body).1, f.results.reverse, 0⟩] []
        (after entry (prologueSize + clear.length)) f.body = .ok (body, fin) ∧
      (∀ x, fin = some x → x = f.results.reverse) ∧ results.length = f.results.length ∧
      (∀ k (hk : k < results.length), k < fr.height ∧
        CopyCode results[k] (fr.opAt k) (fr.size + 8 * k)) ∧
      is = [Instr.subwSpOf 4 fr.size, Instr.movwOf 5 (S.limit.toNat % 65536),
          Instr.movtOf 5 (S.limit.toNat / 65536), Instr.cmpReg 4 5, Instr.bcondTo condCC oq,
          Instr.subwSpSpOf fr.size, Instr.strLr ⟨fr.lrOff, hlr⟩] ++ clear ++ body ++
        results.flatten ++
        [Instr.ldrLr ⟨fr.lrOff, hlr⟩, Instr.addwSpSpOf fr.size, Instr.bxLr, Instr.bxLr]

theorem gen_function {callee : Table} {S : Shared} {entry : UInt32} {f : Function}
    {is : List Instr} {fr : Frame} (hfr : frameOf (sigOf callee) f = fr)
    (hg : genFunction callee S entry f = .ok is) : FunctionCode callee S entry f fr is := by
  subst hfr
  by_cases h1 : (f.params ++ f.results).all intType = true
  case neg =>
    simp [genFunction, h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases h2 : (frameOf (sigOf callee) f).named.all
      (fun i => ((f.params ++ f.locals)[i]?.map intType).getD false) = true
  case neg =>
    simp [genFunction, h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases h3 : 4096 ≤ (frameOf (sigOf callee) f).size ∨
      4096 < (frameOf (sigOf callee) f).size + 8 * max f.params.length f.results.length
  · simp [genFunction, h1, h2, h3, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hnm : ∀ i ∈ (frameOf (sigOf callee) f).named,
      ∃ t, (f.params ++ f.locals)[i]? = some t ∧ intType t = true := by
    intro i hi
    have := List.all_eq_true.mp h2 i hi
    cases ht : (f.params ++ f.locals)[i]? with
    | none => rw [ht] at this; simp at this
    | some t => rw [ht] at this; exact ⟨t, rfl, by simpa using this⟩
  -- what the parts of the code give, once the clearing is known
  let E : Env :=
    { toShared := S, frame := frameOf (sigOf callee) f, localTypes := f.params ++ f.locals,
      callee := callee }
  have key : ∀ (clear : List Instr) (i0 : Instr) (c1 c5 : Fin 4096)
      (v3 : List Instr × Option (List ValueType)) (v4 : List (List Instr)),
      ClearCode (frameOf (sigOf callee) f) clear →
      bcondAt condCC (after entry 4) S.trapStack = .ok i0 →
      imm (frameOf (sigOf callee) f).lrOff = .ok c1 →
      genList E
        [⟨after (after entry (prologueSize + clear.length))
            (listSize (sigOf callee) [f.results.length] 0 f.body).1, f.results.reverse, 0⟩] []
        (after entry (prologueSize + clear.length)) f.body = .ok v3 →
      ¬ Option.any (fun x => !decide (x = f.results.reverse)) v3.2 = true →
      (List.range f.results.length).mapM (fun k =>
        E.op k >>= fun v => copySlot v ((frameOf (sigOf callee) f).size + 8 * k)) = .ok v4 →
      imm (frameOf (sigOf callee) f).lrOff = .ok c5 →
      is = [Instr.subwSpOf 4 (frameOf (sigOf callee) f).size,
          Instr.movwOf 5 (S.limit.toNat % 65536), Instr.movtOf 5 (S.limit.toNat / 65536),
          Instr.cmpReg 4 5, i0, Instr.subwSpSpOf (frameOf (sigOf callee) f).size,
          Instr.strLr c1] ++ clear ++ v3.1 ++ v4.flatten ++
        [Instr.ldrLr c5, Instr.addwSpSpOf (frameOf (sigOf callee) f).size, Instr.bxLr,
          Instr.bxLr] → FunctionCode callee S entry f (frameOf (sigOf callee) f) is := by
    intro clear i0 c1 c5 v3 v4 hcc hi0 hc1 hv3 hend hv4 hc5 his
    obtain ⟨oq, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi0
    obtain ⟨hlr, rfl⟩ := imm_ok hc1
    obtain ⟨hlr5, rfl⟩ := imm_ok hc5
    obtain ⟨hl4, hr4⟩ := mapM_ok hv4
    simp only [List.length_range] at hl4
    refine ⟨h1, hnm, by omega, by omega, hlr, oq, clear, v3.1, v3.2, v4, q1, q2, q3, q4, hcc,
      hv3, any_ne hend, hl4, fun k hk => ?_, his⟩
    have := hr4 k (by simp; omega) hk
    simp only [List.getElem_range] at this
    obtain ⟨o, ho, hc⟩ := except_bind_ok.mp this
    obtain ⟨hkh, rfl⟩ := Env.op_ok ho
    obtain ⟨g0, g1, g2, g3, e⟩ := copySlot_ok hc
    exact ⟨hkh, g0, g1, g2, g3, e⟩
  by_cases hn : (frameOf (sigOf callee) f).named = []
  · simp [genFunction, h1, h3, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hg
    split at hg
    · cases hg
    rename_i i0 hi0
    split at hg
    · cases hg
    rename_i c1 hc1
    split at hg
    · cases hg
    rename_i v3 hv3
    split at hg
    · cases hg
    rename_i hend
    split at hg
    · cases hg
    rename_i v4 hv4
    split at hg
    · cases hg
    rename_i c5 hc5
    cases hg
    exact key [] i0 c1 c5 v3 v4 (.inl ⟨hn, rfl⟩) hi0 hc1 hv3 hend hv4 (by cases hc5; exact hc1)
      (by simp)
  · simp [genFunction, h1, h2, h3, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hg
    split at hg
    · cases hg
    rename_i i0 hi0
    split at hg
    · cases hg
    rename_i c1 hc1
    split at hg
    · cases hg
    rename_i v2 hv2
    split at hg
    · cases hg
    rename_i v3 hv3
    split at hg
    · cases hg
    rename_i hend
    split at hg
    · cases hg
    rename_i v4 hv4
    split at hg
    · cases hg
    rename_i c5 hc5
    cases hg
    rw [← List.length_flatten] at hv3
    obtain ⟨hl2, hr2⟩ := mapM_ok hv2
    refine key (Instr.movImm 0 0 :: v2.flatten) i0 c1 c5 v3 v4 (.inr ⟨v2, hl2, fun j hj => ?_,
      rfl⟩) hi0 hc1 hv3 hend hv4 (by cases hc5; exact hc1) (by simp)
    have := hr2 j (by omega) hj
    split at this
    · cases this
    rename_i o ho
    exact ⟨_, o, List.getElem?_eq_getElem (by omega), Env.loc_ok ho, stPair_ok this⟩

/-! ## The prologue and the epilogue -/

/-- The prologue of a frame of `F` bytes whose LR slot lies at `lr`, from a state whose SP lies at
least `F` bytes above the stack's limit `lim`: the branch to the stub of the stack falls through,
SP drops by `F`, and the LR slot holds LR. -/
theorem run_prologue {F lr : Nat} (hF : F < 4096) (hlr4 : lr < 4096) (hF4 : F % 4 = 0)
    {lim : UInt32} {oq : Int} {entry : UInt32} (q1 : oq % 2 = 0) (q2 : -1048576 ≤ oq)
    (q3 : oq < 1048576)
    (hcode : CodeAt code entry [Instr.subwSpOf 4 F, Instr.movwOf 5 (lim.toNat % 65536),
      Instr.movtOf 5 (lim.toNat / 65536), Instr.cmpReg 4 5, Instr.bcondTo condCC oq,
      Instr.subwSpSpOf F, Instr.strLr ⟨lr, hlr4⟩])
    {ms : State} (hpc : ms.pc = entry) (hal : ms.sp.toNat % 4 = 0)
    (hfit : lim.toNat + F ≤ ms.sp.toNat)
    (hw : WordOk P (ms.sp - UInt32.ofNat F + UInt32.ofNat lr)) :
    ∃ s, Reach P σ code ms s ∧ s.pc = after entry 7 ∧ s.sp = ms.sp - UInt32.ofNat F ∧
      s.lr = ms.lr ∧ s.trace = ms.trace ∧ s.reads = ms.reads ∧
      s.mem = store32 ms.mem (ms.sp - UInt32.ofNat F + UInt32.ofNat lr) ms.lr := by
  have hlim := toNat_lt32 lim
  let L : List Instr := [Instr.subwSpOf 4 F, Instr.movwOf 5 (lim.toNat % 65536),
    Instr.movtOf 5 (lim.toNat / 65536), Instr.cmpReg 4 5]
  have hcode' : CodeAt code entry (L ++ [Instr.bcondTo condCC oq] ++ [Instr.subwSpSpOf F] ++
      [Instr.strLr ⟨lr, hlr4⟩]) := hcode
  obtain ⟨hc3, hcS⟩ := hcode'.split_wide rfl
  obtain ⟨hc2, hcW⟩ := hc3.split_wide rfl
  obtain ⟨hcL, hcB⟩ := hc2.split_wide rfl
  rw [show (L ++ [Instr.bcondTo condCC oq] ++ [Instr.subwSpSpOf F]).length = 6 from rfl] at hcS
  rw [show (L ++ [Instr.bcondTo condCC oq]).length = 5 from rfl] at hcW
  rw [show L.length = 4 from rfl] at hcB
  -- `SUBW`, `MOVW`, `MOVT`, and `CMP`
  have hok : SlotsOk P ms.sp L :=
    slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_cons rfl (fun o ho => by cases ho)
      (slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_cons rfl (fun o ho => by cases ho)
        (slotsOk_nil _))))
  rw [← hpc] at hcL
  obtain ⟨r1, p1, sp1, lr1, tr1, rd1, -⟩ := run_slots (σ := σ) hok hcL
  have hm1 := (slotRun_reg (P := P) (σ := σ) (ops := L) rfl ms).1
  have hC : (slotRun P σ L ms).cFlag = true := by
    simp only [L, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some, Instr.subwSpOf,
      Instr.movwOf, Instr.movtOf]
    state_simp
    rw [carry_cmp, sub_addWithCarry, imm12_field hF, imm16_field (by omega),
      imm16_field (by omega), movt_word (by omega) (by omega),
      show lim.toNat % 65536 + lim.toNat / 65536 * 65536 = lim.toNat by omega,
      UInt32.ofNat_toNat, toNat_sub_frame (sp := ms.sp) (F := F) (by omega)]
    exact decide_eq_true (by omega)
  have hBpc : (slotRun P σ L ms).pc = after entry 4 := by
    rw [p1, hpc, after_eq]
    try rfl
  rw [← hBpc] at hcB
  have rB := reach_bcondTo (P := P) (σ := σ) q1 q2 q3 hcB
  have hc3' : (slotRun P σ L ms).condHolds 3 = false := by rw [condHolds_cc, hC]; rfl
  rw [show condCC = (3 : Fin 14) from rfl, hc3'] at rB
  simp only [Bool.false_eq_true, ↓reduceIte] at rB
  -- `SUBW SP`
  obtain ⟨u2, hu2⟩ : ∃ u2 : State,
      u2 = { slotRun P σ L ms with pc := (slotRun P σ L ms).pc + 4 } := ⟨_, rfl⟩
  have rB' : Reach P σ code (slotRun P σ L ms) u2 := by rw [hu2]; exact rB
  have hu2pc : u2.pc = after entry 5 := by
    rw [hu2, State.pc_withPc, hBpc]
    addr_after
  rw [← hu2pc] at hcW
  obtain ⟨u3, hu3⟩ : ∃ u3 : State, u3 = { u2 with
      sp := (addWithCarry u2.sp (~~~(imm12 (field 2 (F / 2048)) (field 8 (F / 256))
        (field 256 F))) true).1 &&& 0xFFFFFFFC, pc := u2.pc + 4 } := ⟨_, rfl⟩
  have e3 : exec P σ (Instr.subwSpSpOf F) u2 = some u3 := by rw [hu3]; rfl
  have hu2sp : u2.sp = ms.sp := by rw [hu2, State.sp_withPc]; exact sp1
  have hu3sp : u3.sp = ms.sp - UInt32.ofNat F := by
    have h4 : (ms.sp - UInt32.ofNat F).toNat % 4 = 0 := by
      rw [toNat_sub_frame (sp := ms.sp) (F := F) (by omega)]
      omega
    rw [hu3]
    show (addWithCarry u2.sp _ true).1 &&& 0xFFFFFFFC = _
    rw [sub_addWithCarry, imm12_field hF, hu2sp, and_align h4]
  have hu3pc : u3.pc = after entry 6 := by
    rw [hu3]
    show u2.pc + 4 = _
    rw [hu2pc]
    addr_after
  rw [← hu3pc] at hcS
  -- `STR LR`
  have e4 := exec_strLr (P := P) (σ := σ) (s := u3) (o := ⟨lr, hlr4⟩) (by rw [hu3sp]; exact hw)
  refine ⟨_, r1.trans (rB'.trans (reach_exec hcW e3 (reach_exec hcS e4 (.refl _)))), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show u3.pc + 4 = _
    rw [hu3pc]
    addr_after
  · show u3.sp = _
    exact hu3sp
  · show u3.lr = _
    rw [hu3]
    show u2.lr = _
    rw [hu2, State.lr_withPc]
    exact lr1
  · show u3.trace = _
    rw [hu3]
    show u2.trace = _
    rw [hu2, State.trace_withPc]
    exact tr1
  · show u3.reads = _
    rw [hu3]
    show u2.reads = _
    rw [hu2, State.reads_withPc]
    exact rd1
  · show store32 u3.mem (u3.sp + UInt32.ofNat lr) u3.lr = _
    have hm3 : u3.mem = ms.mem := by
      rw [hu3]
      show u2.mem = _
      rw [hu2, State.mem_withPc]
      exact hm1
    have hl3 : u3.lr = ms.lr := by
      rw [hu3]
      show u2.lr = _
      rw [hu2, State.lr_withPc]
      exact lr1
    rw [hm3, hu3sp, hl3]

/-- The epilogue's reload of LR from its slot at `lr`, the rise of SP by `F`, and the return. -/
theorem run_epilogue {F lr : Nat} (hlr4 : lr < 4096) (hF : F < 4096) {a : UInt32} {s : State}
    (hc : CodeAt code a [Instr.ldrLr ⟨lr, hlr4⟩, Instr.addwSpSpOf F, Instr.bxLr])
    (hpc : s.pc = a) (hw : WordOk P (s.sp + UInt32.ofNat lr))
    (hodd : load32 s.mem (s.sp + UInt32.ofNat lr) % 2 = 1)
    (hal : (s.sp + UInt32.ofNat F).toNat % 4 = 0) :
    ∃ t, Reach P σ code s t ∧ t.pc = load32 s.mem (s.sp + UInt32.ofNat lr) &&& 0xFFFFFFFE ∧
      t.sp = s.sp + UInt32.ofNat F ∧ t.lr = load32 s.mem (s.sp + UInt32.ofNat lr) ∧
      t.mem = s.mem ∧ t.trace = s.trace ∧ t.reads = s.reads := by
  have hc' : CodeAt code a ([Instr.ldrLr ⟨lr, hlr4⟩] ++ [Instr.addwSpSpOf F] ++ [Instr.bxLr]) :=
    hc
  obtain ⟨hc2, hcX⟩ := hc'.split_wide rfl
  obtain ⟨hcL, hcA⟩ := hc2.split_wide rfl
  rw [← hpc] at hcL
  obtain ⟨u1, hu1⟩ : ∃ u1 : State,
      u1 = { s with lr := load32 s.mem (s.sp + UInt32.ofNat lr), pc := s.pc + 4 } := ⟨_, rfl⟩
  have e1 : exec P σ (Instr.ldrLr ⟨lr, hlr4⟩) s = some u1 := by rw [hu1]; exact exec_ldrLr hw
  have hu1pc : u1.pc = after a 1 := by
    rw [hu1, State.pc_withLrPc, hpc]
    addr_after
  rw [show ([Instr.ldrLr ⟨lr, hlr4⟩] : List Instr).length = 1 from rfl, ← hu1pc] at hcA
  obtain ⟨u2, hu2⟩ : ∃ u2 : State, u2 = { u1 with
      sp := (addWithCarry u1.sp (imm12 (field 2 (F / 2048)) (field 8 (F / 256))
        (field 256 F)) false).1 &&& 0xFFFFFFFC, pc := u1.pc + 4 } := ⟨_, rfl⟩
  have e2 : exec P σ (Instr.addwSpSpOf F) u1 = some u2 := by rw [hu2]; rfl
  have hu1sp : u1.sp = s.sp := by rw [hu1, State.sp_withLrPc]
  have hu2pc : u2.pc = after a 2 := by
    rw [hu2]
    show u1.pc + 4 = _
    rw [hu1pc]
    addr_after
  rw [show ([Instr.ldrLr ⟨lr, hlr4⟩] ++ [Instr.addwSpSpOf F] : List Instr).length = 2 from rfl,
    ← hu2pc] at hcX
  have hu2lr : u2.lr = load32 s.mem (s.sp + UInt32.ofNat lr) := by
    rw [hu2]
    show u1.lr = _
    rw [hu1, State.lr_withLrPc]
  have rX := reach_bxLr (P := P) (σ := σ) hcX (by rw [hu2lr]; exact hodd)
  refine ⟨_, reach_exec hcL e1 (reach_exec hcA e2 rX), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.pc_withPc, hu2lr]
  · rw [State.sp_withPc, hu2]
    show (addWithCarry u1.sp _ false).1 &&& 0xFFFFFFFC = _
    rw [add_addWithCarry, imm12_field hF, hu1sp, and_align hal]
  · rw [State.lr_withPc, hu2lr]
  · rw [State.mem_withPc, hu2]
    show u1.mem = _
    rw [hu1, State.mem_withLrPc]
  · rw [State.trace_withPc, hu2]
    show u1.trace = _
    rw [hu1, State.trace_withLrPc]
  · rw [State.reads_withPc, hu2]
    show u1.reads = _
    rw [hu1, State.reads_withLrPc]


/-! ## The function -/

theorem not_outside {sp : UInt32} {x y : Nat} (h1 : x ≤ y) (h2 : y < x + 8)
    (hy : y < 4294967296) : ¬ Outside sp x (sp + UInt32.ofNat y) := by
  unfold Outside
  rw [toNat_sub_offsets sp (by omega) hy]
  omega

/-- The simulation of a call of function `k` of `m`, which imports nothing and whose body has the
covered forms, when `genFunction` places its code at the even address `entry`, the code of
`udivmod64` lies at its shared address, the functions of the table simulate below the fuel `g`, and
`need k` bounds the stack that the call uses. -/
theorem fun_sim {callee : Table} {S : Shared} {entry : UInt32} {m : Module} {k : Nat}
    {f : Function} {is : List Instr} (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hcov : coveredList f.body = true) (hg : genFunction callee S entry f = .ok is)
    (hcode : CodeAt code entry is) (hev : entry.toNat % 2 = 0) (hdiv : DivAt code S) {g : Nat}
    {need : Nat → Nat} (hcl : CallsOk P σ code g m callee S need)
    (hneed : NeedOk need (frameOf (sigOf callee) f).size f.body (need k)) :
    FunSim P σ code m S need g k (entry, f.params, f.results) := by
  intro α st vs ms hp hvt hpc hlr hstk hargs
  change f.params.length ≤ vs.length at hp
  change Typed f.params.reverse (vs.take f.params.length) at hvt
  change ms.pc = entry at hpc
  change StackOk P S.limit (max f.params.length f.results.length) (need k) ms at hstk
  change ArgsAt ms (vs.take f.params.length) at hargs
  change CallResult P σ code f.params f.results vs (Wasm.run g m k st vs) ms
  simp only [Wasm.run, hm, List.getElem?_nil, List.length_nil, Nat.sub_zero, hk,
    Function.numParams]
  have hfp : (frameOf (sigOf callee) f).params = f.params.length := rfl
  have hge : ∀ i ∈ (frameOf (sigOf callee) f).named, (frameOf (sigOf callee) f).params ≤ i :=
    fun i hi => frameOf_named_ge hi
  obtain ⟨-, hnm, hF, hFm, hlr4, oq, clear, body, fin, results, q1, q2, q3, q4, hcc, hbody,
    hfin, hrl, hres, his⟩ := gen_function rfl hg
  generalize frameOf (sigOf callee) f = fr at *
  have hsz := fr.size_eq
  have hlrE := fr.lrOff_eq
  have hop : ∀ j, fr.opAt j = 8 * (fr.out + fr.named.length + j) := fun _ => rfl
  -- the stack
  obtain ⟨hal0, hram0, hfit0, ⟨hl1, hl2⟩, hbelow0, hroom0⟩ := hstk
  have hsp0 := toNat_lt32 ms.sp
  have hmax1 := Nat.le_max_left f.params.length f.results.length
  have hmax2 := Nat.le_max_right f.params.length f.results.length
  have hneedk : fr.size + callNeed need f.body ≤ need k := by
    rcases hneed with h | h
    · simp only [Nat.reducePow] at h
      omega
    · exact h
  have hal0n := toNat_mod4 hal0
  obtain ⟨sp1, hsp1⟩ : ∃ x : UInt32, x = ms.sp - UInt32.ofNat fr.size := ⟨_, rfl⟩
  have hsp1n : sp1.toNat = ms.sp.toNat - fr.size := by
    rw [hsp1]
    exact toNat_sub_frame (by omega)
  have hal1n : sp1.toNat % 4 = 0 := by rw [hsp1n]; omega
  have hal1 : sp1 % 4 = 0 := mod4_of_toNat hal1n
  have hramAll : ∀ j < fr.size + 8 * max f.params.length f.results.length,
      Ram P (sp1 + UInt32.ofNat j) := by
    intro j hj
    by_cases hjF : j < fr.size
    · rw [hsp1, sub_frame_below (lim := S.limit) j (by omega)]
      exact hbelow0 _ (by omega)
    · rw [hsp1, sub_frame_above (sp := ms.sp) (F := fr.size) (j := j) (by omega) (by omega)]
      exact hram0 _ (by omega)
  have hword : ∀ o, o % 4 = 0 → o + 4 ≤ fr.size + 8 * max f.params.length f.results.length →
      WordOk P (sp1 + UInt32.ofNat o) :=
    fun o h4 hn => wordOk_of_ram hramAll hal1 h4 hn
  -- the pieces of the code
  let PRO : List Instr := [Instr.subwSpOf 4 fr.size, Instr.movwOf 5 (S.limit.toNat % 65536),
    Instr.movtOf 5 (S.limit.toNat / 65536), Instr.cmpReg 4 5, Instr.bcondTo condCC oq,
    Instr.subwSpSpOf fr.size, Instr.strLr ⟨fr.lrOff, hlr4⟩]
  have hbs := genList_size _ _ _ f.body body fin hcov hbody
  have wC := hcc.wide
  have wR := wide_flatten_copies (src := fun j => fr.opAt j) (dst := fun j => fr.size + 8 * j)
    fun j hj => (hres j hj).2
  have his' : is = PRO ++ clear ++ body ++ results.flatten ++
      [Instr.ldrLr ⟨fr.lrOff, hlr4⟩, Instr.addwSpSpOf fr.size, Instr.bxLr, Instr.bxLr] := his
  rw [his'] at hcode
  obtain ⟨c4, cE⟩ := hcode.split_wide (by
    simp only [List.all_append, wC, hbs.2.2, wR]
    rfl)
  obtain ⟨c3, cR⟩ := c4.split_wide (by
    simp only [List.all_append, wC, hbs.2.2]
    rfl)
  obtain ⟨c2, cB⟩ := c3.split_wide (by
    simp only [List.all_append, wC]
    rfl)
  obtain ⟨cP, cC⟩ := c2.split_wide (rfl : PRO.all Instr.wide = true)
  rw [List.length_append, List.length_append, List.length_append,
    show PRO.length = prologueSize from rfl, ← after_after, ← after_after] at cE
  rw [List.length_append, List.length_append, show PRO.length = prologueSize from rfl,
    ← after_after] at cR
  rw [List.length_append, show PRO.length = prologueSize from rfl] at cB
  rw [show PRO.length = 7 from rfl] at cC
  -- the prologue
  obtain ⟨u4, r4, p4, sp4, lr4, tr4, rd4, hm4⟩ := run_prologue (P := P) (σ := σ) hF hlr4
    (by omega) q1 q2 q3 cP hpc hal0n (by omega)
    (by rw [← hsp1]; exact hword _ (by omega) (by omega))
  rw [← hsp1] at sp4 hm4
  rw [← p4] at cC
  have hu4w : ∀ j < fr.named.length, WordOk P (u4.sp + UInt32.ofNat (8 * (fr.out + j))) ∧
      WordOk P (u4.sp + UInt32.ofNat (8 * (fr.out + j) + 4)) := fun j hj => by
    rw [sp4]
    exact ⟨hword _ (by omega) (by omega), hword _ (by omega) (by omega)⟩
  obtain ⟨s2, r2, p2, sp2, lr2, tr2, rd2, hz2, hm2⟩ := run_clearing (P := P) (σ := σ) hcc hge
    hu4w cC
  have hs2sp : s2.sp = sp1 := sp2.trans sp4
  have hp2' : s2.pc = after entry (prologueSize + clear.length) := by
    rw [p2, p4, after_after]
    try rfl
  -- what the prologue leaves in memory
  have hkeep2 : ∀ b : UInt32, ms.sp.toNat ≤ b.toNat → s2.mem b = ms.mem b := by
    intro b hb
    rw [hm2 b fun j hj => outside_above (by rw [sp4, hsp1n]; omega), hm4]
    apply store32_far
    have hb32 := toNat_lt32 b
    rw [UInt32.lt_iff_toNat_lt, show (4 : UInt32).toNat = 4 from rfl, UInt32.toNat_sub,
      toNat_add_ofNat (a := sp1) (k := fr.lrOff) (by omega)]
    simp only [Nat.reducePow]
    omega
  have hlrw : load32 s2.mem (sp1 + UInt32.ofNat fr.lrOff) = ms.lr := by
    rw [load32_congr (m' := s2.mem) (m := u4.mem) (a := sp1 + UInt32.ofNat fr.lrOff) fun j hj => by
      rw [add_ofNat_add]
      exact hm2 _ fun j' hj' => by
        rw [sp4]
        exact outside_of_disjoint (by omega) (by omega) (by omega) (by omega : j < 8)]
    rw [hm4, load32_store32]
  have hld : ∀ x, x + 4 ≤ 8 * max f.params.length f.results.length →
      load32 s2.mem (ms.sp + UInt32.ofNat x) = load32 ms.mem (ms.sp + UInt32.ofNat x) :=
    fun x hx => load32_above hkeep2
      (by rw [toNat_add_ofNat (a := ms.sp) (k := x) (by omega)]; omega)
      (by rw [toNat_add_ofNat (a := ms.sp) (k := x) (by omega)]; omega)
  -- the relation after the prologue
  let E : Env :=
    { toShared := S, frame := fr, localTypes := f.params ++ f.locals, callee := callee }
  have hframe : FrameOk P fr S.limit s2 := by
    refine ⟨by rw [hs2sp]; exact hal1, fun j hj => by rw [hs2sp]; exact hramAll j (by omega),
      by rw [hs2sp, hsp1n]; omega, ⟨hl1, by rw [hs2sp, hsp1n]; omega⟩, fun j hj => ?_⟩
    rw [hs2sp, hsp1n] at hj
    exact hbelow0 j (by omega)
  have hlen_args : ((vs.take f.params.length).reverse).length = f.params.length := by
    simp
    omega
  have hargt : Typed f.params (vs.take f.params.length).reverse := by
    have := Typed.reverse hvt
    rwa [List.reverse_reverse] at this
  have hinv : Inv P E [] (f.toLocals (vs.take f.params.length).reverse) s2 := by
    refine ⟨Nat.zero_le _, fun h v hv => by simp [Function.toLocals] at hv, ?_, ?_, ?_, hframe,
      trivial⟩
    · simp [Function.toLocals, E]
      try omega
    · intro i v o hv ho
      change fr.localOff i = some o at ho
      simp only [Function.toLocals] at hv
      rcases Frame.localOff_eq ho with ⟨hi, rfl⟩ | ⟨j, hj, hji, rfl⟩
      · rw [List.getElem?_append_left (by omega)] at hv
        have hva := hargs i v hv
        unfold ValAt at hva ⊢
        rw [hs2sp, hsp1, sub_frame_above (sp := ms.sp) (F := fr.size) (j := fr.size + 8 * i)
          (by omega) (by omega), sub_frame_above (sp := ms.sp) (F := fr.size)
          (j := fr.size + 8 * i + 4) (by omega) (by omega),
          show fr.size + 8 * i - fr.size = 8 * i by omega,
          show fr.size + 8 * i + 4 - fr.size = 8 * i + 4 by omega, hld _ (by omega),
          hld _ (by omega)]
        exact hva
      · have hpi := hge i (List.mem_of_getElem? hji)
        rw [List.getElem?_append_right (by omega), hlen_args, List.getElem?_map] at hv
        obtain ⟨t, hnt, hit⟩ := hnm i (List.mem_of_getElem? hji)
        rw [List.getElem?_append_right (by omega)] at hnt
        rw [hnt] at hv
        simp at hv
        subst hv
        have ho' : fr.localOff i = some (8 * (fr.out + j)) := ho
        unfold ValAt
        rw [sp2, load32_zero (m := s2.mem) (a := u4.sp + UInt32.ofNat (8 * (fr.out + j)))
            fun k hk => by
              rw [add_ofNat_add]
              exact hz2 i _ hpi ho' _ (not_outside (by omega) (by omega) (by omega)),
          load32_zero (m := s2.mem) (a := u4.sp + UInt32.ofNat (8 * (fr.out + j) + 4))
            fun k hk => by
              rw [add_ofNat_add]
              exact hz2 i _ hpi ho' _ (not_outside (by omega) (by omega) (by omega))]
        exact slotRel_zero hit
    · intro i v t o hv ht ho
      change fr.localOff i = some o at ho
      simp only [Function.toLocals] at hv
      rcases Frame.localOff_eq ho with ⟨hi, -⟩ | ⟨j, hj, hji, -⟩
      · rw [List.getElem?_append_left (by omega)] at hv
        rw [List.getElem?_append_left (by omega)] at ht
        exact hargt.of_getElem? ht hv
      · have hpi := hge i (List.mem_of_getElem? hji)
        rw [List.getElem?_append_right (by omega), hlen_args, List.getElem?_map] at hv
        obtain ⟨t', hnt, hit⟩ := hnm i (List.mem_of_getElem? hji)
        rw [ht] at hnt
        cases hnt
        rw [List.getElem?_append_right (by omega)] at ht
        rw [ht] at hv
        simp at hv
        subst hv
        exact hasType_zero hit
  -- the body
  have ho := list_sim (P := P) (σ := σ) (code := code) g E
    [⟨after (after entry (prologueSize + clear.length))
      (listSize (sigOf callee) [f.results.length] 0 f.body).1, f.results.reverse, 0⟩] []
    _ f.body body fin hcov hbody cB (even_after hev _) hdiv (Nat.le_refl _) m st
    (f.toLocals (vs.take f.params.length).reverse) s2 hinv hp2' need (callNeed need f.body) hcl
    (fun j hj => le_callNeed hj)
    (by show callNeed need f.body ≤ s2.sp.toNat - S.limit.toNat; rw [hs2sp, hsp1n]; omega)
  generalize Wasm.exec g m st (f.toLocals (vs.take f.params.length).reverse) f.body = res at ho ⊢
  cases res with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf', ms', hr', hp', hsp', htr', hrd', hk', -, hinv'⟩ := ho
      have e := hfin σ' hf'
      subst e
      have hty' := hinv'.types
      have hl' : sl'.values.length = f.results.length := by
        rw [← hty'.length, List.length_reverse]
      have hms'sp : ms'.sp = sp1 := hsp'.trans hs2sp
      -- the copies of the results
      rw [← hp'] at cR
      obtain ⟨t, rt, pt, spt, lrt, trt, rdt, hwt, hmt⟩ := run_copies (P := P) (σ := σ)
        (src := fun j => fr.opAt j) (dst := fun j => fr.size + 8 * j) (fun j hj => (hres j hj).2)
        (fun j hj => by
          have := (hres j hj).1
          have := hop j
          rw [hms'sp]
          exact ⟨hword _ (by omega) (by omega), hword _ (by omega) (by omega),
            hword _ (by omega) (by omega), hword _ (by omega) (by omega)⟩)
        (fun i hi j hj => by have := (hres i hi).1; have := hop i; omega)
        (fun i hi j hj hij => by omega)
        (fun i hi => by have := (hres i hi).1; have := hop i; omega) cR
      have htsp : t.sp = sp1 := spt.trans hms'sp
      -- the epilogue
      rw [length_copies fun j hj => (hres j hj).2] at cE
      have htpc : t.pc = after (after (after entry (prologueSize + clear.length)) body.length)
          (4 * results.length) := by
        rw [pt, hp', after_eq (n := 4 * results.length)]
        congr 2
        omega
      have hcE : CodeAt code t.pc
          ([Instr.ldrLr ⟨fr.lrOff, hlr4⟩, Instr.addwSpSpOf fr.size, Instr.bxLr] ++
            [Instr.bxLr]) := by
        rw [htpc]
        exact cE
      have hlrT : load32 t.mem (t.sp + UInt32.ofNat fr.lrOff) = ms.lr := by
        have hkl : load32 ms'.mem (s2.sp + UInt32.ofNat fr.lrOff) =
            load32 s2.mem (s2.sp + UInt32.ofNat fr.lrOff) := hk'.lr
        rw [htsp, load32_congr (m' := t.mem) (m := ms'.mem) (a := sp1 + UInt32.ofNat fr.lrOff)
          fun j hj => by
          rw [add_ofNat_add]
          exact hmt _ fun i hi => by
            rw [hms'sp]
            exact outside_of_disjoint (by omega) (by omega) (by omega) (by omega : j < 8)]
        rw [← hs2sp, hkl, hs2sp, hlrw]
      obtain ⟨t3, rt3, pt3, spt3, lrt3, mt3, trt3, rdt3⟩ := run_epilogue (P := P) (σ := σ)
        (s := t) hlr4 hF (CodeAt.append.mp hcE).1 rfl (by rw [htsp]; exact hword _ (by omega) (by omega))
        (by rw [hlrT]; exact hlr)
        (by rw [htsp, toNat_add_ofNat (a := sp1) (k := fr.size) (by omega), hsp1n]; omega)
      rw [hlrT] at pt3 lrt3
      rw [htsp, hsp1, UInt32.sub_add_cancel] at spt3
      have hvals : (sl'.values.take f.results.length ++ vs.drop f.params.length).take
          f.results.length = sl'.values := by
        rw [List.take_left' (l₁ := sl'.values.take f.results.length) (by simp [hl']),
          List.take_of_length_le (l := sl'.values) (by omega)]
      refine ⟨t3, r4.trans (r2.trans (hr'.trans (rt.trans rt3))), pt3, spt3, lrt3, ?_, ?_,
        fun a ha => ?_, by simp [hl'],
        List.drop_left' (l₁ := sl'.values.take f.results.length) (by simp [hl']), ?_, ?_⟩
      · rw [trt3, trt, htr', tr2, tr4]
      · rw [rdt3, rdt, hrd', rd2, rd4]
      · have ha32 := toNat_lt32 a
        have hab : s2.sp.toNat + fr.size + 8 * fr.params ≤ a.toNat := by
          rw [hs2sp, hsp1n]
          omega
        rw [mt3, hmt a fun i hi => outside_above (x := fr.size + 8 * i)
            (by rw [hms'sp, hsp1n]; omega),
          hk'.above a hab, hkeep2 a (by omega)]
      · rw [hvals]
        intro i v hv
        have hi : i < f.results.length := by have := getElem?_reverse_lt hv; omega
        have hv0 := hinv'.stack i v hv
        have e : slotWords t (fr.size + 8 * i) = slotWords ms' (fr.opAt i) := hwt i (by omega)
        unfold slotWords at e
        rw [Prod.mk.injEq] at e
        unfold ValAt at hv0 ⊢
        have ha1 : t3.sp + UInt32.ofNat (8 * i) = t.sp + UInt32.ofNat (fr.size + 8 * i) := by
          rw [spt3, htsp, hsp1, sub_frame_above (sp := ms.sp) (F := fr.size)
            (j := fr.size + 8 * i) (by omega) (by omega),
            show fr.size + 8 * i - fr.size = 8 * i by omega]
        have ha2 : t3.sp + UInt32.ofNat (8 * i + 4) =
            t.sp + UInt32.ofNat (fr.size + 8 * i + 4) := by
          rw [spt3, htsp, hsp1, sub_frame_above (sp := ms.sp) (F := fr.size)
            (j := fr.size + 8 * i + 4) (by omega) (by omega),
            show fr.size + 8 * i + 4 - fr.size = 8 * i + 4 by omega]
        rw [mt3, ha1, ha2, e.1, e.2]
        exact hv0
      · rw [hvals]
        exact hty'
  | Break _ _ _ => exact ho.elim
  | Return _ _ => exact ho.elim
  | Trap _ _ => trivial
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-- The functions of a table whose code `genFunction` places at their even entries, in a module
that imports nothing, with covered bodies, simulate at every fuel, with bounds `need` of the stack
that their calls use, when the code of `udivmod64` lies at its shared address. -/
theorem calls_ok {callee : Table} {S : Shared} {m : Module} (hm : m.imports = [])
    (hdiv : DivAt code S)
    (htab : ∀ k c, callee k = some c → ∃ f is, m.funcs[k]? = some f ∧
      c.2 = (f.params, f.results) ∧ coveredList f.body = true ∧
      genFunction callee S c.1 f = .ok is ∧ CodeAt code c.1 is ∧ c.1.toNat % 2 = 0)
    {need : Nat → Nat}
    (hneed : ∀ k f, m.funcs[k]? = some f →
      NeedOk need (frameOf (sigOf callee) f).size f.body (need k)) :
    ∀ F, CallsOk P σ code F m callee S need := by
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      intro k c hk g hg
      obtain ⟨f, is, hf, hc2, hcov, hgen, hcode, hev⟩ := htab k c hk
      obtain ⟨e, p, r⟩ := c
      simp only [Prod.mk.injEq] at hc2
      obtain ⟨rfl, rfl⟩ := hc2
      exact fun_sim hm hf hcov hgen hcode hev hdiv (ih g hg) (hneed k f hf)

end LeanExe.M7
