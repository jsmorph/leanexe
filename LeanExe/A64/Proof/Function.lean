import LeanExe.A64.Proof.Constructs

/-!
The simulation of a function.  The prologue compares SP less the frame's `frameSize n` bytes
with the stack's limit in X18 and branches to the stub of an overflow of the stack when the frame
does not fit.  Otherwise it allocates the frame below SP, saves X30 in the slot above the `n`
locals and their spill slots, and stores the parameters from X0 up and zeros for the other locals
into their slots, so that Talos's locals on entry and the machine's state after the prologue
satisfy `Inv`.  The body's outcome under the function's construct leads to the epilogue, which
reloads X30 from its slot, which the body's code leaves unchanged, frees the frame, and returns.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The generator's function -/

theorem frameSize_bounds {n : Nat} (h : frameSize n < 4096) :
    8 * (n + spillSlots + 1) ≤ frameSize n ∧ frameSize n % 16 = 0 ∧
      n + spillSlots + 1 < 512 := by
  unfold frameSize at h ⊢
  omega

theorem gen_function {callee : Table} {S : Shared} {entry : UInt64}
    {f : Function} {is : List Instr} (hg : genFunction callee S entry f = .ok is) :
    let p := f.params.length
    let n := p + f.locals.length
    let r := f.results.length
    let bodyA := after entry (5 + n)
    p ≤ 8 ∧ r ≤ 1 ∧ (∀ t ∈ f.locals, numeric t = true) ∧
      ∃ (hf : frameSize n < 4096) (hn : n + spillSlots < 4096)
      (stores body : List Instr) (fin : Option (List ValueType)) (g : Fin 524288),
      stores.length = n ∧
      (∀ i (hi : i < stores.length), ∃ hs, stores[i] =
        .str (if i < p then ⟨i % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31 ⟨i, hs⟩) ∧
      genList { toShared := S, localTypes := f.params ++ f.locals, callee }
        [⟨after bodyA (listSize (sigOf callee) [r] 0 f.body).1, f.results.reverse, 0⟩] []
        bodyA f.body = .ok (body, fin) ∧ (∀ x, fin = some x → x = f.results.reverse) ∧
      cbField (after entry 2) S.trapStack = .ok g ∧
      is = [.subImm 16 31 ⟨frameSize n, hf⟩, .subsReg 31 16 18, .bcond 3 g,
          .subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n + spillSlots, hn⟩] ++ stores ++ body ++
        [.ldr 30 31 ⟨n + spillSlots, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30] := by
  dsimp only
  by_cases hc : f.params.length > 8 ∨ f.results.length > 1
  · simp [genFunction, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have h1 : ¬ f.params.length > 8 := by omega
  have h2 : ¬ f.results.length > 1 := by omega
  by_cases hnum0 : f.locals.all numeric = false
  · simp [genFunction, h1, h2, hnum0, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind] at hg
  have hnum : f.locals.all numeric = true := by simpa using hnum0
  have hloc : ∀ t ∈ f.locals, numeric t = true := List.all_eq_true.mp hnum
  by_cases hf : frameSize (f.params.length + f.locals.length) < 4096
  · simp [genFunction, h1, h2, hnum, hf, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hg
    split at hg
    · cases hg
    rename_i v hl
    split at hg
    · cases hg
    rename_i hend
    split at hg
    · cases hg
    rename_i g hcb
    cases hg
    have hn : f.params.length + f.locals.length + spillSlots < 4096 := by
      have := (frameSize_bounds hf).2.2; omega
    exact ⟨by omega, by omega, hloc, hf, hn,
      List.ofFn (fun i : Fin (f.params.length + f.locals.length) =>
        Instr.str (if i.val < f.params.length then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31)
          31 ⟨i.val, by omega⟩), v.1, v.2, g, by simp, fun i hi => ⟨by simp at hi; omega, by simp⟩,
      hl, any_ne hend, hcb, by simp [List.append_assoc]⟩
  · simp [genFunction, h1, h2, hnum, hf, throw, throwThe, MonadExceptOf.throw] at hg

/-! ## The prologue -/

/-- The run of the prologue's check of the stack: with at least `fs` bytes from the stack's limit
in X18 up to SP, the machine goes on to the allocation of the frame, and with fewer it branches to
the stub `tS`. -/
theorem run_check {fs : Nat} (hf : fs < 4096) {g : Fin 524288} {entry tS : UInt64}
    (hg : cbField (after entry 2) tS = .ok g)
    (hcode : CodeAt code entry [.subImm 16 31 ⟨fs, hf⟩, .subsReg 31 16 18, .bcond 3 g])
    {ms : State} (hpc : ms.pc = entry) (hl : fs ≤ (ms.x 18).toNat)
    (hsp : (ms.x 18).toNat ≤ ms.sp.toNat) :
    ∃ s, Reach P code ms s ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.out = ms.out ∧
      (∀ q, q ≠ 16 → s.x q = ms.x q) ∧
      s.pc = if fs ≤ (ms.sp - ms.x 18).toNat then after entry 3 else tS := by
  have c0 := (CodeAt.cons.mp hcode).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).2).1
  rw [after_after] at c2
  let s1 : State := { ms.setX 16 (ms.sp - UInt64.ofNat fs) with pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 16 31 ⟨fs, hf⟩) ms = some s1 := rfl
  let s2 : State := { s1.subs 31 (s1.x 16) (s1.x 18) with pc := s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.subsReg 31 16 18) s1 = some s2 := rfl
  let s3 : State :=
    { s2 with pc := if s2.condHolds 3 then s2.pc + sext 19 g.val * 4 else s2.pc + 4 }
  have e3 : LeanExe.A64.exec P (.bcond 3 g) s2 = some s3 := rfl
  have p1 : s1.pc = after entry 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after entry 2 := by
    show ms.pc + 4 + 4 = entry + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  have hx2 : ∀ q, s2.x q = s1.x q := by
    intro q
    show (s1.setX 31 (s1.x 16 - s1.x 18)).x q = s1.x q
    unfold State.setX; rw [ite_eq_right (by decide)]
  have hx1 : ∀ q, q ≠ 16 → s1.x q = ms.x q := fun q hq => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
  have h16 : s1.x 16 = ms.sp - UInt64.ofNat fs := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
  have hc : s2.condHolds 3 = !decide (fs ≤ (ms.sp - ms.x 18).toNat) := by
    rw [condHolds_3]
    show (!decide (s1.x 18 ≤ s1.x 16)) = _
    rw [h16, hx1 18 (by decide)]
    congr 1
    apply decide_eq_decide.mpr
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_ofNat']
    have := ms.sp.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  refine ⟨s3, reach_exec P code (by rw [hpc]; exact c0) e1
    (reach_exec P code (by rw [p1]; exact c1) e2
      (reach_exec P code (by rw [p2]; exact c2) e3 (.refl _))), ?_, ?_, ?_, ?_, ?_⟩
  · simp [s3, s2, s1, State.subs]
  · simp [s3, s2, s1, State.subs]
  · simp [s3, s2, s1, State.subs]
  · intro q hq
    rw [State.x_withPc, hx2, hx1 q hq]
  · show (if s2.condHolds 3 then s2.pc + sext 19 g.val * 4 else s2.pc + 4) = _
    rw [hc, p2]
    by_cases h : fs ≤ (ms.sp - ms.x 18).toNat
    · simp only [h, decide_true, Bool.not_true]
      exact (after_succ entry 2).symm
    · simp only [h, decide_false, Bool.not_false, ite_true]
      exact cbField_target hg

/-- The run of the prologue's part after the check of the stack: the frame of `fs` bytes below
SP, X30 in slot `j` at or above the `n` locals, and the word of register `src i` in the slot of
local `i`. -/
theorem run_frame {n j fs : Nat} (hj : n ≤ j) (hfs : 8 * (j + 1) ≤ fs) (hfs16 : fs % 16 = 0)
    (hf : fs < 4096) (hjs : j < 4096) (hj512 : j + 1 < 512) {src : Nat → Fin 32}
    {stores : List Instr} (hlen : stores.length = n)
    (hst : ∀ i (hi : i < n), ∃ hs, stores[i]'(by omega) = .str (src i) 31 ⟨i, hs⟩)
    {entry : UInt64} {ms : State}
    (hcode : CodeAt code entry ([.subImm 31 31 ⟨fs, hf⟩, .str 30 31 ⟨j, hjs⟩] ++ stores))
    (hpc : ms.pc = entry) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < fs, P.normal (ms.sp - UInt64.ofNat fs + UInt64.ofNat j) = true) :
    ∃ s, Reach P code ms s ∧ s.pc = after entry (2 + n) ∧ s.sp = ms.sp - UInt64.ofNat fs ∧
      (∀ q, s.x q = ms.x q) ∧ s.out = ms.out ∧ load64 s.mem (slotAddr s.sp j) = ms.x 30 ∧
      (∀ i < n, load64 s.mem (slotAddr s.sp i) = ms.x (src i)) ∧
      (∀ a, ¬ a - s.sp < UInt64.ofNat fs → s.mem a = ms.mem a) := by
  have hal' := sub_aligned hal hfs16
  have c0 := (CodeAt.cons.mp hcode).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).1
  have cs : CodeAt code (after entry 2) stores := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).2
    rwa [after_after] at this
  let s1 : State := { ms with sp := ms.sp - UInt64.ofNat fs, pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 31 31 ⟨fs, hf⟩) ms = some s1 := rfl
  have hmap1 : ∀ i ≤ j, ∀ k < 8, P.normal (s1.sp + UInt64.ofNat (8 * i + k)) = true :=
    fun i hi k hk => hmap (8 * i + k) (by omega)
  let s2 : State :=
    { s1 with mem := store64 s1.mem (slotAddr s1.sp j) (s1.x 30), pc := s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 ⟨j, hjs⟩) s1 = some s2 :=
    exec_str_sp P hjs hal' (hmap1 j (Nat.le_refl _))
  have r2 : Reach P code ms s2 :=
    reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by show code (ms.pc + 4) = _; rw [hpc]; simpa [after] using c1) e2
        (.refl _))
  have key : ∀ k ≤ n, ∃ M,
      Reach P code s2 { s2 with mem := M, pc := after (after entry 2) k } ∧
      (∀ i < k, load64 M (slotAddr s1.sp i) = ms.x (src i)) ∧
      (∀ a, (∀ i < k, ¬ a - slotAddr s1.sp i < 8) → M a = s2.mem a) := by
    intro k
    induction k with
    | zero =>
        refine fun _ => ⟨s2.mem, ?_, fun i hi => absurd hi (by omega), fun _ _ => rfl⟩
        have : s2.pc = after (after entry 2) 0 := by
          rw [after_zero]
          show ms.pc + 4 + 4 = entry + 4 * UInt64.ofNat 2
          rw [hpc, UInt64.add_assoc]
          congr 1
        rw [← this]
        exact .refl _
    | succ k ih =>
        intro hk
        obtain ⟨M, hr, hload, hout⟩ := ih (by omega)
        obtain ⟨hs, hsk⟩ := hst k (by omega)
        have ck : code (after (after entry 2) k) = some (encode (.str (src k) 31 ⟨k, hs⟩)) := by
          have := cs k (by omega)
          rwa [hsk] at this
        let t : State := { s2 with mem := M, pc := after (after entry 2) k }
        have et := exec_str_sp P (s := t) (r := src k) hs hal' (hmap1 k (by omega))
        refine ⟨store64 M (slotAddr s1.sp k) (ms.x (src k)),
          hr.trans (reach_exec P code ck et ?_), ?_, ?_⟩
        · rw [after_succ]
          exact .refl _
        · intro i hi
          by_cases hik : i = k
          · subst hik
            exact load64_store64_same _ _ _
          · rw [load64_store64_other _ _ _ _ (slot_apart (by omega) (by omega) (Ne.symm hik))]
            exact hload i (by omega)
        · intro a ha
          rw [store64_other _ _ _ _ (ha k (by omega))]
          exact hout a fun i hi => ha i (by omega)
  obtain ⟨M, hr, hload, hout⟩ := key n (Nat.le_refl _)
  have hoth : ∀ a, ¬ a - s1.sp < UInt64.ofNat fs →
      ∀ i < j + 1, ¬ a - slotAddr s1.sp i < 8 :=
    fun a ha i hi => slot_inside hi hj512 (not_lt_mono hfs (by omega) ha)
  refine ⟨_, r2.trans hr, by show after (after entry 2) n = _; rw [after_after], rfl,
    fun _ => rfl, rfl, ?_, hload, ?_⟩
  · show load64 M (slotAddr s1.sp j) = ms.x 30
    rw [load64_congr (m' := s2.mem) fun k hk => hout _ fun i hi =>
      slot_apart (by omega) (by omega) (by omega) k hk]
    exact load64_store64_same _ _ _
  · intro a ha
    show M a = ms.mem a
    rw [hout a fun i hi => hoth a ha i (by omega)]
    show store64 s1.mem (slotAddr s1.sp j) (s1.x 30) a = ms.mem a
    rw [store64_other _ _ _ _ (hoth a ha j (by omega))]

/-! ## The epilogue -/

/-- The epilogue's run from the state `s` that the body reaches at its end: X30 reloaded from the
slot `n`, the frame of `fs` bytes freed, and a return to the reloaded address. -/
theorem run_epilogue {n fs : Nat} (hf : fs < 4096) (hn : n < 4096) {a : UInt64} {s : State}
    (hcode : CodeAt code a [.ldr 30 31 ⟨n, hn⟩, .addImm 31 31 ⟨fs, hf⟩, .ret 30])
    (hpc : s.pc = a) (hal : s.sp % 16 = 0)
    (hmap : ∀ j < 8, P.normal (s.sp + UInt64.ofNat (8 * n + j)) = true) :
    ∃ s', Reach P code s s' ∧ s'.pc = load64 s.mem (slotAddr s.sp n) ∧
      s'.sp = s.sp + UInt64.ofNat fs ∧ s'.out = s.out ∧ s'.mem = s.mem ∧
      ∀ q, q ≠ 30 → s'.x q = s.x q := by
  have c0 := (CodeAt.cons.mp hcode).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).2).1
  rw [after_after] at c2
  let w := load64 s.mem (slotAddr s.sp n)
  let s1 : State := { s.setX 30 w with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.ldr 30 31 ⟨n, hn⟩) s = some s1 := exec_ldr_sp P hn hal hmap
  let s2 : State := { s1 with sp := s.sp + UInt64.ofNat fs, pc := s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.addImm 31 31 ⟨fs, hf⟩) s1 = some s2 := rfl
  have e3 : LeanExe.A64.exec P (.ret 30) s2 = some { s2 with pc := s2.x 30 } := rfl
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s.pc + 4 + 4 = a + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  refine ⟨_, reach_exec P code (by rw [hpc]; exact c0) e1
    (reach_exec P code (by rw [p1]; exact c1) e2
      (reach_exec P code (by rw [p2]; exact c2) e3 (.refl _))), ?_, rfl, ?_, ?_, ?_⟩
  · show (s.setX 30 w).x 30 = w
    exact State.x_setX_same (by decide)
  · show (s.setX 30 w).out = s.out
    exact State.setX_out
  · show (s.setX 30 w).mem = s.mem
    exact State.setX_mem
  · intro q hq
    show (s.setX 30 w).x q = s.x q
    exact State.x_setX_ne (Ne.symm hq)

/-! ## The function -/

theorem ValRel_zero {t : ValueType} (h : numeric t = true) : ValRel t.zero 0 := by
  cases t <;> simp [numeric] at h <;> rfl

theorem hasType_zero {t : ValueType} (h : numeric t = true) : HasType t t.zero := by
  cases t <;> simp [numeric] at h <;> trivial

theorem typed_zeros : ∀ {ts : List ValueType}, (∀ t ∈ ts, numeric t = true) →
    Typed ts (ts.map ValueType.zero)
  | [], _ => trivial
  | t :: ts, h => ⟨hasType_zero (h t (by simp)), typed_zeros fun t' ht' => h t' (by simp [ht'])⟩

/-- The machine returned from the function that it entered at `ms`: at the address that X30 held,
with SP, X18, and the UART's output as they were, the memory outside the bytes from the stack's
limit in X18 up to SP unchanged, and the result, the top of `vs` when the function has one, in
X0. -/
structure Returned (rs : List ValueType) (vs : List Value) (ms ms' : State) : Prop where
  pc : ms'.pc = ms.x 30
  sp : ms'.sp = ms.sp
  x18 : ms'.x 18 = ms.x 18
  out : ms'.out = ms.out
  mem : MemFrame ms.sp 0 ms ms'
  len : rs.length ≤ vs.length
  res : ∀ v ∈ vs.take rs.length, ValRel v (ms'.x 0)
  types : Typed rs.reverse (vs.take rs.length)

/-- What the machine does from `ms` at the entry of a function with a frame of `fs` bytes,
results of the types `rs`, and calls to the functions of `callee` when Talos's run of the
function's body gives `r`: a return reaches the return address with the final store in the area,
and a trap reaches the stub of its code.  When the frame does not fit between the stack's limit
and SP, or when the function may call another, the machine may instead reach the stub of an
overflow of the stack. -/
def FunOutcome (callee : Table) (S : Shared) (fs : Nat) (rs : List ValueType)
    {α : Type} (r : Continuation α) (ms : State) : Prop :=
  (((ms.sp - ms.x 18).toNat < fs ∨ HasCalls callee) ∧ Overflows P code S.trapStack ms) ∨
  match r with
  | .Fallthrough st' sl' => ∃ ms', Reach P code ms ms' ∧ Returned rs sl'.values ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Break 0 st' sl' => ∃ ms', Reach P code ms ms' ∧ Returned rs sl'.values ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Return st' vs => ∃ ms', Reach P code ms ms' ∧ Returned rs vs ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg ms'.pc
  | .Break (_ + 1) _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

/-- The values that a branch to a construct of base 0 and at most one value keeps: the top in
X0. -/
theorem kept_res {t : Ctl} {vs : List Value} {s : State} (hk : Kept t vs s) (hb : t.base = 0)
    (ha : t.arity ≤ 1) : ∀ v ∈ vs.take t.arity, ValRel v (s.x 0) := by
  intro v hv
  by_cases h0 : t.arity = 0
  · rw [h0] at hv
    simp at hv
  · have e : t.arity = 1 := by omega
    have hv0 := hk.vals 0 (by omega)
    rw [hb, show regOf (0 + 0) = 0 by decide] at hv0
    rw [e] at hv
    cases vs with
    | nil => simp at hv
    | cons w ws =>
        simp at hv
        subst hv
        simpa [e] using hv0

/-- The address of byte `j` of the `fs` bytes below `sp`, which lie above the stack's limit
`lim`, as an address above `lim`. -/
theorem below_sp {lim sp : UInt64} {fs j : Nat} (hl : lim.toNat ≤ sp.toNat)
    (hfs : fs ≤ (sp - lim).toNat) :
    sp - UInt64.ofNat fs + UInt64.ofNat j = lim + UInt64.ofNat ((sp - lim).toNat - fs + j) := by
  have h1 := sp.toNat_lt
  have hd : (sp - lim).toNat = sp.toNat - lim.toNat := by
    rw [UInt64.toNat_sub]
    simp only [Nat.reducePow] at *
    omega
  rw [hd] at hfs ⊢
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- An address outside the bytes from the stack's limit `lim` up to `sp` lies outside the frame
of `fs` bytes below `sp` and outside the bytes from `lim` to the end of the frame's first `k`
bytes. -/
theorem outside_frame {a sp : UInt64} {fs k : Nat} (hk : k ≤ fs) (hfs : fs < 4096)
    (hl : fs ≤ sp.toNat) (h : sp.toNat + 8 * 0 ≤ a.toNat) :
    ¬ a - (sp - UInt64.ofNat fs) < UInt64.ofNat fs ∧
      (sp - UInt64.ofNat fs).toNat + k ≤ a.toNat := by
  have := a.toNat_lt
  have := sp.toNat_lt
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_ofNat', Nat.reducePow,
    Nat.mul_zero] at *
  constructor <;> omega

theorem function_sim {callee : Table} {S : Shared} {entry : UInt64}
    {f : Function} {is : List Instr} (hg : genFunction callee S entry f = .ok is)
    (hcode : CodeAt code entry is) (F : Nat) {α : Type} (m : Module) (st : Store α)
    (args : List Value) (hargs : args.length = f.params.length) (hargt : Typed f.params args)
    (ms : State) (hpc : ms.pc = entry) (hstk : StackOk P ms)
    (hsr : StoreRel P S.cap S.globalTypes st ms) (h64 : m.memIs64 = false)
    (hregs : ∀ i (hi : i < args.length),
      ValRel args[i] (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩))
    (hcl : CallsOk P code F m callee S) :
    FunOutcome P code callee S (frameSize (f.params.length + f.locals.length))
      f.results (Wasm.exec F m st (f.toLocals args) f.body) ms := by
  obtain ⟨hp8, hr1, hnum, hf, hn, stores, body, fin, g, hsl, hsti, hl, hfin, hgc, his⟩ :=
    gen_function hg
  have hloc : ∀ t ∈ f.locals, ValRel t.zero 0 := fun t ht => ValRel_zero (hnum t ht)
  obtain ⟨hfs, hfs16, hn512⟩ := frameSize_bounds hf
  obtain ⟨hl1, hl2, hl3⟩ := hstk.limit
  generalize hpd : f.params.length = p at *
  generalize hnd : p + f.locals.length = n at *
  generalize hfsd : frameSize n = fs at *
  generalize hrd : f.results.length = r at *
  rw [his] at hcode
  have hca := (CodeAt.append (code := code)).mp hcode
  have hcb := (CodeAt.append (code := code)).mp hca.1
  have hpre : CodeAt code entry ([.subImm 16 31 ⟨fs, hf⟩, .subsReg 31 16 18, .bcond 3 g] ++
      ([.subImm 31 31 ⟨fs, hf⟩, .str 30 31 ⟨n + spillSlots, hn⟩] ++ stores)) := hcb.1
  have hpro := (CodeAt.append (code := code)).mp hpre
  have cbody : CodeAt code (after entry (5 + n)) body := by
    have := hcb.2
    rw [List.length_append, hsl] at this
    exact this
  have cepi : CodeAt code (after (after entry (5 + n)) body.length)
      [.ldr 30 31 ⟨n + spillSlots, hn⟩, .addImm 31 31 ⟨fs, hf⟩, .ret 30] := by
    have := hca.2
    rw [List.length_append, List.length_append, hsl, ← after_after] at this
    exact this
  have hd : (ms.sp - ms.x 18).toNat = ms.sp.toNat - (ms.x 18).toNat := by
    rw [UInt64.toNat_sub]
    simp only [Nat.reducePow] at *
    omega
  obtain ⟨c, hrc, hspc, hmemc, houtc, hxc, hpcc⟩ :=
    run_check P code hf hgc hpro.1 hpc (by omega) hl2
  rcases Nat.lt_or_ge (ms.sp - ms.x 18).toNat fs with hfit | hfit
  · rw [ite_eq_right (by omega)] at hpcc
    exact .inl ⟨.inl hfit, c, hrc, hpcc, houtc⟩
  rw [ite_eq_left hfit] at hpcc
  have hmap : ∀ j < fs, P.normal (ms.sp - UInt64.ofNat fs + UInt64.ofNat j) = true := by
    intro j hj
    rw [below_sp hl2 hfit]
    exact hstk.below _ (by omega)
  obtain ⟨s, hrs, hps, hsps, hxs, hos, h30, hslots, hmems⟩ :=
    run_frame P code (n := n) (j := n + spillSlots) (fs := fs)
      (src := fun i => if i < p then ⟨i % 32, Nat.mod_lt _ (by decide)⟩ else 31)
      (by omega) hfs hfs16 hf hn hn512 hsl (fun i hi => hsti i (by omega)) hpro.2 hpcc
      (by rw [hspc]; exact hstk.aligned) (by rw [hspc]; exact hmap)
  have hsp' : s.sp = ms.sp - UInt64.ofNat fs := by rw [hsps, hspc]
  have h18 : s.x 18 = ms.x 18 := by rw [hxs, hxc 18 (by decide)]
  have hsn : (ms.sp - UInt64.ofNat fs).toNat = ms.sp.toNat - fs := by
    rw [UInt64.toNat_sub, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  have hframe : FrameOk P n s := by
    refine ⟨?_, ?_, hn512, ?_, ?_⟩
    · rw [hsp']; exact sub_aligned hstk.aligned hfs16
    · intro j hj; rw [hsp']; exact hmap j (by omega)
    · rw [hsp', h18, hsn]; omega
    · intro j hj
      rw [h18]
      rw [hsp', h18, UInt64.toNat_sub, hsn] at hj
      simp only [Nat.reducePow] at hj
      exact hstk.below j (by omega)
  have hlts : (f.params ++ f.locals).length = n := by rw [List.length_append, hpd, hnd]
  have hsrs : StoreRel P S.cap S.globalTypes st s := by
    refine hsr.congr (by rw [hxs, hxc 17 (by decide)]) h18 fun a ha => ?_
    rw [hmems a ?_, hmemc]
    rw [hsp', UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, hsn, UInt64.toNat_ofNat']
    have := a.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have hinv : Inv P (f.params ++ f.locals) [] (f.toLocals args) s := by
    refine ⟨⟨by simp [Function.toLocals],
      fun k hk => absurd hk (by simp [Function.toLocals])⟩,
      fun i hi => ?_, by rw [hlts]; simp [Function.toLocals, hargs, ← hnd],
      by rw [hlts]; exact hframe, trivial,
      hargt.append (typed_zeros hnum)⟩
    simp only [Function.toLocals, List.length_append, List.length_map] at hi
    rw [hslots i (by omega)]
    simp only [Function.toLocals]
    by_cases hip : i < p
    · rw [List.getElem_append_left (by omega), ite_eq_left hip,
        hxc _ (by rw [Ne, Fin.ext_iff]; show ¬ i % 32 = 16; omega)]
      exact hregs i (by omega)
    · rw [List.getElem_append_right (by omega), ite_eq_right hip, List.getElem_map]
      exact hloc _ (List.getElem_mem _)
  have hps' : s.pc = after entry (5 + n) := by
    rw [hps, after_after]
    congr 1
    simp only [List.length_cons, List.length_nil]
    omega
  let fn : Ctl :=
    ⟨after (after entry (5 + n)) (listSize (sigOf callee) [r] 0 f.body).1, f.results.reverse, 0⟩
  have hfa : fn.arity = r := by simp [fn, Ctl.arity, hrd]
  have hsize := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil, List.length_nil, Ctl.arity_mk, List.length_reverse,
    hrd] at hsize
  have ho := list_sim P code F { toShared := S, localTypes := f.params ++ f.locals, callee }
    [fn] [] _ f.body body fin hl cbody (Nat.le_refl _)
    ⟨List.cons_ne_nil _ _, fun t ht => by simp at ht; subst ht; exact Nat.le_refl _⟩ m st
    (f.toLocals args) s hinv hsrs h64 hps' hcl
  have ret : ∀ (st' : Store α) (vs : List Value) (ms' : State), Reach P code s ms' →
      ms'.pc = after (after entry (5 + n)) body.length → ms'.sp = s.sp → ms'.out = s.out →
      ms'.x 18 = s.x 18 →
      MemFrame s.sp ((f.params ++ f.locals).length + spillSlots) s ms' → Kept fn vs ms' →
      StoreRel P S.cap S.globalTypes st' ms' →
      ∃ ms'', Reach P code ms ms'' ∧ Returned f.results vs ms ms'' ∧
        StoreRel P S.cap S.globalTypes st' ms'' := by
    intro st' vs ms' hr hp hsp hout h18' hmf0 hk hsr'
    have hmf : MemFrame s.sp (n + spillSlots) s ms' := by rw [← hlts]; exact hmf0
    obtain ⟨ms'', hr', hp', hsp'', hout', hmem', hx'⟩ := run_epilogue P code hf hn cepi hp
      (by rw [hsp]; exact hframe.aligned)
      (fun j hj => by rw [hsp]; exact hframe.mapped (8 * (n + spillSlots) + j) (by omega))
    have hlim := hframe.limit
    have hkl := hk.len
    rw [hfa] at hkl
    have hkt := hk.types
    simp only [fn, Ctl.arity_mk, List.length_reverse] at hkt
    refine ⟨ms'', hrc.trans (hrs.trans (hr.trans hr')),
      ⟨?_, ?_, ?_, ?_, ?_, by rw [hrd]; exact hkl, ?_, hkt⟩,
      hsr'.regs (hx' 17 (by decide)) (hx' 18 (by decide)) hmem'⟩
    · rw [hp', hsp, load64_congr (m' := s.mem) fun k hk' =>
        hmf _ (le_slot hk' hlim.2.2 (by omega) (Nat.le_refl _)), h30, hxc 30 (by decide)]
    · rw [hsp'', hsp, hsps, hspc, UInt64.sub_add_cancel]
    · rw [hx' 18 (by decide), h18', h18]
    · rw [hout', hout, hos, houtc]
    · intro a ha
      obtain ⟨o1, o2⟩ :=
        outside_frame (fs := fs) (k := 8 * (n + spillSlots)) (by omega) hf (by omega) ha
      rw [hmem', hmf a (by rw [hsps, hspc]; exact o2), hmems a (by rw [hsps, hspc]; exact o1),
        hmemc]
    · rw [hx' 0 (by decide), hrd, ← hfa]
      exact kept_res hk rfl (by rw [hfa]; exact hr1)
  generalize Wasm.exec F m st (f.toLocals args) f.body = res at ho ⊢
  rcases ho with ⟨hc, ms', hr, hp, hout⟩ | ho
  · exact .inl ⟨.inr hc, ms', hrc.trans (hrs.trans hr), hp, by rw [hout, hos, houtc]⟩
  refine .inr ?_
  cases res with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf', ms', hr, hp, hsp, hout, h18', hmf, hinv', -, hsr'⟩ := ho
      have e := hfin σ' hf'
      have hty' := hinv'.types
      rw [e] at hty'
      exact ret st' _ ms' hr hp hsp hout h18' hmf
        (StackRel.kept hinv'.stack (by rw [← hty'.length]; simp [fn, Ctl.arity])
          (by
            rw [List.take_of_length_le (by rw [← hty'.length]; simp [fn, Ctl.arity])]
            exact hty')) hsr'
  | Break k st' sl' =>
      cases k with
      | zero =>
          obtain ⟨t, ht, ms', hr, hp, hsp, hout, h18', hmf, -, -, hk, -, hsr'⟩ := ho
          have e : t = fn := by simpa using ht.symm
          subst e
          exact ret st' _ ms' hr (by rw [hp, hsize]) hsp hout h18' hmf hk hsr'
      | succ k => trivial
  | Return st' vs =>
      obtain ⟨t, ht, ms', hr, hp, hsp, hout, h18', hmf, hk, hsr'⟩ := ho
      have e : t = fn := by simpa using ht.symm
      subst e
      exact ret st' _ ms' hr (by rw [hp, hsize]) hsp hout h18' hmf hk hsr'
  | Trap st' msg =>
      obtain ⟨ms', hr, hout, hpc'⟩ := ho
      exact ⟨ms', hrc.trans (hrs.trans hr), by rw [hout, hos, houtc], hpc'⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-! ## Calls -/

/-- What the machine does from the entry of function `k` of `m`, which imports nothing, whose
code `genFunction` places at `entry`, when Talos runs a call of it at fuel `g` on the operand stack
`vs`, the top `f.params.length` values in X0 upward, the deepest first, and the functions of its
table simulate below `g`: `CallResult`, or, when the frame does not fit between the stack's limit
and SP or the function may call another, the machine reaches the stub `tS` of an overflow of the
stack. -/
theorem run_outcome {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (hm : m.imports = []) (h64 : m.memIs64 = false) (hk : m.funcs[k]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} (hcl : CallsOk P code g m callee S) {α : Type} (st : Store α)
    (vs : List Value) (ms : State) (hp : f.params.length ≤ vs.length)
    (hvt : Typed f.params.reverse (vs.take f.params.length)) (hpc : ms.pc = entry)
    (hstk : StackOk P ms) (hsr : StoreRel P S.cap S.globalTypes st ms)
    (hargs : ∀ i (hi : i < f.params.length),
      ValRel (vs[f.params.length - 1 - i]'(by omega)) (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩)) :
    (((ms.sp - ms.x 18).toNat < frameSize (f.params.length + f.locals.length) ∨
        HasCalls callee) ∧ Overflows P code S.trapStack ms) ∨
      CallResult P code S f.params f.results vs (Wasm.run g m k st vs) ms := by
  have hargs' : ((vs.take f.params.length).reverse).length = f.params.length := by
    simp
    omega
  have hregs : ∀ i (hi : i < ((vs.take f.params.length).reverse).length),
      ValRel ((vs.take f.params.length).reverse)[i]
        (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩) := by
    intro i hi
    rw [hargs'] at hi
    have := hargs i hi
    simp only [List.getElem_reverse, List.getElem_take, List.length_take]
    have e : min f.params.length vs.length - 1 - i = f.params.length - 1 - i := by omega
    simp only [e]
    exact this
  have hargt : Typed f.params (vs.take f.params.length).reverse := by
    have := Typed.reverse hvt
    rwa [List.reverse_reverse] at this
  have ho := function_sim P code hg hcode g m st _ hargs' hargt ms hpc hstk hsr h64 hregs hcl
  simp only [Wasm.run, hm, List.getElem?_nil, List.length_nil, Nat.sub_zero, hk,
    Function.numParams]
  rcases ho with hov | ho
  · exact .inl hov
  refine .inr ?_
  revert ho
  generalize Wasm.exec g m st (f.toLocals (vs.take f.params.length).reverse) f.body = res
  have hout : ∀ (st' : Store α) (vals : List Value) (ms' : State), Reach P code ms ms' →
      Returned f.results vals ms ms' → StoreRel P S.cap S.globalTypes st' ms' →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = ms.x 30 ∧ ms'.sp = ms.sp ∧ ms'.x 18 = ms.x 18 ∧
        ms'.out = ms.out ∧ MemFrame ms.sp 0 ms ms' ∧
        (vals.take f.results.length ++ vs.drop f.params.length).length =
          f.results.length + (vs.length - f.params.length) ∧
        (vals.take f.results.length ++ vs.drop f.params.length).drop f.results.length =
          vs.drop f.params.length ∧
        (∀ v ∈ (vals.take f.results.length ++ vs.drop f.params.length).take f.results.length,
          ValRel v (ms'.x 0)) ∧
        Typed f.results.reverse
          ((vals.take f.results.length ++ vs.drop f.params.length).take f.results.length) ∧
        StoreRel P S.cap S.globalTypes st' ms' := by
    intro st' vals ms' hr hret hsr'
    have hl : (vals.take f.results.length).length = f.results.length := by
      have := hret.len
      simp
      omega
    refine ⟨ms', hr, hret.pc, hret.sp, hret.x18, hret.out, hret.mem, by simp [hl], ?_, ?_⟩
    · exact List.drop_left' hl
    · rw [List.take_left' hl]
      exact ⟨hret.res, hret.types, hsr'⟩
  cases res with
  | Fallthrough st' sl' =>
      intro ho
      obtain ⟨ms', hr, hret, hsr'⟩ := ho
      exact hout st' _ ms' hr hret hsr'
  | Break n st' sl' =>
      cases n with
      | zero =>
          intro ho
          obtain ⟨ms', hr, hret, hsr'⟩ := ho
          exact hout st' _ ms' hr hret hsr'
      | succ n => intro _; trivial
  | Return st' vals =>
      intro ho
      obtain ⟨ms', hr, hret, hsr'⟩ := ho
      exact hout st' _ ms' hr hret hsr'
  | Trap st' msg => intro ho; exact ho
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | ReturnCall _ _ _ => intro ho; exact ho.elim
  | Throwing _ _ _ _ => intro ho; exact ho.elim

/-- The simulation of a call of function `k` of `m`, which imports nothing, whose code
`genFunction` places at `entry`, at fuel `g`, when the functions of its table simulate below
`g`. -/
theorem fun_sim {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (hm : m.imports = []) (h64 : m.memIs64 = false) (hk : m.funcs[k]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} (hcl : CallsOk P code g m callee S) :
    FunSim P code m S g k (entry, f.params, f.results) := by
  intro α st vs ms hp hvt hpc hstk hsr hargs
  rcases run_outcome P code hm h64 hk hg hcode hcl st vs ms hp hvt hpc hstk hsr hargs with
    ⟨-, hov⟩ | h
  · exact .inl hov
  · exact .inr h

/-- The functions of a table whose code `genFunction` places at their entries, in a module that
imports nothing, simulate at every fuel. -/
theorem calls_ok {callee : Table} {S : Shared}
    {m : Module} (hm : m.imports = []) (h64 : m.memIs64 = false)
    (htab : ∀ k c, callee k = some c → ∃ f is, m.funcs[k]? = some f ∧
      c.2 = (f.params, f.results) ∧ genFunction callee S c.1 f = .ok is ∧
      CodeAt code c.1 is) :
    ∀ F, CallsOk P code F m callee S := by
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      intro k c hk g hg
      obtain ⟨f, is, hf, hc2, hgen, hcode⟩ := htab k c hk
      obtain ⟨e, p, r⟩ := c
      simp only [Prod.mk.injEq] at hc2
      obtain ⟨rfl, rfl⟩ := hc2
      exact fun_sim P code hm h64 hf hgen hcode (ih g hg)

end LeanExe.A64
