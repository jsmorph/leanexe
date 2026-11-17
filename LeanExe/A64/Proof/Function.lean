import LeanExe.A64.Proof.Constructs

/-!
The simulation of a function.  The prologue compares SP less the frame's `frameSize n` bytes
with the stack's limit in X18 and branches to the stub of an overflow of the stack when the frame
does not fit.  Otherwise it allocates the frame below SP, saves X30 in the slot above the `n`
locals and their spill slots, and stores the parameters from X0 up and zeros for the other locals
into their slots, so that Talos's locals on entry and the machine's state after the prologue
satisfy `Inv`.  The body's outcome under the function's construct leads to the epilogue, which
reloads X30 from its slot, which the body's code leaves unchanged, frees the frame, and returns.

The proofs hold over every `Machine`, for modules with imports: a function's index lies at or
above the number of imports and its position in `m.funcs` is the index less that number.  A call
of an import's index runs a stub, whose behavior `Machine.StubSim` states as a premise:
`Machine.fun_sim_import` derives the call's simulation under the machine's host environment from
it, and `Machine.calls_ok` gives `CallsOk` at every fuel for a table of stubs and generated
functions.  The theorems for modules without imports follow at `bare P code α`.
-/

namespace LeanExe.A64

open Wasm

export LeanExe.CallGraph (foldr_max_le le_foldr_max callNeed le_callNeed callNeed_mono NeedOk
  NeedOk.lt)

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
    p ≤ 26 ∧ r ≤ 26 ∧ (∀ t ∈ f.locals, numeric t = true) ∧
      ∃ (hf : frameSize n < 4096) (hn : n + spillSlots < 4096)
      (stores body : List Instr) (fin : Option (List ValueType)) (g : Fin 524288),
      stores.length = n ∧
      (∀ i (hi : i < stores.length), ∃ hs, stores[i] =
        .str (if i < p then regOf i else 31) 31 ⟨i, hs⟩) ∧
      genList { toShared := S, localTypes := f.params ++ f.locals, callee }
        [⟨after bodyA (listSize (sigOf callee) [r] 0 f.body).1, f.results.reverse, 0⟩] []
        bodyA f.body = .ok (body, fin) ∧ (∀ x, fin = some x → x = f.results.reverse) ∧
      cbField (after entry 2) S.trapStack = .ok g ∧
      is = [.subImm 16 31 ⟨frameSize n, hf⟩, .subsReg 31 16 18, .bcond 3 g,
          .subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n + spillSlots, hn⟩] ++ stores ++ body ++
        [.ldr 30 31 ⟨n + spillSlots, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30] := by
  dsimp only
  by_cases hc : f.params.length > 26 ∨ f.results.length > 26
  · simp [genFunction, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have h1 : ¬ f.params.length > 26 := by omega
  have h2 : ¬ f.results.length > 26 := by omega
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
        Instr.str (if i.val < f.params.length then regOf i.val else 31) 31 ⟨i.val, by omega⟩),
      v.1, v.2, g, by simp, fun i hi => ⟨by simp at hi; omega, by simp⟩,
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
    ∃ s, Reach P code ms s ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.io = ms.io ∧
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
      (∀ q, s.x q = ms.x q) ∧ s.io = ms.io ∧ load64 s.mem (slotAddr s.sp j) = ms.x 30 ∧
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
      s'.sp = s.sp + UInt64.ofNat fs ∧ s'.io = s.io ∧ s'.mem = s.mem ∧
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
  · show (s.setX 30 w).io = s.io
    exact State.setX_io
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
  out : ms'.io = ms.io
  mem : MemFrame ms.sp 0 ms ms'
  len : rs.length ≤ vs.length
  res : StackRel ms' (vs.take rs.length)
  types : Typed rs.reverse (vs.take rs.length)

/-- What the machine does from `ms` at the entry of a function with results of the types `rs`
when Talos's run of the function's body gives `r`: a return reaches the return address with the
final store in the area, and a trap reaches the stub of its code.  When fewer than `n` bytes lie
between the stack's limit and SP, the machine may instead reach the stub of an overflow of the
stack. -/
def FunOutcome (S : Shared) (n : Nat) (rs : List ValueType)
    {α : Type} (r : Continuation α) (ms : State) : Prop :=
  ((ms.sp - ms.x 18).toNat < n ∧ Overflows P code S.trapStack ms) ∨
  match r with
  | .Fallthrough st' sl' => ∃ ms', Reach P code ms ms' ∧ Returned rs sl'.values ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Break 0 st' sl' => ∃ ms', Reach P code ms ms' ∧ Returned rs sl'.values ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Return st' vs => ∃ ms', Reach P code ms ms' ∧ Returned rs vs ms ms' ∧
      StoreRel P S.cap S.globalTypes st' ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.io = ms.io ∧
      TrapAt S.trapUnreachable S.trapBounds S.trapDiv msg ms'.pc
  | .Break (_ + 1) _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

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

/-! ## The simulation over a machine -/

namespace Machine

section General

variable {P code}
variable {α : Type} (M : Machine P code α)

/-- `FunOutcome` over the machine `M`. -/
def FunOutcome (S : Shared) (n : Nat) (rs : List ValueType) (r : Continuation α) (q : M.Q) :
    Prop :=
  (((M.core q).sp - (M.core q).x 18).toNat < n ∧ M.Overflows S.trapStack q) ∨
  match r with
  | .Fallthrough st' sl' => ∃ q', M.Rch q q' ∧ Returned rs sl'.values (M.core q) (M.core q') ∧
      M.SR S.cap S.globalTypes st' q'
  | .Break 0 st' sl' => ∃ q', M.Rch q q' ∧ Returned rs sl'.values (M.core q) (M.core q') ∧
      M.SR S.cap S.globalTypes st' q'
  | .Return st' vs => ∃ q', M.Rch q q' ∧ Returned rs vs (M.core q) (M.core q') ∧
      M.SR S.cap S.globalTypes st' q'
  | .Trap _ msg => ∃ q', M.Rch q q' ∧ (M.core q').io = (M.core q).io ∧ M.Trapped S msg q'
  | .Break (_ + 1) _ _ => True
  | .Invalid _ => True
  | .OutOfFuel => True
  | .ReturnCall _ _ _ => False
  | .Throwing _ _ _ _ => False

theorem function_sim {callee : Table} {S : Shared} {entry : UInt64}
    {f : Function} {is : List Instr} (hg : genFunction callee S entry f = .ok is)
    (hcode : CodeAt code entry is) (F : Nat) (m : Module) (st : Store α)
    (args : List Value) (hargs : args.length = f.params.length) (hargt : Typed f.params args)
    (q : M.Q) (hpc : (M.core q).pc = entry) (hstk : StackOk P (M.core q))
    (hsr : M.SR S.cap S.globalTypes st q) (h64 : m.memIs64 = false)
    (hregs : ∀ i (hi : i < args.length), ValRel args[i] ((M.core q).x (regOf i)))
    {need : Nat → Nat} (hcl : M.CallsOk F m callee S need) {n0 : Nat}
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body n0) :
    M.FunOutcome S n0 f.results (Wasm.exec F m st (f.toLocals args) f.body M.env) q := by
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
  have hd : ((M.core q).sp - (M.core q).x 18).toNat =
      (M.core q).sp.toNat - ((M.core q).x 18).toNat := by
    rw [UInt64.toNat_sub]
    simp only [Nat.reducePow] at *
    omega
  obtain ⟨c, hrc, hspc, hmemc, houtc, hxc, hpcc⟩ :=
    run_check P code hf hgc hpro.1 hpc (by omega) hl2
  have hd64 := ((M.core q).sp - (M.core q).x 18).toNat_lt
  rcases Nat.lt_or_ge ((M.core q).sp - (M.core q).x 18).toNat fs with hfit | hfit
  · rw [ite_eq_right (by omega)] at hpcc
    obtain ⟨qc, hqc, hcc, -⟩ := M.lift hsr hrc
    subst hcc
    exact .inl ⟨hneed.lt hd64 (by omega), qc, hqc, hpcc, houtc⟩
  rw [ite_eq_left hfit] at hpcc
  have hmap : ∀ j < fs, P.normal ((M.core q).sp - UInt64.ofNat fs + UInt64.ofNat j) = true := by
    intro j hj
    rw [below_sp hl2 hfit]
    exact hstk.below _ (by omega)
  obtain ⟨s, hrs, hps, hsps, hxs, hos, h30, hslots, hmems⟩ :=
    run_frame P code (n := n) (j := n + spillSlots) (fs := fs)
      (src := fun i => if i < p then regOf i else 31)
      (by omega) hfs hfs16 hf hn hn512 hsl (fun i hi => hsti i (by omega)) hpro.2 hpcc
      (by rw [hspc]; exact hstk.aligned) (by rw [hspc]; exact hmap)
  have hsp' : s.sp = (M.core q).sp - UInt64.ofNat fs := by rw [hsps, hspc]
  have h18 : s.x 18 = (M.core q).x 18 := by rw [hxs, hxc 18 (by decide)]
  have hsn : ((M.core q).sp - UInt64.ofNat fs).toNat = (M.core q).sp.toNat - fs := by
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
    refine (M.storeRel hsr).congr (by rw [hxs, hxc 17 (by decide)]) h18 fun a ha => ?_
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
        hxc _ (regOf_ne_scratch i (by omega))]
      exact hregs i (by omega)
    · rw [List.getElem_append_right (by omega), ite_eq_right hip, List.getElem_map]
      exact hloc _ (List.getElem_mem _)
  have hps' : s.pc = after entry (5 + n) := by
    rw [hps, after_after]
    congr 1
    simp only [List.length_cons, List.length_nil]
    omega
  obtain ⟨qs, hqs, hcs, hsts⟩ := M.lift hsr (hrc.trans hrs)
  have hsrqs := hsts st hsrs rfl
  subst hcs
  let fn : Ctl :=
    ⟨after (after entry (5 + n)) (listSize (sigOf callee) [r] 0 f.body).1, f.results.reverse, 0⟩
  have hfa : fn.arity = r := by simp [fn, Ctl.arity, hrd]
  have hsize := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil, List.length_nil, Ctl.arity_mk, List.length_reverse,
    hrd] at hsize
  have ho := list_sim M F { toShared := S, localTypes := f.params ++ f.locals, callee }
    [fn] [] _ f.body body fin hl cbody (Nat.le_refl _)
    ⟨List.cons_ne_nil _ _, fun t ht => by simp at ht; subst ht; exact Nat.le_refl _⟩ m st
    (f.toLocals args) qs hinv hsrqs h64 hps' need (callNeed need f.body) hcl
    fun j hj => le_callNeed hj
  have ret : ∀ (st' : Store α) (vs : List Value) (q' : M.Q), M.Rch qs q' →
      (M.core q').pc = after (after entry (5 + n)) body.length →
      (M.core q').sp = (M.core qs).sp → (M.core q').io = (M.core qs).io →
      (M.core q').x 18 = (M.core qs).x 18 →
      MemFrame (M.core qs).sp ((f.params ++ f.locals).length + spillSlots) (M.core qs)
        (M.core q') → Kept fn vs (M.core q') → M.SR S.cap S.globalTypes st' q' →
      ∃ q'', M.Rch q q'' ∧ Returned f.results vs (M.core q) (M.core q'') ∧
        M.SR S.cap S.globalTypes st' q'' := by
    intro st' vs q' hr hp hsp hout h18' hmf0 hk hsr'
    have hmf : MemFrame (M.core qs).sp (n + spillSlots) (M.core qs) (M.core q') := by
      rw [← hlts]; exact hmf0
    obtain ⟨ms'', hr', hp', hsp'', hout', hmem', hx'⟩ := run_epilogue P code hf hn cepi hp
      (by rw [hsp]; exact hframe.aligned)
      (fun j hj => by rw [hsp]; exact hframe.mapped (8 * (n + spillSlots) + j) (by omega))
    have hlim := hframe.limit
    have hkl := hk.len
    rw [hfa] at hkl
    have hkt := hk.types
    simp only [fn, Ctl.arity_mk, List.length_reverse] at hkt
    obtain ⟨q'', hq'', hc'', hst''⟩ := M.lift hsr' hr'
    have hsr'' := hst'' st'
      ((M.storeRel hsr').regs (hx' 17 (by decide)) (hx' 18 (by decide)) hmem') rfl
    subst hc''
    refine ⟨q'', M.trans hqs (M.trans hr hq''),
      ⟨?_, ?_, ?_, ?_, ?_, by rw [hrd]; exact hkl, ?_, hkt⟩, hsr''⟩
    · rw [hp', hsp, load64_congr (m' := (M.core qs).mem) fun k hk' =>
        hmf _ (le_slot hk' hlim.2.2 (by omega) (Nat.le_refl _)), h30, hxc 30 (by decide)]
    · rw [hsp'', hsp, hsps, hspc, UInt64.sub_add_cancel]
    · rw [hx' 18 (by decide), h18', h18]
    · rw [hout', hout, hos, houtc]
    · intro a ha
      obtain ⟨o1, o2⟩ :=
        outside_frame (fs := fs) (k := 8 * (n + spillSlots)) (by omega) hf (by omega) ha
      rw [hmem', hmf a (by rw [hsps, hspc]; exact o2), hmems a (by rw [hsps, hspc]; exact o1),
        hmemc]
    · rw [hrd, ← hfa]
      have := StackRel.of_kept (s := M.core q') (below := []) hk
        ⟨by simp, fun k hk => absurd hk (by simp)⟩ rfl
        (fun k hk => absurd hk (by simp [fn]))
      rw [List.append_nil] at this
      exact this.congr fun k hk => hx' _ (regOf_ne_30 k (by have := this.1; omega))
  generalize Wasm.exec F m st (f.toLocals args) f.body M.env = res at ho ⊢
  rcases ho with ⟨hc, q', hr, hp, hout⟩ | ho
  · have hds : ((M.core qs).sp - (M.core qs).x 18).toNat + fs =
        ((M.core q).sp - (M.core q).x 18).toNat := by
      rw [hsp', h18, UInt64.toNat_sub_of_le ((M.core q).sp - UInt64.ofNat fs) ((M.core q).x 18)
        (UInt64.le_iff_toNat_le.mpr (by omega)), hsn]
      omega
    exact .inl ⟨hneed.lt hd64 (by omega), q', M.trans hqs hr, hp,
      by rw [hout, hos, houtc]⟩
  refine .inr ?_
  cases res with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf', q', hr, hp, hsp, hout, h18', hmf, hinv', -, hsr'⟩ := ho
      have e := hfin σ' hf'
      have hty' := hinv'.types
      rw [e] at hty'
      exact ret st' _ q' hr hp hsp hout h18' hmf
        (StackRel.kept hinv'.stack (by rw [← hty'.length]; simp [fn, Ctl.arity])
          (by
            rw [List.take_of_length_le (by rw [← hty'.length]; simp [fn, Ctl.arity])]
            exact hty')) hsr'
  | Break k st' sl' =>
      cases k with
      | zero =>
          obtain ⟨t, ht, q', hr, hp, hsp, hout, h18', hmf, -, -, hk, -, hsr'⟩ := ho
          have e : t = fn := by simpa using ht.symm
          subst e
          exact ret st' _ q' hr (by rw [hp, hsize]) hsp hout h18' hmf hk hsr'
      | succ k => trivial
  | Return st' vs =>
      obtain ⟨t, ht, q', hr, hp, hsp, hout, h18', hmf, hk, hsr'⟩ := ho
      have e : t = fn := by simpa using ht.symm
      subst e
      exact ret st' _ q' hr (by rw [hp, hsize]) hsp hout h18' hmf hk hsr'
  | Trap st' msg =>
      obtain ⟨q', hr, hout, hpc'⟩ := ho
      exact ⟨q', M.trans hqs hr, by rw [hout, hos, houtc], hpc'⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-- A return to the caller with the results `vals` of the types `rs`, from a call on the stack
`vs` whose arguments have the types `ps`, gives `CallResult`'s success for the results that
Talos's `run` passes back. -/
theorem callResult_success {S : Shared} {ps rs : List ValueType} {vs vals : List Value}
    {st' : Store α} {q q' : M.Q} (hr : M.Rch q q')
    (hret : Returned rs vals (M.core q) (M.core q')) (hsr' : M.SR S.cap S.globalTypes st' q') :
    M.CallResult S ps rs vs (.Success (vals.take rs.length ++ vs.drop ps.length) st') q := by
  have hl : (vals.take rs.length).length = rs.length := by
    have := hret.len
    simp
    omega
  refine ⟨q', hr, hret.pc, hret.sp, hret.x18, hret.out, hret.mem, by simp [hl], ?_, ?_⟩
  · exact List.drop_left' hl
  · rw [List.take_left' hl]
    exact ⟨hret.res, hret.types, hsr'⟩

/-! ## Calls -/

/-- What the machine does from the entry of function `k` of `m`, whose code `genFunction` places
at `entry`, when Talos runs a call of it at fuel `g` on the operand stack `vs` under `M.env`, the
top `f.params.length` values in X0 upward, the deepest first, and the functions of its table
simulate below `g` with the bounds `need`: `CallOutcome` with the bound `n` of the stack that the
call uses.  The function is defined: its index lies at or above the number of imports. -/
theorem run_outcome {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (himp : m.imports.length ≤ k) (h64 : m.memIs64 = false)
    (hk : m.funcs[k - m.imports.length]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} {need : Nat → Nat} (hcl : M.CallsOk g m callee S need) {n : Nat}
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body n)
    (st : Store α) (vs : List Value) (q : M.Q) (hp : f.params.length ≤ vs.length)
    (hvt : Typed f.params.reverse (vs.take f.params.length)) (hpc : (M.core q).pc = entry)
    (hstk : StackOk P (M.core q)) (hsr : M.SR S.cap S.globalTypes st q)
    (hargs : StackRel (M.core q) (vs.take f.params.length)) :
    M.CallOutcome S n f.params f.results vs (Wasm.run g m k st vs M.env) q := by
  have hargs' : ((vs.take f.params.length).reverse).length = f.params.length := by
    simp
    omega
  have hregs : ∀ i (hi : i < ((vs.take f.params.length).reverse).length),
      ValRel ((vs.take f.params.length).reverse)[i] ((M.core q).x (regOf i)) := fun i hi =>
    hargs.2 i (by simpa using hi)
  have hargt : Typed f.params (vs.take f.params.length).reverse := by
    have := Typed.reverse hvt
    rwa [List.reverse_reverse] at this
  have ho := function_sim M hg hcode g m st _ hargs' hargt q hpc hstk hsr h64 hregs hcl hneed
  simp only [Wasm.run, List.getElem?_eq_none himp, hk, Function.numParams]
  rcases ho with hov | ho
  · exact .inl hov
  refine .inr ?_
  revert ho
  generalize Wasm.exec g m st (f.toLocals (vs.take f.params.length).reverse) f.body M.env = res
  cases res with
  | Fallthrough st' sl' =>
      intro ho
      obtain ⟨q', hr, hret, hsr'⟩ := ho
      exact callResult_success M hr hret hsr'
  | Break n st' sl' =>
      cases n with
      | zero =>
          intro ho
          obtain ⟨q', hr, hret, hsr'⟩ := ho
          exact callResult_success M hr hret hsr'
      | succ n => intro _; trivial
  | Return st' vals =>
      intro ho
      obtain ⟨q', hr, hret, hsr'⟩ := ho
      exact callResult_success M hr hret hsr'
  | Trap st' msg => intro ho; exact ho
  | Invalid _ => intro _; trivial
  | OutOfFuel => intro _; trivial
  | ReturnCall _ _ _ => intro ho; exact ho.elim
  | Throwing _ _ _ _ => intro ho; exact ho.elim

/-- The simulation of a call of the defined function `k` of `m`, whose code `genFunction` places
at `entry`, at fuel `g`, when the functions of its table simulate below `g` and `need k` bounds
the stack that the call uses. -/
theorem fun_sim {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (himp : m.imports.length ≤ k) (h64 : m.memIs64 = false)
    (hk : m.funcs[k - m.imports.length]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} {need : Nat → Nat} (hcl : M.CallsOk g m callee S need)
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    M.FunSim m S need g k (entry, f.params, f.results) :=
  fun st vs q hp hvt hpc hstk hsr hargs =>
    run_outcome M himp h64 hk hg hcode hcl hneed st vs q hp hvt hpc hstk hsr hargs

/-! ## Imports -/

/-- What the machine does from `q` at the entry of a stub of an import with results of the types
`rs`, when the host function gives `r`: a return reaches the return address in X30 as a function
returns, with the results, top first, in the registers of the heights from 0 and the host's
store held, and a trap ends where `M.Trapped` admits.  When fewer than `n` bytes lie between the
stack's limit and SP, the machine may instead reach the stub of an overflow of the stack. -/
def StubResult (S : Shared) (n : Nat) (rs : List ValueType) (r : HostResult α) (q : M.Q) :
    Prop :=
  (((M.core q).sp - (M.core q).x 18).toNat < n ∧ M.Overflows S.trapStack q) ∨
  match r with
  | .Return vs st' => ∃ q', M.Rch q q' ∧ Returned rs vs (M.core q) (M.core q') ∧
      M.SR S.cap S.globalTypes st' q'
  | .Trap _ msg => ∃ q', M.Rch q q' ∧ (M.core q').io = (M.core q).io ∧ M.Trapped S msg q'
  | .Throw _ _ _ => False

/-- What a stub at `entry` must satisfy to stand for the host function `hf` of an import with
parameters of the types `ps` and results of the types `rs`: from the entry, with the stack's
limit in X18, the store held, and the arguments `args`, first parameter first, in the registers
of the heights from 0, the machine does what `StubResult` states of `hf.invoke st args`. -/
def StubSim (S : Shared) (n : Nat) (ps rs : List ValueType) (hf : HostFn α) (entry : UInt64) :
    Prop :=
  ∀ (st : Store α) (args : List Value) (q : M.Q), args.length = ps.length → Typed ps args →
    (M.core q).pc = entry → StackOk P (M.core q) → M.SR S.cap S.globalTypes st q →
    (∀ i (hi : i < args.length), ValRel args[i] ((M.core q).x (regOf i))) →
    M.StubResult S n rs (hf.invoke st args) q

/-- The simulation of a call of import `k` of `m`, whose host function in `M.env` is `hf`, by a
stub at `entry` that meets `StubSim`, at every fuel. -/
theorem fun_sim_import {m : Module} {S : Shared} {need : Nat → Nat} {k : Nat}
    {imp : ImportDecl} {hf : HostFn α} {entry : UInt64} (himp : m.imports[k]? = some imp)
    (hhf : M.env.funcs[k]? = some hf)
    (hstub : M.StubSim S (need k) imp.params imp.results hf entry) (g : Nat) :
    M.FunSim m S need g k (entry, imp.params, imp.results) := by
  intro st vs q hp hvt hpc hstk hsr hargs
  have hargs' : ((vs.take imp.params.length).reverse).length = imp.params.length := by
    simp only [List.length_reverse, List.length_take]
    exact Nat.min_eq_left hp
  have hregs : ∀ i (hi : i < ((vs.take imp.params.length).reverse).length),
      ValRel ((vs.take imp.params.length).reverse)[i] ((M.core q).x (regOf i)) := fun i hi =>
    hargs.2 i (by simpa using hi)
  have hargt : Typed imp.params (vs.take imp.params.length).reverse := by
    have := Typed.reverse hvt
    rwa [List.reverse_reverse] at this
  have ho := hstub st _ q hargs' hargt hpc hstk hsr hregs
  simp only [Wasm.run, himp, hhf]
  rcases ho with hov | ho
  · exact .inl hov
  refine .inr ?_
  revert ho
  cases hf.invoke st (vs.take imp.params.length).reverse with
  | Return vals st' =>
      intro ho
      obtain ⟨q', hr, hret, hsr'⟩ := ho
      exact callResult_success M hr hret hsr'
  | Trap st' msg => intro ho; exact ho
  | Throw _ _ _ => intro ho; exact ho.elim

/-- The functions of a table simulate at every fuel, with bounds `need` of the stack that their
calls use, on a platform that meets what their code assumes of it, when each entry of the table
is an import whose host function in `M.env` a stub at the entry stands for, or a defined function
whose code `genFunction` places at the entry. -/
theorem calls_ok {callee : Table} {S : Shared} {m : Module} (h64 : m.memIs64 = false)
    (hU : S.byteStores = true → P.normal P.uart = false) {need : Nat → Nat}
    (htab : ∀ k c, callee k = some c →
      (∃ imp hf, m.imports[k]? = some imp ∧ M.env.funcs[k]? = some hf ∧
        c.2 = (imp.params, imp.results) ∧ M.StubSim S (need k) imp.params imp.results hf c.1) ∨
      ∃ f is, m.imports.length ≤ k ∧ m.funcs[k - m.imports.length]? = some f ∧
        c.2 = (f.params, f.results) ∧ genFunction callee S c.1 f = .ok is ∧ CodeAt code c.1 is)
    (hneed : ∀ k f, m.imports.length ≤ k → m.funcs[k - m.imports.length]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    ∀ F, M.CallsOk F m callee S need := by
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      refine ⟨hU, fun k c hk g hg => ?_⟩
      rcases htab k c hk with ⟨imp, hf, himp, hhf, hc2, hstub⟩ |
        ⟨f, is, himp, hf, hc2, hgen, hcode⟩
      · obtain ⟨e, p, r⟩ := c
        simp only [Prod.mk.injEq] at hc2
        obtain ⟨rfl, rfl⟩ := hc2
        exact fun_sim_import M himp hhf hstub g
      · obtain ⟨e, p, r⟩ := c
        simp only [Prod.mk.injEq] at hc2
        obtain ⟨rfl, rfl⟩ := hc2
        exact fun_sim M himp h64 hf hgen hcode (ih g hg) (hneed k f himp hf)

/-- The simulation of Talos's run of each function of the table under `M.env`, defined or
imported, at every fuel, under the premises of `calls_ok`. -/
theorem callee_sim {callee : Table} {S : Shared} {m : Module} (h64 : m.memIs64 = false)
    (hU : S.byteStores = true → P.normal P.uart = false) {need : Nat → Nat}
    (htab : ∀ k c, callee k = some c →
      (∃ imp hf, m.imports[k]? = some imp ∧ M.env.funcs[k]? = some hf ∧
        c.2 = (imp.params, imp.results) ∧ M.StubSim S (need k) imp.params imp.results hf c.1) ∨
      ∃ f is, m.imports.length ≤ k ∧ m.funcs[k - m.imports.length]? = some f ∧
        c.2 = (f.params, f.results) ∧ genFunction callee S c.1 f = .ok is ∧ CodeAt code c.1 is)
    (hneed : ∀ k f, m.imports.length ≤ k → m.funcs[k - m.imports.length]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k))
    {k : Nat} {c : UInt64 × List ValueType × List ValueType} (hk : callee k = some c)
    (g : Nat) : M.FunSim m S need g k c :=
  (calls_ok M h64 hU htab hneed (g + 1)).2 k c hk g (Nat.lt_succ_self g)

end General

end Machine

/-! ## At the bare machine -/

theorem FunOutcome.eq_bare (S : Shared) (n : Nat) (rs : List ValueType) {α : Type}
    (r : Continuation α) (ms : State) :
    FunOutcome P code S n rs r ms = (bare P code α).FunOutcome S n rs r ms := rfl

theorem function_sim {callee : Table} {S : Shared} {entry : UInt64}
    {f : Function} {is : List Instr} (hg : genFunction callee S entry f = .ok is)
    (hcode : CodeAt code entry is) (F : Nat) {α : Type} (m : Module) (st : Store α)
    (args : List Value) (hargs : args.length = f.params.length) (hargt : Typed f.params args)
    (ms : State) (hpc : ms.pc = entry) (hstk : StackOk P ms)
    (hsr : StoreRel P S.cap S.globalTypes st ms) (h64 : m.memIs64 = false)
    (hregs : ∀ i (hi : i < args.length), ValRel args[i] (ms.x (regOf i)))
    {need : Nat → Nat} (hcl : CallsOk P code F m callee S need) {n0 : Nat}
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body n0) :
    FunOutcome P code S n0 f.results (Wasm.exec F m st (f.toLocals args) f.body) ms :=
  Machine.function_sim (bare P code α) hg hcode F m st args hargs hargt ms hpc hstk hsr h64 hregs
    ((CallsOk.iff_bare P code _ _ _ _ _).mp hcl α) hneed

/-- What the machine does from the entry of function `k` of `m`, which imports nothing, whose
code `genFunction` places at `entry`, when Talos runs a call of it at fuel `g` on the operand stack
`vs`, the top `f.params.length` values in X0 upward, the deepest first, and the functions of its
table simulate below `g` with the bounds `need`: `CallOutcome` with the bound `n` of the stack
that the call uses. -/
theorem run_outcome {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (hm : m.imports = []) (h64 : m.memIs64 = false) (hk : m.funcs[k]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} {need : Nat → Nat} (hcl : CallsOk P code g m callee S need) {n : Nat}
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body n)
    {α : Type} (st : Store α)
    (vs : List Value) (ms : State) (hp : f.params.length ≤ vs.length)
    (hvt : Typed f.params.reverse (vs.take f.params.length)) (hpc : ms.pc = entry)
    (hstk : StackOk P ms) (hsr : StoreRel P S.cap S.globalTypes st ms)
    (hargs : StackRel ms (vs.take f.params.length)) :
    CallOutcome P code S n f.params f.results vs (Wasm.run g m k st vs) ms :=
  Machine.run_outcome (bare P code α) (by simp [hm]) h64 (by simp [hm, hk]) hg hcode
    ((CallsOk.iff_bare P code _ _ _ _ _).mp hcl α) hneed st vs ms hp hvt hpc hstk hsr hargs

/-- The simulation of a call of function `k` of `m`, which imports nothing, whose code
`genFunction` places at `entry`, at fuel `g`, when the functions of its table simulate below
`g` and `need k` bounds the stack that the call uses. -/
theorem fun_sim {callee : Table} {S : Shared} {entry : UInt64}
    {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (hm : m.imports = []) (h64 : m.memIs64 = false) (hk : m.funcs[k]? = some f)
    (hg : genFunction callee S entry f = .ok is) (hcode : CodeAt code entry is)
    {g : Nat} {need : Nat → Nat} (hcl : CallsOk P code g m callee S need)
    (hneed : NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    FunSim P code m S need g k (entry, f.params, f.results) :=
  (FunSim.iff_bare P code _ _ _ _ _ _).mpr fun α =>
    Machine.fun_sim (bare P code α) (by simp [hm]) h64 (by simp [hm, hk]) hg hcode
      ((CallsOk.iff_bare P code _ _ _ _ _).mp hcl α) hneed

/-- The functions of a table whose code `genFunction` places at their entries, in a module that
imports nothing, simulate at every fuel, with bounds `need` of the stack that their calls use, on a
platform that meets what their code assumes of it. -/
theorem calls_ok {callee : Table} {S : Shared}
    {m : Module} (hm : m.imports = []) (h64 : m.memIs64 = false)
    (hU : S.byteStores = true → P.normal P.uart = false)
    (htab : ∀ k c, callee k = some c → ∃ f is, m.funcs[k]? = some f ∧
      c.2 = (f.params, f.results) ∧ genFunction callee S c.1 f = .ok is ∧
      CodeAt code c.1 is) {need : Nat → Nat}
    (hneed : ∀ k f, m.funcs[k]? = some f →
      NeedOk need (frameSize (f.params.length + f.locals.length)) f.body (need k)) :
    ∀ F, CallsOk P code F m callee S need :=
  fun F => (CallsOk.iff_bare P code _ _ _ _ _).mpr fun α =>
    Machine.calls_ok (bare P code α) h64 hU
      (fun k c hk => by
        obtain ⟨f, is, hf, h2, hgen, hcode⟩ := htab k c hk
        exact .inr ⟨f, is, by simp [hm], by simp [hm, hf], h2, hgen, hcode⟩)
      (fun k f _ hf => hneed k f (by simpa [hm] using hf)) F

end LeanExe.A64
