import LeanExe.A64.Proof.Constructs

/-!
The simulation of a function.  The prologue allocates a frame of `frameSize n` bytes below SP,
saves X30 in the slot above the `n` locals, and stores the parameters from X0 up and zeros for
the other locals into their slots, so that Talos's locals on entry and the machine's state after
the prologue satisfy `Inv`.  The body's outcome under the function's construct leads to the
epilogue, which reloads X30 from its slot, which the body's code leaves unchanged, frees the
frame, and returns.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The generator's function -/

theorem frameSize_bounds {n : Nat} (h : frameSize n < 4096) :
    8 * (n + 1) ≤ frameSize n ∧ frameSize n % 16 = 0 ∧ n + 1 < 512 := by
  unfold frameSize at h ⊢
  omega

theorem gen_function {tU tD entry : UInt64} {f : Function} {is : List Instr}
    (hg : genFunction tU tD entry f = .ok is) :
    let p := f.params.length
    let n := p + f.locals.length
    let r := f.results.length
    let bodyA := after entry (2 + n)
    p ≤ 8 ∧ r ≤ 1 ∧ ∃ (hf : frameSize n < 4096) (hn : n < 4096) (body : List Instr)
      (fin : Option Nat),
      genList ⟨n, tU, tD⟩ [⟨after bodyA (listSize [r] f.body).1, r, 0⟩] 0 bodyA f.body =
        .ok (body, fin) ∧ (∀ x, fin = some x → x = r) ∧
      is = [.subImm 31 31 ⟨frameSize n, hf⟩, .str 30 31 ⟨n, hn⟩] ++
        List.ofFn (fun i : Fin n =>
          Instr.str (if i.val < p then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31
            ⟨i.val, Nat.lt_trans i.isLt hn⟩) ++ body ++
        [.ldr 30 31 ⟨n, hn⟩, .addImm 31 31 ⟨frameSize n, hf⟩, .ret 30] := by
  dsimp only
  by_cases hc : f.params.length > 8 ∨ f.results.length > 1
  · simp [genFunction, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have h1 : ¬ f.params.length > 8 := by omega
  have h2 : ¬ f.results.length > 1 := by omega
  by_cases hf : frameSize (f.params.length + f.locals.length) < 4096
  · simp [genFunction, h1, h2, hf, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hg
    split at hg
    · cases hg
    rename_i v hl
    split at hg
    · cases hg
    rename_i hend
    cases hg
    exact ⟨by omega, by omega, hf, by have := (frameSize_bounds hf).2.2; omega, v.1, v.2, hl,
      any_ne hend, by simp [List.append_assoc]⟩
  · simp [genFunction, h1, h2, hf, throw, throwThe, MonadExceptOf.throw] at hg

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

theorem load64_congr {m m' : UInt64 → UInt8} {a : UInt64}
    (h : ∀ k < 8, m (a + UInt64.ofNat k) = m' (a + UInt64.ofNat k)) :
    load64 m a = load64 m' a := by
  unfold load64
  have e0 := h 0 (by decide)
  rw [add_ofNat_zero] at e0
  rw [e0, show a + 1 = a + UInt64.ofNat 1 from rfl, show a + 2 = a + UInt64.ofNat 2 from rfl,
    show a + 3 = a + UInt64.ofNat 3 from rfl, show a + 4 = a + UInt64.ofNat 4 from rfl,
    show a + 5 = a + UInt64.ofNat 5 from rfl, show a + 6 = a + UInt64.ofNat 6 from rfl,
    show a + 7 = a + UInt64.ofNat 7 from rfl, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- An address at least `k` bytes above `sp`, for `k ≤ k'`, when it is at least `k'` above. -/
theorem not_lt_mono {a sp : UInt64} {k k' : Nat} (hk : k ≤ k') (hk' : k' < 2 ^ 64)
    (h : ¬ a - sp < UInt64.ofNat k') : ¬ a - sp < UInt64.ofNat k := by
  intro hc
  apply h
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hc ⊢
  omega

/-! ## The prologue -/

/-- The prologue's run: the frame of `fs` bytes below SP, X30 in the slot above the `n` locals,
and the word of register `src i` in the slot of local `i`. -/
theorem run_prologue {n fs : Nat} (hfs : 8 * (n + 1) ≤ fs) (hfs16 : fs % 16 = 0)
    (hf : fs < 4096) (hn : n < 4096) (hn512 : n + 1 < 512) {src : Nat → Fin 32}
    {stores : List Instr} (hlen : stores.length = n)
    (hst : ∀ i (hi : i < n), ∃ hs, stores[i]'(by omega) = .str (src i) 31 ⟨i, hs⟩)
    {entry : UInt64} {ms : State}
    (hcode : CodeAt code entry ([.subImm 31 31 ⟨fs, hf⟩, .str 30 31 ⟨n, hn⟩] ++ stores))
    (hpc : ms.pc = entry) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < fs, P.normal (ms.sp - UInt64.ofNat fs + UInt64.ofNat j) = true) :
    ∃ s, Reach P code ms s ∧ s.pc = after entry (2 + n) ∧ s.sp = ms.sp - UInt64.ofNat fs ∧
      (∀ q, s.x q = ms.x q) ∧ s.out = ms.out ∧ load64 s.mem (slotAddr s.sp n) = ms.x 30 ∧
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
  have hmap1 : ∀ i ≤ n, ∀ j < 8, P.normal (s1.sp + UInt64.ofNat (8 * i + j)) = true :=
    fun i hi j hj => hmap (8 * i + j) (by omega)
  let s2 : State :=
    { s1 with mem := store64 s1.mem (slotAddr s1.sp n) (s1.x 30), pc := s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 ⟨n, hn⟩) s1 = some s2 :=
    exec_str_sp P hn hal' (hmap1 n (Nat.le_refl _))
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
      ∀ i < n + 1, ¬ a - slotAddr s1.sp i < 8 :=
    fun a ha i hi => slot_inside hi hn512 (not_lt_mono hfs (by omega) ha)
  refine ⟨_, r2.trans hr, by show after (after entry 2) n = _; rw [after_after], rfl,
    fun _ => rfl, rfl, ?_, hload, ?_⟩
  · show load64 M (slotAddr s1.sp n) = ms.x 30
    rw [load64_congr (m' := s2.mem) fun k hk => hout _ fun i hi =>
      slot_apart (by omega) (by omega) (by omega) k hk]
    exact load64_store64_same _ _ _
  · intro a ha
    show M a = ms.mem a
    rw [hout a fun i hi => hoth a ha i (by omega)]
    show store64 s1.mem (slotAddr s1.sp n) (s1.x 30) a = ms.mem a
    rw [store64_other _ _ _ _ (hoth a ha n (by omega))]

/-! ## The epilogue -/

/-- The bytes of the slot above `n` locals lie outside the locals' frame. -/
theorem slot_above {sp : UInt64} {n k : Nat} (hk : k < 8) :
    ¬ slotAddr sp n + UInt64.ofNat k - sp < UInt64.ofNat (8 * n) := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, toNat_slot sp n,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have := sp.toNat_lt
  omega

/-- The epilogue's run from the state `s` that the body reaches at its end: X30 reloaded from the
slot above the `n` locals, the frame of `fs` bytes freed, and a return to the reloaded address. -/
theorem run_epilogue {n fs : Nat} (hf : fs < 4096) (hn : n < 4096) {a : UInt64} {s : State}
    (hcode : CodeAt code a [.ldr 30 31 ⟨n, hn⟩, .addImm 31 31 ⟨fs, hf⟩, .ret 30])
    (hpc : s.pc = a) (hal : s.sp % 16 = 0)
    (hmap : ∀ j < 8, P.normal (s.sp + UInt64.ofNat (8 * n + j)) = true) :
    ∃ s', Reach P code s s' ∧ s'.pc = load64 s.mem (slotAddr s.sp n) ∧
      s'.sp = s.sp + UInt64.ofNat fs ∧ s'.out = s.out ∧ s'.mem = s.mem ∧ s'.x 0 = s.x 0 := by
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
  · show (s.setX 30 w).x 0 = s.x 0
    exact State.x_setX_ne (by decide)

/-! ## The function -/

/-- The machine returned from the function that it entered at `ms`: at the address that X30 held,
with SP and the UART's output as they were, the memory outside the frame of `fs` bytes below SP
unchanged, and the result, the top of `vs` when the function has one, in X0. -/
structure Returned (fs nres : Nat) (vs : List Value) (ms ms' : State) : Prop where
  pc : ms'.pc = ms.x 30
  sp : ms'.sp = ms.sp
  out : ms'.out = ms.out
  mem : ∀ a, ¬ a - (ms.sp - UInt64.ofNat fs) < UInt64.ofNat fs → ms'.mem a = ms.mem a
  len : nres ≤ vs.length
  res : ∀ v ∈ vs.take nres, ValRel v (ms'.x 0)

/-- What the machine does from `ms` at the entry of a function with a frame of `fs` bytes and
`nres` results when Talos's run of the function's body gives `r`: a return reaches the return
address, and a trap reaches the stub of its code. -/
def FunOutcome (tU tD : UInt64) (fs nres : Nat) {α : Type} (r : Continuation α) (ms : State) :
    Prop :=
  match r with
  | .Fallthrough _ sl' => ∃ ms', Reach P code ms ms' ∧ Returned fs nres sl'.values ms ms'
  | .Break 0 _ sl' => ∃ ms', Reach P code ms ms' ∧ Returned fs nres sl'.values ms ms'
  | .Return _ vs => ∃ ms', Reach P code ms ms' ∧ Returned fs nres vs ms ms'
  | .Trap _ msg => ∃ ms', Reach P code ms ms' ∧ ms'.out = ms.out ∧
      ((msg = "unreachable" ∧ ms'.pc = tU) ∨ (msg = "integer divide by zero" ∧ ms'.pc = tD))
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

theorem function_sim {tU tD entry : UInt64} {f : Function} {is : List Instr}
    (hg : genFunction tU tD entry f = .ok is) (hcode : CodeAt code entry is)
    (hloc : ∀ t ∈ f.locals, ValRel t.zero 0) (F : Nat) {α : Type} (m : Module) (st : Store α)
    (args : List Value) (hargs : args.length = f.params.length) (ms : State)
    (hpc : ms.pc = entry) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < frameSize (f.params.length + f.locals.length),
      P.normal (ms.sp - UInt64.ofNat (frameSize (f.params.length + f.locals.length)) +
        UInt64.ofNat j) = true)
    (hregs : ∀ i (hi : i < args.length),
      ValRel args[i] (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩)) :
    FunOutcome P code tU tD (frameSize (f.params.length + f.locals.length)) f.results.length
      (Wasm.exec F m st (f.toLocals args) f.body) ms := by
  obtain ⟨hp8, hr1, hf, hn, body, fin, hl, hfin, his⟩ := gen_function hg
  obtain ⟨hfs, hfs16, hn512⟩ := frameSize_bounds hf
  generalize hpd : f.params.length = p at *
  generalize hnd : p + f.locals.length = n at *
  generalize hfsd : frameSize n = fs at *
  generalize hrd : f.results.length = r at *
  rw [his] at hcode
  have hca := (CodeAt.append (code := code)).mp hcode
  have hcb := (CodeAt.append (code := code)).mp hca.1
  have hpre : CodeAt code entry ([.subImm 31 31 ⟨fs, hf⟩, .str 30 31 ⟨n, hn⟩] ++
      List.ofFn (fun i : Fin n =>
        Instr.str (if i.val < p then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31
          ⟨i.val, Nat.lt_trans i.isLt hn⟩)) := hcb.1
  have hlen2 : ([Instr.subImm 31 31 ⟨fs, hf⟩, .str 30 31 ⟨n, hn⟩] ++
      List.ofFn (fun i : Fin n =>
        Instr.str (if i.val < p then ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩ else 31) 31
          ⟨i.val, Nat.lt_trans i.isLt hn⟩)).length = 2 + n := by
    simp; omega
  have cbody : CodeAt code (after entry (2 + n)) body := by
    have := hcb.2
    rwa [hlen2] at this
  have cepi : CodeAt code (after (after entry (2 + n)) body.length)
      [.ldr 30 31 ⟨n, hn⟩, .addImm 31 31 ⟨fs, hf⟩, .ret 30] := by
    have := hca.2
    rwa [List.length_append, hlen2, ← after_after] at this
  obtain ⟨s, hrs, hps, hsps, hxs, hos, h30, hslots, hmems⟩ :=
    run_prologue P code
      (src := fun i => if i < p then ⟨i % 32, Nat.mod_lt _ (by decide)⟩ else 31)
      hfs hfs16 hf hn hn512 (by simp) (fun i hi => ⟨by omega, by simp⟩) hpre hpc hal hmap
  have hals : s.sp % 16 = 0 := by rw [hsps]; exact sub_aligned hal hfs16
  have hmaps : ∀ j < fs, P.normal (s.sp + UInt64.ofNat j) = true := by
    rw [hsps]; exact hmap
  have hinv : Inv P n (f.toLocals args) s := by
    refine ⟨⟨by simp [Function.toLocals],
      fun k hk => absurd hk (by simp [Function.toLocals])⟩,
      fun i hi => ?_, by simp [Function.toLocals, hargs, ← hnd, ← hpd], hals,
      fun j hj => hmaps j (by omega), by omega⟩
    simp only [Function.toLocals, List.length_append, List.length_map] at hi
    rw [hslots i (by omega)]
    simp only [Function.toLocals]
    by_cases hip : i < p
    · rw [List.getElem_append_left (by omega), ite_eq_left hip]
      exact hregs i (by omega)
    · rw [List.getElem_append_right (by omega), ite_eq_right hip, List.getElem_map]
      exact hloc _ (List.getElem_mem _)
  let fn : Ctl := ⟨after (after entry (2 + n)) (listSize [r] f.body).1, r, 0⟩
  have hsize := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil] at hsize
  have ho := list_sim P code F ⟨n, tU, tD⟩ [fn] 0 _ f.body body fin hl cbody (Nat.le_refl _)
    ⟨List.cons_ne_nil _ _, fun t ht => by simp at ht; subst ht; exact Nat.le_refl _⟩ m st
    (f.toLocals args) s hinv rfl hps
  have ret : ∀ (vs : List Value) (ms' : State), Reach P code s ms' →
      ms'.pc = after (after entry (2 + n)) body.length → ms'.sp = s.sp → ms'.out = s.out →
      MemFrame s.sp n s ms' → Kept fn vs ms' →
      ∃ ms'', Reach P code ms ms'' ∧ Returned fs r vs ms ms'' := by
    intro vs ms' hr hp hsp hout hmf hk
    obtain ⟨ms'', hr', hp', hsp', hout', hmem', hx0⟩ := run_epilogue P code hf hn cepi hp
      (by rw [hsp]; exact hals) (fun j hj => by rw [hsp]; exact hmaps (8 * n + j) (by omega))
    refine ⟨ms'', hrs.trans (hr.trans hr'), ⟨?_, ?_, ?_, ?_, hk.len, ?_⟩⟩
    · rw [hp', hsp, load64_congr (m' := s.mem) fun k hk' => hmf _ (slot_above hk'),
        h30]
    · rw [hsp', hsp, hsps, UInt64.sub_add_cancel]
    · rw [hout', hout, hos]
    · intro a ha
      rw [← hsps] at ha
      rw [hmem', hmf a (not_lt_mono (by omega) (by omega) ha), hmems a ha]
    · rw [hx0]
      exact kept_res hk rfl hr1
  generalize Wasm.exec F m st (f.toLocals args) f.body = res at ho ⊢
  cases res with
  | Fallthrough st' sl' =>
      obtain ⟨h', hf', ms', hr, hp, hsp, hout, hmf, hinv', hh', -⟩ := ho
      have e := hfin h' hf'
      exact ret _ ms' hr hp hsp hout hmf (StackRel.kept hinv'.stack (by simp [fn]; omega))
  | Break k st' sl' =>
      cases k with
      | zero =>
          obtain ⟨t, ht, ms', hr, hp, hsp, hout, hmf, -, -, hk, -⟩ := ho
          have e : t = fn := by simpa using ht.symm
          subst e
          exact ret _ ms' hr (by rw [hp, hsize]) hsp hout hmf hk
      | succ k => trivial
  | Return st' vs =>
      obtain ⟨t, ht, ms', hr, hp, hsp, hout, hmf, hk⟩ := ho
      have e : t = fn := by simpa using ht.symm
      subst e
      exact ret _ ms' hr (by rw [hp, hsize]) hsp hout hmf hk
  | Trap st' msg =>
      obtain ⟨ms', hr, hout, hpc'⟩ := ho
      exact ⟨ms', hrs.trans hr, by rw [hout, hos], hpc'⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-! ## Talos's run of the function -/

theorem Returned.take {fs r : Nat} {vals : List Value} {ms ms' : State}
    (h : Returned fs r vals ms ms') : Returned fs (vals.take r).length (vals.take r) ms ms' :=
  ⟨h.pc, h.sp, h.out, h.mem, Nat.le_refl _, by
    rw [List.take_of_length_le (Nat.le_refl _)]
    exact h.res⟩

/-- The return from function `k` of `m`, which imports nothing, when Talos's run of it on the
arguments `args`, in declaration order, returns `vs`. -/
theorem run_sim {tU tD entry : UInt64} {m : Module} {k : Nat} {f : Function} {is : List Instr}
    (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hg : genFunction tU tD entry f = .ok is) (hcode : CodeAt code entry is)
    (hloc : ∀ t ∈ f.locals, ValRel t.zero 0) {F : Nat} {α : Type} {st st' : Store α}
    {args vs : List Value} (hargs : args.length = f.params.length)
    (hrun : Wasm.run F m k st args.reverse = .Success vs st') (ms : State)
    (hpc : ms.pc = entry) (hal : ms.sp % 16 = 0)
    (hmap : ∀ j < frameSize (f.params.length + f.locals.length),
      P.normal (ms.sp - UInt64.ofNat (frameSize (f.params.length + f.locals.length)) +
        UInt64.ofNat j) = true)
    (hregs : ∀ i (hi : i < args.length),
      ValRel args[i] (ms.x ⟨i % 32, Nat.mod_lt _ (by decide)⟩)) :
    ∃ ms', Reach P code ms ms' ∧
      Returned (frameSize (f.params.length + f.locals.length)) vs.length vs ms ms' := by
  have ho := function_sim P code hg hcode hloc F m st args hargs ms hpc hal hmap hregs
  have hta : (args.reverse.take f.numParams).reverse = args := by
    rw [Function.numParams, ← hargs, ← List.length_reverse, List.take_length,
      List.reverse_reverse]
  have hdr : args.reverse.drop f.numParams = [] := by
    rw [Function.numParams, ← hargs, ← List.length_reverse, List.drop_length]
  simp only [Wasm.run, hm, List.getElem?_nil, List.length_nil, Nat.sub_zero, hk, hta, hdr,
    List.append_nil] at hrun
  revert ho hrun
  generalize Wasm.exec F m st (f.toLocals args) f.body = res
  cases res with
  | Fallthrough st'' sl' =>
      intro ho hrun
      obtain ⟨ms', hr, hret⟩ := ho
      cases hrun
      exact ⟨ms', hr, hret.take⟩
  | Break k st'' sl' =>
      cases k with
      | zero =>
          intro ho hrun
          obtain ⟨ms', hr, hret⟩ := ho
          cases hrun
          exact ⟨ms', hr, hret.take⟩
      | succ k => intro _ hrun; cases hrun
  | Return st'' vs' =>
      intro ho hrun
      obtain ⟨ms', hr, hret⟩ := ho
      cases hrun
      exact ⟨ms', hr, hret.take⟩
  | Trap _ _ => intro _ hrun; cases hrun
  | Invalid _ => intro _ hrun; cases hrun
  | OutOfFuel => intro _ hrun; cases hrun
  | ReturnCall _ _ _ => intro ho; exact ho.elim
  | Throwing _ _ _ _ => intro ho; exact ho.elim

end LeanExe.A64
