module

public import LeanExe.A64.Proof.Linux
public import LeanExe.A64.Startup
public import LeanExe.Linux.Replies

@[expose] public section

/-!
Facts about the binding of the Linux call layer in `LeanExe/A64/Linux.lean`.  `a64Memory_lawful`
gives the layer's laws for the process's memory, and `writeBytes_a64` and `readBytes_a64` state
the layer's byte functions there as `writeList` and `readList`, so the lemmas over those two apply
to a call's effect.  `pstepWith_of_pstep` takes a step of `pstep` at a word other than `SVC #0` to
`pstepWith`, and `ProcReachWith.of_reach'` lifts a run of the program's model into
`ProcReachWith`.  `pstepWith_svc` takes `SVC #0` to `sysCall` for a call of the table, and the
`sysCall_` lemmas evaluate `sysCall` for each described call.  `run_svcRet` follows the runtime's
routine `SVC #0; RET` from its first word to the return.
-/

namespace LeanExe.A64

open LeanExe.Linux (Call Replies)

/-! ## The memory -/

theorem a64Memory_lawful (P : Platform) : (a64Memory P).Lawful where
  read_write_same m a v _ := by simp [a64Memory, store8]
  read_write_other m a b v _ h := by simp [a64Memory, store8, h]
  mapped_bytes m a n h i hi := by
    simp only [a64Memory, Platform.mapped, List.all_eq_true, List.mem_range] at h ⊢
    intro j hj
    have : j = 0 := by omega
    subst this
    simpa using h i hi
  mapped_write _ _ _ _ _ _ := rfl

theorem writeBytes_a64 (P : Platform) : ∀ (m : UInt64 → UInt8) (a : UInt64) (bs : List UInt8),
    (a64Memory P).writeBytes m a bs = writeList m a bs
  | _, _, [] => rfl
  | m, a, b :: bs => writeBytes_a64 P (store8 m a b) (a + 1) bs

theorem readBytes_a64 (P : Platform) : ∀ (m : UInt64 → UInt8) (a : UInt64) (n : Nat),
    (a64Memory P).readBytes m a n = readList m a n
  | _, _, 0 => rfl
  | m, a, n + 1 => congrArg (m a :: ·) (readBytes_a64 P m (a + 1) n)

/-! ## Registers -/

theorem reg_zero (s : State) : reg s 0 = s.x 0 := rfl
theorem reg_one (s : State) : reg s 1 = s.x 1 := rfl
theorem reg_two (s : State) : reg s 2 = s.x 2 := rfl
theorem reg_three (s : State) : reg s 3 = s.x 3 := rfl

theorem argWords_one {s : State} {c : Call} (hc : c.words = 1) : argWords s c = [s.x 0] := by
  simp only [argWords, hc]
  rfl

theorem argWords_two {s : State} {c : Call} (hc : c.words = 2) :
    argWords s c = [s.x 0, s.x 1] := by
  simp only [argWords, hc]
  rfl

theorem argWords_three {s : State} {c : Call} (hc : c.words = 3) :
    argWords s c = [s.x 0, s.x 1, s.x 2] := by
  simp only [argWords, hc]
  rfl

theorem argWords_four {s : State} {c : Call} (hc : c.words = 4) :
    argWords s c = [s.x 0, s.x 1, s.x 2, s.x 3] := by
  simp only [argWords, hc]
  rfl

/-! ## Steps other than calls -/

/-- A step of `pstep` at a word other than `SVC #0` is a step of `pstepWith`. -/
theorem pstepWith_of_pstep {T : List Call} {R : Replies} {K : Kernel} {P : Platform}
    {code : UInt64 → Option UInt32} {p q : Proc} (h : pstep K P code p = some q)
    (hc : code p.core.pc ≠ some svcWord) : pstepWith T R P code p = some q := by
  rw [pstepWith_istep hc, ← pstep_eq_istep hc]
  exact h

theorem pstepWith_exec {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p : Proc} {w : UInt32} {i : Instr} {c : State}
    (hc : code p.core.pc = some w) (hd : decode w = some i)
    (hfp : i.isFP = false ∨ p.fpcr = fpcrValue) (he : exec P i p.core = some c)
    (ht : c.pc.toNat < 2 ^ 55) : pstepWith T R P code p = some { p with core := c } :=
  pstepWith_of_istep (istep_exec hc hd hfp he ht)

theorem pstepWith_at {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p : Proc} {i : Instr} {c : State}
    (hc : code p.core.pc = some (encode i)) (hfp : i.isFP = false ∨ p.fpcr = fpcrValue)
    (he : exec P i p.core = some c) (ht : c.pc.toNat < 2 ^ 55) :
    pstepWith T R P code p = some { p with core := c } :=
  pstepWith_exec hc (decode_encode i) hfp he ht

/-- A step of `MSR FPCR, Xt` sets the process's `FPCR`. -/
theorem pstepWith_fpcr {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p : Proc} {t : Fin 32}
    (hc : code p.core.pc = some (encode (msrOf .fpcr t))) :
    pstepWith T R P code p = some { p.goto (p.core.pc + 4) with fpcr := p.core.x t } :=
  pstepWith_of_istep (istep_fpcr hc)

theorem ProcReachWith.trans {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p q r : Proc} (h1 : ProcReachWith T R P code p q)
    (h2 : ProcReachWith T R P code q r) : ProcReachWith T R P code p r := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem ProcReachWith.single {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p q : Proc} (h : pstepWith T R P code p = some q) :
    ProcReachWith T R P code p q :=
  .next h (.refl q)

/-- A run of the program's model is a run of `pstepWith` with `FPCR` at `fpcrValue`, its trace
unchanged, when the code holds words only below 2^55 and the run ends below 2^55. -/
theorem ProcReachWith.of_reach {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    {s t : State} (h : Reach P code s t) (ht : t.pc.toNat < 2 ^ 55) (tr : List Event) :
    ProcReachWith T R P code ⟨s, fpcrValue, tr⟩ ⟨t, fpcrValue, tr⟩ :=
  (IReach.of_reach hdom h ht tr).toWith T R

/-- A run of the program's model from a process whose `FPCR` holds `fpcrValue`. -/
theorem ProcReachWith.of_reach' {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    {p : Proc} (hf : p.fpcr = fpcrValue) {t : State} (h : Reach P code p.core t)
    (ht : t.pc.toNat < 2 ^ 55) : ProcReachWith T R P code p { p with core := t } :=
  (IReach.of_reach' hdom hf h ht).toWith T R

/-! ## Calls -/

/-- `SVC #0` at a call of the table that does not end the process takes the call's rule. -/
theorem pstepWith_svc {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p : Proc} {c : Call}
    (hc : code p.core.pc = some svcWord)
    (hT : T.find? (fun c => c.arm64 == p.core.x 8) = some c) (ht : c.terminal = false) :
    pstepWith T R P code p = sysCall R P c p := by
  unfold pstepWith
  rw [if_pos hc, hT]
  simp only [ht, Bool.false_eq_true, ↓reduceIte]

/-- `SVC #0` at a call outside the table, or at a terminal call, ends the run. -/
theorem pstepWith_end {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p : Proc} (hc : code p.core.pc = some svcWord)
    (hT : T.find? (fun c => c.arm64 == p.core.x 8) = none ∨
      ∃ c, T.find? (fun c => c.arm64 == p.core.x 8) = some c ∧ c.terminal = true) :
    pstepWith T R P code p = none := by
  unfold pstepWith
  rw [if_pos hc]
  rcases hT with hT | ⟨c, hT, ht⟩
  · rw [hT]
  · rw [hT]
    simp only [ht, ↓reduceIte]

theorem sysCall_read {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 1) (p.core.x 2).toNat = true) :
    sysCall R P LeanExe.Linux.readCall p = some (p.ret (R p.trace.length).ret
      (writeList p.core.mem (p.core.x 1)
        ((List.range (p.core.x 2).toNat).map (R p.trace.length).bytes))
      (.sys ⟨LeanExe.Linux.readCall, [p.core.x 0, p.core.x 1, p.core.x 2], [],
        readList p.core.mem (p.core.x 1) (p.core.x 2).toNat, (R p.trace.length).ret,
        (List.range (p.core.x 2).toNat).map (R p.trace.length).bytes⟩)) := by
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 1) (p.core.x 2).toNat = true := hmap
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_read (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1) (p.core.x 2)
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_three (show LeanExe.Linux.readCall.words = 3 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, Bool.and_self, ↓reduceIte, writeBytes_a64, readBytes_a64,
    List.map_nil]

theorem sysCall_write {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 1) (p.core.x 2).toNat = true) :
    sysCall R P LeanExe.Linux.writeCall p = some (p.ret (R p.trace.length).ret p.core.mem
      (.sys ⟨LeanExe.Linux.writeCall, [p.core.x 0, p.core.x 1, p.core.x 2],
        [readList p.core.mem (p.core.x 1) (p.core.x 2).toNat], [], (R p.trace.length).ret,
        []⟩)) := by
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 1) (p.core.x 2).toNat = true := hmap
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_write (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1) (p.core.x 2)
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_three (show LeanExe.Linux.writeCall.words = 3 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, Bool.and_self, ↓reduceIte, readBytes_a64, List.map_cons,
    List.map_nil]

theorem sysCall_close {R : Replies} {P : Platform} {p : Proc} :
    sysCall R P LeanExe.Linux.closeCall p = some (p.ret (R p.trace.length).ret p.core.mem
      (.sys ⟨LeanExe.Linux.closeCall, [p.core.x 0], [], [], (R p.trace.length).ret, []⟩)) := by
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_close (a64Memory P) p.core.mem (p.core.x 0)
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_one (show LeanExe.Linux.closeCall.words = 1 from rfl), hi, ho,
    List.all_nil, Bool.and_self, ↓reduceIte, List.map_nil]

theorem sysCall_clockGettime {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 1) 16 = true) :
    sysCall R P LeanExe.Linux.clockGettimeCall p = some (p.ret (R p.trace.length).ret
      (writeList p.core.mem (p.core.x 1) ((List.range 16).map (R p.trace.length).bytes))
      (.sys ⟨LeanExe.Linux.clockGettimeCall, [p.core.x 0, p.core.x 1], [],
        readList p.core.mem (p.core.x 1) 16, (R p.trace.length).ret,
        (List.range 16).map (R p.trace.length).bytes⟩)) := by
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 1) 16 = true := hmap
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_clockGettime (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1)
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_two (show LeanExe.Linux.clockGettimeCall.words = 2 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, Bool.and_self, ↓reduceIte, writeBytes_a64, readBytes_a64,
    List.map_nil]

theorem sysCall_getrandom {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 0) (p.core.x 1).toNat = true) :
    sysCall R P LeanExe.Linux.getrandomCall p = some (p.ret (R p.trace.length).ret
      (writeList p.core.mem (p.core.x 0)
        ((List.range (p.core.x 1).toNat).map (R p.trace.length).bytes))
      (.sys ⟨LeanExe.Linux.getrandomCall, [p.core.x 0, p.core.x 1, p.core.x 2], [],
        readList p.core.mem (p.core.x 0) (p.core.x 1).toNat, (R p.trace.length).ret,
        (List.range (p.core.x 1).toNat).map (R p.trace.length).bytes⟩)) := by
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 0) (p.core.x 1).toNat = true := hmap
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_getrandom (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1) (p.core.x 2)
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_three (show LeanExe.Linux.getrandomCall.words = 3 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, Bool.and_self, ↓reduceIte, writeBytes_a64, readBytes_a64,
    List.map_nil]

theorem sysCall_openat {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 1) ((a64Memory P).pathLength p.core.mem (p.core.x 1)) = true) :
    sysCall R P LeanExe.Linux.openatCall p = some (p.ret (R p.trace.length).ret p.core.mem
      (.sys ⟨LeanExe.Linux.openatCall, [p.core.x 0, p.core.x 1, p.core.x 2, p.core.x 3],
        [readList p.core.mem (p.core.x 1) ((a64Memory P).pathLength p.core.mem (p.core.x 1))],
        [], (R p.trace.length).ret, []⟩)) := by
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_openat (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1) (p.core.x 2) (p.core.x 3)
  generalize (a64Memory P).pathLength p.core.mem (p.core.x 1) = n at hmap hi ⊢
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 1) n = true := hmap
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_four (show LeanExe.Linux.openatCall.words = 4 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, Bool.and_self, ↓reduceIte, readBytes_a64, List.map_cons,
    List.map_nil]

theorem sysCall_openat2 {R : Replies} {P : Platform} {p : Proc}
    (hmap : P.mapped (p.core.x 1) ((a64Memory P).pathLength p.core.mem (p.core.x 1)) = true)
    (hmap2 : P.mapped (p.core.x 2) (p.core.x 3).toNat = true) :
    sysCall R P LeanExe.Linux.openat2Call p = some (p.ret (R p.trace.length).ret p.core.mem
      (.sys ⟨LeanExe.Linux.openat2Call, [p.core.x 0, p.core.x 1, p.core.x 2, p.core.x 3],
        [readList p.core.mem (p.core.x 1) ((a64Memory P).pathLength p.core.mem (p.core.x 1)),
          readList p.core.mem (p.core.x 2) (p.core.x 3).toNat],
        [], (R p.trace.length).ret, []⟩)) := by
  have hm2 : (a64Memory P).mapped p.core.mem (p.core.x 2) (p.core.x 3).toNat = true := hmap2
  obtain ⟨hi, ho⟩ := LeanExe.Linux.regions_openat2 (a64Memory P) p.core.mem (p.core.x 0)
    (p.core.x 1) (p.core.x 2) (p.core.x 3)
  generalize (a64Memory P).pathLength p.core.mem (p.core.x 1) = n at hmap hi ⊢
  have hm : (a64Memory P).mapped p.core.mem (p.core.x 1) n = true := hmap
  unfold sysCall LeanExe.Linux.step
  simp only [argWords_four (show LeanExe.Linux.openat2Call.words = 4 from rfl), hi, ho,
    List.all_nil, List.all_cons, hm, hm2, Bool.and_self, ↓reduceIte, readBytes_a64,
    List.map_cons, List.map_nil]

/-- A call keeps the program counter's successor, X30, `FPCR`, SP, and the UART's state. -/
theorem sysCall_some {R : Replies} {P : Platform} {c : Call} {p q : Proc}
    (h : sysCall R P c p = some q) :
    q.core.pc = p.core.pc + 4 ∧ q.core.x 30 = p.core.x 30 ∧ q.fpcr = p.fpcr ∧
      q.core.sp = p.core.sp ∧ q.core.io = p.core.io ∧
      (∀ r : Fin 32, r ≠ 0 → q.core.x r = p.core.x r) ∧
      ∃ e, q.trace = p.trace ++ [.sys e] := by
  unfold sysCall at h
  split at h
  · rename_i m e _
    cases h
    exact ⟨rfl, Proc.ret_x _ _ _ _ (by decide), rfl, Proc.ret_sp _ _ _ _, Proc.ret_io _ _ _ _,
      fun r hr => Proc.ret_x _ _ _ _ hr, e, rfl⟩
  · cases h

/-- The run of the runtime's routine `SVC #0; RET` at `a` from its first word to the return, for
a call `c` of the table whose number X8 holds: the call's effect, and a return to the address in
X30, which the call keeps. -/
theorem run_svcRet {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {a : UInt64} (hcode : OpsAt code a [.svc, .ins (.ret 30)])
    {p q : Proc} {c : Call} (hpc : p.core.pc = a)
    (hT : T.find? (fun c => c.arm64 == p.core.x 8) = some c) (ht : c.terminal = false)
    (hsys : sysCall R P c p = some q) (hret : (p.core.x 30).toNat < 2 ^ 55) :
    ProcReachWith T R P code p (q.goto (p.core.x 30)) := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, Op.word] at c0 c1
  obtain ⟨hq, h30, -⟩ := sysCall_some hsys
  have s0 : pstepWith T R P code p = some q := by
    rw [pstepWith_svc (by rw [hpc]; exact c0) hT ht, hsys]
  have e1 : exec P (.ret 30) q.core = some { q.core with pc := q.core.x 30 } := rfl
  have s1 := pstepWith_at (T := T) (R := R) (code := code) (p := q) (i := .ret 30)
    (by rw [hq, hpc, show a + 4 = after a 1 by simp [after]]; exact c1) (.inl rfl) e1
    (by rw [h30]; exact hret)
  rw [h30] at s1
  exact .next s0 (.single s1)

end LeanExe.A64
