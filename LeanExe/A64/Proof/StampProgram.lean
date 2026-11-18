import LeanExe.A64.Proof.StampStages

/-!
The run of a program of `genStampProgram` from `main`: the frame and the allocation of the block,
then the stages of `LeanExe/A64/Proof/StampStages.lean` and the call of the function, composed in
`stampProgram_run`.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies readCall writeCall readData writeData)

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-! ## The program -/

theorem bField_at {A t : UInt64} {n m : Nat} {g : Fin 67108864} (h : bField (after A m) t = .ok g)
    (e : n = m) : bField (after A n) t = .ok g := e ▸ h

theorem bField_at2 {A : UInt64} {n m n' m' : Nat} {g : Fin 67108864}
    (h : bField (after A m) (after A m') = .ok g) (e : n = m) (e' : n' = m') :
    bField (after A n) (after A n') = .ok g := e ▸ e' ▸ h

theorem cbField_at {A t : UInt64} {n m : Nat} {g : Fin 524288} (h : cbField (after A m) t = .ok g)
    (e : n = m) : cbField (after A n) t = .ok g := e ▸ h

theorem cbField_at2 {A : UInt64} {n m n' m' : Nat} {g : Fin 524288}
    (h : cbField (after A m) (after A m') = .ok g) (e : n = m) (e' : n' = m') :
    cbField (after A n) (after A n') = .ok g := e ▸ e' ▸ h

theorem CodeAt.atEq {A : UInt64} {n m : Nat} {l : List Instr} (h : CodeAt code (after A m) l)
    (e : n = m) : CodeAt code (after A n) l := e ▸ h

/-- The first eight instructions of `genStampMain`: the frame of `fr` bytes with X30 in its first
slot and the stack's limit in X18 `room` bytes below it. -/
theorem run_stampFront {A room : UInt64} {fr : Fin 4096} {ms : State}
    (hc : CodeAt code A ([.subImm 31 31 fr, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
      [.subReg 18 18 16]))
    (hpc : ms.pc = A) (hal : (ms.sp - UInt64.ofNat fr.val) % 16 = 0)
    (hmain : ∀ j < 8, P.normal (ms.sp - UInt64.ofNat fr.val + UInt64.ofNat j) = true) :
    ∃ t, Reach P code ms t ∧ t.pc = after A 8 ∧ t.sp = ms.sp - UInt64.ofNat fr.val ∧
      t.x 18 = ms.sp - UInt64.ofNat fr.val - room ∧
      (∀ q : Fin 32, q ≠ 16 → q ≠ 18 → t.x q = ms.x q) ∧ t.io = ms.io ∧
      t.mem = store64 ms.mem (slotAddr (ms.sp - UInt64.ofNat fr.val) 0) (ms.x 30) := by
  have s2 := CodeAt.split code hc (n := 7) (by simp [movImm])
  have s1 := CodeAt.split code s2.1 (n := 3) rfl
  have c0 := (CodeAt.cons.mp s1.1).1
  have c1 := (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).1
  have c2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp s1.1).2).2).1
  rw [after_after] at c2
  let t1 : State := { ms with sp := ms.sp - UInt64.ofNat fr.val, pc := ms.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subImm 31 31 fr) ms = some t1 := rfl
  let t2 : State :=
    { t1 with mem := store64 t1.mem (slotAddr t1.sp 0) (t1.x 30), pc := t1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.str 30 31 0) t1 = some t2 :=
    exec_str_sp P (i := 0) (by decide) hal fun j hj => by
      simpa using hmain j (by omega)
  let t2a : State := { t2.setX 18 (t2.sp + UInt64.ofNat 0) with pc := t2.pc + 4 }
  have e2a : LeanExe.A64.exec P (.addImm 18 31 0) t2 = some t2a := rfl
  have p2 : t2.pc = after A 2 := by
    show ms.pc + 4 + 4 = A + 4 * UInt64.ofNat 2
    rw [hpc, UInt64.add_assoc]
    congr 1
  have p2a : t2a.pc = after A 3 := by
    show t2.pc + 4 = _
    rw [p2, ← after_succ]
  have h18a : t2a.x 18 = ms.sp - UInt64.ofNat fr.val := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    exact add_ofNat_zero _
  have r2 : Reach P code ms t2a :=
    reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by show code (ms.pc + 4) = _; rw [hpc]; simpa [after] using c1) e2
        (reach_exec P code (by rw [p2]; exact c2) e2a (.refl _)))
  have hk2a : ∀ q : Fin 32, q ≠ 18 → t2a.x q = ms.x q := fun q hq => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
    rfl
  obtain ⟨t3a, r3a, p3a, hx16, hk3a, sp3a, mem3a, out3a⟩ :=
    run_movImm P code (d := 16) (v := room) (by decide) s1.2 p2a
  have csub : code (after A 7) = some (encode (.subReg 18 18 16)) := (CodeAt.cons.mp s2.2).1
  let t3b : State := { t3a.setX 18 (t3a.x 18 - t3a.x 16) with pc := t3a.pc + 4 }
  have e3b : LeanExe.A64.exec P (.subReg 18 18 16) t3a = some t3b := rfl
  refine ⟨t3b, r2.trans (r3a.trans (reach_exec P code (by rw [p3a, after_after]; exact csub)
    e3b (.refl _))), by show t3a.pc + 4 = _; rw [p3a, ← after_succ, after_after], ?_, ?_,
    fun q h16 h18 => ?_, ?_, ?_⟩
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).sp = _
    rw [State.setX_sp, sp3a]
    rfl
  · rw [State.x_withPc, State.x_setX_same (by decide), hx16, hk3a 18 (by decide), h18a]
  · rw [State.x_withPc, State.x_setX_ne (Ne.symm h18), hk3a q h16, hk2a q h18]
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).io = _
    rw [State.setX_io, out3a]
    rfl
  · show (t3a.setX 18 (t3a.x 18 - t3a.x 16)).mem = _
    rw [State.setX_mem, mem3a]
    rfl

/-- What Talos's run `res` of the stamp program's function on the bytes `D` gives the program:
the root and the length of a buffer of `Out D`, or a trap whose status `Tr` allows. -/
def StampFunOut (Out : List UInt8 → List UInt8) (Tr : List UInt8 → UInt64 → Prop)
    (D : List UInt8) (res : Result Unit) : Prop :=
  match res with
  | .Success vs st => ∃ root len : UInt64, vs = [.i64 len, .i64 root] ∧
      len.toNat = (Out D).length ∧ root.toNat + (Out D).length ≤ st.mem.pages * 65536 ∧
      ∀ i (h : i < (Out D).length), st.mem.bytes (root.toNat + i) = (Out D)[i]
  | .Trap _ msg => (msg = "unreachable" ∧ Tr D 1) ∨
      (msg = "out of bounds memory access" ∧ Tr D 2) ∨ (msg = "integer divide by zero" ∧ Tr D 3)
  | _ => False

/-- The stub that a trap of the function reaches, with the status that `Tr` allows for it. -/
theorem trapAt_status {tU tB tD pc : UInt64} {Out : List UInt8 → List UInt8}
    {Tr : List UInt8 → UInt64 → Prop} {D : List UInt8} {st : Store Unit} {msg : String}
    (h : TrapAt tU tB tD msg pc) (ht : StampFunOut Out Tr D (.Trap st msg)) :
    (pc = tU ∧ Tr D 1) ∨ (pc = tB ∧ Tr D 2) ∨ (pc = tD ∧ Tr D 3) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    rcases ht with ⟨e, ht⟩ | ⟨e, ht⟩ | ⟨e, ht⟩ <;>
    first
      | exact absurd e (by decide)
      | exact .inl ⟨h, ht⟩
      | exact .inr (.inl ⟨h, ht⟩)
      | exact .inr (.inr ⟨h, ht⟩)

/-- From a run of the function to the stub at `a` of a status `c` that `Tr` allows on the bytes
that the function received: the exit word, with the events of `StampEvents`. -/
theorem stamp_stub {a base sp0 inMax B : UInt64} {c : Nat} {g : Fin 67108864}
    {pin pout : List UInt8} {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop}
    {ec er eo ecl : LeanExe.Linux.Event} {rs : List LeanExe.Linux.Event}
    (hca : CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]))
    (hga : bField (after a 4) base = .ok g) (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hbase : base.toNat < 2 ^ 55) {q : Proc} (hf : q.fpcr = fpcrValue) {v : State}
    (rv : Reach P code q.core v) (pv : v.pc = a)
    (hin : StampInput sp0 inMax pin pout B ec er eo rs ecl)
    (hlen : (readData eo.ret rs).length ≤ inMax.toNat)
    (htr : sysEvents q.trace = [ec, er, eo] ++ rs ++ [ecl])
    (ht : Tr (ec.output ++ er.output ++ readData eo.ret rs) (UInt64.ofNat c)) :
    ∃ q', ProcReachWith LeanExe.Linux.table R P code q q' ∧ q'.core.io = v.io ∧
      q'.core.pc = base ∧
      StampEvents sp0 inMax pin pout Out Tr (some (q'.core.x 0)) (sysEvents q'.trace) := by
  obtain ⟨v2, rv2, pv2, xv2, iov2⟩ := run_stub P code hca hga pv
  refine ⟨{ q with core := v2 }, ProcReachWith.of_reach' hdom hf (rv.trans rv2)
    (by rw [pv2]; exact hbase), iov2, pv2, ?_⟩
  show StampEvents sp0 inMax pin pout Out Tr (some (v2.x 0)) (sysEvents q.trace)
  rw [xv2, htr]
  exact StampEvents.function hin hlen ht

/-- The run of a program of `genStampProgram`, whose function `k` of `m` takes and returns the
two words of a buffer and whose function 0 is the allocator, from `main` at `after base 1` with
`FPCR` at `fpcrValue` and no event in the trace, on a platform whose UART lies outside Normal
memory, for every replies `R` and `inMax` below 2^32, when the allocator's run at fuel `F0` on
`inMax + 33` gives the root `root` and the store `st1`, whose memory holds the block of
`inMax + 33` bytes from `root` (`hfit`), and when Talos's runs of the function do what `hfun` and
`hov` state: for every store with the memory's cap written only within the block, with bytes `D`
of at most `inMax + 32` at its start, some fuel at which the run returns a buffer of `Out D` or
traps with a status that `Tr` allows, and an overflow of the stack only when `Tr` allows
status 4.  The process returns 0 or reaches the exit word, with the
events of `StampEvents`. -/
theorem stampProgram_run {R : Replies} {m : Module} {k : Nat} {fk : Function}
    {inMax svc base room area : UInt64} {cap : Nat} {pin pout : List UInt8} {is : List Instr}
    {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop}
    (hg : genStampProgram m k inMax svc base room cap pin pout = .ok is)
    (hcode : CodeAt code (after base 1) is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : base.toNat < 2 ^ 55)
    (hm : m.imports = []) (hk : m.funcs[k]? = some fk) (hpk : fk.params = [.i64, .i64])
    (hrk : fk.results = [.i64, .i64]) {typeIdx : Nat}
    (h0 : m.funcs[0]? = some (LeanExe.Runtime.allocFunction typeIdx))
    (h0room : stackBound m 0 ≤ room.toNat) (F0 : Nat)
    (p : Proc) (hpc : p.core.pc = after base 1) (hf : p.fpcr = fpcrValue) (htr : p.trace = [])
    (h30 : (p.core.x 30).toNat < 2 ^ 55)
    (hal : p.core.sp % 16 = 0) (htop : p.core.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + stampFrame pin pout,
      P.normal (p.core.sp - UInt64.ofNat (stampFrame pin pout) - room + UInt64.ofNat j) = true)
    (h17 : p.core.x 17 = area)
    (harea : ∀ j < areaSize cap, p.core.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + stampFrame pin pout ≤ p.core.sp.toNat)
    (hU : P.normal P.uart = false)
    (hin : inMax.toNat < 2 ^ 32) (root : UInt64) (st1 : Store Unit)
    (hrun : Wasm.run F0 m 0 (initStore m cap) [.i64 (inMax + 33)] = .Success [.i64 root] st1)
    (hfit : root.toNat + (inMax.toNat + 33) ≤ st1.mem.pages * 65536)
    (hfun : ∀ (st : Store Unit) (D : List UInt8), D.length ≤ inMax.toNat + 32 →
      st.memoryCaps = [cap] →
      LeanExe.Pipeline.WritesWithin st1 st root.toNat (inMax.toNat + 33) →
      (∀ i < D.length, st.mem.bytes (root.toNat + i) = D.getD i 0) →
      ∃ F1, StampFunOut Out Tr D (Wasm.run F1 m k st [.i64 (UInt64.ofNat D.length), .i64 root]))
    (hov : room.toNat < stackBound m k → ∀ D, Tr D 4) :
    ∃ p', ProcReachWith LeanExe.Linux.table R P code p p' ∧ p'.core.io = p.core.io ∧
      ((p'.core.pc = p.core.x 30 ∧ p'.core.x 0 = 0 ∧
          StampEvents p.core.sp inMax pin pout Out Tr none (sysEvents p'.trace)) ∨
        (p'.core.pc = base ∧
          StampEvents p.core.sp inMax pin pout Out Tr (some (p'.core.x 0))
            (sysEvents p'.trace))) := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, a0, p0, r0, g1, g2, g3, g4, hok', hgt, hgl,
    hfs, hfirst, hT, hen, hen0, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_stampProgram hg
  subst his
  have hml := genStampMain_length hmg
  obtain ⟨wi, wo, fr, outSlot, sIn, sOut, ga, c20, c26, cI, cR, g64, cC, gk, cO, cW, gb, cD, f72,
    f73, f67, fe, f68, fr', f69, f70, fd, fz, fw, f71, x64, x67, x68, x69, x70, x71, x72, x73,
    x74, hwi, hwo, hpin, hpout, hfrv, hos, hsIn, hsOut, hga, hc20, hf72, hc26, hf73, hcI, hf67,
    hcR, hfe, hf68, hfr', hg64, hcC, hf69, hgk, hcO, hf70, hfd, hcW, hfz, hfw, hgb, hcD, hf71,
    hx64, hx67, hx68, hx69, hx70, hx71, hx72, hx73, hx74, hmeq⟩ := gen_stampMain hmg
  subst hwi hwo
  -- the sizes
  obtain ⟨-, hpl64, -⟩ := pathOk_facts hpin
  obtain ⟨-, hpo64, -⟩ := pathOk_facts hpout
  have hwl := pathWords_length pin
  have hwo' := pathWords_length pout
  have hF' : stampFrame pin pout =
      16 * ((32 + 8 * ((pathWords pin).length + (pathWords pout).length) + 15) / 16) := rfl
  have hF16 : (stampFrame pin pout) % 16 = 0 := by omega
  have hFl : 32 + 8 * ((pathWords pin).length + (pathWords pout).length) ≤ (stampFrame pin pout) := by omega
  have hF4096 : (stampFrame pin pout) < 4096 := by rw [← hfrv]; exact fr.isLt
  generalize hA : after base 1 = A at *
  generalize hSPf : p.core.sp - UInt64.ofNat (stampFrame pin pout) = SPf
  have hSPfn : SPf.toNat = p.core.sp.toNat - (stampFrame pin pout) := by
    rw [← hSPf, toNat_sub_le (by rw [UInt64.toNat_ofNat']; omega), UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  have hSPfal : SPf % 16 = 0 := by
    rw [← hSPf]
    exact sub_aligned hal hF16

  have hsp0 : SPf.toNat < 2 ^ 63 := by omega
  have hFn : (UInt64.ofNat (stampFrame pin pout)).toNat = (stampFrame pin pout) := by rw [UInt64.toNat_ofNat']; omega
  have hlim : (SPf - room).toNat = p.core.sp.toNat - (stampFrame pin pout) - room.toNat := by
    rw [toNat_sub_le (by omega), hSPfn]
  have hframe : ∀ j < (stampFrame pin pout), P.normal (SPf + UInt64.ofNat j) = true := by
    intro j hj
    have e : SPf + UInt64.ofNat j = p.core.sp - UInt64.ofNat (stampFrame pin pout) - room +
        UInt64.ofNat (room.toNat + j) := by
      apply UInt64.toNat_inj.mp
      rw [← hSPf]
      simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat']
      have := room.toNat_lt
      simp only [Nat.reducePow] at *
      omega
    rw [e]
    exact hstack _ (by omega)
  -- the code's parts
  have hc := (CodeAt.append (code := code)).mp hcode
  have hc2 := CodeAt.split code hc.1 hml
  have cfns : CodeAt code first fns := by rw [hfirst]; exact hc2.2
  have cst : CodeAt code T (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
      (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
      (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) := by
    have := hc.2
    rw [List.length_append, hml, ← after_after, ← hfirst, ← (genFunctions_length
      (sigOf_tableOf (callTargets m k) first fs) hfg).2, ← hT] at this
    exact this
  have cs4 := CodeAt.split code cst (n := 15) (by simp [movImm])
  have cs3 := CodeAt.split code cs4.1 (n := 10) (by simp [movImm])
  have cs1 := CodeAt.split code cs3.1 (n := 5) (by simp [movImm])
  have hAi : ∀ i < stampMainSize pin pout, (after A i).toNat < 2 ^ 55 := fun i hi =>
    hdom _ _ (hc2.1 i (by rw [hml]; exact hi))
  have hmsz : stampMainSize pin pout = 162 + 5 * ((pathWords pin).length +
    (pathWords pout).length) := rfl
  have cmain := hc2.1
  rw [hmeq, ← after_zero A] at cmain
  have q1 := CodeAt.peel code cmain (k := 17) (by simp [movImm])
  have q2 := CodeAt.peel code q1.2 (k := 5) rfl
  have q3 := CodeAt.peel code q2.2 (k := 7) rfl
  have q4 := CodeAt.peel code q3.2 (k := 5 * (pathWords pin).length) (storeWords_length hsIn)
  have q5 := CodeAt.peel code q4.2 (k := 20) (by simp [movImm])
  have q6 := CodeAt.peel code q5.2 (k := 10) rfl
  have q7 := CodeAt.peel code q6.2 (k := 20) (by simp [movImm])
  have q8 := CodeAt.peel code q7.2 (k := 5 * (pathWords pout).length) (storeWords_length hsOut)
  have q9 := CodeAt.peel code q8.2 (k := 17) (by simp [movImm])
  have q10 := CodeAt.peel code q9.2 (k := 10) rfl
  have q11 := CodeAt.peel code q10.2 (k := 11) (by simp [movImm])
  have st8 := CodeAt.split code q11.2 (n := 40) (by simp [movImm])
  have st7 := CodeAt.split code st8.1 (n := 35) (by simp [movImm])
  have st6 := CodeAt.split code st7.1 (n := 30) (by simp [movImm])
  have st5 := CodeAt.split code st6.1 (n := 25) (by simp [movImm])
  have st4 := CodeAt.split code st5.1 (n := 20) (by simp [movImm])
  have st3 := CodeAt.split code st4.1 (n := 15) (by simp [movImm])
  have st2 := CodeAt.split code st3.1 (n := 10) (by simp [movImm])
  have st1' := CodeAt.split code st2.1 (n := 5) (by simp [movImm])
  simp only [Nat.zero_add] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  simp only [after_after] at st8 st7 st6 st5 st4 st3 st2 st1'

  have h64 : m.memIs64 = false := memIs64_of_areaOk hok'
  have hfm := mapM_funcOf hfs
  have hsig := sigOf_tableOf (callTargets m k) first fs
  -- the functions
  have hfuns : ∀ {j : Nat} {c : UInt64 × List ValueType × List ValueType},
      entryIn (sigIn (callTargets m k) fs) first fs j = some c → ∃ f fis, (j, f) ∈ fs ∧
        c.2 = (f.params, f.results) ∧
        genFunction (tableOf (callTargets m k) first fs)
          ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ c.1 f = .ok fis ∧
        CodeAt code c.1 fis :=
    fun h => gen_functions code hsig hfg cfns _ (entryIn_mem h)
  have htab : ∀ j c, tableOf (callTargets m k) first fs j = some c → ∃ f is,
      m.funcs[j]? = some f ∧ c.2 = (f.params, f.results) ∧
      genFunction (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ c.1 f = .ok is ∧
        CodeAt code c.1 is := by
    intro j c hj
    unfold tableOf at hj
    split at hj
    · obtain ⟨f', fis, hmem, hpr, hgen, hcd⟩ := hfuns hj
      exact ⟨f', fis, hfm _ hmem, hpr, hgen, hcd⟩
    · cases hj
  have hcl := calls_ok P code hm h64 (fun _ => hU) htab (need := stackNeed m m.funcs.length)
    (fun _ _ hj => stackNeed_ok hj _)
  obtain ⟨f0', fis0, hm0, hp0, hg0, cf0⟩ := hfuns hen0
  have hf0 := hfm _ hm0
  simp only at hf0
  rw [h0] at hf0
  cases hf0
  obtain ⟨fk', fisk, hmk, hpk', hgk', cfk⟩ := hfuns hen
  have hfk := hfm _ hmk
  simp only at hfk
  rw [hk] at hfk
  cases hfk
  -- the frame and X18
  have qf := q1.1
  rw [after_zero] at qf
  have fs1 := CodeAt.split code qf (n := 12) (by simp [movImm])
  have fs2 := CodeAt.split code fs1.1 (n := 8) (by simp [movImm])
  obtain ⟨t1, r1, p1, sp1, x181, k1, io1, mem1⟩ := run_stampFront (P := P) fs2.1 hpc
    (by rw [hfrv, hSPf]; exact hSPfal)
    (fun j hj => by rw [hfrv, hSPf]; exact hframe j (by omega))
  rw [hfrv, hSPf] at sp1 x181 mem1
  -- X0 at inMax + 33 and the call of the allocator
  obtain ⟨t2, r2, p2, x02, k2, sp2, mem2, io2⟩ :=
    run_movImm P code (d := 0) (v := inMax + 33) (by decide) fs2.2 p1
  have cbl : code (after A 12) = some (encode (.bl ga)) := (CodeAt.cons.mp fs1.2).1
  let t3 : State := { t2.setX 30 (t2.pc + 4) with pc := t2.pc + sext 26 ga.val * 4 }
  have r3 : Reach P code p.core t3 := r1.trans (r2.trans
    (reach_exec P code (by rw [p2, after_after]; exact cbl) rfl (.refl _)))
  have p3 : t3.pc = a0 := by
    show t2.pc + sext 26 ga.val * 4 = _
    rw [p2, after_after]
    exact bField_target hga
  have h303 : t3.x 30 = after A 13 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p2, after_after, ← after_succ]
  have hk3 : ∀ q : Fin 32, q ≠ 30 → q ≠ 0 → q ≠ 16 → q ≠ 18 → t3.x q = p.core.x q :=
    fun q h30' h0' h16 h18 => by
      rw [State.x_withPc, State.x_setX_ne (Ne.symm h30'), k2 q h0', k1 q h16 h18]
  have hsp3 : t3.sp = SPf := by
    show (t2.setX 30 (t2.pc + 4)).sp = _
    rw [State.setX_sp, sp2, sp1]
  have h183 : t3.x 18 = SPf - room := by
    rw [State.x_withPc, State.x_setX_ne (by decide), k2 18 (by decide), x181]
  have h173 : t3.x 17 = area := by
    rw [hk3 17 (by decide) (by decide) (by decide) (by decide), h17]
  have hmem3 : t3.mem = store64 p.core.mem (slotAddr SPf 0) (p.core.x 30) := by
    show (t2.setX 30 (t2.pc + 4)).mem = _
    rw [State.setX_mem, mem2, mem1]
  have hio3 : t3.io = p.core.io := by
    show (t2.setX 30 (t2.pc + 4)).io = _
    rw [State.setX_io, io2, io1]
  have hd3 : (t3.sp - t3.x 18).toNat = room.toNat := by
    rw [hsp3, h183, toNat_sub_le (by omega), hlim]
    omega
  have hstk3 : StackOk P t3 := by
    refine ⟨by rw [hsp3]; exact hSPfal, ?_, ?_⟩
    · rw [hsp3, h183, hlim]
      unfold areaSize at habove
      omega
    · intro j hj
      rw [hd3] at hj
      rw [h183, ← hSPf]
      exact hstack j (by omega)
  have hsr3 : StoreRel P cap gts (initStore m cap) t3 := by
    refine storeRel_init P hok' hgt hgl (fun j hj => ?_)
      (fun j hj => by rw [h173]; exact hamap j hj) (by rw [h173, h183, hlim]; omega)
    have := area.toNat_lt
    unfold areaSize at habove hj
    have hjl : (area + UInt64.ofNat j).toNat < (SPf - room).toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', hlim]
      simp only [Nat.reducePow] at *
      omega
    rw [hmem3, h173, store64_other _ _ _ _ (below_slot (by rw [hlim, hSPfn]; omega) hsp0
      (by decide) hjl)]
    exact harea j hj
  have hvt0 : Typed (LeanExe.Runtime.allocFunction typeIdx).params.reverse
      ([Value.i64 (inMax + 33)].take (LeanExe.Runtime.allocFunction typeIdx).params.length) :=
    by simp [LeanExe.Runtime.allocFunction, Typed, HasType]
  rcases run_outcome P code hm h64 h0 hg0 cf0 (hcl F0) (stackNeed_ok h0 _) (initStore m cap)
      [.i64 (inMax + 33)] t3 (by simp [LeanExe.Runtime.allocFunction]) hvt0 p3 hstk3 hsr3
      (by
        refine ⟨by simp [LeanExe.Runtime.allocFunction], fun i hi => ?_⟩
        simp only [LeanExe.Runtime.allocFunction, List.length_cons, List.length_nil,
          List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
          List.nil_append] at hi ⊢
        obtain rfl : i = 0 := by omega
        show t3.x (regOf 0) = inMax + 33
        rw [show regOf 0 = 0 by decide, State.x_withPc, State.x_setX_ne (by decide)]
        exact x02) with ⟨hov0, -⟩ | hro0
  · rw [hd3] at hov0
    exact absurd h0room (by unfold stackBound; omega)
  rw [hrun] at hro0
  obtain ⟨t4, r4, p4, sp4, h184, io4, mf4, -, -, hres4, -, hsr4⟩ := hro0
  have hx04 : t4.x 0 = root := by
    have := hres4.2 0 (by simp [LeanExe.Runtime.allocFunction])
    simpa [show regOf 0 = 0 by decide, LeanExe.Runtime.allocFunction, ValRel] using this
  have p4' : t4.pc = after A 13 := by rw [p4, h303]
  have hsp4 : t4.sp = SPf := by rw [sp4, hsp3]
  have h184' : t4.x 18 = SPf - room := by rw [h184, h183]
  have hfr4 : ∀ a : UInt64, SPf.toNat ≤ a.toNat → t4.mem a = t3.mem a :=
    fun a ha => mf4 a (by rw [hsp3]; omega)
  -- the root into the frame's slot 1 and X19 at the block
  have cstr : code (after A 13) = some (encode (.str 0 31 1)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp fs1.2).2).1
    simp only [after_after] at this
    exact this
  let t5 : State := { t4 with mem := store64 t4.mem (slotAddr t4.sp 1) (t4.x 0), pc := t4.pc + 4 }
  have e5 : LeanExe.A64.exec P (.str 0 31 1) t4 = some t5 :=
    exec_str_sp P (i := 1) (by decide) (by rw [hsp4]; exact hSPfal) fun j hj => by
      rw [hsp4]
      exact hframe _ (by omega)

  have c14 : code (after A 14) = some (encode (.addReg 19 17 0)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp fs1.2).2).2).1
    simp only [after_after] at this
    exact this
  have c15 : code (after A 15) = some (encode (.addImm 19 19 2048)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp fs1.2).2).2).2).1
    simp only [after_after] at this
    exact this
  have c16 : code (after A 16) = some (encode (.addImm 19 19 2048)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp
      (CodeAt.cons.mp fs1.2).2).2).2).2).1
    simp only [after_after] at this
    exact this
  have p5 : t5.pc = after A 14 := by show t4.pc + 4 = _; rw [p4', ← after_succ]
  obtain ⟨t6, r6, p6, x196, k6, sp6, mem6, io6⟩ := run_setX P code (d := 19) (by decide)
    (by rw [p5]; exact c14) (rfl : LeanExe.A64.exec P (.addReg 19 17 0) t5 = _)
  have p6' : t6.pc = after A 15 := by rw [p6, p5, ← after_succ]
  obtain ⟨t7, r7, p7, x197, k7, sp7, mem7, io7⟩ := run_setX P code (d := 19) (by decide)
    (by rw [p6']; exact c15)
    (exec_addImm_x P (s := t6) (d := 19) (n := 19) (imm := 2048) (by decide) (by decide))
  have p7' : t7.pc = after A 16 := by rw [p7, p6', ← after_succ]
  obtain ⟨t8, r8, p8, x198, k8, sp8, mem8, io8⟩ := run_setX P code (d := 19) (by decide)
    (by rw [p7']; exact c16)
    (exec_addImm_x P (s := t7) (d := 19) (n := 19) (imm := 2048) (by decide) (by decide))
  have p8' : t8.pc = after A 17 := by rw [p8, p7', ← after_succ]
  have hk8 : ∀ q : Fin 32, q ≠ 19 → t8.x q = t4.x q := fun q h => by
    rw [k8 q h, k7 q h, k6 q h]
    rfl
  generalize harea' : t4.x 17 = area'
  have h178 : t8.x 17 = area' := by rw [hk8 17 (by decide), harea']
  have h188 : t8.x 18 = SPf - room := by rw [hk8 18 (by decide), h184']
  have h198 : t8.x 19 = area' + UInt64.ofNat (4096 + root.toNat) := by
    rw [x198, x197, x196]
    show t5.x 17 + t5.x 0 + UInt64.ofNat (2048 : Fin 4096).val +
      UInt64.ofNat (2048 : Fin 4096).val = _
    show t4.x 17 + t4.x 0 + UInt64.ofNat 2048 + UInt64.ofNat 2048 = _
    rw [harea', hx04, show area' + root = area' + UInt64.ofNat root.toNat by
      rw [UInt64.ofNat_toNat], add_ofNat_add, add_ofNat_add]
    exact congrArg (fun x => area' + UInt64.ofNat x) (by omega)
  have hsp8 : t8.sp = SPf := by rw [sp8, sp7, sp6]; exact hsp4
  have hmem8 : t8.mem = store64 t4.mem (slotAddr SPf 1) root := by
    rw [mem8, mem7, mem6]
    show store64 t4.mem (slotAddr t4.sp 1) (t4.x 0) = _
    rw [hsp4, hx04]
  have hio8 : t8.io = p.core.io := by
    rw [io8, io7, io6]
    show t4.io = _
    rw [io4, hio3]
  have hpg1 := hsr4.pages
  have hbel := hsr4.below
  rw [h184'] at hbel
  have hsr8 : StoreRel P cap gts st1 t8 := hsr4.congr (by rw [h178, harea']) (by rw [h188, h184'])
    fun b hb => by
      rw [hmem8, store64_other _ _ _ _ (below_slot (lim := SPf - room) (by rw [hlim, hSPfn]; omega)
        hsp0 (by decide) (by rw [h184'] at hb; exact hb))]
  have hst8 : ReadStore P cap gts st1 root.toNat (inMax.toNat + 33) [] t8 :=
    ⟨st1, hsr8, ⟨rfl, rfl, fun _ _ => rfl⟩, fun i hi => absurd hi (by simp)⟩
  have hs08 : load64 t8.mem (slotAddr SPf 0) = p.core.x 30 := by
    rw [hmem8, load64_store64_other _ _ _ _
      (slot_apart (sp := SPf) (i := 1) (j := 0) (by decide) (by decide) (by decide)),
      load64_congr (m' := t3.mem) fun k hk => hfr4 _ (by
        have := slot_le (sp := SPf) (i := 0) hsp0 (by decide) hk
        omega), hmem3, load64_store64_same]
  have hs18 : load64 t8.mem (slotAddr SPf 1) = root := by rw [hmem8, load64_store64_same]
  have r8' : Reach P code p.core t8 := r3.trans (r4.trans (reach_exec P code
    (by rw [p4']; exact cstr) e5 (r6.trans (r7.trans r8))))
  have q0 : ProcReachWith LeanExe.Linux.table R P code p { p with core := t8 } :=
    ProcReachWith.of_reach' hdom hf r8' (by rw [p8']; exact hAi 17 (by rw [hmsz]; omega))

  -- the calls before the read loop
  have q4' := CodeAt.split code q5.1 (l1 := movImm 0 atFdcwd ++ [.addImm 1 31 32] ++
    movImm 2 stampInFlags ++ [.movz 3 0 0, .movz 8 56 0, .bl cI, .lsrImm 16 0 31, .cbnz 16 f67,
      .str 0 31 2]) (l2 := [.addImm 1 19 32] ++ movImm 2 (inMax + 1)) (n := 15)
    (by simp [movImm])
  simp only [after_after] at q4'
  have hrandom : CodeAt code (after (after A 17) 5) [.addImm 0 19 16, .movz 1 16 0, .movz 2 0 0,
      .movz 8 278 0, .bl c26, .subsImm 31 0 16, .bcond 1 f73] := by
    rw [after_after]
    exact q3.1.atEq (by omega)
  have hclockr : CodeAt code (after A 17) ([.movz 0 0 0, .addImm 1 19 0, .movz 8 113 0, .bl c20,
      .cbnz 0 f72] ++ [.addImm 0 19 16, .movz 1 16 0, .movz 2 0 0, .movz 8 278 0, .bl c26,
      .subsImm 31 0 16, .bcond 1 f73]) :=
    (CodeAt.append (code := code)).mpr ⟨q2.1.atEq (by omega), hrandom⟩
  have hB8 : area'.toNat + 4096 + root.toNat + inMax.toNat + 33 ≤
      p.core.sp.toNat - stampFrame pin pout := by
    rw [← harea'] at ⊢
    have := hpg1.2
    have : st1.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg1.2
    unfold areaSize at hbel
    rw [hlim] at hbel
    omega
  rcases stamp_open (R := R) (P := P) (code := code) (a := after A 17) (svc := svc)
    (e72 := after A (147 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (e73 := after A (152 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (e67 := after A (122 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (base := base) (Out := Out) (Tr := Tr) hclockr
    (by rw [after_after]; exact hc20) (by rw [after_after]; exact hf72)
    (by rw [after_after]; exact hc26) (by rw [after_after]; exact hf73)
    hsIn (by rw [after_after]; exact q4.1.atEq (by omega))
    (by rw [after_after]; exact q4'.1.atEq (by omega))
    (by rw [after_after]; exact q4'.2.atEq (by omega))
    (by simp only [after_after]; exact bField_at hcI (by omega))
    (by simp only [after_after]; exact cbField_at hf67 (by omega))
    (st6.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx72 (by omega))
    (st7.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx73 (by omega))
    (st1'.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx67 (by omega))
    hsvc hdom hbase (by rw [after_after]; exact hAi _ (by rw [hmsz]; omega)) hpin
    (by omega) hin (q := { p with core := t8 }) p8' hf htr (by rw [hsp8, hSPf])
    (by rw [hSPf]; exact hSPfal) (by rw [hSPf]; exact hsp0) (by rw [hSPf]; exact hframe)
    h178 (by rw [h188, hSPf, hlim, hSPfn]; omega) h198 hst8 hfit hB8 with
    ⟨q', rq', ioq', pcq', hevq'⟩ | ⟨q', ec, er, eo, rq', fq', ioq', hop, hl16, hr16, htrq', pcq',
      spq', x17q', x18q', x1q', x2q', s2q', s01q', hstq'⟩
  · exact ⟨q', q0.trans rq', by rw [ioq']; exact hio8, .inr ⟨pcq', hevq'⟩⟩
  -- the read loop, the input's close, and the call of the function
  rw [hSPf] at s01q' s2q'
  have he : e.toNat < 2 ^ 55 := by
    have := cfk 0 (by rw [genFunction_length hgk']; unfold functionSize; omega)
    rw [after_zero] at this
    exact hdom _ _ this
  have q7s := CodeAt.split code q7.1 (l1 := movImm 16 (inMax + 1) ++ [.subReg 16 16 2,
    .str 16 31 3, .ldr 0 31 2, .movz 8 57 0, .bl cC, .cbnz 0 f69, .ldr 0 31 1, .ldr 1 31 3,
    .addImm 1 1 32, .bl gk]) (l2 := [mov 2 1, .addReg 1 17 0, .addImm 1 1 2048,
    .addImm 1 1 2048, .str 1 31 1, .str 2 31 3]) (n := 14) (by simp [movImm])
  simp only [after_after] at q7s
  rcases stamp_read (R := R) (P := P) (code := code)
    (H := after A (49 + 5 * (pathWords pin).length))
    (e64 := after A (117 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (e68 := after A (127 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (e69 := after A (132 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
    (base := base) (rootU := root) (Out := Out) (Tr := Tr) (q6.1.atEq (by omega))
    (by rw [after_after]; exact bField_at hcR (by omega))
    (by simp only [after_after]; exact cbField_at2 hfe (by omega) (by omega))
    (by rw [after_after]; exact cbField_at hf68 (by omega))
    (by rw [after_after]; exact cbField_at hfr' (by omega))
    (by rw [after_after]; exact bField_at hg64 (by omega))
    (by rw [after_after]; exact q7s.1.atEq (by omega))
    (by rw [after_after]; exact bField_at hcC (by omega))
    (by rw [after_after]; exact cbField_at hf69 (by omega))
    (by rw [after_after]; exact bField_at hgk (by omega))
    (st1'.1.atEq (by omega)) (by rw [after_after]; exact bField_at hx64 (by omega))
    (st2.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx68 (by omega))
    (st3.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx69 (by omega))
    hsvc hdom hbase he (by rw [after_after]; exact hAi _ (by rw [hmsz]; omega)) hin
    (q := q') (pcq'.trans ((after_after _ _ _).trans (after_congr A (by omega)))) fq' hop hl16
    hr16 htrq' (by rw [spq']; exact hsp8) hSPfal hsp0 (fun j hj => hframe j (by omega))
    (by rw [x18q', h188, hlim, hSPfn]; omega) (by rw [x1q', x17q'])
    (x1q'.trans (block_addr _ _ 32).symm) x2q' (by rw [s01q' 1 (by decide)]; exact hs18) s2q'
    hstq' hfit with
    ⟨q2, rq2, ioq2, pcq2, hevq2⟩ |
    ⟨q2, rs, ecl, rq2, fq2, ioq2, hin2, hlen2, htr2, pcq2, x30q2, x0q2, x1q2, spq2, x17q2,
      x18q2, s0q2, hstq2⟩
  · exact ⟨q2, q0.trans (rq'.trans rq2), by rw [ioq2, ioq']; exact hio8, .inr ⟨pcq2, hevq2⟩⟩
  have qq2 : ProcReachWith LeanExe.Linux.table R P code p q2 := q0.trans (rq'.trans rq2)
  have hio2 : q2.core.io = p.core.io := by rw [ioq2, ioq']; exact hio8
  have hx18q2 : q2.core.x 18 = SPf - room := by rw [x18q2, x18q']; exact h188
  have hd2 : (q2.core.sp - q2.core.x 18).toNat = room.toNat := by
    rw [spq2, hx18q2, toNat_sub_le (by omega), hlim]
    omega
  have hstk2 : StackOk P q2.core := hstk3.congr (by rw [spq2, hsp3]) (by rw [hx18q2, h183])
  obtain ⟨st2, hsr2, hW2, hD2⟩ := hstq2
  obtain ⟨F1, hF1⟩ := hfun st2 (ec.output ++ er.output ++ readData eo.ret rs) (by
    rw [List.length_append, List.length_append, hl16, hr16]
    omega) hsr2.caps hW2 hD2
  rcases run_outcome P code hm h64 hk hgk' cfk (hcl F1) (stackNeed_ok hk _) st2
      [.i64 (UInt64.ofNat (ec.output ++ er.output ++ readData eo.ret rs).length), .i64 root]
      q2.core (by rw [hpk]; simp) (by rw [hpk]; simp [Typed, HasType]) pcq2 hstk2 hsr2 (by
        rw [hpk]
        refine ⟨by simp, fun i hi => ?_⟩
        simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
          List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hi ⊢
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · show q2.core.x (regOf 0) = root
          rw [show regOf 0 = 0 by decide]
          exact x0q2
        · show q2.core.x (regOf 1) =
            UInt64.ofNat (ec.output ++ er.output ++ readData eo.ret rs).length
          rw [show regOf 1 = 1 by decide]
          exact x1q2) with ⟨hov', hovr⟩ | hro
  · -- an overflow of the stack: the stub of status 4
    rw [hd2] at hov'
    obtain ⟨v, rv, pv, iov⟩ := hovr
    obtain ⟨q3, rq3, ioq3, pq3, evq3⟩ := stamp_stub (R := R) (Out := Out) cs4.2 hb4 hdom hbase
      fq2 rv pv hin2 hlen2 htr2 (hov (by unfold stackBound; omega) _)
    exact ⟨q3, qq2.trans rq3, by rw [ioq3, iov, hio2], .inr ⟨pq3, evq3⟩⟩
  revert hro hF1
  cases Wasm.run F1 m k st2
      [.i64 (UInt64.ofNat (ec.output ++ er.output ++ readData eo.ret rs).length), .i64 root] with
  | Trap st' tmsg =>
      intro hF1 hro
      obtain ⟨v, rv, iov, hat⟩ := hro
      rcases trapAt_status hat hF1 with ⟨pv, ht⟩ | ⟨pv, ht⟩ | ⟨pv, ht⟩
      · obtain ⟨q3, rq3, ioq3, pq3, evq3⟩ := stamp_stub (R := R) (Out := Out) cs1.1 hb1 hdom
          hbase fq2 rv pv hin2 hlen2 htr2 ht
        exact ⟨q3, qq2.trans rq3, by rw [ioq3, iov, hio2], .inr ⟨pq3, evq3⟩⟩
      · obtain ⟨q3, rq3, ioq3, pq3, evq3⟩ := stamp_stub (R := R) (Out := Out) cs1.2 hb2 hdom
          hbase fq2 rv pv hin2 hlen2 htr2 ht
        exact ⟨q3, qq2.trans rq3, by rw [ioq3, iov, hio2], .inr ⟨pq3, evq3⟩⟩
      · obtain ⟨q3, rq3, ioq3, pq3, evq3⟩ := stamp_stub (R := R) (Out := Out) cs3.2 hb3 hdom
          hbase fq2 rv pv hin2 hlen2 htr2 ht
        exact ⟨q3, qq2.trans rq3, by rw [ioq3, iov, hio2], .inr ⟨pq3, evq3⟩⟩
  | Invalid _ => intro h _; exact (h : False).elim
  | OutOfFuel => intro h _; exact (h : False).elim
  | Thrown _ _ _ => intro h _; exact (h : False).elim
  | Success vs' st3 =>
      intro hF1 hro
      obtain ⟨root', len, hvs, hlenbs, hfitbs, hbytes⟩ := hF1
      subst hvs
      obtain ⟨v5, rv5, pv5, spv5, h18v5, iov5, mfv5, -, -, hresv5, -, hsrv5⟩ := hro
      rw [hrk] at hresv5
      have hx0v5 : v5.x 0 = root' := by
        have := hresv5.2 0 (by simp)
        simpa [show regOf 0 = 0 by decide, ValRel] using this
      have hx1v5 : v5.x 1 =
          UInt64.ofNat (Out (ec.output ++ er.output ++ readData eo.ret rs)).length := by
        have := hresv5.2 1 (by simp)
        have e : v5.x 1 = len := by simpa [show regOf 1 = 1 by decide, ValRel] using this
        rw [e, ← hlenbs, UInt64.ofNat_toNat]
      have pv5' : v5.pc = after A (73 + 5 * (pathWords pin).length) :=
        pv5.trans (x30q2.trans ((after_after _ _ _).trans (after_congr A (by omega))))
      have hs0v5 : load64 v5.mem (slotAddr SPf 0) = p.core.x 30 := by
        rw [load64_congr (a := slotAddr SPf 0) (m' := q2.core.mem) fun k hk => mfv5 _ (by
          have := slot_le (sp := SPf) (i := 0) hsp0 (by decide) hk
          rw [spq2]
          omega), s0q2, s01q' 0 (by decide)]
        exact hs08
      -- the output
      have q9s := CodeAt.split code q9.1 (l1 := movImm 0 atFdcwd ++ [.addImm 1 31 outSlot] ++
        movImm 2 stampOutFlags ++ [.movz 3 stampOutMode 0, .movz 8 56 0, .bl cO,
          .lsrImm 16 0 31, .cbnz 16 f70, .str 0 31 2]) (l2 := [.ldr 1 31 1, .ldr 2 31 3])
        (n := 15) (by simp [movImm])
      simp only [after_after] at q9s
      obtain ⟨p', rp', iop', hp'⟩ := stamp_output (R := R) (P := P) (code := code)
        (a := after A (73 + 5 * (pathWords pin).length))
        (e70 := after A (137 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
        (e74 := after A (157 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
        (e71 := after A (142 + 5 * (pathWords pin).length + 5 * (pathWords pout).length))
        (Out := Out) (Tr := Tr)
        (q7s.2.atEq (by omega)) hsOut (by rw [after_after]; exact q8.1.atEq (by omega))
        (by rw [after_after]; exact q9s.1.atEq (by omega))
        (by simp only [after_after]; exact bField_at hcO (by omega))
        (by simp only [after_after]; exact cbField_at hf70 (by omega))
        (by rw [after_after]; exact q9s.2.atEq (by omega))
        (by rw [after_after]; exact q10.1.atEq (by omega))
        (by simp only [after_after]; exact cbField_at2 hfd (by omega) (by omega))
        (by rw [after_after]; exact bField_at hcW (by omega))
        (by rw [after_after]; exact cbField_at hfz (by omega))
        (by rw [after_after]; exact cbField_at hfw (by omega))
        (by simp only [after_after]; exact bField_at2 hgb (by omega) (by omega))
        (by rw [after_after]; exact q11.1.atEq (by omega))
        (by rw [after_after]; exact bField_at hcD (by omega))
        (by rw [after_after]; exact cbField_at hf71 (by omega))
        (st4.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx70 (by omega))
        (st8.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx74 (by omega))
        (st5.2.atEq (by omega)) (by rw [after_after]; exact bField_at hx71 (by omega))
        hsvc hdom hbase hpout hFl hfrv hos h30 (q := { q2 with core := v5 }) pv5' fq2 hin2
        hlen2 htr2 hSPf.symm (by show v5.sp = _; rw [spv5, spq2]) hSPfal hsp0 hframe
        (by show (v5.x 18).toNat ≤ _; rw [h18v5, hx18q2, hlim, hSPfn]; omega) hs0v5 rfl hx0v5
        hx1v5 hsrv5 hfitbs hbytes
      refine ⟨p', qq2.trans ((ProcReachWith.of_reach' hdom fq2 rv5 (by
        rw [pv5']; exact hAi _ (by rw [hmsz]; omega))).trans rp'), ?_, hp'⟩
      rw [iop']
      show v5.io = _
      rw [iov5, hio2]

end LeanExe.A64
