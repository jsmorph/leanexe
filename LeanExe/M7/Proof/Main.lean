import LeanExe.M7.Proof.Step
import LeanExe.Requests.Windows

/-!
`main`'s windows and its loop.  `main` lowers SP by the outgoing area of the step's `n + 1`
parameters and results, stores the words of the step's initial state into slots 0 to `n - 1` and
0 into slot `n`, and then repeats a window from the loop's head: the call of the step, the
decoding of the request in slot `n`, and either a word load of the device register, whose value
slot `n` then holds, or a word store of the request's low word, after which slot `n` holds 0.
`devBus dev` records a request's access as the model's device access at `dev + 4 r` for register
`r`, so the one access of a window is `reqEvent (devBus dev)` of `LeanExe/Requests/Windows.lean`.

`main_window` states one window from `step_call`, and `main_loop` the first `n` windows, by
induction on `n`: the machine returns to the loop's head with the state of `reqRun` in the
outgoing area and the window traces of `reqTrace (devBus dev)` appended to its trace.  The reads
of the windows take the values of `σ` from the number of reads before the loop on.  `main_start`
runs `main`'s start to the loop's head, and `main_run` combines the two from `main`'s entry.  The
relation of the simulation holds no Talos store, so each call passes the same store to
`step_call`.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph LeanExe.Pipeline LeanExe.Requests

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## The device accesses of requests -/

theorem devAddr_inj {dev : UInt32} {r r' : UInt64} (hr : r.toNat < 65536)
    (hr' : r'.toNat < 65536)
    (h : dev + UInt32.ofNat (4 * r.toNat) = dev + UInt32.ofNat (4 * r'.toNat)) : r = r' := by
  have h1 := congrArg UInt32.toNat h
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat'] at h1
  have := toNat_lt32 dev
  apply UInt64.toNat_inj.mp
  simp only [Nat.reducePow] at h1
  omega

/-- The register accesses of requests as the model's device accesses: register `r` is the word
at `dev + 4 r`. -/
def devBus (dev : UInt32) : Bus Access where
  read r v := .read (dev + UInt32.ofNat (4 * r.toNat)) v
  write r v := .write (dev + UInt32.ofNat (4 * r.toNat)) v
  readOf r e := match e with
    | .read a v => if a = dev + UInt32.ofNat (4 * r.toNat) then some v else none
    | .write _ _ => none
  writeOf r e := match e with
    | .write a v => if a = dev + UInt32.ofNat (4 * r.toNat) then some v else none
    | .read _ _ => none
  readOf_read r v := by simp
  readOf_read_ne r r' v hr hr' hne := by
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false]
    exact fun h => hne (devAddr_inj hr' hr h).symm
  readOf_write _ _ _ := rfl
  writeOf_write r v := by simp
  writeOf_read _ _ _ := rfl

/-- The device window of `main`'s requests on the platform `P`: `dev` is a multiple of 4, and the
word at `dev + 4 j` is a device register for each of the 65,536 indices `j` of a request. -/
structure DevWindow (P : Platform) (dev : UInt32) : Prop where
  aligned : dev.toNat % 4 = 0
  device : ∀ j < 65536, P.device (dev + UInt32.ofNat (4 * j)) = true

theorem DevWindow.reg {dev : UInt32} (h : DevWindow P dev) (q : UInt64) :
    (dev + UInt32.ofNat (4 * (reqReg q).toNat)) % 4 = 0 ∧
      P.device (dev + UInt32.ofNat (4 * (reqReg q).toNat)) = true :=
  ⟨mod4_add (mod4_of_toNat h.aligned) (by omega), h.device _ (reqReg_lt q)⟩

/-! ## The words of the outgoing area -/

theorem WordsAt.init {s : State} {ws : List UInt64} {x : UInt64} (h : WordsAt s (ws ++ [x])) :
    ∀ i (hi : i < ws.length), ValAt s (8 * i) (.i64 ws[i]) := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem WordsAt.last {s : State} {ws : List UInt64} {x : UInt64} (h : WordsAt s (ws ++ [x])) :
    ValAt s (8 * ws.length) (.i64 x) := by
  have := h ws.length (by simp)
  simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem_cons_zero] using this

theorem WordsAt.of_parts {s : State} {ws : List UInt64} {x : UInt64}
    (h1 : ∀ i (hi : i < ws.length), ValAt s (8 * i) (.i64 ws[i]))
    (h2 : ValAt s (8 * ws.length) (.i64 x)) : WordsAt s (ws ++ [x]) := by
  intro i hi
  by_cases hl : i < ws.length
  · rw [List.getElem_append_left hl]
    exact h1 i hl
  · have e : i = ws.length := by simp at hi; omega
    subst e
    simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero] using h2

theorem StackOk.congr {lim : UInt32} {n need : Nat} {s t : State} (h : StackOk P lim n need s)
    (hsp : t.sp = s.sp) : StackOk P lim n need t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨hsp ▸ h1, hsp ▸ h2, hsp ▸ h3, hsp ▸ h4, hsp ▸ h5, hsp ▸ h6⟩

/-- The two words of slot `n` of the outgoing area, for a stack of `n + 1` slots, pass the checks
of a load and a store. -/
theorem StackOk.words {lim : UInt32} {n need : Nat} {s : State}
    (h : StackOk P lim (n + 1) need s) {i : Nat} (hi : i ≤ n) :
    WordOk P (s.sp + UInt32.ofNat (8 * i)) ∧ WordOk P (s.sp + UInt32.ofNat (8 * i + 4)) :=
  ⟨wordOk_of_ram h.ram h.aligned (by omega) (by omega),
    wordOk_of_ram h.ram h.aligned (by omega) (by omega)⟩

/-- Two stores into slot `n` leave every slot below it. -/
theorem valAt_below {s t : State} {n i : Nat} {w0 w1 : UInt32} {v : Value} (hsp : t.sp = s.sp)
    (hmem : t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat (8 * n)) w0)
      (s.sp + UInt32.ofNat (8 * n + 4)) w1)
    (hn : 8 * n + 8 ≤ 4294967296) (hi : i < n) (h : ValAt s (8 * i) v) : ValAt t (8 * i) v :=
  h.congr hsp (slotSame_store2 hmem hn (by omega) (by omega))

/-! ## `main`'s code -/

/-- The decoding of the request whose high word lies at the offset `qh` from SP: the high word
into r1, the register's index `(q >> 32) & 65535` into r2, the address `dev + 4 * index` into r3,
and the write bit, bit 63, into r4, compared with 0. -/
def mainDecode (qh : Fin 4096) (dev : UInt32) : List Instr :=
  [.ldrSp 1 qh, .lslBy 2 1 16, .lsrBy 2 2 16, .movwOf 3 (dev.toNat % 65536),
    .movtOf 3 (dev.toNat / 65536), .addLsl 0 3 3 2 2, .lsrBy 4 1 31, .cmpImm 4 0]

/-- The read of the device register at r3 into the slot at `q` and `qh`. -/
def mainRead (q qh : Fin 4096) : List Instr :=
  [.ldr 0 3 0, .strSp 0 q, .movImm 0 0, .strSp 0 qh]

/-- The write of the low word of the slot at `q` to the device register at r3, and the clearing of
the slot. -/
def mainWrite (q qh : Fin 4096) : List Instr :=
  [.ldrSp 0 q, .str 0 3 0, .movImm 0 0, .strSp 0 q, .strSp 0 qh]

/-- The stores of the words `ws` into the slots from `k`, as `genMain` emits them for the step's
initial state. -/
abbrev wordStores (ws : List UInt64) (k : Nat) : GenM (List (List Instr)) :=
  (ws.zipIdx k).mapM fun (w, i) => do pure (movPair w ++ (← stPair 0 1 (8 * i)))

/-- The code of `main` for the step at `step` from the state `s0`, placed at `a`: the start, the
window's call and decoding with the branch to the write, the read with the branch back to the
loop's head, and the write with the branch back. -/
theorem gen_main {a step dev : UInt32} {s0 : List UInt64} {main : List Instr}
    (hg : genMain a step dev s0 = .ok main) :
    ∃ (start : List Instr) (wds : List (List Instr)) (hq : 8 * s0.length < 4096)
      (hqh : 8 * s0.length + 4 < 4096) (o1 o2 o3 o4 : Int),
      8 * (s0.length + 1) < 4096 ∧ wordStores s0 0 = .ok wds ∧
      start = [Instr.subwSpSpOf (8 * (s0.length + 1))] ++ wds.flatten ++
        [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩] ∧
      main = start ++ ([.blTo o1] ++ mainDecode ⟨8 * s0.length + 4, hqh⟩ dev ++
          [.bcondTo condNE o2]) ++
        (mainRead ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩ ++ [.bTo o3]) ++
        (mainWrite ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩ ++ [.bTo o4]) ∧
      (o1 % 2 = 0 ∧ -16777216 ≤ o1 ∧ o1 < 16777216 ∧
        after a start.length + 4 + UInt32.ofInt o1 = step) ∧
      (o2 % 2 = 0 ∧ -1048576 ≤ o2 ∧ o2 < 1048576 ∧
        after (after a start.length) 9 + 4 + UInt32.ofInt o2 =
          after (after (after a start.length) 10) 5) ∧
      (o3 % 2 = 0 ∧ -16777216 ≤ o3 ∧ o3 < 16777216 ∧
        after (after (after a start.length) 10) 4 + 4 + UInt32.ofInt o3 = after a start.length) ∧
      (o4 % 2 = 0 ∧ -16777216 ≤ o4 ∧ o4 < 16777216 ∧
        after (after (after (after a start.length) 10) 5) 5 + 4 + UInt32.ofInt o4 =
          after a start.length) := by
  unfold genMain at hg
  simp only [except_bind_ok, except_pure_ok] at hg
  obtain ⟨area, harea, q, hq, qh, hqh, wds, hw, b1, hb1, b2, hb2, b3, hb3, b4, hb4, rfl⟩ := hg
  obtain ⟨pa, rfl⟩ := imm_ok harea
  obtain ⟨pq, rfl⟩ := imm_ok hq
  obtain ⟨pqh, rfl⟩ := imm_ok hqh
  obtain ⟨o1, rfl, e1⟩ := blAt_ok hb1
  obtain ⟨o2, rfl, e2⟩ := bcondAt_ok hb2
  obtain ⟨o3, rfl, e3⟩ := bAt_ok hb3
  obtain ⟨o4, rfl, e4⟩ := bAt_ok hb4
  exact ⟨_, wds, pq, pqh, o1, o2, o3, o4, pa, hw, rfl, rfl, e1, e2, e3, e4⟩

/-! ## The pieces of a window -/

theorem all_left {l1 l2 : List Instr} (h : (l1 ++ l2).all Instr.wide = true) :
    l1.all Instr.wide = true := by
  rw [List.all_append, Bool.and_eq_true] at h
  exact h.1

/-- A value read from a device register lies in a slot as an `i64`, zero-extended. -/
theorem slotRel_read (v : UInt32) : SlotRel (.i64 (UInt64.ofNat v.toNat)) v 0 := by
  have := toNat_lt32 v
  constructor
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  · apply UInt32.toNat_inj.mp
    rw [toNat_hi64, UInt64.toNat_ofNat']
    show 0 = _
    simp only [Nat.reducePow]
    omega

theorem decode_index (q : UInt64) :
    shl (shr (shl (q >>> 32).toUInt32 16) 16) 2 = UInt32.ofNat (4 * (reqReg q).toNat) := by
  apply UInt32.toNat_inj.mp
  rw [toNat_shl, toNat_shr, toNat_shl, toNat_hi64, UInt32.toNat_ofNat', reqReg_toNat]
  have := UInt64.toNat_lt q
  simp only [Nat.reducePow] at *
  omega

theorem decode_write (q : UInt64) : (shr (q >>> 32).toUInt32 31 == 0) = !reqWrite q := by
  have h := reqWrite_iff q
  have e : (shr (q >>> 32).toUInt32 31).toNat = q.toNat / 9223372036854775808 := by
    rw [toNat_shr, toNat_hi64]
    have := UInt64.toNat_lt q
    simp only [Nat.reducePow] at *
    omega
  cases hw : reqWrite q
  · have hlt : q.toNat < 9223372036854775808 := by
      apply Nat.lt_of_not_le
      intro hc
      rw [h.mpr hc] at hw
      cases hw
    have h0 : shr (q >>> 32).toUInt32 31 = 0 :=
      UInt32.toNat_inj.mp (by rw [e]; show _ = 0; omega)
    rw [h0]
    rfl
  · have hge := h.mp hw
    have h0 : shr (q >>> 32).toUInt32 31 ≠ 0 := fun h0 => by
      have := congrArg UInt32.toNat h0
      rw [e] at this
      change _ = 0 at this
      omega
    simp [h0]

theorem dev_word (dev : UInt32) :
    UInt32.ofNat (dev.toNat % 65536) &&& (0xFFFF : UInt32) |||
      UInt32.ofNat (dev.toNat / 65536) <<< (16 : UInt32) = dev := by
  have := toNat_lt32 dev
  rw [movt_word (by omega) (by omega), show dev.toNat % 65536 + dev.toNat / 65536 * 65536 =
    dev.toNat by omega, UInt32.ofNat_toNat]

/-- The decoding of the request `q`, whose high word lies at the offset `x` from SP, leaves the
address of its register in r3 and Z clear exactly when it is a write. -/
theorem run_decode {dev : UInt32} {x : Nat} {hx : x < 4096} {s : State} {q : UInt64}
    (hc : CodeAt code s.pc (mainDecode ⟨x, hx⟩ dev)) (hw : WordOk P (s.sp + UInt32.ofNat x))
    (hq : load32 s.mem (s.sp + UInt32.ofNat x) = (q >>> 32).toUInt32) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat 32 ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.trace = s.trace ∧ t.reads = s.reads ∧
      t.r 3 = dev + UInt32.ofNat (4 * (reqReg q).toNat) ∧ t.zFlag = !reqWrite q := by
  have := toNat_lt32 dev
  have hok : SlotsOk P s.sp (mainDecode ⟨x, hx⟩ dev) :=
    slotsOk_ld hw (slotsOk_reg rfl _)
  obtain ⟨r1, p1, sp1, -, tr1, rd1, -⟩ := run_slots (σ := σ) hok hc
  refine ⟨_, r1, by rw [p1]; rfl, sp1, ?_, tr1, rd1, ?_, ?_⟩
  · simp only [mainDecode, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some,
      Instr.lslBy, Instr.lsrBy, Instr.movwOf, Instr.movtOf, Instr.addLsl,
      State.mem_setR, State.mem_setNZCV, State.mem_result]
  · simp only [mainDecode, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some,
      Instr.lslBy, Instr.lsrBy, Instr.movwOf, Instr.movtOf, Instr.addLsl]
    state_simp
    rw [add_addWithCarry, imm16_field (by omega), imm16_field (by omega), dev_word, hq,
      decode_index]
  · simp only [mainDecode, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some,
      Instr.lslBy, Instr.lsrBy, Instr.movwOf, Instr.movtOf, Instr.addLsl]
    state_simp
    rw [cmp_imm0, hq, decode_write]

/-- The read of the device register at `a` in r3, whose value the slot at the offset `x` then
holds, zero-extended. -/
theorem run_read {x : Nat} {hx0 : x < 4096} {hx1 : x + 4 < 4096} {s : State} {a : UInt32}
    (hc : CodeAt code s.pc (mainRead ⟨x, hx0⟩ ⟨x + 4, hx1⟩)) (ha : s.r 3 = a) (hal : a % 4 = 0)
    (hdev : P.device a = true) (hw0 : WordOk P (s.sp + UInt32.ofNat x))
    (hw1 : WordOk P (s.sp + UInt32.ofNat (x + 4))) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat 16 ∧ t.sp = s.sp ∧
      t.trace = s.trace ++ [.read a (σ s.reads)] ∧ t.reads = s.reads + 1 ∧
      t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat x) (σ s.reads))
        (s.sp + UInt32.ofNat (x + 4)) 0 := by
  obtain ⟨c0, c1⟩ := CodeAt.cons.mp hc
  obtain ⟨u0, hu0⟩ : ∃ u0 : State, u0 =
      { s with trace := s.trace ++ [Access.read a (σ s.reads)], reads := s.reads + 1 } :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : State, u = { u0.setR 0 (σ s.reads) with pc := s.pc + 4 } := ⟨_, rfl⟩
  have e0 : exec P σ (.ldr 0 3 0) s = some u := by
    rw [hu, hu0]
    simp only [exec, loadWord, ha, show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl,
      UInt32.add_zero, hal, hdev, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some]
  have husp : u.sp = s.sp := by rw [hu, hu0]; rfl
  have hupc : u.pc = s.pc + UInt32.ofNat 4 := by rw [hu]; rfl
  rw [show Instr.size (.ldr 0 3 0) = 4 from rfl, ← hupc] at c1
  have hok : SlotsOk P u.sp [.strSp 0 ⟨x, hx0⟩, .movImm 0 0, .strSp 0 ⟨x + 4, hx1⟩] := by
    rw [husp]
    exact slotsOk_st hw0 (slotsOk_cons rfl (fun o ho => by cases ho)
      (slotsOk_st hw1 (slotsOk_nil _)))
  obtain ⟨r1, p1, sp1, -, tr1, rd1, -⟩ := run_slots (σ := σ) hok c1
  refine ⟨_, reach_exec c0 e0 r1, ?_, sp1.trans husp, ?_, ?_, ?_⟩
  · rw [p1, hupc]
    simp only [List.length_cons, List.length_nil]
    addr_eq
  · rw [tr1, hu, hu0]
    rfl
  · rw [rd1, hu, hu0]
    rfl
  · rw [hu, hu0]
    rfl

/-- The write of the low word of the slot at the offset `x` to the device register at `a` in r3,
after which the slot holds 0. -/
theorem run_write {x : Nat} {hx0 : x < 4096} {hx1 : x + 4 < 4096} {s : State} {a : UInt32}
    (hc : CodeAt code s.pc (mainWrite ⟨x, hx0⟩ ⟨x + 4, hx1⟩)) (ha : s.r 3 = a)
    (hal : a % 4 = 0) (hdev : P.device a = true) (hw0 : WordOk P (s.sp + UInt32.ofNat x))
    (hw1 : WordOk P (s.sp + UInt32.ofNat (x + 4))) :
    ∃ t, Reach P σ code s t ∧ t.pc = s.pc + UInt32.ofNat 20 ∧ t.sp = s.sp ∧
      t.trace = s.trace ++ [.write a (load32 s.mem (s.sp + UInt32.ofNat x))] ∧
      t.reads = s.reads ∧
      t.mem = store32 (store32 s.mem (s.sp + UInt32.ofNat x) 0)
        (s.sp + UInt32.ofNat (x + 4)) 0 := by
  obtain ⟨c0, c1⟩ := CodeAt.cons.mp hc
  obtain ⟨c1, c2⟩ := CodeAt.cons.mp c1
  have e0 := exec_ldrSp (P := P) (σ := σ) (s := s) (t := 0) (o := ⟨x, hx0⟩) hw0
  obtain ⟨u1, hu1⟩ : ∃ u1 : State, u1 = { s.setR 0 (load32 s.mem (s.sp + UInt32.ofNat x))
      with pc := s.pc + 4 } := ⟨_, rfl⟩
  rw [← hu1] at e0
  have hu1r3 : u1.r 3 = a := by rw [hu1, State.r_withPc, State.r_setR_ne _ _ (by decide), ha]
  obtain ⟨u2, hu2⟩ : ∃ u2 : State, u2 = { ({ u1 with trace := u1.trace ++ [.write a (u1.r 0)] } :
      State) with pc := u1.pc + 4 } := ⟨_, rfl⟩
  have e1 : exec P σ (.str 0 3 0) u1 = some u2 := by
    rw [hu2]
    simp only [exec, storeWord, hu1r3, show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl,
      UInt32.add_zero, hal, hdev, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some]
  have hu1pc : u1.pc = s.pc + UInt32.ofNat 4 := by rw [hu1]; rfl
  have hu2pc : u2.pc = u1.pc + UInt32.ofNat 4 := by rw [hu2]; rfl
  have hu2sp : u2.sp = s.sp := by rw [hu2, hu1]; rfl
  simp only [Instr.size] at c1 c2
  rw [← hu1pc] at c1 c2
  rw [← hu2pc] at c2
  have hok : SlotsOk P u2.sp [.movImm 0 0, .strSp 0 ⟨x, hx0⟩, .strSp 0 ⟨x + 4, hx1⟩] := by
    rw [hu2sp]
    exact slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_st hw0
      (slotsOk_st hw1 (slotsOk_nil _)))
  obtain ⟨r2, p2, sp2, -, tr2, rd2, -⟩ := run_slots (σ := σ) hok c2
  refine ⟨_, reach_exec c0 e0 (reach_exec c1 e1 r2), ?_, sp2.trans hu2sp, ?_, ?_, ?_⟩
  · rw [p2, hu2pc, hu1pc]
    simp only [List.length_cons, List.length_nil]
    addr_eq
  · rw [tr2, hu2, hu1]
    rfl
  · rw [rd2, hu2, hu1]
    rfl
  · rw [hu2, hu1]
    rfl

/-! ## The stores of the initial state -/

theorem slotRun_movPair (w : UInt64) (s : State) :
    (slotRun P σ (movPair w) s).r 0 = w.toUInt32 ∧
      (slotRun P σ (movPair w) s).r 1 = (w >>> 32).toUInt32 := by
  have hv := w.toNat_lt_size
  have e0 := slotRun_movConst (P := P) (σ := σ) 0 (w := w.toNat % 4294967296) (by omega) s
  have e1 := slotRun_movConst (P := P) (σ := σ) 1 (w := w.toNat / 4294967296)
    (by simp only [UInt64.size] at hv; omega) (slotRun P σ (movConst 0 (w.toNat % 4294967296)) s)
  simp only [movPair, slotRun_append]
  rw [e1.1, e1.2 0 (by decide), e0.1, toUInt32_ofNat_lo, toUInt32_ofNat_hi]
  exact ⟨rfl, rfl⟩

/-- The stores of the words `ws` into the slots from `k` leave each word in its slot and every
byte outside those slots unchanged. -/
theorem run_stores : ∀ (ws : List UInt64) (k : Nat) {L : List (List Instr)},
    wordStores ws k = .ok L → ∀ (u : State),
    (∀ i < ws.length, WordOk P (u.sp + UInt32.ofNat (8 * (k + i))) ∧
      WordOk P (u.sp + UInt32.ofNat (8 * (k + i) + 4))) →
    8 * (k + ws.length) ≤ 4294967296 →
    SlotsOk P u.sp L.flatten ∧ (slotRun P σ L.flatten u).sp = u.sp ∧
      (∀ i (hi : i < ws.length), ValAt (slotRun P σ L.flatten u) (8 * (k + i)) (.i64 ws[i])) ∧
      (∀ b, (∀ i < ws.length, Outside u.sp (8 * (k + i)) b) →
        (slotRun P σ L.flatten u).mem b = u.mem b)
  | [], k, L, h, u, _, _ => by
      simp only [wordStores, List.zipIdx_nil, List.mapM_nil, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      exact ⟨slotsOk_nil _, rfl, fun i hi => absurd hi (by simp), fun _ _ => rfl⟩
  | w :: ws, k, L, h, u, hw, hfit => by
      simp only [wordStores, List.zipIdx_cons, List.mapM_cons, except_bind_ok,
        except_pure_ok] at h
      obtain ⟨c, hc, L', hL', rfl⟩ := h
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨h0, h1, rfl⟩ := stPair_ok hy
      have hreg : (movPair w).all Instr.regForm = true := by
        simp only [movPair, List.all_append, movConst_regForm, Bool.and_self]
      obtain ⟨hm0, hs0, -⟩ := slotRun_reg (P := P) (σ := σ) hreg u
      obtain ⟨ew0, ew1⟩ := slotRun_movPair (P := P) (σ := σ) w u
      generalize hv : slotRun P σ (movPair w ++ [.strSp 0 ⟨8 * k, h0⟩,
        .strSp 1 ⟨8 * k + 4, h1⟩]) u = v
      have hvsp : v.sp = u.sp := by rw [← hv, slotRun_append]; exact hs0
      have hvmem : v.mem = store32 (store32 u.mem (u.sp + UInt32.ofNat (8 * k)) w.toUInt32)
          (u.sp + UInt32.ofNat (8 * k + 4)) (w >>> 32).toUInt32 := by
        rw [← hv, slotRun_append, slotRun_st2, hm0, hs0, ew0, ew1]
      have hw' : ∀ i < ws.length, WordOk P (v.sp + UInt32.ofNat (8 * (k + 1 + i))) ∧
          WordOk P (v.sp + UInt32.ofNat (8 * (k + 1 + i) + 4)) := fun i hi => by
        rw [hvsp, show k + 1 + i = k + (i + 1) by omega]
        exact hw (i + 1) (by simp; omega)
      have hfit' : 8 * (k + 1 + ws.length) ≤ 4294967296 := by simp at hfit; omega
      obtain ⟨ok', sp', val', out'⟩ := run_stores ws (k + 1) hL' v hw' hfit'
      have hw0 := hw 0 (by simp)
      rw [Nat.add_zero] at hw0
      rw [List.flatten_cons, slotRun_append, hv]
      refine ⟨slotsOk_append (slotsOk_append (slotsOk_reg hreg _)
          (slotsOk_st hw0.1 (slotsOk_st hw0.2 (slotsOk_nil _)))) (by rw [← hvsp]; exact ok'),
        sp'.trans hvsp, fun i hi => ?_, fun b hb => ?_⟩
      · cases i with
        | zero =>
            rw [Nat.add_zero, List.getElem_cons_zero]
            have hslot : ValAt v (8 * k) (.i64 w) :=
              valAt_store2 hvsp hvmem (by simp at hfit; omega) ⟨rfl, rfl⟩
            refine hslot.congr sp' (slotSame_of_words (slotWords_congr sp' fun j hj => ?_) sp')
            refine out' _ fun i hi => ?_
            exact outside_of_disjoint (by omega) (by omega) (by omega) hj
        | succ i =>
            rw [List.getElem_cons_succ, show k + (i + 1) = k + 1 + i by omega]
            exact val' i (by simp at hi; omega)
      · rw [out' b fun i hi => by
          rw [hvsp, show k + 1 + i = k + (i + 1) by omega]
          exact hb (i + 1) (by simp; omega), hvmem]
        have := hb 0 (by simp)
        rw [Nat.add_zero] at this
        exact store2_outside this

/-- `main`'s start from its entry: SP drops by the outgoing area of `s0.length + 1` slots, slot
`i` receives word `i` of `s0`, and the last slot 0. -/
theorem main_start {s0 : List UInt64} {wds : List (List Instr)} {hq : 8 * s0.length < 4096}
    {hqh : 8 * s0.length + 4 < 4096} (harea : 8 * (s0.length + 1) < 4096)
    (hw : wordStores s0 0 = .ok wds) {b : State}
    (hc : CodeAt code b.pc ([Instr.subwSpSpOf (8 * (s0.length + 1))] ++ wds.flatten ++
      [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩]))
    (hal : b.sp.toNat % 4 = 0) (hfit : 8 * (s0.length + 1) ≤ b.sp.toNat)
    (hram : ∀ j < 8 * (s0.length + 1),
      Ram P (b.sp - UInt32.ofNat (8 * (s0.length + 1)) + UInt32.ofNat j)) :
    ∃ t, Reach P σ code b t ∧
      t.pc = b.pc + UInt32.ofNat (4 * (wds.flatten.length + 4)) ∧
      t.sp = b.sp - UInt32.ofNat (8 * (s0.length + 1)) ∧ t.trace = b.trace ∧
      t.reads = b.reads ∧ WordsAt t (s0 ++ [0]) ∧
      ∀ a : UInt32, a.toNat < t.sp.toNat → t.mem a = b.mem a := by
  have hc' : CodeAt code b.pc (Instr.subwSpSpOf (8 * (s0.length + 1)) :: (wds.flatten ++
      [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩])) := by
    simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using hc
  obtain ⟨c0, c1⟩ := CodeAt.cons.mp hc'
  -- `SUBW SP`
  have h4 : (b.sp - UInt32.ofNat (8 * (s0.length + 1))).toNat % 4 = 0 := by
    rw [toNat_sub_frame hfit]
    omega
  obtain ⟨u1, hu1⟩ : ∃ u1 : State, u1 = { b with
      sp := (addWithCarry b.sp (~~~(imm12 (field 2 (8 * (s0.length + 1) / 2048))
        (field 8 (8 * (s0.length + 1) / 256)) (field 256 (8 * (s0.length + 1))))) true).1 &&&
          0xFFFFFFFC, pc := b.pc + 4 } := ⟨_, rfl⟩
  have e0 : exec P σ (Instr.subwSpSpOf (8 * (s0.length + 1))) b = some u1 := by rw [hu1]; rfl
  have hu1sp : u1.sp = b.sp - UInt32.ofNat (8 * (s0.length + 1)) := by
    rw [hu1]
    show (addWithCarry b.sp _ true).1 &&& 0xFFFFFFFC = _
    rw [sub_addWithCarry, imm12_field harea, and_align h4]
  have hu1pc : u1.pc = b.pc + UInt32.ofNat 4 := by rw [hu1]; rfl
  rw [show Instr.size (Instr.subwSpSpOf (8 * (s0.length + 1))) = 4 from rfl, ← hu1pc] at c1
  -- the stores
  have hal1 : u1.sp % 4 = 0 := by rw [hu1sp]; exact mod4_of_toNat h4
  have hram1 : ∀ j < 8 * (s0.length + 1), Ram P (u1.sp + UInt32.ofNat j) := by
    rw [hu1sp]; exact hram
  have hwk : ∀ i < s0.length, WordOk P (u1.sp + UInt32.ofNat (8 * (0 + i))) ∧
      WordOk P (u1.sp + UInt32.ofNat (8 * (0 + i) + 4)) := fun i hi =>
    ⟨wordOk_of_ram hram1 hal1 (by omega) (by omega),
      wordOk_of_ram hram1 hal1 (by omega) (by omega)⟩
  obtain ⟨ok1, sp1, val1, out1⟩ := run_stores (P := P) (σ := σ) s0 0 hw u1 hwk
    (by have := toNat_lt32 b.sp; omega)
  have hok : SlotsOk P u1.sp (wds.flatten ++
      [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩]) :=
    slotsOk_append ok1 (slotsOk_cons rfl (fun o ho => by cases ho)
      (slotsOk_st (wordOk_of_ram hram1 hal1 (by omega) (by omega))
        (slotsOk_st (wordOk_of_ram hram1 hal1 (by omega) (by omega)) (slotsOk_nil _))))
  obtain ⟨r1, p1, sp1', -, tr1, rd1, -⟩ := run_slots (σ := σ) hok c1
  generalize hv : slotRun P σ wds.flatten u1 = v at sp1 val1 out1
  have hfin : slotRun P σ (wds.flatten ++
      [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩]) u1 =
      slotRun P σ [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩, .strSp 0 ⟨8 * s0.length + 4, hqh⟩]
        v := by rw [slotRun_append, hv]
  have hmem : (slotRun P σ [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩,
      .strSp 0 ⟨8 * s0.length + 4, hqh⟩] v).mem =
      store32 (store32 v.mem (v.sp + UInt32.ofNat (8 * s0.length)) 0)
        (v.sp + UInt32.ofNat (8 * s0.length + 4)) 0 := rfl
  have hsp : (slotRun P σ [.movImm 0 0, .strSp 0 ⟨8 * s0.length, hq⟩,
      .strSp 0 ⟨8 * s0.length + 4, hqh⟩] v).sp = v.sp := rfl
  have hu1n : u1.sp.toNat = b.sp.toNat - 8 * (s0.length + 1) := by
    rw [hu1sp, toNat_sub_frame hfit]
  have hb32 := toNat_lt32 b.sp
  refine ⟨_, reach_exec c0 e0 r1, ?_, ?_, ?_, ?_, ?_, fun c hc => ?_⟩
  · rw [p1, hu1pc]
    simp only [List.length_append, List.length_cons, List.length_nil]
    addr_eq
  · rw [sp1', hu1sp]
  · rw [tr1, hu1]
  · rw [rd1, hu1]
  · rw [hfin]
    refine WordsAt.of_parts (fun i hi => ?_) ?_
    · have := val1 i hi
      rw [Nat.zero_add] at this
      exact valAt_below hsp hmem (by have := toNat_lt32 b.sp; omega) hi this
    · exact valAt_store2 hsp hmem (by have := toNat_lt32 b.sp; omega) ⟨rfl, rfl⟩
  · rw [sp1', hu1n] at hc
    rw [hfin, hmem, store2_below (by rw [sp1, hu1n]; omega) (by rw [sp1, hu1n]; omega),
      out1 c fun i hi => outside_below (by rw [hu1n]; omega) (by rw [hu1n]; omega), hu1]

/-! ## One window and the loop -/

/-- One window of `main` from the loop's head, for the step `k` of the generator's program, whose
run `hcall` states: from the state `r` of `reqRun` in the outgoing area and the store in the area
of a program with one, the machine returns to the loop's head with the state after the window
there, the window's access appended to its trace, its read counted, and the store after the call
in the area, which keeps `J`.  The reads before the loop number `r0`, so the windows read `σ` from
`r0` on. -/
theorem main_window {G : Type} {m : Module} {k : Nat} {s0 : List UInt64}
    {base limit dev : UInt32} {is : List Instr} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true) (hdev : DevWindow P dev)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hJ : J heap st)
    (hcap : st.memoryCap m 0 ≤ 65535) (r0 : Nat) (r : ReqState G) (ms : State)
    (hpc : ms.pc = after base (mainStart s0)) (hrd : ms.reads = r.reads + r0)
    (hstk : StackOk P limit (s0.length + 1) (stackBound m k) ms)
    (hsr : AreaHolds P m k limit st ms) (hargs : WordsAt ms (words r.state ++ [r.last])) :
    ∃ ms', Reach P σ code ms ms' ∧ ms'.pc = ms.pc ∧ ms'.sp = ms.sp ∧
      ms'.trace = ms.trace ++ [reqEvent (devBus dev) tick (fun j => σ (j + r0)) r] ∧
      ms'.reads = (reqNext tick (fun j => σ (j + r0)) r).reads + r0 ∧
      WordsAt ms' (words (reqNext tick (fun j => σ (j + r0)) r).state ++
        [(reqNext tick (fun j => σ (j + r0)) r).last]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ J heap' st' ∧
        st'.memoryCaps = st.memoryCaps ∧ AreaHolds P m k limit st' ms' := by
  obtain ⟨f, fs', -, -, -, -, main, fns, _, hmain, hml, -, -, his⟩ := gen_program_entry hg
  have hmw := genMain_wide hmain
  obtain ⟨start, wds, hq, hqh, o1, o2, o3, o4, -, -, -, hmeq, b1, b2, b3, b4⟩ := gen_main hmain
  subst hmeq
  have hlW : ([Instr.blTo o1] ++ mainDecode ⟨8 * s0.length + 4, hqh⟩ dev ++
      [Instr.bcondTo condNE o2]).length = 10 := rfl
  have hlR : (mainRead ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩ ++
      [Instr.bTo o3]).length = 5 := rfl
  have hlWr : (mainWrite ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩ ++
      [Instr.bTo o4]).length = 6 := rfl
  have hsl : start.length = mainStart s0 := by
    rw [List.length_append, List.length_append, List.length_append, hlW, hlR, hlWr] at hml
    simp only [mainSize] at hml
    omega
  rw [hsl] at b1 b2 b3 b4
  -- the code of the window
  have hcode' := hcode
  rw [his] at hcode'
  have hcM := (CodeAt.append.mp (CodeAt.append.mp (CodeAt.append.mp hcode').1).1).1
  have hw3 := all_left hmw
  have hw2 := all_left hw3
  obtain ⟨hc3, hcWr⟩ := hcM.split_wide hw3
  obtain ⟨hc2, hcR⟩ := hc3.split_wide hw2
  obtain ⟨-, hcW⟩ := hc2.split_wide (all_left hw2)
  rw [hsl, ← hpc] at hcW
  rw [List.length_append, hsl, hlW, ← after_after, ← hpc] at hcR
  rw [List.length_append, List.length_append, hsl, hlW, hlR, ← after_after, ← after_after,
    ← hpc] at hcWr
  rw [← hpc] at b1 b2 b3 b4
  obtain ⟨hcW1, hcB⟩ := hcW.split_wide (l1 := [Instr.blTo o1] ++
    mainDecode ⟨8 * s0.length + 4, hqh⟩ dev) rfl
  obtain ⟨hcBL, hcD⟩ := hcW1.split_wide (l1 := [Instr.blTo o1]) rfl
  obtain ⟨hcRd, hcRB⟩ := hcR.split_wide (l1 := mainRead ⟨8 * s0.length, hq⟩
    ⟨8 * s0.length + 4, hqh⟩) rfl
  obtain ⟨hcWt, hcWB⟩ := hcWr.split_wide (l1 := mainWrite ⟨8 * s0.length, hq⟩
    ⟨8 * s0.length + 4, hqh⟩) rfl
  -- the call
  obtain ⟨q1, q2, q3, q4⟩ := b1
  have eBL := exec_blTo (P := P) (σ := σ) q1 q2 q3 ms
  obtain ⟨s1, hs1⟩ : ∃ s1 : State,
      s1 = { ms with lr := (ms.pc + 4) ||| 1, pc := ms.pc + 4 + UInt32.ofInt o1 } := ⟨_, rfl⟩
  rw [← hs1] at eBL
  have hev4 : (ms.pc + 4).toNat % 2 = 0 := by
    rw [hpc, show after base (mainStart s0) + 4 = after base (mainStart s0 + 1) by addr_after]
    exact even_after hev _
  have hs1pc : s1.pc = after base (mainSize s0) := by
    rw [hs1, State.pc_withLrPc]
    exact q4
  have hs1sp : s1.sp = ms.sp := by rw [hs1, State.sp_withLrPc]
  have hs1tr : s1.trace = ms.trace := by rw [hs1, State.trace_withLrPc]
  have hs1rd : s1.reads = ms.reads := by rw [hs1, State.reads_withLrPc]
  have hs1m : s1.mem = ms.mem := by rw [hs1, State.mem_withLrPc]
  obtain ⟨ms2, r2, p2, sp2, -, tr2, rd2, -, wa2, st', heap', hat', hJ', hcaps', hsr2⟩ :=
    step_call (P := P) (σ := σ) (code := code) hlen hcall hm hg hcode hev hcov hat hJ hcap
    r.state r.last s1 hs1pc (by rw [hs1, State.lr_withLrPc]; exact or1_odd _) (hstk.congr hs1sp)
    (hsr.congr (KeepsBelow.of_mem hs1m)) (by rw [hs1]; exact hargs)
  have hms2pc : ms2.pc = after ms.pc 1 := by
    rw [p2, hs1, State.lr_withLrPc, or1_and _ hev4, after_eq]
    rfl
  have hsp2 : ms2.sp = ms.sp := sp2.trans hs1sp
  have hkb : ∀ (w0 w1 : UInt32) (t : State), t.mem = store32 (store32 ms2.mem
      (ms2.sp + UInt32.ofNat (8 * s0.length)) w0) (ms2.sp + UInt32.ofNat (8 * s0.length + 4)) w1 →
      KeepsBelow limit ms2 t := fun w0 w1 t ht a ha => by
    have := hstk.fits
    have := hstk.limit
    rw [ht]
    exact store2_below (by rw [hsp2]; omega) (by rw [hsp2]; omega)
  obtain ⟨g', q, ht⟩ : ∃ g' q, tick r.state r.last = (g', q) := ⟨_, _, rfl⟩
  rw [ht] at wa2
  have hl' : (words g').length = s0.length := hlen g'
  have hlast := wa2.last
  rw [hl'] at hlast
  obtain ⟨hlo, hhi⟩ := hlast
  obtain ⟨hwq, hwqh⟩ := (hstk.congr hsp2).words (Nat.le_refl s0.length)
  -- the decoding
  have hcD' : CodeAt code ms2.pc (mainDecode ⟨8 * s0.length + 4, hqh⟩ dev) := by
    rw [hms2pc]
    exact hcD
  obtain ⟨t3, r3, p3, sp3, m3, tr3, rd3, e3, z3⟩ := run_decode (P := P) (σ := σ) (dev := dev)
    (q := q) hcD' hwqh hhi
  have hpc3 : t3.pc = after ms.pc 9 := by
    rw [p3, hms2pc]
    addr_after
  have hcB' : CodeAt code t3.pc [Instr.bcondTo condNE o2] := by
    rw [hpc3]
    exact hcB
  obtain ⟨c1, c2, c3, c4⟩ := b2
  have rB := reach_branch (P := P) (σ := σ) (code := code) (after (after ms.pc 10) 5) c1 c2 c3
    hcB' (by rw [hpc3]; exact c4)
  have hcond : t3.condHolds condNE = reqWrite q := by
    rw [show condNE = (1 : Fin 14) from rfl, condHolds_ne, z3, Bool.not_not]
  rw [hcond] at rB
  have hsp3 : t3.sp = ms2.sp := sp3
  have htr3 : t3.trace = ms.trace := tr3.trans (tr2.trans hs1tr)
  have hrd3 : t3.reads = ms.reads := rd3.trans (rd2.trans hs1rd)
  obtain ⟨hal, hdv⟩ := hdev.reg q
  have hreach : Reach P σ code ms t3 := reach_exec hcBL eBL (r2.trans r3)
  obtain ⟨hn1, hn2, hn3, hn4⟩ := reqNext_of (B := devBus dev) (σ := fun j => σ (j + r0)) ht
  cases hw : reqWrite q
  · -- a read
    rw [hw] at rB
    change Reach P σ code t3 { t3 with pc := t3.pc + 4 } at rB
    rw [hw] at hn2 hn3 hn4
    simp only [Bool.false_eq_true, ↓reduceIte] at hn2 hn3 hn4
    obtain ⟨u4, hu4⟩ : ∃ u4 : State, u4 = { t3 with pc := t3.pc + 4 } := ⟨_, rfl⟩
    rw [← hu4] at rB
    have hu4pc : u4.pc = after ms.pc 10 := by
      rw [hu4, State.pc_withPc, hpc3]
      addr_after
    have hu4sp : u4.sp = ms2.sp := by rw [hu4, State.sp_withPc, hsp3]
    have hu4tr : u4.trace = ms.trace := by rw [hu4, State.trace_withPc, htr3]
    have hu4rd : u4.reads = ms.reads := by rw [hu4, State.reads_withPc, hrd3]
    have hu4m : u4.mem = ms2.mem := by rw [hu4, State.mem_withPc, m3]
    have hcRd' : CodeAt code u4.pc (mainRead ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩) := by
      rw [hu4pc]
      exact hcRd
    obtain ⟨t5, r5, p5, sp5, tr5, rd5, m5⟩ := run_read (P := P) (σ := σ) hcRd'
      (by rw [hu4, State.r_withPc, e3]) hal hdv (by rw [hu4sp]; exact hwq)
      (by rw [hu4sp]; exact hwqh)
    have hp5 : t5.pc = after (after ms.pc 10) 4 := by
      rw [p5, hu4pc]
      addr_after
    have hcRB' : CodeAt code t5.pc [Instr.bTo o3] := by
      rw [hp5]
      exact hcRB
    obtain ⟨d1, d2, d3, d4⟩ := b3
    have e6 := exec_bTo (P := P) (σ := σ) d1 d2 d3 t5
    have hsp5 : t5.sp = ms2.sp := sp5.trans hu4sp
    have hm6 : t5.mem = store32 (store32 ms2.mem (ms2.sp + UInt32.ofNat (8 * s0.length))
        (σ (r.reads + r0))) (ms2.sp + UInt32.ofNat (8 * s0.length + 4)) 0 := by
      rw [m5, hu4sp, hu4m, hu4rd, hrd]
    refine ⟨_, hreach.trans (rB.trans (r5.trans (reach_exec hcRB' e6 (.refl _)))), ?_, ?_, ?_,
      ?_, ?_, st', heap', hat', hJ', hcaps', hsr2.congr (hkb _ _ _ hm6)⟩
    · show t5.pc + 4 + UInt32.ofInt o3 = ms.pc
      rw [hp5]
      exact d4
    · show t5.sp = ms.sp
      rw [hsp5, hsp2]
    · show t5.trace = _
      rw [tr5, hn4, hu4tr, hu4rd, hrd]
      rfl
    · show t5.reads = _
      rw [rd5, hn3, hu4rd, hrd]
      omega
    · rw [hn1, hn2]
      refine WordsAt.of_parts (fun i hi => ?_) ?_
      · exact valAt_below (s := ms2) (t := { t5 with pc := t5.pc + 4 + UInt32.ofInt o3 })
          hsp5 hm6 (by omega) (by omega) (wa2.init i hi)
      · rw [hl']
        exact valAt_store2 (s := ms2) hsp5 hm6 (by omega) (slotRel_read _)
  · -- a write
    rw [hw] at rB
    change Reach P σ code t3 { t3 with pc := after (after ms.pc 10) 5 } at rB
    rw [hw] at hn2 hn3 hn4
    simp only [↓reduceIte] at hn2 hn3 hn4
    obtain ⟨u4, hu4⟩ : ∃ u4 : State, u4 = { t3 with pc := after (after ms.pc 10) 5 } :=
      ⟨_, rfl⟩
    rw [← hu4] at rB
    have hu4pc : u4.pc = after (after ms.pc 10) 5 := by rw [hu4, State.pc_withPc]
    have hu4sp : u4.sp = ms2.sp := by rw [hu4, State.sp_withPc, hsp3]
    have hu4tr : u4.trace = ms.trace := by rw [hu4, State.trace_withPc, htr3]
    have hu4rd : u4.reads = ms.reads := by rw [hu4, State.reads_withPc, hrd3]
    have hu4m : u4.mem = ms2.mem := by rw [hu4, State.mem_withPc, m3]
    have hcWt' : CodeAt code u4.pc (mainWrite ⟨8 * s0.length, hq⟩ ⟨8 * s0.length + 4, hqh⟩) := by
      rw [hu4pc]
      exact hcWt
    obtain ⟨t5, r5, p5, sp5, tr5, rd5, m5⟩ := run_write (P := P) (σ := σ) hcWt'
      (by rw [hu4, State.r_withPc, e3]) hal hdv (by rw [hu4sp]; exact hwq)
      (by rw [hu4sp]; exact hwqh)
    have hp5 : t5.pc = after (after (after ms.pc 10) 5) 5 := by
      rw [p5, hu4pc]
      addr_after
    have hcWB' : CodeAt code t5.pc [Instr.bTo o4] := by
      rw [hp5]
      exact hcWB
    obtain ⟨d1, d2, d3, d4⟩ := b4
    have e6 := exec_bTo (P := P) (σ := σ) d1 d2 d3 t5
    have hsp5 : t5.sp = ms2.sp := sp5.trans hu4sp
    have hm6 : t5.mem = store32 (store32 ms2.mem (ms2.sp + UInt32.ofNat (8 * s0.length)) 0)
        (ms2.sp + UInt32.ofNat (8 * s0.length + 4)) 0 := by
      rw [m5, hu4sp, hu4m]
    refine ⟨_, hreach.trans (rB.trans (r5.trans (reach_exec hcWB' e6 (.refl _)))), ?_, ?_, ?_,
      ?_, ?_, st', heap', hat', hJ', hcaps', hsr2.congr (hkb _ _ _ hm6)⟩
    · show t5.pc + 4 + UInt32.ofInt o4 = ms.pc
      rw [hp5]
      exact d4
    · show t5.sp = ms.sp
      rw [hsp5, hsp2]
    · show t5.trace = _
      rw [tr5, hn4, hu4tr, hu4m, hu4sp, hlo, ← toUInt32_ofNat_lo]
      rfl
    · show t5.reads = _
      rw [rd5, hn3, hu4rd, hrd]
    · rw [hn1, hn2]
      refine WordsAt.of_parts (fun i hi => ?_) ?_
      · exact valAt_below (s := ms2) (t := { t5 with pc := t5.pc + 4 + UInt32.ofInt o4 })
          hsp5 hm6 (by omega) (by omega) (wa2.init i hi)
      · rw [hl']
        exact valAt_store2 (s := ms2) hsp5 hm6 (by omega) ⟨rfl, rfl⟩

/-- The first `n` windows of `main` from the loop's head with the words of `g0` and 0 in the
outgoing area: the machine returns to the loop's head with the state `reqRun tick g0 σ' n` in the
outgoing area and the traces of the windows appended, where `σ'` takes the values of `σ` from
the reads before the loop on. -/
theorem main_loop {G : Type} {m : Module} {k : Nat} {s0 : List UInt64}
    {base limit dev : UInt32} {is : List Instr} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true) (hdev : DevWindow P dev)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hJ : J heap st)
    (hcap : st.memoryCap m 0 ≤ 65535) (g0 : G) (ms : State)
    (hpc : ms.pc = after base (mainStart s0))
    (hstk : StackOk P limit (s0.length + 1) (stackBound m k) ms)
    (hsr : AreaHolds P m k limit st ms) (hargs : WordsAt ms (words g0 ++ [0])) (n : Nat) :
    ∃ t, Reach P σ code ms t ∧ t.pc = ms.pc ∧ t.sp = ms.sp ∧
      t.trace = ms.trace ++ windows (reqTrace (devBus dev) tick g0 (fun j => σ (j + ms.reads))) n ∧
      t.reads = (reqRun tick g0 (fun j => σ (j + ms.reads)) n).reads + ms.reads ∧
      WordsAt t (words (reqRun tick g0 (fun j => σ (j + ms.reads)) n).state ++
        [(reqRun tick g0 (fun j => σ (j + ms.reads)) n).last]) ∧
      ∃ (st' : Store Unit) (heap' : Heap), heap'.At st' ∧ J heap' st' ∧
        st'.memoryCap m 0 ≤ 65535 ∧ AreaHolds P m k limit st' t := by
  induction n with
  | zero =>
      exact ⟨ms, .refl _, rfl, rfl, (List.append_nil _).symm, (Nat.zero_add _).symm, hargs, st,
        heap, hat, hJ, hcap, hsr⟩
  | succ n ih =>
      obtain ⟨t, rt, pt, spt, trt, rdt, wat, st1, heap1, hat1, hJ1, hcap1, hsr1⟩ := ih
      obtain ⟨t', rt', pt', spt', trt', rdt', wat', st2, heap2, hat2, hJ2, hcaps2, hsr2⟩ :=
        main_window (P := P) (σ := σ) (code := code) hlen hcall hm hg hcode hev hcov hdev hat1
          hJ1 hcap1 ms.reads (reqRun tick g0 (fun j => σ (j + ms.reads)) n) t (pt.trans hpc) rdt
          (hstk.congr spt) hsr1 wat
      refine ⟨t', rt.trans rt', pt'.trans pt, spt'.trans spt, ?_, rdt', wat', st2, heap2, hat2,
        hJ2, by rw [memoryCap_of_caps hcaps2]; exact hcap1, hsr2⟩
      rw [trt', trt, windows, reqTrace, List.append_assoc]

/-- `main` from its entry at `base`, with SP at a multiple of 4 above the outgoing area and the
stack that `StackOk` states below the area: the start and the first `n` windows reach the loop's
head with the traces of the windows appended. -/
theorem main_run {G : Type} {m : Module} {k : Nat} {s0 : List UInt64}
    {base limit dev : UInt32} {is : List Instr} {words : G → List UInt64}
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {J : Heap → Store Unit → Prop} (hcall : StepCall m k words tick J) (hm : m.imports = [])
    (hg : genProgram m k s0 base limit dev udivmod64 = .ok is) (hcode : CodeAt code base is)
    (hev : base.toNat % 2 = 0) (hcov : reachCovered m k = true) (hdev : DevWindow P dev)
    {st : Store Unit} {heap : Heap} (hat : heap.At st) (hJ : J heap st)
    (hcap : st.memoryCap m 0 ≤ 65535) (g0 : G) (hs0 : words g0 = s0) (b : State)
    (hpc : b.pc = base) (hal : b.sp.toNat % 4 = 0) (hfit : 8 * (s0.length + 1) ≤ b.sp.toNat)
    (hstk : StackOk P limit (s0.length + 1) (stackBound m k)
      { b with sp := b.sp - UInt32.ofNat (8 * (s0.length + 1)) })
    (hsr : AreaHolds P m k limit st b) (n : Nat) :
    ∃ t, Reach P σ code b t ∧ t.pc = after base (mainStart s0) ∧
      t.trace = b.trace ++ windows (reqTrace (devBus dev) tick g0 (fun j => σ (j + b.reads))) n := by
  obtain ⟨f, fs', -, -, -, -, main, fns, _, hmain, hml, -, -, his⟩ := gen_program_entry hg
  obtain ⟨start, wds, hq, hqh, o1, o2, o3, o4, harea, hw, hst, hmeq, -⟩ := gen_main hmain
  have hmw := genMain_wide hmain
  subst hmeq
  have hsl : start.length = mainStart s0 := by
    simp only [mainSize, mainDecode, mainRead, mainWrite, List.length_append, List.length_cons,
      List.length_nil] at hml
    omega
  have hcode' := hcode
  rw [his] at hcode'
  have hcM := (CodeAt.append.mp (CodeAt.append.mp (CodeAt.append.mp hcode').1).1).1
  have hcS : CodeAt code base start :=
    (((hcM.split_wide (all_left hmw)).1.split_wide (all_left (all_left hmw))).1.split_wide
      (all_left (all_left (all_left hmw)))).1
  rw [hst, ← hpc] at hcS
  obtain ⟨t0, r0, p0, sp0, tr0, rd0, wa0, mem0⟩ := main_start (P := P) (σ := σ) harea hw hcS hal
    hfit hstk.ram
  have hlen0 : wds.flatten.length + 4 = mainStart s0 := by
    rw [← hsl, hst]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hp0 : t0.pc = after base (mainStart s0) := by rw [p0, hpc, after_eq, hlen0]
  have hlim := hstk.limit
  obtain ⟨t, rt, pt, -, trt, -, -, -⟩ := main_loop (P := P) (σ := σ) (code := code) hlen hcall hm
    hg hcode hev hcov hdev hat hJ hcap g0 t0 hp0 (hstk.congr (by rw [sp0]))
    (hsr.congr fun a ha => mem0 a (by rw [sp0]; exact Nat.lt_of_lt_of_le ha hlim.2))
    (by rw [hs0]; exact wa0) n
  exact ⟨t, r0.trans rt, pt.trans hp0, by rw [trt, tr0, rd0]⟩

end LeanExe.M7
