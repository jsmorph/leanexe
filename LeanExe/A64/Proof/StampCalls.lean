import LeanExe.A64.Proof.LinuxMain
import LeanExe.A64.Proof.LinuxCalls
import LeanExe.A64.Proof.StampCode
import LeanExe.A64.Proof.StampTrace

/-!
The call sites of the stamp program under `ProcReachWith`.  `run_callSvc` follows a `BL` to the
routine `SVC #0; RET` and back for a call of the table; `run_stubWith` a stub that sets X0 to a
status and branches to the exit word.  `run_storeWords` follows the stores of the words of a path
into `main`'s frame, and `pathWords_byte` gives the path's bytes that they leave there, so that
`run_open` evaluates the `openat` of the path with its bytes and terminating zero as the event's
input.  `run_close` follows the `close` of the descriptor in the frame's slot 2.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies)

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-! ## The call of the routine `SVC #0; RET` -/

/-- The process `p` at the routine `svc` after `BL` at `a`: X30 at the word after the `BL`. -/
def Proc.call (p : Proc) (a svc : UInt64) : Proc :=
  { p with core := { p.core.setX 30 (after a 1) with pc := svc } }

theorem Proc.call_x (p : Proc) (a svc : UInt64) {r : Fin 32} (h : r ≠ 30) :
    (p.call a svc).core.x r = p.core.x r := by
  show ({ p.core.setX 30 (after a 1) with pc := svc } : State).x r = _
  rw [State.x_withPc, State.x_setX_ne (Ne.symm h)]

@[simp] theorem Proc.call_mem (p : Proc) (a svc : UInt64) : (p.call a svc).core.mem = p.core.mem :=
  State.setX_mem

@[simp] theorem Proc.call_trace (p : Proc) (a svc : UInt64) : (p.call a svc).trace = p.trace :=
  rfl

theorem Proc.call_x30 (p : Proc) (a svc : UInt64) : (p.call a svc).core.x 30 = after a 1 := by
  show ({ p.core.setX 30 (after a 1) with pc := svc } : State).x 30 = _
  rw [State.x_withPc, State.x_setX_same (by decide)]

/-- `BL` at `a` to the routine `SVC #0; RET` at `svc` for a call `c` of the table whose number X8
holds, when the call from the process at the routine returns `v`, leaves the memory `mem`, and
records the event `e`: the run returns to the word after the `BL` with X0 at `v`, X30 at that word,
the memory `mem`, the event appended, and every other register, SP, `FPCR`, and the UART's state
as they were. -/
theorem run_callSvc {a svc : UInt64} {g : Fin 67108864}
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hbl : code a = some (encode (.bl g)))
    (hg : bField a svc = .ok g) (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hnext : (after a 1).toNat < 2 ^ 55) {p : Proc} (hpc : p.core.pc = a) {c : Call}
    (hT : T.find? (fun c => c.arm64 == p.core.x 8) = some c) (ht : c.terminal = false)
    {v : UInt64} {mem : UInt64 → UInt8} {e : LeanExe.Linux.Event}
    (hsys : sysCall R P c (p.call a svc) = some ((p.call a svc).ret v mem (.sys e))) :
    ∃ q, ProcReachWith T R P code p q ∧ q.core.pc = after a 1 ∧ q.core.x 0 = v ∧
      q.core.x 30 = after a 1 ∧ (∀ r : Fin 32, r ≠ 0 → r ≠ 30 → q.core.x r = p.core.x r) ∧
      q.core.sp = p.core.sp ∧ q.core.mem = mem ∧ q.core.io = p.core.io ∧ q.fpcr = p.fpcr ∧
      q.trace = p.trace ++ [.sys e] := by
  have c0 := hsvc 0 (by simp)
  simp only [List.getElem_cons_zero, after_zero, Op.word] at c0
  have e1 : exec P (.bl g) p.core = some (p.call a svc).core := by
    show some { p.core.setX 30 (p.core.pc + 4) with pc := p.core.pc + sext 26 g.val * 4 } = _
    rw [hpc, bField_target hg, ← after_one]
    rfl
  have s0 : pstepWith T R P code p = some (p.call a svc) :=
    pstepWith_at (by rw [hpc]; exact hbl) (.inl rfl) e1 (hdom _ _ c0)
  have r1 := run_svcRet (T := T) (R := R) (P := P) hsvc (p := p.call a svc) rfl
    (by rw [Proc.call_x _ _ _ (by decide)]; exact hT) ht hsys
    (by rw [Proc.call_x30]; exact hnext)
  refine ⟨_, .next s0 r1, by rw [Proc.goto_pc, Proc.call_x30], by rw [Proc.goto_x, Proc.ret_x0],
    by rw [Proc.goto_x, Proc.ret_x _ _ _ _ (by decide), Proc.call_x30],
    fun r h0 h30 => by rw [Proc.goto_x, Proc.ret_x _ _ _ _ h0, Proc.call_x _ _ _ h30], ?_, rfl,
    ?_, rfl, rfl⟩
  · rw [Proc.goto_sp, Proc.ret_sp]
    exact State.setX_sp
  · rw [Proc.goto_io, Proc.ret_io]
    exact State.setX_io

/-- A stub at `a` that sets X0 to `c` and branches to the exit word at `base`. -/
theorem run_stubWith {a base : UInt64} {c : Nat} {g : Fin 67108864}
    (hca : CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]))
    (hga : bField (after a 4) base = .ok g) (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (hbase : base.toNat < 2 ^ 55) {q : Proc} (hq : q.core.pc = a) (hf : q.fpcr = fpcrValue) :
    ∃ q', ProcReachWith T R P code q q' ∧ q'.core.pc = base ∧ q'.core.x 0 = UInt64.ofNat c ∧
      q'.trace = q.trace ∧ q'.core.io = q.core.io := by
  obtain ⟨u, ru, pu, xu, iou⟩ := run_stub P code hca hga hq
  exact ⟨{ q with core := u }, ProcReachWith.of_reach' hdom hf ru (by rw [pu]; exact hbase), pu,
    xu, rfl, iou⟩

/-! ## Bytes of words -/

theorem store64_byteOf (m : UInt64 → UInt8) (a w : UInt64) {k : Nat} (hk : k < 8) :
    store64 m a w (a + UInt64.ofNat k) = byteOf w k := by
  have e : a + UInt64.ofNat k - a = UInt64.ofNat k := by
    rw [UInt64.add_comm, UInt64.add_sub_cancel]
  have hlt : UInt64.ofNat k < 8 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
    have : (8 : UInt64).toNat = 8 := rfl
    rw [this]
    omega
  simp only [store64, e, hlt, ite_true, byteOf]
  congr 2
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', UInt64.toNat_mul, UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  omega

theorem byteOf_toNat (w : UInt64) {k : Nat} (hk : k < 8) :
    (byteOf w k).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  simp only [byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  have : 8 * k % 2 ^ 64 % 64 = 8 * k := by omega
  rw [this]

/-- The little-endian value of the bytes of a word. -/
theorem leWord_toNat : ∀ bs : List UInt8, bs.length ≤ 8 →
    (leWord bs).toNat = LeanExe.Linux.leValue bs ∧ LeanExe.Linux.leValue bs < 256 ^ bs.length
  | [], _ => ⟨rfl, by decide⟩
  | b :: bs, h => by
    simp only [List.length_cons] at h
    obtain ⟨h1, h2⟩ := leWord_toNat bs (by omega)
    have hb := b.toNat_lt
    have hp : 256 ^ bs.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have e : leWord (b :: bs) = leWord bs * 256 + b.toUInt64 := rfl
    refine ⟨?_, ?_⟩
    · rw [e, UInt64.toNat_add, UInt64.toNat_mul, h1, UInt8.toNat_toUInt64]
      simp only [LeanExe.Linux.leValue, UInt64.reduceToNat, Nat.reducePow] at *
      omega
    · simp only [LeanExe.Linux.leValue, List.length_cons, Nat.pow_succ]
      simp only [Nat.reducePow] at *
      omega

theorem leValue_byte : ∀ (bs : List UInt8) (k : Nat),
    LeanExe.Linux.leValue bs / 256 ^ k % 256 = (bs.getD k 0).toNat
  | [], k => by simp [LeanExe.Linux.leValue]
  | b :: bs, 0 => by
    have := b.toNat_lt
    simp only [LeanExe.Linux.leValue, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | b :: bs, k + 1 => by
    have := b.toNat_lt
    rw [List.getD_cons_succ, ← leValue_byte bs k, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256,
      ← Nat.div_div_eq_div_mul]
    congr 2
    simp only [LeanExe.Linux.leValue]
    omega

/-- Byte `k` of the word of at most 8 bytes `bs`. -/
theorem byteOf_leWord {bs : List UInt8} (h : bs.length ≤ 8) {k : Nat} (hk : k < 8) :
    byteOf (leWord bs) k = bs.getD k 0 := by
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat _ hk, (leWord_toNat bs h).1, show 2 ^ (8 * k) = 256 ^ k by
    rw [Nat.pow_mul], leValue_byte]

theorem pathWords_length (path : List UInt8) : (pathWords path).length = path.length / 8 + 1 := by
  simp [pathWords]

/-- Byte `j` of the words of a path, the path's byte `j`, and 0 past its end. -/
theorem pathWords_byte (path : List UInt8) {j : Nat} (hj : j < 8 * (pathWords path).length) :
    byteOf ((pathWords path).getD (j / 8) 0) (j % 8) = path.getD j 0 := by
  rw [pathWords_length] at hj
  have hj8 : j / 8 < path.length / 8 + 1 := by omega
  simp only [pathWords]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj8, Option.map_some,
    Option.getD_some, byteOf_leWord (by simp) (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos (by omega), List.getElem?_drop,
    show 8 * (j / 8) + j % 8 = j by omega, List.getD_eq_getElem?_getD]
  by_cases hl : j < path.length
  · rw [List.getElem?_append_left hl]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := path) (by omega),
      List.getElem?_replicate]
    split <;> rfl

/-! ## The stores of a path's words -/

theorem slotAddr_succ (sp : UInt64) (i : Nat) :
    slotAddr sp (i + 1) = slotAddr sp i + UInt64.ofNat 8 := by
  simp only [slotAddr, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]
  rfl

/-- The stores of the words `ws` into the frame's slots from `slot` by the code of
`storeWords ws slot`: the words' bytes in the slots, every other byte kept, and every register
but X16 kept. -/
theorem run_storeWords :
    ∀ (ws : List UInt64) (slot : Nat) {a : UInt64} {s : State},
      (∀ i < ws.length, ∃ h : slot + i < 4096,
        CodeAt code (after a (5 * i)) (movImm 16 (ws.getD i 0) ++ [.str 16 31 ⟨slot + i, h⟩])) →
      s.pc = a → s.sp % 16 = 0 → s.sp.toNat < 2 ^ 63 →
      (∀ j < 8 * (slot + ws.length), P.normal (s.sp + UInt64.ofNat j) = true) →
      ∃ t, Reach P code s t ∧ t.pc = after a (5 * ws.length) ∧ t.sp = s.sp ∧ t.io = s.io ∧
        (∀ r : Fin 32, r ≠ 16 → t.x r = s.x r) ∧
        (∀ j < 8 * ws.length,
          t.mem (slotAddr s.sp slot + UInt64.ofNat j) = byteOf (ws.getD (j / 8) 0) (j % 8)) ∧
        (∀ b : UInt64, ¬ (b - slotAddr s.sp slot).toNat < 8 * ws.length → t.mem b = s.mem b)
  | [], slot, a, s, _, hpc, _, _, _ =>
    ⟨s, .refl _, by rw [hpc]; simp [after], rfl, rfl, fun _ _ => rfl,
      fun j hj => absurd hj (by simp), fun _ _ => rfl⟩
  | w :: ws, slot, a, s, hc, hpc, hal, htop, hmap => by
    obtain ⟨h0, c0⟩ := hc 0 (by simp)
    simp only [Nat.mul_zero, after_zero, Nat.add_zero, List.getD_cons_zero] at c0
    have sp := CodeAt.split code c0 (movImm_length 16 w)
    obtain ⟨s1, r1, p1, x1, k1, sp1, mem1, io1⟩ := run_movImm P code (d := 16) (by decide) sp.1 hpc
    have cs : code (after a 4) = some (encode (.str 16 31 ⟨slot, by simpa using h0⟩)) := by
      have := (CodeAt.cons.mp sp.2).1
      simpa using this
    have hs1 : s1.sp % 16 = 0 := by rw [sp1]; exact hal
    let s2 : State :=
      { s1 with mem := store64 s1.mem (slotAddr s1.sp slot) (s1.x 16), pc := s1.pc + 4 }
    have e2 : exec P (.str 16 31 ⟨slot, by simpa using h0⟩) s1 = some s2 :=
      exec_str_sp P (i := slot) (by simpa using h0) hs1 fun j hj => by
        rw [sp1]
        exact hmap _ (by simp only [List.length_cons]; omega)
    have r2 : Reach P code s s2 := r1.trans (reach_exec P code (by rw [p1]; exact cs) e2 (.refl _))
    have p2 : s2.pc = after (after a 5) 0 := by
      show s1.pc + 4 = _
      rw [p1, after_zero, ← after_succ]
    have hc' : ∀ i < ws.length, ∃ h : slot + 1 + i < 4096,
        CodeAt code (after (after a 5) (5 * i))
          (movImm 16 (ws.getD i 0) ++ [.str 16 31 ⟨slot + 1 + i, h⟩]) := by
      intro i hi
      obtain ⟨h, c⟩ := hc (i + 1) (by simp; omega)
      refine ⟨by omega, ?_⟩
      rw [after_after, show 5 + 5 * i = 5 * (i + 1) by omega]
      simpa [show slot + (i + 1) = slot + 1 + i by omega] using c
    obtain ⟨t, rt, pt, spt, iot, kt, hin, hout⟩ := run_storeWords ws (slot + 1) hc'
      (by rw [after_zero] at p2; exact p2)
      (by show s1.sp % 16 = 0; exact hs1) (by show s1.sp.toNat < _; rw [sp1]; exact htop)
      (fun j hj => by
        show P.normal (s1.sp + _) = true
        rw [sp1]
        exact hmap j (by simp only [List.length_cons]; omega))
    have hwl : ws.length ≤ 4096 := by
      rcases Nat.eq_zero_or_pos ws.length with h | h
      · omega
      · obtain ⟨h', -⟩ := hc ws.length (by simp)
        omega
    have hsp2 : s2.sp = s.sp := sp1
    rw [hsp2] at hin hout
    have hw : s1.x 16 = w := x1
    have hsl := slotAddr_succ s.sp slot
    have hsl8 : ∀ j : Nat, slotAddr s.sp slot + UInt64.ofNat (8 + j) =
        slotAddr s.sp (slot + 1) + UInt64.ofNat j := fun j => by
      rw [hsl, UInt64.add_assoc, ← UInt64.ofNat_add]
    have htl : (slotAddr s.sp slot).toNat = s.sp.toNat + 8 * slot := by
      rw [toNat_slot]
      simp only [Nat.reducePow] at *
      omega
    refine ⟨t, r2.trans rt, by rw [pt, after_after]; congr 1; simp; omega, by rw [spt, hsp2],
      by rw [iot]; show s1.io = _; exact io1, fun r hr => by rw [kt r hr]; exact k1 r hr,
      fun j hj => ?_, fun b hb => ?_⟩
    · by_cases hj8 : j < 8
      · rw [hout _ ?_]
        · show store64 s1.mem (slotAddr s1.sp slot) (s1.x 16) _ = _
          rw [sp1, hw, store64_byteOf _ _ _ hj8, Nat.div_eq_of_lt hj8, Nat.mod_eq_of_lt hj8]
          rfl
        · have hX := (slotAddr s.sp slot).toNat_lt
          rw [hsl]
          simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at *
          omega
      · have := hin (j - 8) (by simp only [List.length_cons] at hj; omega)
        rw [← hsl8, show 8 + (j - 8) = j by omega] at this
        rw [this, show (j - 8) / 8 = j / 8 - 1 by omega, show (j - 8) % 8 = j % 8 by omega]
        rw [show j / 8 = (j / 8 - 1) + 1 by omega, List.getD_cons_succ]
        simp only [Nat.add_sub_cancel]
    · have hbt := (b - slotAddr s.sp slot).toNat_lt
      simp only [List.length_cons] at hb
      rw [hout b ?_]
      · show store64 s1.mem (slotAddr s1.sp slot) (s1.x 16) b = _
        rw [sp1, store64_other _ _ _ _ ?_, mem1]
        rw [UInt64.lt_iff_toNat_lt]
        have : (8 : UInt64).toNat = 8 := rfl
        rw [this]
        omega
      · have hX := (slotAddr s.sp slot).toNat_lt
        have hB := b.toNat_lt
        rw [hsl]
        simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at *
        omega

/-! ## Opening a path -/

/-- The `n` bytes from `a` that hold the bytes of `l`, `n` its length. -/
theorem readList_eq (m : UInt64 → UInt8) : ∀ (a : UInt64) (l : List UInt8),
    (∀ j < l.length, m (a + UInt64.ofNat j) = l.getD j 0) → readList m a l.length = l
  | _, [], _ => rfl
  | a, b :: l, h => by
    have h0 := h 0 (by simp)
    rw [add_ofNat_zero] at h0
    rw [List.length_cons, readList, h0, readList_eq m (a + 1) l fun j hj => by
      rw [LeanExe.Linux.succ_ofNat]
      exact h (j + 1) (by simp; omega)]
    rfl

theorem shr31_eq_zero (x : UInt64) : x >>> UInt64.ofNat 31 = 0 ↔ x.toNat < 2 ^ 31 := by
  have e : (x >>> UInt64.ofNat 31).toNat = x.toNat / 2 ^ 31 := by
    simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    rw [e] at this
    simp only [UInt64.toNat_zero, Nat.reducePow] at *
    omega
  · intro h
    apply UInt64.toNat_inj.mp
    rw [e]
    simp only [UInt64.toNat_zero, Nat.reducePow] at *
    omega

/-- The bytes of a path that hold no zero, then a zero, as the event of `openat` reads them. -/
theorem path_read {m : UInt64 → UInt8} {S : UInt64} {path : List UInt8}
    (hlen : path.length < 4096) (hnz : ∀ i < path.length, path.getD i 0 ≠ 0)
    (hpath : ∀ j ≤ path.length, m (S + UInt64.ofNat j) = path.getD j 0) :
    (a64Memory P).pathLength m S = path.length + 1 ∧
      readList m S (path.length + 1) = path ++ [0] := by
  have hz : m (S + UInt64.ofNat path.length) = 0 := by
    rw [hpath _ (Nat.le_refl _)]
    simp [List.getD_eq_getElem?_getD]
  have hl : (a64Memory P).pathLength m S = path.length + 1 :=
    LeanExe.Linux.Memory.pathLength_eq (a64Memory P) m S hlen hz fun i hi => by
      show m (S + UInt64.ofNat i) ≠ 0
      rw [hpath i (by omega)]
      exact hnz i hi
  refine ⟨hl, ?_⟩
  have := readList_eq m S (path ++ [0]) fun j hj => by
    simp only [List.length_append, List.length_singleton] at hj
    rw [hpath j (by omega)]
    by_cases h : j < path.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · have : j = path.length := by omega
      subst this
      simp
  simpa using this

/-- The code of an `openat` of the path at `SP + off` with `flags` and `mode` at `o`, whose result
it tests and stores in the frame's slot 2: the call's event, with the path's bytes and their zero
as its input; a result of 2^31 or more branches to `e`, and a smaller one is stored. -/
theorem run_open {o svc e : UInt64} {off : Fin 4096} {flags : UInt64} {mode : Fin 65536}
    {g : Fin 67108864} {f : Fin 524288}
    (hc : CodeAt code o (movImm 0 atFdcwd ++ [.addImm 1 31 off] ++ movImm 2 flags ++
      [.movz 3 mode 0, .movz 8 56 0, .bl g, .lsrImm 16 0 31, .cbnz 16 f, .str 0 31 2]))
    (hg : bField (after o 11) svc = .ok g) (hf : cbField (after o 13) e = .ok f)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hT : T.find? (fun c => c.arm64 == 56) = some LeanExe.Linux.openatCall)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (h15 : (after o 15).toNat < 2 ^ 55)
    (he : e.toNat < 2 ^ 55)
    {path : List UInt8} (hlen : path.length < 4096) (hnz : ∀ i < path.length, path.getD i 0 ≠ 0)
    {q : Proc} (hpc : q.core.pc = o) (hfp : q.fpcr = fpcrValue) (hal : q.core.sp % 16 = 0)
    (hmap : ∀ j < 24, P.normal (q.core.sp + UInt64.ofNat j) = true)
    (hpath : ∀ j ≤ path.length,
      q.core.mem (q.core.sp + UInt64.ofNat off.val + UInt64.ofNat j) = path.getD j 0)
    (hpm : ∀ j ≤ path.length,
      P.normal (q.core.sp + UInt64.ofNat off.val + UInt64.ofNat j) = true) :
    ∃ q' ev, ProcReachWith T R P code q q' ∧ q'.fpcr = fpcrValue ∧ q'.core.io = q.core.io ∧
      q'.trace = q.trace ++ [.sys ev] ∧ ev.call = LeanExe.Linux.openatCall ∧
      ev.args = [atFdcwd, q.core.sp + UInt64.ofNat off.val, flags, UInt64.ofNat mode.val] ∧
      ev.inputs = [path ++ [0]] ∧
      ((2 ^ 31 ≤ ev.ret.toNat ∧ q'.core.pc = e) ∨
       (ev.ret.toNat < 2 ^ 31 ∧ q'.core.pc = after o 15 ∧ q'.core.sp = q.core.sp ∧
        q'.core.mem = store64 q.core.mem (slotAddr q.core.sp 2) ev.ret ∧
        (∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 16 → r ≠ 30 →
          q'.core.x r = q.core.x r))) := by
  have s1 := CodeAt.split code hc (n := 9) (by simp [movImm])
  have s2 := CodeAt.split code s1.1 (n := 5) (by simp [movImm])
  have s3 := CodeAt.split code s2.1 (n := 4) (by simp [movImm])
  have ca : code (after o 4) = some (encode (.addImm 1 31 off)) := (CodeAt.cons.mp s3.2).1
  have tail := s1.2
  have c9 : code (after o 9) = some (encode (.movz 3 mode 0)) := (CodeAt.cons.mp tail).1
  have c10 : code (after o 10) = some (encode (.movz 8 56 0)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp tail).2).1
    rwa [after_after] at this
  have c11 : code (after o 11) = some (encode (.bl g)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp tail).2).2).1
    rwa [after_after, after_after] at this
  have c12 : code (after o 12) = some (encode (.lsrImm 16 0 31)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp tail).2).2).2).1
    rwa [after_after, after_after, after_after] at this
  have c13 : code (after o 13) = some (encode (.cbnz 16 f)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp
      (CodeAt.cons.mp tail).2).2).2).2).1
    rwa [after_after, after_after, after_after, after_after] at this
  have c14 : code (after o 14) = some (encode (.str 0 31 2)) := by
    have := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp
      (CodeAt.cons.mp (CodeAt.cons.mp tail).2).2).2).2).2).1
    rwa [after_after, after_after, after_after, after_after, after_after] at this
  -- the arguments
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ :=
    run_movImm P code (d := 0) (v := atFdcwd) (by decide) s3.1 hpc
  obtain ⟨t2, r2, p2, x12, k2, sp2, mem2, io2⟩ := run_setX P code (d := 1)
    (v := t1.sp + UInt64.ofNat off.val) (by decide) (by rw [p1]; exact ca)
    (rfl : exec P (.addImm 1 31 off) t1 = _)
  have p2' : t2.pc = after o 5 := by rw [p2, p1, ← after_succ]
  obtain ⟨t3, r3, p3, x23, k3, sp3, mem3, io3⟩ :=
    run_movImm P code (d := 2) (v := flags) (by decide) s2.2 p2'
  obtain ⟨t4, r4, p4, x34, k4, sp4, mem4, io4⟩ := run_movz P code (d := 3) (v := mode) (by decide)
    (by rw [p3, after_after]; exact c9)
  obtain ⟨t5, r5, p5, x85, k5, sp5, mem5, io5⟩ := run_movz P code (d := 8) (v := 56) (by decide)
    (by rw [p4, p3, after_after, ← after_succ]; exact c10)
  have p5' : t5.pc = after o 11 := by rw [p5, p4, p3, after_after, ← after_succ, ← after_succ]
  have hsp5 : t5.sp = q.core.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have hmem5 : t5.mem = q.core.mem := by rw [mem5, mem4, mem3, mem2, mem1]
  have hio5 : t5.io = q.core.io := by rw [io5, io4, io3, io2, io1]
  have hx0 : t5.x 0 = atFdcwd := by
    rw [k5 0 (by decide), k4 0 (by decide), k3 0 (by decide), k2 0 (by decide), x01]
  have hx1 : t5.x 1 = q.core.sp + UInt64.ofNat off.val := by
    rw [k5 1 (by decide), k4 1 (by decide), k3 1 (by decide), x12, sp1]
  have hx2 : t5.x 2 = flags := by rw [k5 2 (by decide), k4 2 (by decide), x23]
  have hx3 : t5.x 3 = UInt64.ofNat mode.val := by rw [k5 3 (by decide), x34]
  have hk5 : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → t5.x r = q.core.x r :=
    fun r h0 h1 h2 h3 h8 => by rw [k5 r h8, k4 r h3, k3 r h2, k2 r h1, k1 r h0]
  have q1 : ProcReachWith T R P code q { q with core := t5 } :=
    ProcReachWith.of_reach' hdom hfp (r1.trans (r2.trans (r3.trans (r4.trans r5))))
      (by rw [p5']; exact hdom _ _ c11)
  -- the call
  obtain ⟨hpl, hrl⟩ := path_read (P := P) (m := q.core.mem)
    (S := q.core.sp + UInt64.ofNat off.val) hlen hnz hpath
  have hsys := sysCall_openat (R := R) (P := P) (p := ({ q with core := t5 } : Proc).call
    (after o 11) svc) (by
      rw [Proc.call_x _ _ _ (by decide), Proc.call_mem]
      show P.mapped (t5.x 1) ((a64Memory P).pathLength t5.mem (t5.x 1)) = true
      rw [hx1, hmem5, hpl]
      exact mapped_of_all P fun i hi => hpm i (by omega))
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_mem] at hsys
  change sysCall R P _ _ = some (Proc.ret _ _ _ (.sys ⟨_, [t5.x 0, t5.x 1, t5.x 2, t5.x 3],
    [readList t5.mem (t5.x 1) ((a64Memory P).pathLength t5.mem (t5.x 1))], [], _, []⟩)) at hsys
  rw [hx0, hx1, hx2, hx3, hmem5, hpl, hrl] at hsys
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c11 hg hdom
    (by rw [after_after]; exact hdom _ _ c12) (p := { q with core := t5 }) p5'
    (by show T.find? (fun c => c.arm64 == t5.x 8) = _; rw [x85]; exact hT) rfl hsys
  -- the test of the result and its store
  generalize hv : (R (({ q with core := t5 } : Proc).call (after o 11) svc).trace.length).ret = v
    at x0q2
  obtain ⟨u1, ru1, pu1, xu1, ku1, spu1, memu1, iou1⟩ := run_setX P code (d := 16) (by decide)
    (by rw [pq2, after_after]; exact c12) (rfl : exec P (.lsrImm 16 0 31) q2.core = _)
  have pu1' : u1.pc = after o 13 := by rw [pu1, pq2, after_after, ← after_succ]
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hfp
  have hio : u1.io = q.core.io := by rw [iou1, ioq2]; exact hio5
  by_cases hbig : v.toNat < 2 ^ 31
  · have h16 : u1.x 16 = 0 := by
      rw [xu1, x0q2]
      exact (shr31_eq_zero v).mpr hbig
    have pu2 : ({ u1 with pc := u1.pc + 4 } : State).pc = after o 14 := by
      show u1.pc + 4 = _
      rw [pu1', ← after_succ]
    have hsp : u1.sp = q.core.sp := by rw [spu1, spq2]; exact hsp5
    have e3 := exec_str_sp P (s := { u1 with pc := u1.pc + 4 }) (r := 0) (i := 2) (by decide)
      (by show u1.sp % 16 = 0; rw [hsp]; exact hal)
      (fun j hj => by show P.normal (u1.sp + _) = true; rw [hsp]; exact hmap _ (by omega))
    have ru : Reach P code q2.core _ := ru1.trans (reach_exec P code (by rw [pu1']; exact c13)
      (cbnz_next P h16) (reach_exec P code (by rw [pu2]; exact c14) e3 (.refl _)))
    have pend : u1.pc + 4 + 4 = after o 15 := by rw [pu1', ← after_succ, ← after_succ]
    refine ⟨_, ⟨LeanExe.Linux.openatCall, [atFdcwd, q.core.sp + UInt64.ofNat off.val, flags,
      UInt64.ofNat mode.val], [path ++ [0]], [], v, []⟩,
      q1.trans (rq2.trans (ProcReachWith.of_reach' hdom fq2' ru (by
        show (u1.pc + 4 + 4).toNat < _
        rw [pend]
        exact h15))), fq2', hio, by rw [trq2, ← hv], rfl, rfl, rfl,
      .inr ⟨hbig, pend, hsp, ?_, fun r h0 h1 h2 h3 h8 h16 h30 => ?_⟩⟩
    · show store64 u1.mem (slotAddr u1.sp 2) (u1.x 0) = _
      rw [memu1, memq2, hsp, ku1 0 (by decide), x0q2]
    · show u1.x r = _
      rw [ku1 r h16, kq2 r h0 h30]
      exact hk5 r h0 h1 h2 h3 h8
  · have h16 : u1.x 16 ≠ 0 := by
      rw [xu1, x0q2]
      exact fun h => hbig ((shr31_eq_zero v).mp h)
    have ru := ru1.trans (cbnz_taken P code (by rw [pu1']; exact c13) pu1' hf h16)
    exact ⟨_, ⟨LeanExe.Linux.openatCall, [atFdcwd, q.core.sp + UInt64.ofNat off.val, flags,
      UInt64.ofNat mode.val], [path ++ [0]], [], v, []⟩,
      q1.trans (rq2.trans (ProcReachWith.of_reach' hdom fq2' ru he)), fq2', hio,
      by rw [trq2, ← hv], rfl, rfl, rfl, .inl ⟨by show 2 ^ 31 ≤ v.toNat; omega, rfl⟩⟩

/-! ## Closing a descriptor -/

/-- The code of a `close` of the descriptor in the frame's slot 2 at `c`, which tests its result:
the call's event; a result other than 0 branches to `e`. -/
theorem run_close {c svc e : UInt64} {g : Fin 67108864} {f : Fin 524288}
    (hc : CodeAt code c [.ldr 0 31 2, .movz 8 57 0, .bl g, .cbnz 0 f])
    (hg : bField (after c 2) svc = .ok g) (hf : cbField (after c 3) e = .ok f)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hT : T.find? (fun c => c.arm64 == 57) = some LeanExe.Linux.closeCall)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (h4 : (after c 4).toNat < 2 ^ 55)
    (he : e.toNat < 2 ^ 55)
    {q : Proc} (hpc : q.core.pc = c) (hfp : q.fpcr = fpcrValue) (hal : q.core.sp % 16 = 0)
    (hmap : ∀ j < 24, P.normal (q.core.sp + UInt64.ofNat j) = true) :
    ∃ q' ev, ProcReachWith T R P code q q' ∧ q'.fpcr = fpcrValue ∧ q'.core.io = q.core.io ∧
      q'.trace = q.trace ++ [.sys ev] ∧ ev.call = LeanExe.Linux.closeCall ∧
      ev.args = [load64 q.core.mem (slotAddr q.core.sp 2)] ∧
      ((ev.ret ≠ 0 ∧ q'.core.pc = e) ∨
       (ev.ret = 0 ∧ q'.core.pc = after c 4 ∧ q'.core.sp = q.core.sp ∧
        q'.core.mem = q.core.mem ∧
        (∀ r : Fin 32, r ≠ 0 → r ≠ 8 → r ≠ 30 → q'.core.x r = q.core.x r))) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ := run_setX P code (d := 0) (by decide)
    (by rw [hpc]; exact c0) (exec_ldr_sp P (s := q.core) (r := 0) (i := 2) _ hal
      fun j hj => hmap _ (by omega))
  obtain ⟨t2, r2, p2, x82, k2, sp2, mem2, io2⟩ := run_movz P code (d := 8) (v := 57) (by decide)
    (by rw [p1, hpc, ← after_one]; exact c1)
  have p2' : t2.pc = after c 2 := by rw [p2, p1, hpc, after_succ c 1, after_one]
  have q1 : ProcReachWith T R P code q { q with core := t2 } :=
    ProcReachWith.of_reach' hdom hfp (r1.trans r2) (by rw [p2']; exact hdom _ _ c2)
  have hsys := sysCall_close (R := R) (P := P) (p := ({ q with core := t2 } : Proc).call
    (after c 2) svc)
  rw [Proc.call_x _ _ _ (by decide)] at hsys
  have hx0 : ({ q with core := t2 } : Proc).core.x 0 =
      load64 q.core.mem (slotAddr q.core.sp 2) := by
    show t2.x 0 = _
    rw [k2 0 (by decide), x01]
  rw [hx0] at hsys
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c2 hg hdom
    (by rw [after_after]; exact hdom _ _ c3) (p := { q with core := t2 }) p2'
    (by show T.find? (fun c => c.arm64 == t2.x 8) = _; rw [x82]; exact hT) rfl hsys
  generalize hv : (R (({ q with core := t2 } : Proc).call (after c 2) svc).trace.length).ret = v
    at x0q2
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hfp
  have hio : q2.core.io = q.core.io := by rw [ioq2]; show t2.io = _; rw [io2, io1]
  by_cases h0 : v = 0
  · have ru : Reach P code q2.core { q2.core with pc := q2.core.pc + 4 } :=
      reach_exec P code (by rw [pq2, after_after]; exact c3) (cbnz_next P (by rw [x0q2]; exact h0))
        (.refl _)
    have pend : q2.core.pc + 4 = after c 4 := by rw [pq2, after_after, ← after_succ]
    refine ⟨_, ⟨LeanExe.Linux.closeCall, [load64 q.core.mem (slotAddr q.core.sp 2)], [], [], v,
      []⟩, q1.trans (rq2.trans (ProcReachWith.of_reach' hdom fq2' ru (by
        show (q2.core.pc + 4).toNat < _
        rw [pend]
        exact h4))), fq2', hio, by rw [trq2, ← hv], rfl, rfl,
      .inr ⟨h0, pend, ?_, ?_, fun r h0' h8 h30 => ?_⟩⟩
    · show q2.core.sp = _
      rw [spq2]
      show t2.sp = _
      rw [sp2, sp1]
    · show q2.core.mem = _
      rw [memq2]
      show t2.mem = _
      rw [mem2, mem1]
    · show q2.core.x r = _
      rw [kq2 r h0' h30]
      show t2.x r = _
      rw [k2 r h8, k1 r h0']
  · have ru := cbnz_taken P code (by rw [pq2, after_after]; exact c3) (by rw [pq2, after_after]) hf
      (by rw [x0q2]; exact h0)
    exact ⟨_, ⟨LeanExe.Linux.closeCall, [load64 q.core.mem (slotAddr q.core.sp 2)], [], [], v,
      []⟩, q1.trans (rq2.trans (ProcReachWith.of_reach' hdom fq2' ru he)), fq2', hio,
      by rw [trq2, ← hv], rfl, rfl, .inl ⟨h0, rfl⟩⟩

end LeanExe.A64
