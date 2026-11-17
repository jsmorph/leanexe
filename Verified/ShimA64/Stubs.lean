import Verified.ShimA64.Machine

/-!
The stubs of the stream functions against the shim's host environment: each
stub of `LeanExe/A64/Wasi.lean` meets `Machine.StubSim` for its host function of `linuxEnv` on
`shimMachine`.  A request that `readInvoke` or `writeInvoke` refuses reaches the trap stub with
the store unchanged.  An accepted one reaches `SVC #0` with the call of `LeanExe.Linux.table`
whose event is the shim's `readEvent` or `writeEvent`, the kernel's writes land in the store's
memory as `Linux.step` on `shimMemory` places them, and the result reaches the return with the
WASI reply, with the count stored at guest address 8 when the errno is 0, or the trap stub with
the shim's trap.  The
stub of `proc_exit` reaches the exit word with the accepted status or with 1.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

variable {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {area base : UInt64} {size : Nat}

/-- A run of the program's model to the trap stub from a state that holds the store `st` ends in a
trap of the shim with that store. -/
theorem trapped_shim {S : Shared} {cap : Nat} {gts : List ValueType}
    {st : Store (Observed LinuxWorld)} {q : Proc}
    (hsr : (shimMachine R P code hdom hk area base size).SR cap gts st q) {s : State}
    (hr : Reach P code q.core s) (hpc : s.pc = S.trapUnreachable) (hio : s.io = q.core.io) :
    ∃ q', (shimMachine R P code hdom hk area base size).Rch q q' ∧
      ((shimMachine R P code hdom hk area base size).core q').io =
        ((shimMachine R P code hdom hk area base size).core q).io ∧
      (shimMachine R P code hdom hk area base size).Trapped S st shimTrap q' :=
  ⟨{ q with core := s }, ProcRunWith.ofReach hsr.2.1 hr, hio,
    .inr (.inr (.inr ⟨rfl, hpc⟩)), hsr.2.1, hsr.2.2.2⟩

/-- The store relation keeps no part of the store's host state. -/
theorem StoreRel.withHost {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s : State} (h : StoreRel P cap gts st s) (host : α) :
    StoreRel P cap gts { st with host } s :=
  ⟨h.caps, h.cap_lt, h.glen, h.pages, h.size, h.types, h.globals, h.bytes, h.mapped, h.below⟩

theorem memBytes_readBytes (m : Mem) : ∀ (n p : Nat), memBytes m p n = m.readBytes p n
  | 0, _ => rfl
  | n + 1, p => by
    rw [memBytes, memBytes_readBytes m n (p + 1), Mem.readBytes, Mem.readBytes,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    congr 1
    omega

/-- The address of byte `p` of the memory of the area at `area`. -/
theorem guest_addr (area : UInt64) (p : UInt32) :
    area + UInt64.ofNat 4096 + p.toUInt64 = area + UInt64.ofNat (4096 + p.toNat) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  omega

/-- The bytes `[b0, b1, b2, b3]` that the count's store writes, as those of `write32`. -/
theorem count_bytes {r : UInt64} (hr : r.toNat < 2 ^ 32) :
    [r.toUInt8, (r >>> UInt64.ofNat 8).toUInt8, (r >>> UInt64.ofNat 16).toUInt8,
      (r >>> UInt64.ofNat 24).toUInt8] =
    [(r.toUInt32 &&& 0xFF).toUInt8, ((r.toUInt32 >>> 8) &&& 0xFF).toUInt8,
      ((r.toUInt32 >>> 16) &&& 0xFF).toUInt8, ((r.toUInt32 >>> 24) &&& 0xFF).toUInt8] := by
  have e : r = r.toUInt32.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    omega
  conv => lhs; rw [e]
  exact strb4_bytes r.toUInt32

/-- `Linux.isError` of a result above a count below `2^32` is its negation's lying at most
4095. -/
theorem isError_iff {r c : UInt64} (hc : c.toNat < 2 ^ 32) (hlt : c < r) :
    Linux.isError r = true ↔ 0 - r ≤ 4095 := by
  simp only [Linux.isError, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_sub,
    UInt64.reduceToNat]
  rw [UInt64.lt_iff_toNat_lt] at hlt
  have := r.toNat_lt
  simp only [Nat.reducePow] at *
  omega

/-- An errno of the shim fits the 32-bit result. -/
theorem errno_toUInt64 (x : UInt64) : (errnoOf x).toUInt32.toUInt64 = errnoOf x := by
  have := (errnoOf_valid x).1
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  omega

/-- Four values of type `i32` from their typing. -/
theorem typed_i32x4 {args : List Value} (hlen : args.length = 4)
    (hty : Typed [.i32, .i32, .i32, .i32] args) :
    ∃ a0 a1 a2 a3 : UInt32, args = [.i32 a0, .i32 a1, .i32 a2, .i32 a3] := by
  match args, hlen, hty with
  | [v0, v1, v2, v3], _, ⟨t0, t1, t2, t3, _⟩ =>
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := by
      cases v0 <;> first | exact ⟨_, rfl⟩ | exact t0.elim
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := by
      cases v1 <;> first | exact ⟨_, rfl⟩ | exact t1.elim
    obtain ⟨a2, rfl⟩ : ∃ a, v2 = .i32 a := by
      cases v2 <;> first | exact ⟨_, rfl⟩ | exact t2.elim
    obtain ⟨a3, rfl⟩ : ∃ a, v3 = .i32 a := by
      cases v3 <;> first | exact ⟨_, rfl⟩ | exact t3.elim
    exact ⟨a0, a1, a2, a3, rfl⟩

/-- `readInvoke` of a request other than `fd_read` of descriptor 0 with the iovec at 0, one iovec,
and the count at 8 is the shim's trap. -/
theorem readInvoke_refused (L : ShimLayout) (R : Linux.Replies) (st : Store (Observed LinuxWorld))
    {a0 a1 a2 a3 : UInt32} (h : ¬ (a0 = 0 ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 8)) :
    readInvoke L R st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] = .Trap st shimTrap := by
  unfold readInvoke
  split
  · rename_i heq
    simp only [List.cons.injEq, Value.i32.injEq, and_true] at heq
    exact absurd heq h
  · rfl

/-- Bytes written below a limit keep every byte from the limit up. -/
theorem writeList_below {m : UInt64 → UInt8} {a : UInt64} {bs : List UInt8} {lim c : UInt64}
    (ha : a.toNat + bs.length ≤ lim.toNat) (hc : lim.toNat ≤ c.toNat) :
    writeList m a bs c = m c :=
  writeList_other m bs a c (by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega)

theorem toUInt64_eq {a b : UInt32} (h : a.toUInt64 = b.toUInt64) : a = b := by
  apply UInt32.toNat_inj.mp
  have := congrArg UInt64.toNat h
  simpa using this

/-- The stub of `fd_read` stands for the shim's `fd_read` of descriptor 0. -/
theorem readStub_sim (S : Shared) (n : Nat) {rd svc en : UInt64} {is : List Instr}
    (hg : readStub rd svc S.trapUnreachable en = .ok is) (hcode : CodeAt code rd is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (hU : P.normal P.uart = false) (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R P code hdom hk area base size).StubSim S n [.i32, .i32, .i32, .i32] [.i32]
      (readFn (layoutAt area) R) rd := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = rd at hpc
  change StackOk P q.core at hstk
  obtain ⟨a0, a1, a2, a3, rfl⟩ := typed_i32x4 hlen hty
  have x0 : q.core.x 0 = a0.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = a1.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = a2.toUInt64 := hregs 2 (by simp)
  have x3 : q.core.x 3 = a3.toUInt64 := hregs 3 (by simp)
  obtain ⟨hst, hf, h17, htr⟩ := hsr
  refine .inr ?_
  obtain ⟨f0, f1, f3, f5, f17, f19, checks, call, tail, hf0, hf1, hf3, hf5, hc, hf17, hf19,
    hcall, htl, rfl⟩ := readStub_ok hg
  obtain ⟨g1, g2, hg1, hg2, rfl⟩ := bufferChecks_ok hc
  obtain ⟨gb, hgb, rfl⟩ := bufferCall_ok hcall
  obtain ⟨t1, t2, t3, ht1, ht2, ht3, rfl⟩ := resultTail_ok htl
  have cA := CodeAt.split code hcode (n := 28) (by simp)
  have cB := CodeAt.split code cA.1 (n := 21) (by simp)
  have cC := CodeAt.split code cB.1 (n := 17) (by simp)
  have cD := CodeAt.split code cC.1 (n := 6) (by simp)
  have hinv : (readFn (layoutAt area) R).invoke st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] =
      readInvoke (layoutAt area) R st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] := rfl
  rw [hinv]
  obtain ⟨u1, r1, k1, sp1, m1, io1, p1⟩ := run_readHead P code cD.1 hf0 hf1 hf3 hf5 hpc
  rw [x0, x1, x2, x3] at p1
  by_cases hreq : a0 = 0 ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 8
  swap
  · rw [if_neg (fun h => hreq ⟨toUInt64_eq h.1, toUInt64_eq h.2.1, toUInt64_eq h.2.2.1,
      toUInt64_eq h.2.2.2⟩)] at p1
    rw [readInvoke_refused _ _ _ hreq]
    exact trapped_shim ⟨hst, hf, h17, htr⟩ r1 p1 io1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hreq
  rw [if_pos (by decide)] at p1
  have hst1 : StoreRel P S.cap S.globalTypes st u1 := hst.regs (k1 17) (k1 18) m1
  obtain ⟨u2, r2, sp2, m2, io2, k2, hc2⟩ := run_bufferChecks P code cD.2 hg1 hg2 hst1 p1
  have hpg := hst.pages
  have hcap := hst.cap_lt
  simp only [readInvoke]
  have h16 : 16 ≤ st.mem.pages * 65536 := by omega
  have hio2 : u2.io = q.core.io := by rw [io2, io1]
  by_cases hb : (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ st.mem.pages * 65536 ∧
      (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ 2 ^ 32
  swap
  · rw [if_neg hb] at hc2
    rw [if_neg (fun h => hb ⟨h.2.1, h.2.2.1⟩)]
    exact trapped_shim ⟨hst, hf, h17, htr⟩ (r1.trans r2) hc2 hio2
  rw [if_pos hb] at hc2
  obtain ⟨p2, x10, x11⟩ := hc2
  rw [after_after] at p2
  obtain ⟨u3, r3, k3, sp3, m3, io3, hc3⟩ := run_readLow P code cC.2
    (by rw [after_after]; exact hf17) (by rw [after_after]; exact hf19) p2
  rw [x10, x11] at hc3
  have hlowIff : ((st.mem.read32 4).toUInt64 = 0 ∨ 16 ≤ (st.mem.read32 0).toUInt64) ↔
      (st.mem.read32 4 = 0 ∨ 16 ≤ (st.mem.read32 0).toNat) := by
    simp only [← UInt64.toNat_inj, UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64,
      ← UInt32.toNat_inj, UInt64.reduceToNat, UInt32.reduceToNat]
  have hio3 : u3.io = q.core.io := by rw [io3, hio2]
  by_cases hlow : st.mem.read32 4 = 0 ∨ 16 ≤ (st.mem.read32 0).toNat
  swap
  · rw [if_neg (fun h => hlow (hlowIff.mp h))] at hc3
    rw [if_neg (fun h => hlow h.2.2.2)]
    exact trapped_shim ⟨hst, hf, h17, htr⟩ (r1.trans (r2.trans r3)) hc3 hio3
  rw [if_pos (hlowIff.mpr hlow)] at hc3
  obtain ⟨p3, x03⟩ := hc3
  rw [after_after] at p3
  rw [if_pos ⟨h16, hb.1, hb.2, hlow⟩]
  generalize hptr : st.mem.read32 0 = ptr at *
  generalize hlen : st.mem.read32 4 = len at *
  -- registers before the call
  obtain ⟨u4, r4, p4, x14, x24, x84, x194, k4, sp4, m4, io4⟩ := run_bufferCall P code cB.2 p3
  rw [after_after] at p4
  have k21 : ∀ r : Fin 32, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → u2.x r = q.core.x r :=
    fun r h9 h10 h11 h12 h13 => by rw [k2 r h9 h10 h11 h12 h13, k1]
  have u4x17 : u4.x 17 = area := by
    rw [k4 17 (by decide) (by decide) (by decide) (by decide), k3 17 (by decide),
      k21 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h17
  have u4x1 : u4.x 1 = area + UInt64.ofNat 4096 + ptr.toUInt64 := by
    rw [x14, k3 17 (by decide), k3 10 (by decide), x10,
      k21 17 (by decide) (by decide) (by decide) (by decide) (by decide), h17]
  have u4x2 : u4.x 2 = len.toUInt64 := by rw [x24, k3 11 (by decide), x11]
  have u4x0 : u4.x 0 = 0 := by
    rw [k4 0 (by decide) (by decide) (by decide) (by decide), x03]
  have u4x30 : u4.x 30 = q.core.x 30 := by
    rw [k4 30 (by decide) (by decide) (by decide) (by decide), k3 30 (by decide),
      k21 30 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have u4x18 : u4.x 18 = q.core.x 18 := by
    rw [k4 18 (by decide) (by decide) (by decide) (by decide), k3 18 (by decide),
      k21 18 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have u4mem : u4.mem = q.core.mem := by rw [m4, m3, m2, m1]
  have r14 : Reach P code q.core u4 := r1.trans (r2.trans (r3.trans r4))
  -- the call
  have cbl : code (after rd 27) = some (encode (.bl gb)) := by
    have := cB.2 6 (by simp)
    rw [after_after] at this
    simpa using this
  have cnext := cA.2 0 (by simp)
  rw [after_zero] at cnext
  have hnext : (after (after rd 27) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hT : Linux.table.find? (fun c => c.arm64 == ({ q with core := u4 } : Proc).core.x 8) =
      some Linux.readCall := by
    show Linux.table.find? (fun c => c.arm64 == u4.x 8) = _
    rw [x84, show UInt64.ofNat (63 : Fin 65536).val = 63 by decide]
    exact table_read
  have hlenle : ptr.toNat + len.toNat ≤ S.cap * 65536 :=
    Nat.le_trans hb.1 (Nat.mul_le_mul_right _ hpg.2)
  have hmapR : P.mapped ((({ q with core := u4 } : Proc).call (after rd 27) svc).core.x 1)
      ((({ q with core := u4 } : Proc).call (after rd 27) svc).core.x 2).toNat = true := by
    rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
    show P.mapped (u4.x 1) (u4.x 2).toNat = true
    rw [u4x1, u4x2, guest_addr]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, UInt32.toNat_toUInt64] at hi
    rw [← h17, add_ofNat_add]
    exact hst.mapped _ (by unfold areaSize; omega)
  obtain ⟨q5, rq5, p5, x05, x305, k5, sp5, m5, io5, f5, tr5⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl
      (by rw [after_after] at hgb; exact hgb) hdom hnext (p := { q with core := u4 }) p4 hT rfl
      (sysCall_read hmapR)
  simp only [Proc.call_trace, Proc.call_mem] at x05 m5 tr5
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)] at m5 tr5
  have hlenk : q.trace.length = st.host.world.events.length := by rw [htr.1, List.length_map]
  change q5.core.mem = writeList u4.mem (u4.x 1) _ at m5
  change q5.core.x 0 = (R q.trace.length).ret at x05
  rw [hlenk] at x05 m5 tr5
  generalize hRk : R st.host.world.events.length = rk at x05 m5 tr5 ⊢
  have hout : (u4.x 2).toNat = len.toNat := by rw [u4x2, UInt32.toNat_toUInt64]
  have hlenle' : ptr.toNat + len.toNat ≤ S.cap * 65536 := hlenle
  have hrl : readList u4.mem (u4.x 1) len.toNat = st.mem.readBytes ptr.toNat len.toNat := by
    rw [u4x1, guest_addr, u4mem, ← h17, readList_bytes P hst len.toNat ptr.toNat hlenle',
      memBytes_readBytes]
  have hev : (⟨Linux.readCall, [u4.x 0, u4.x 1, u4.x 2], [], readList u4.mem (u4.x 1)
      (u4.x 2).toNat, rk.ret, (List.range (u4.x 2).toNat).map rk.bytes⟩ : Linux.Event) =
      readEvent (layoutAt area) st.mem ptr len rk := by
    rw [hout, hrl, u4x0, u4x1, u4x2]
    rfl
  change q5.trace = q.trace ++ [A64.Event.sys ⟨Linux.readCall, [u4.x 0, u4.x 1, u4.x 2], [],
    readList u4.mem (u4.x 1) (u4.x 2).toNat, rk.ret, (List.range (u4.x 2).toNat).map rk.bytes⟩]
    at tr5
  rw [hev] at tr5
  change q5.core.mem = writeList u4.mem (u4.x 1) ((List.range (u4.x 2).toNat).map rk.bytes)
    at m5
  rw [hout, u4x1, guest_addr, u4mem, ← h17] at m5
  rw [step_read (layoutAt area) st.mem ptr len rk hb.1]
  dsimp only [readEvent]
  -- the result
  have hq5pc : q5.core.pc = after rd 28 := by rw [p5, after_after]
  have q5x17 : q5.core.x 17 = area := by
    rw [k5 17 (by decide) (by decide)]
    exact u4x17
  have q5x18 : q5.core.x 18 = q.core.x 18 := by
    rw [k5 18 (by decide) (by decide)]
    exact u4x18
  have hmap4 : ∀ k < 4, P.normal (q5.core.x 17 + UInt64.ofNat (4104 + k)) = true :=
    fun k hk => by
      rw [q5x17, ← h17]
      exact hst.mapped _ (by unfold areaSize; omega)
  obtain ⟨u6, r6, sp6, io6, x176, x186, hcases⟩ :=
    run_resultTail P code cA.2 ht1 ht2 ht3 hen hq5pc hmap4 hU
  have q5x11 : q5.core.x 11 = len.toUInt64 := by
    rw [k5 11 (by decide) (by decide)]
    show u4.x 11 = _
    rw [k4 11 (by decide) (by decide) (by decide) (by decide), k3 11 (by decide), x11]
  have q5x19 : q5.core.x 19 = q.core.x 30 := by
    rw [k5 19 (by decide) (by decide)]
    show u4.x 19 = _
    rw [x194, k3 30 (by decide), k21 30 (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  rw [x05, q5x11, q5x19] at hcases
  have hf5 : q5.fpcr = fpcrValue := by rw [f5]; exact hf
  have hrch : (shimMachine R P code hdom hk area base size).Rch q { q5 with core := u6 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r14)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq5 hf5) (ProcRunWith.ofReach hf5 r6))
  have hsp6 : u6.sp = q.core.sp := by rw [sp6, sp5]; show u4.sp = _; rw [sp4, sp3, sp2, sp1]
  have hio6 : u6.io = q.core.io := by rw [io6, io5]; show u4.io = _; rw [io4, hio3]
  have h186 : u6.x 18 = q.core.x 18 := by rw [x186, q5x18]
  have hlim := hst.below
  have hstk2 := hstk.limit
  have harea : (q.core.x 17 + UInt64.ofNat (4096 + ptr.toNat)).toNat + len.toNat ≤
      (q.core.x 18).toNat := by
    rw [hst.toNat_addr (j := 4096 + ptr.toNat) (by unfold areaSize; omega)]
    unfold areaSize at hlim
    omega
  have hkern : ∀ a : UInt64, q.core.sp.toNat ≤ a.toNat → q5.core.mem a = q.core.mem a := by
    intro a ha
    rw [m5]
    exact writeList_below (lim := q.core.x 18) (by simpa using harea) (by omega)
  have hst5 : StoreRel P S.cap S.globalTypes
      { st with mem := st.mem.writeBytes ptr.toNat ((List.range len.toNat).map rk.bytes) }
      q5.core :=
    hst.ofWriteList P ((List.range len.toNat).map rk.bytes)
      (by simpa only [List.length_map, List.length_range] using hb.1)
      (by rw [q5x17, h17]) q5x18 m5
  have hwithin : ∀ e ∈ st.host.world.events ++ [readEvent (layoutAt area) st.mem ptr len rk],
      WritesWithin (layoutAt area) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact readEvent_writesWithin (layoutAt area) st.mem ptr len rk (by omega)
  have htrace : ({ q5 with core := u6 } : Proc).trace =
      (st.host.world.events ++ [readEvent (layoutAt area) st.mem ptr len rk]).map
        A64.Event.sys := by
    show q5.trace = _
    rw [tr5, htr.1, List.map_append]
    rfl
  rcases hcases with ⟨hle, p6, x06, m6⟩ | ⟨hgt, h4095, p6, x06, m6⟩ | ⟨hgt, hbig, p6, m6⟩
  · -- a count
    have hret : rk.ret.toNat ≤ len.toNat := by
      simpa only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64] using hle
    have hrr : readReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .returned 0 (bytesOfList (((List.range len.toNat).map rk.bytes).take rk.ret.toNat)) := by
      unfold readReply
      rw [if_pos (by rw [UInt32.toNat_toUInt64]; exact hret)]
    rw [hrr]
    dsimp only
    rw [if_pos rfl]
    have hsz : UInt32.ofNat (bytesOfList (((List.range len.toNat).map rk.bytes).take
        rk.ret.toNat)).data.size = rk.ret.toUInt32 := by
      simp only [bytesOfList_size, List.length_take, List.length_map, List.length_range]
      rw [Nat.min_eq_left hret]
      rfl
    have hret32 : rk.ret.toNat < 2 ^ 32 := by
      have := len.toNat_lt
      omega
    rw [hsz, write32_writeBytes]
    have hcnt : (q5.core.x 17 + UInt64.ofNat 4104).toNat + 4 ≤ (q.core.x 18).toNat := by
      rw [q5x17, ← h17, hst.toNat_addr (j := 4104) (by unfold areaSize; omega)]
      unfold areaSize at hlim
      omega
    refine ⟨{ q5 with core := u6 }, hrch, ⟨p6, hsp6, h186, hio6, fun a ha => ?_, by simp,
      ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, ?_, ?_, ?_, htrace, ?_⟩
    · show u6.mem a = q.core.mem a
      have ha' : q.core.sp.toNat ≤ a.toNat := by
        have := ha
        simp only [Nat.mul_zero, Nat.add_zero] at this
        exact this
      rw [m6, writeList_below (lim := q.core.x 18) (by simpa using hcnt) (by omega)]
      exact hkern a ha'
    · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      show u6.x 0 = (0 : UInt64).toUInt32.toUInt64
      rw [x06]
      rfl
    · exact StoreRel.withHost (hst5.ofWriteList P [(rk.ret.toUInt32 &&& 0xFF).toUInt8,
        ((rk.ret.toUInt32 >>> 8) &&& 0xFF).toUInt8, ((rk.ret.toUInt32 >>> 16) &&& 0xFF).toUInt8,
        ((rk.ret.toUInt32 >>> 24) &&& 0xFF).toUInt8] (p := 8)
        (by simp only [List.length_cons, List.length_nil, Mem.writeBytes]; omega) x176 x186
        (by rw [m6, count_bytes hret32])) _
    · show q5.fpcr = fpcrValue
      exact hf5
    · show u6.x 17 = area
      rw [x176, q5x17]
    · intro e he
      exact hwithin e he
  · -- an error
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hgt
      omega
    have hErr : Linux.isError rk.ret = true :=
      (isError_iff (c := len.toUInt64) (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt)
        hgt).mpr h4095
    have hrr : readReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .returned (errnoOf (0 - rk.ret)) Bytes.empty := by
      unfold readReply
      rw [if_neg hnot, if_pos hErr]
    rw [hrr]
    dsimp only
    rw [if_neg (errnoOf_valid _).2]
    refine ⟨{ q5 with core := u6 }, hrch, ⟨p6, hsp6, h186, hio6, fun a ha => ?_, by simp,
      ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, ?_, ?_, ?_, htrace, ?_⟩
    · show u6.mem a = q.core.mem a
      rw [m6]
      exact hkern a (by
        have := ha
        simp only [Nat.mul_zero, Nat.add_zero] at this
        exact this)
    · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      show u6.x 0 = (errnoOf (0 - rk.ret)).toUInt32.toUInt64
      rw [x06, errno_toUInt64, errnoOf_lookup]
    · exact StoreRel.withHost (hst5.regs x176 x186 m6) _
    · show q5.fpcr = fpcrValue
      exact hf5
    · show u6.x 17 = area
      rw [x176, q5x17]
    · intro e he
      exact hwithin e he
  · -- a trap of the shim
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hgt
      omega
    have hErr : Linux.isError rk.ret = false := by
      cases h : Linux.isError rk.ret with
      | false => rfl
      | true =>
        exact absurd ((isError_iff (c := len.toUInt64)
          (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt) hgt).mp h)
          (UInt64.not_le.mpr hbig)
    have hrr : readReply len.toUInt64 rk.ret ((List.range len.toNat).map rk.bytes) =
        .trapped shimTrap Bytes.empty := by
      unfold readReply
      rw [if_neg hnot, if_neg (by rw [hErr]; decide)]
    rw [hrr]
    dsimp only
    exact ⟨{ q5 with core := u6 }, hrch, hio6, .inr (.inr (.inr ⟨rfl, p6⟩)), hf5,
      htrace, hwithin⟩

/-- `writeInvoke` of a request other than `fd_write` of descriptor 1 or 2 with the iovec at 0, one
iovec, and the count at 8 is the shim's trap. -/
theorem writeInvoke_refused (L : ShimLayout) (R : Linux.Replies)
    (st : Store (Observed LinuxWorld)) {a0 a1 a2 a3 : UInt32}
    (h : ¬ ((a0 = 1 ∨ a0 = 2) ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 8)) :
    writeInvoke L R st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] = .Trap st shimTrap := by
  unfold writeInvoke
  split
  · rename_i heq
    simp only [List.cons.injEq, Value.i32.injEq, and_true] at heq
    exact absurd ⟨.inl heq.1, heq.2⟩ h
  · rename_i heq
    simp only [List.cons.injEq, Value.i32.injEq, and_true] at heq
    exact absurd ⟨.inr heq.1, heq.2⟩ h
  · rfl

/-- `writeInvoke` of an accepted request is the shim's write to the stream of its descriptor. -/
theorem writeInvoke_accepted (L : ShimLayout) (R : Linux.Replies)
    (st : Store (Observed LinuxWorld)) {a0 : UInt32} (h : a0 = 1 ∨ a0 = 2) :
    ∃ out : LeanExe.Wasi.Output, out.fd = a0.toUInt64 ∧
      writeInvoke L R st [.i32 a0, .i32 0, .i32 1, .i32 8] = writeOutput L R out st := by
  rcases h with rfl | rfl
  · exact ⟨.stdout, rfl, rfl⟩
  · exact ⟨.stderr, rfl, rfl⟩

/-- The stub of `fd_write` stands for the shim's `fd_write` to descriptor 1 or 2. -/
theorem writeStub_sim (S : Shared) (n : Nat) {wr svc en : UInt64} {is : List Instr}
    (hg : writeStub wr svc S.trapUnreachable en = .ok is) (hcode : CodeAt code wr is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (hU : P.normal P.uart = false) :
    (shimMachine R P code hdom hk area base size).StubSim S n [.i32, .i32, .i32, .i32] [.i32]
      (writeFn (layoutAt area) R) wr := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = wr at hpc
  change StackOk P q.core at hstk
  obtain ⟨a0, a1, a2, a3, rfl⟩ := typed_i32x4 hlen hty
  have x0 : q.core.x 0 = a0.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = a1.toUInt64 := hregs 1 (by simp)
  have x2 : q.core.x 2 = a2.toUInt64 := hregs 2 (by simp)
  have x3 : q.core.x 3 = a3.toUInt64 := hregs 3 (by simp)
  obtain ⟨hst, hf, h17, htr⟩ := hsr
  refine .inr ?_
  obtain ⟨f2, f3, f5, f7, checks, call, tail, hf2, hf3, hf5, hf7, hc, hcall, htl, rfl⟩ :=
    writeStub_ok hg
  obtain ⟨g1, g2, hg1, hg2, rfl⟩ := bufferChecks_ok hc
  obtain ⟨gb, hgb, rfl⟩ := bufferCall_ok hcall
  obtain ⟨t1, t2, t3, ht1, ht2, ht3, rfl⟩ := resultTail_ok htl
  have cA := CodeAt.split code hcode (n := 26) (by simp)
  have cB := CodeAt.split code cA.1 (n := 19) (by simp)
  have cD := CodeAt.split code cB.1 (n := 8) (by simp)
  have hinv : (writeFn (layoutAt area) R).invoke st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] =
      writeInvoke (layoutAt area) R st [.i32 a0, .i32 a1, .i32 a2, .i32 a3] := rfl
  rw [hinv]
  obtain ⟨u1, r1, k1, sp1, m1, io1, p1⟩ := run_writeHead P code cD.1 hf2 hf3 hf5 hf7 hpc
  rw [x0, x1, x2, x3] at p1
  have h1u : (a0.toUInt64 = 1 ∨ a0.toUInt64 = 2) ↔ (a0 = 1 ∨ a0 = 2) := by
    constructor
    · rintro (h | h)
      · exact .inl (toUInt64_eq h)
      · exact .inr (toUInt64_eq h)
    · rintro (rfl | rfl)
      · exact .inl rfl
      · exact .inr rfl
  by_cases hreq : (a0 = 1 ∨ a0 = 2) ∧ a1 = 0 ∧ a2 = 1 ∧ a3 = 8
  swap
  · rw [if_neg (fun h => hreq ⟨h1u.mp h.1, toUInt64_eq h.2.1, toUInt64_eq h.2.2.1,
      toUInt64_eq h.2.2.2⟩)] at p1
    rw [writeInvoke_refused _ _ _ hreq]
    exact trapped_shim ⟨hst, hf, h17, htr⟩ r1 p1 io1
  obtain ⟨hd, rfl, rfl, rfl⟩ := hreq
  rw [if_pos ⟨h1u.mpr hd, rfl, rfl, rfl⟩] at p1
  obtain ⟨out, hfd, hw⟩ := writeInvoke_accepted (layoutAt area) R st hd
  rw [hw]
  have hst1 : StoreRel P S.cap S.globalTypes st u1 :=
    hst.regs (k1 17 (by decide)) (k1 18 (by decide)) m1
  obtain ⟨u2, r2, sp2, m2, io2, k2, hc2⟩ := run_bufferChecks P code cD.2 hg1 hg2 hst1 p1
  have hpg := hst.pages
  have hcap := hst.cap_lt
  simp only [writeOutput]
  have h16 : 16 ≤ st.mem.pages * 65536 := by omega
  have hio2 : u2.io = q.core.io := by rw [io2, io1]
  by_cases hb : (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ st.mem.pages * 65536 ∧
      (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ 2 ^ 32
  swap
  · rw [if_neg hb] at hc2
    rw [if_neg (fun h => hb ⟨h.2.1, h.2.2⟩)]
    exact trapped_shim ⟨hst, hf, h17, htr⟩ (r1.trans r2) hc2 hio2
  rw [if_pos hb] at hc2
  obtain ⟨p2, x10, x11⟩ := hc2
  rw [after_after] at p2
  rw [if_pos ⟨h16, hb.1, hb.2⟩]
  generalize hptr : st.mem.read32 0 = ptr at *
  generalize hlen : st.mem.read32 4 = len at *
  obtain ⟨u4, r4, p4, x14, x24, x84, x194, k4, sp4, m4, io4⟩ := run_bufferCall P code cB.2 p2
  rw [after_after] at p4
  have k21 : ∀ r : Fin 32, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → u2.x r = q.core.x r :=
    fun r h9 h10 h11 h12 h13 => by rw [k2 r h9 h10 h11 h12 h13, k1 r h9]
  have u4x17 : u4.x 17 = area := by
    rw [k4 17 (by decide) (by decide) (by decide) (by decide),
      k21 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact h17
  have u4x1 : u4.x 1 = area + UInt64.ofNat 4096 + ptr.toUInt64 := by
    rw [x14, x10, k21 17 (by decide) (by decide) (by decide) (by decide) (by decide), h17]
  have u4x2 : u4.x 2 = len.toUInt64 := by rw [x24, x11]
  have u4x0 : u4.x 0 = out.fd := by
    rw [k4 0 (by decide) (by decide) (by decide) (by decide),
      k21 0 (by decide) (by decide) (by decide) (by decide) (by decide), x0, hfd]
  have u4x18 : u4.x 18 = q.core.x 18 := by
    rw [k4 18 (by decide) (by decide) (by decide) (by decide),
      k21 18 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have u4mem : u4.mem = q.core.mem := by rw [m4, m2, m1]
  have r14 : Reach P code q.core u4 := r1.trans (r2.trans r4)
  have cbl : code (after wr 25) = some (encode (.bl gb)) := by
    have := cB.2 6 (by simp)
    rw [after_after] at this
    simpa using this
  have cnext := cA.2 0 (by simp)
  rw [after_zero] at cnext
  have hnext : (after (after wr 25) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  have hT : Linux.table.find? (fun c => c.arm64 == ({ q with core := u4 } : Proc).core.x 8) =
      some Linux.writeCall := by
    show Linux.table.find? (fun c => c.arm64 == u4.x 8) = _
    rw [x84, show UInt64.ofNat (64 : Fin 65536).val = 64 by decide]
    exact table_write
  have hlenle : ptr.toNat + len.toNat ≤ S.cap * 65536 :=
    Nat.le_trans hb.1 (Nat.mul_le_mul_right _ hpg.2)
  have hmapW : P.mapped ((({ q with core := u4 } : Proc).call (after wr 25) svc).core.x 1)
      ((({ q with core := u4 } : Proc).call (after wr 25) svc).core.x 2).toNat = true := by
    rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
    show P.mapped (u4.x 1) (u4.x 2).toNat = true
    rw [u4x1, u4x2, guest_addr]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, UInt32.toNat_toUInt64] at hi
    rw [← h17, add_ofNat_add]
    exact hst.mapped _ (by unfold areaSize; omega)
  obtain ⟨q5, rq5, p5, x05, x305, k5, sp5, m5, io5, f5, tr5⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl
      (by rw [after_after] at hgb; exact hgb) hdom hnext (p := { q with core := u4 }) p4 hT rfl
      (sysCall_write hmapW)
  simp only [Proc.call_trace, Proc.call_mem] at x05 m5 tr5
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_x _ _ _ (by decide)] at tr5
  have hlenk : q.trace.length = st.host.world.events.length := by rw [htr.1, List.length_map]
  change q5.core.x 0 = (R q.trace.length).ret at x05
  rw [hlenk] at x05 tr5
  generalize hRk : R st.host.world.events.length = rk at x05 tr5 ⊢
  have hout : (u4.x 2).toNat = len.toNat := by rw [u4x2, UInt32.toNat_toUInt64]
  have hrl : readList u4.mem (u4.x 1) len.toNat = st.mem.readBytes ptr.toNat len.toNat := by
    rw [u4x1, guest_addr, u4mem, ← h17, readList_bytes P hst len.toNat ptr.toNat hlenle,
      memBytes_readBytes]
  have hev : (⟨Linux.writeCall, [u4.x 0, u4.x 1, u4.x 2],
      [readList u4.mem (u4.x 1) (u4.x 2).toNat], [], rk.ret, []⟩ : Linux.Event) =
      writeEvent (layoutAt area) st.mem out.fd ptr len rk := by
    rw [hout, hrl, u4x0, u4x1, u4x2]
    rfl
  change q5.trace = q.trace ++ [A64.Event.sys ⟨Linux.writeCall, [u4.x 0, u4.x 1, u4.x 2],
    [readList u4.mem (u4.x 1) (u4.x 2).toNat], [], rk.ret, []⟩] at tr5
  rw [hev] at tr5
  change q5.core.mem = u4.mem at m5
  rw [u4mem] at m5
  rw [step_write (layoutAt area) st.mem out.fd ptr len rk hb.1]
  dsimp only [writeEvent]
  have hq5pc : q5.core.pc = after wr 26 := by rw [p5, after_after]
  have q5x17 : q5.core.x 17 = area := by
    rw [k5 17 (by decide) (by decide)]
    exact u4x17
  have q5x18 : q5.core.x 18 = q.core.x 18 := by
    rw [k5 18 (by decide) (by decide)]
    exact u4x18
  have hmap4 : ∀ k < 4, P.normal (q5.core.x 17 + UInt64.ofNat (4104 + k)) = true :=
    fun k hk => by
      rw [q5x17, ← h17]
      exact hst.mapped _ (by unfold areaSize; omega)
  obtain ⟨u6, r6, sp6, io6, x176, x186, hcases⟩ :=
    run_resultTail P code cA.2 ht1 ht2 ht3 hen hq5pc hmap4 hU
  have q5x11 : q5.core.x 11 = len.toUInt64 := by
    rw [k5 11 (by decide) (by decide)]
    show u4.x 11 = _
    rw [k4 11 (by decide) (by decide) (by decide) (by decide), x11]
  have q5x19 : q5.core.x 19 = q.core.x 30 := by
    rw [k5 19 (by decide) (by decide)]
    show u4.x 19 = _
    rw [x194, k21 30 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [x05, q5x11, q5x19] at hcases
  have hf5 : q5.fpcr = fpcrValue := by rw [f5]; exact hf
  have hrch : (shimMachine R P code hdom hk area base size).Rch q { q5 with core := u6 } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r14)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq5 hf5) (ProcRunWith.ofReach hf5 r6))
  have hsp6 : u6.sp = q.core.sp := by rw [sp6, sp5]; show u4.sp = _; rw [sp4, sp2, sp1]
  have hio6 : u6.io = q.core.io := by rw [io6, io5]; show u4.io = _; rw [io4, hio2]
  have h186 : u6.x 18 = q.core.x 18 := by rw [x186, q5x18]
  have hlim := hst.below
  have hstk2 := hstk.limit
  have hst5 : StoreRel P S.cap S.globalTypes st q5.core :=
    hst.regs (by rw [q5x17, h17]) q5x18 m5
  have hwithin : ∀ e ∈ st.host.world.events ++
      [writeEvent (layoutAt area) st.mem out.fd ptr len rk],
      WritesWithin (layoutAt area) size e := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact htr.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact writeEvent_writesWithin (layoutAt area) st.mem out.fd ptr len rk size
  have htrace : ({ q5 with core := u6 } : Proc).trace =
      (st.host.world.events ++ [writeEvent (layoutAt area) st.mem out.fd ptr len rk]).map
        A64.Event.sys := by
    show q5.trace = _
    rw [tr5, htr.1, List.map_append]
    rfl
  rcases hcases with ⟨hle, p6, x06, m6⟩ | ⟨hgt, h4095, p6, x06, m6⟩ | ⟨hgt, hbig, p6, m6⟩
  · -- a count
    have hret : rk.ret.toNat ≤ len.toNat := by
      simpa only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64] using hle
    have hrr : writeReply len.toUInt64 rk.ret = .returned 0 rk.ret := by
      unfold writeReply
      rw [if_pos (by rw [UInt32.toNat_toUInt64]; exact hret)]
    rw [hrr]
    dsimp only
    rw [if_pos rfl]
    have hret32 : rk.ret.toNat < 2 ^ 32 := by
      have := len.toNat_lt
      omega
    rw [write32_writeBytes]
    have hcnt : (q5.core.x 17 + UInt64.ofNat 4104).toNat + 4 ≤ (q.core.x 18).toNat := by
      rw [q5x17, ← h17, hst.toNat_addr (j := 4104) (by unfold areaSize; omega)]
      unfold areaSize at hlim
      omega
    refine ⟨{ q5 with core := u6 }, hrch, ⟨p6, hsp6, h186, hio6, fun a ha => ?_, by simp,
      ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, ?_, ?_, ?_, htrace, ?_⟩
    · show u6.mem a = q.core.mem a
      have ha' : q.core.sp.toNat ≤ a.toNat := by
        have := ha
        simp only [Nat.mul_zero, Nat.add_zero] at this
        exact this
      rw [m6, writeList_below (lim := q.core.x 18) (by simpa using hcnt) (by omega), m5]
    · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      show u6.x 0 = (0 : UInt64).toUInt32.toUInt64
      rw [x06]
      rfl
    · exact StoreRel.withHost (hst5.ofWriteList P [(rk.ret.toUInt32 &&& 0xFF).toUInt8,
        ((rk.ret.toUInt32 >>> 8) &&& 0xFF).toUInt8, ((rk.ret.toUInt32 >>> 16) &&& 0xFF).toUInt8,
        ((rk.ret.toUInt32 >>> 24) &&& 0xFF).toUInt8] (p := 8)
        (by simp only [List.length_cons, List.length_nil]; omega) x176 x186
        (by rw [m6, count_bytes hret32])) _
    · show q5.fpcr = fpcrValue
      exact hf5
    · show u6.x 17 = area
      rw [x176, q5x17]
    · intro e he
      exact hwithin e he
  · -- an error
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hgt
      omega
    have hErr : Linux.isError rk.ret = true :=
      (isError_iff (c := len.toUInt64) (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt)
        hgt).mpr h4095
    have hrr : writeReply len.toUInt64 rk.ret = .returned (errnoOf (0 - rk.ret)) 0 := by
      unfold writeReply
      rw [if_neg hnot, if_pos hErr]
    rw [hrr]
    dsimp only
    rw [if_neg (errnoOf_valid _).2]
    refine ⟨{ q5 with core := u6 }, hrch, ⟨p6, hsp6, h186, hio6, fun a ha => ?_, by simp,
      ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, ?_, ?_, ?_, htrace, ?_⟩
    · show u6.mem a = q.core.mem a
      rw [m6, m5]
    · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      show u6.x 0 = (errnoOf (0 - rk.ret)).toUInt32.toUInt64
      rw [x06, errno_toUInt64, errnoOf_lookup]
    · exact StoreRel.withHost (hst5.regs x176 x186 m6) _
    · show q5.fpcr = fpcrValue
      exact hf5
    · show u6.x 17 = area
      rw [x176, q5x17]
    · intro e he
      exact hwithin e he
  · -- a trap of the shim
    have hnot : ¬ rk.ret.toNat ≤ (len.toUInt64).toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hgt
      omega
    have hErr : Linux.isError rk.ret = false := by
      cases h : Linux.isError rk.ret with
      | false => rfl
      | true =>
        exact absurd ((isError_iff (c := len.toUInt64)
          (by rw [UInt32.toNat_toUInt64]; exact len.toNat_lt) hgt).mp h)
          (UInt64.not_le.mpr hbig)
    have hrr : writeReply len.toUInt64 rk.ret = .trapped shimTrap 0 := by
      unfold writeReply
      rw [if_neg hnot, if_neg (by rw [hErr]; decide)]
    rw [hrr]
    dsimp only
    exact ⟨{ q5 with core := u6 }, hrch, hio6, .inr (.inr (.inr ⟨rfl, p6⟩)), hf5,
      htrace, hwithin⟩

theorem exitStub_ok {a base : UInt64} {is : List Instr} (hg : exitStub a base = .ok is) :
    ∃ f1 g3, cbField (after a 1) base = .ok f1 ∧ bField (after a 3) base = .ok g3 ∧
      is = [.subsImm 31 0 126, .bcond 3 f1, .movz 0 1 0, .b g3] := by
  unfold exitStub at hg
  cases h1 : cbField (after a 1) base with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok f1 =>
  cases h3 : bField (after a 3) base with
  | error err => simp [h1, h3, bind, Except.bind] at hg
  | ok g3 =>
  simp only [h1, h3, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨f1, g3, rfl, rfl, hg.symm⟩

/-- The stub of `proc_exit` stands for the shim's `proc_exit`: it reaches the exit word with the
status below 126 in X0, or with 1 for a status of 126 or more. -/
theorem exitStub_sim (S : Shared) (n : Nat) {ex : UInt64} {is : List Instr}
    (hg : exitStub ex base = .ok is) (hcode : CodeAt code ex is) :
    (shimMachine R P code hdom hk area base size).StubSim S n [.i32] [] exitFn ex := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = ex at hpc
  obtain ⟨c, rfl⟩ : ∃ c : UInt32, args = [.i32 c] := by
    match args, hlen, hty with
    | [v], _, ⟨t, _⟩ => cases v <;> first | exact ⟨_, rfl⟩ | exact t.elim
  have x0 : q.core.x 0 = c.toUInt64 := hregs 0 (by simp)
  obtain ⟨hst, hf, h17, htr⟩ := hsr
  refine .inr ?_
  obtain ⟨f1, g3, hf1, hg3, rfl⟩ := exitStub_ok hg
  have c01 : CodeAt code ex [.subsImm 31 0 126, .bcond 3 f1] :=
    (CodeAt.split code (l1 := [.subsImm 31 0 126, .bcond 3 f1]) hcode rfl).1
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c2 c3
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_loImm P code (tB := base) (by decide) c01
    (cbField_target hf1) hpc
  rw [show UInt64.ofNat (126 : Fin 4096).val = 126 by decide, x0] at p1
  have hinv : exitFn.invoke st [.i32 c] = exitInvoke st [.i32 c] := rfl
  rw [hinv]
  simp only [exitInvoke]
  have hlt : c.toUInt64 < 126 ↔ c.toNat < 126 := by
    rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64]
    rfl
  by_cases hc : c.toNat < 126
  · rw [if_pos (hlt.mpr hc)] at p1
    rw [if_pos hc]
    exact ⟨{ q with core := u1 }, ProcRunWith.ofReach hf r1, io1,
      .inr (.inl ⟨rfl, c.toUInt64, rfl, p1, by rw [k1, x0]⟩), hf, htr⟩
  · rw [if_neg (fun h => hc (hlt.mp h))] at p1
    rw [if_neg hc]
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_movz P code (s := u1) (d := 0) (imm := 1)
      (hw := 0) (by decide) (by rw [p1]; exact c2)
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_b P code (s := u2) (target := base)
      (by rw [p2, p1, ← after_succ]; exact c3)
      (by rw [p2, p1, ← after_succ]; exact bField_target hg3)
    exact ⟨{ q with core := u3 }, ProcRunWith.ofReach hf (r1.trans (r2.trans r3)),
      by show u3.io = q.core.io; rw [io3, io2, io1],
      .inr (.inr (.inl ⟨rfl, p3, by rw [k3, x2, movz0_val]; decide⟩)), hf, htr⟩

end Verified.ShimA64
