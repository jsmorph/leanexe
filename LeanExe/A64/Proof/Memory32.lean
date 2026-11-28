module

public import LeanExe.A64.Proof.ByteMemory
public import LeanExe.A64.Proof.Linux

@[expose] public section

/-!
The simulation of `i32.load` and `i32.store`.  Each compares the address with the memory's size
less 8, plus 4 less the offset `off`, and branches to the stub of an access outside the memory
above it.  `i32.load` loads the word of the eight bytes from `X17 + 4092 + a + off`, 4088 bytes
above `X17 + a + off + 4`, and shifts it right by 32, which leaves the memory's four bytes from
`a + off`.  The four bytes below them lie in the area, in its header when `a + off` lies below 4.
`i32.store` writes the value's four bytes with `STRB` from 4092 to 4095 bytes above
`X17 + a + off + 4`, the higher three shifted down into a scratch register, the run of
`run_strb4`.  `StoreRel.ofWriteList` gives the store relation after bytes written into the memory
one after another, as the four bytes of a store and a Linux call's output are, and
`write32_writeBytes` states Talos's `write32` as such a write.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Bytes -/

private theorem or_add_shift {x y k : Nat} (hx : x < 2 ^ k) :
    x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

private theorem toNat_shiftLeft32 (x j : UInt32) (n : Nat) (hj : j.toNat = n) (hn : n < 32)
    (hx : x.toNat * 2 ^ n < 4294967296) : (x <<< j).toNat = x.toNat * 2 ^ n := by
  rw [UInt32.toNat_shiftLeft, hj, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt hx

/-- Talos's `read32` is the little-endian sum of its four bytes. -/
theorem read32_toNat (m : Mem) (b : UInt32) :
    (m.read32 b).toNat = (m.bytes b.toNat).toNat + 256 * (m.bytes (b.toNat + 1)).toNat +
      65536 * (m.bytes (b.toNat + 2)).toNat + 16777216 * (m.bytes (b.toNat + 3)).toNat := by
  simp only [Mem.read32]
  generalize m.bytes b.toNat = b0
  generalize m.bytes (b.toNat + 1) = b1
  generalize m.bytes (b.toNat + 2) = b2
  generalize m.bytes (b.toNat + 3) = b3
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    toNat_shiftLeft32 _ 8 8 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 16 16 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 24 24 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
    or_add_shift (x := b0.toNat) (y := b1.toNat) (k := 8) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8) (y := b2.toNat) (k := 16) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) (y := b3.toNat) (k := 24)
      (by omega)]
  omega

/-- The upper half of the word of eight bytes whose upper four hold Talos's memory from `x` is
Talos's `read32` at `x`. -/
theorem load64_shr32 {mem : UInt64 → UInt8} {b : UInt64} {m : Mem} {x : UInt32}
    (h4 : mem (b + 4) = m.bytes x.toNat) (h5 : mem (b + 5) = m.bytes (x.toNat + 1))
    (h6 : mem (b + 6) = m.bytes (x.toNat + 2)) (h7 : mem (b + 7) = m.bytes (x.toNat + 3)) :
    load64 mem b >>> UInt64.ofNat 32 = (m.read32 x).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, load64_toNat, UInt32.toNat_toUInt64, read32_toNat, h4, h5, h6, h7]
  have e : (UInt64.ofNat 32).toNat % 64 = 32 := rfl
  rw [e, Nat.shiftRight_eq_div_pow]
  have := byte_lt (mem b)
  have := byte_lt (mem (b + 1))
  have := byte_lt (mem (b + 2))
  have := byte_lt (mem (b + 3))
  have := byte_lt (m.bytes x.toNat)
  have := byte_lt (m.bytes (x.toNat + 1))
  have := byte_lt (m.bytes (x.toNat + 2))
  have := byte_lt (m.bytes (x.toNat + 3))
  simp only [Nat.reducePow] at *
  omega

/-- Byte `k` of a 32-bit word, as the shift of its 64-bit word that `STRB` stores. -/
theorem byte_shift (v : UInt32) (k : Nat) (hk : k < 4) :
    (v.toUInt64 >>> UInt64.ofNat (8 * k)).toUInt8 =
      ((v >>> UInt32.ofNat (8 * k)) &&& 0xFF).toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt32.toNat_toUInt64,
    UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_shiftRight, UInt64.toNat_ofNat',
    UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, and255]
  have := v.toNat_lt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.pow_zero, Nat.div_one] at * <;>
    omega

/-- Talos's `write32` as the write of its four bytes, the lowest first. -/
theorem write32_writeBytes (m : Mem) (y v : UInt32) :
    m.write32 y v = m.writeBytes y.toNat [(v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8,
      ((v >>> 16) &&& 0xFF).toUInt8, ((v >>> 24) &&& 0xFF).toUInt8] := by
  cases m with
  | mk pages bytes =>
    simp only [Mem.write32, Mem.writeBytes, List.length_cons, List.length_nil]
    congr 1
    funext i
    rcases (show i < y.toNat ∨ i = y.toNat ∨ i = y.toNat + 1 ∨ i = y.toNat + 2 ∨
        i = y.toNat + 3 ∨ y.toNat + 4 ≤ i by omega) with h | rfl | rfl | rfl | rfl | h
    · rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    · rw [dif_pos (by omega), if_pos rfl]
      simp
    · rw [dif_pos (by omega), if_neg (by omega), if_pos rfl]
      simp
    · rw [dif_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      simp
    · rw [dif_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      simp
    · rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]

/-- The store relation after the bytes `bs` written into the memory from its byte `p`, within its
size, one after another from `X17 + 4096 + p`. -/
theorem StoreRel.ofWriteList {cap : Nat} {gts : List ValueType} {α : Type} :
    ∀ (bs : List UInt8) {st : Store α} {s s' : State} {p : Nat}, StoreRel P cap gts st s →
      p + bs.length ≤ st.mem.pages * 65536 → s'.x 17 = s.x 17 → s'.x 18 = s.x 18 →
      s'.mem = writeList s.mem (s.x 17 + UInt64.ofNat (4096 + p)) bs →
      StoreRel P cap gts { st with mem := st.mem.writeBytes p bs } s'
  | [], st, s, s', p, h, _, h17, h18, hmem => by
      rw [Mem.writeBytes_nil]
      exact h.regs h17 h18 hmem
  | b :: bs, st, s, s', p, h, hfit, h17, h18, hmem => by
      simp only [List.length_cons] at hfit
      have hcap := h.cap_lt
      have hpg := h.pages
      have hsize : p < UInt32.size :=
        Nat.lt_of_lt_of_le (by omega : p < 4294967296) (by decide)
      have hp : (UInt32.ofNat p).toNat = p := UInt32.toNat_ofNat_of_lt' hsize
      let s1 : State := { s with mem := store8 s.mem (s.x 17 + UInt64.ofNat (4096 + p)) b }
      have h1 : StoreRel P cap gts { st with mem := st.mem.write8 (UInt32.ofNat p) b } s1 :=
        h.write8 P (by rw [hp]; omega) rfl rfl (by rw [hp])
      rw [Mem.writeBytes_cons _ _ _ _ hsize]
      refine StoreRel.ofWriteList bs (st := { st with mem := st.mem.write8 (UInt32.ofNat p) b })
        (s := s1) (s' := s') (p := p + 1) h1 (by simp only [Mem.write8]; omega) h17 h18 ?_
      rw [hmem, LeanExe.A64.writeList]
      congr 1
      show s.x 17 + UInt64.ofNat (4096 + p) + 1 = s.x 17 + UInt64.ofNat (4096 + (p + 1))
      rw [UInt64.add_assoc, ← Nat.add_assoc, UInt64.ofNat_add (4096 + p) 1]
      rfl

/-! ## Steps

A step of the program's model at a placed instruction, stated by its effect on the state's parts
rather than by the state it builds, so that a run of many steps keeps its states small. -/

/-- A step that sets register `d` to `v` and changes nothing else but the program counter. -/
theorem step_setX {s : State} {i : Instr} {d : Fin 32} {v : UInt64} (hd : d.val < 31)
    (hc : code s.pc = some (encode i))
    (he : LeanExe.A64.exec P i s = some { s.setX d v with pc := s.pc + 4 }) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = v ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  ⟨_, reach_exec P code hc he (.refl _), rfl,
    by rw [State.x_withPc, State.x_setX_same hd],
    fun q hq => by rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)],
    State.setX_sp, State.setX_mem, State.setX_io⟩

/-- A step of `STRB` with a base other than SP to the byte `addr` of Normal memory, on a platform
whose UART lies outside Normal memory. -/
theorem step_strb {s : State} {t n : Fin 32} {imm : Fin 4096} {k : Nat} {addr : UInt64}
    (hn : n.val < 31) (hc : code s.pc = some (encode (.strb t n imm))) (hk : imm.val = k)
    (haddr : s.x n + UInt64.ofNat k = addr)
    (hmap : P.normal addr = true) (hU : P.normal P.uart = false) :
    ∃ s', Reach P code s s' ∧ s'.pc = s.pc + 4 ∧ (∀ q : Fin 32, s'.x q = s.x q) ∧
      s'.sp = s.sp ∧ s'.io = s.io ∧ s'.mem = store8 s.mem addr (s.x t).toUInt8 := by
  subst hk haddr
  exact ⟨_, reach_exec P code hc (exec_strb_base P hn hmap hU) (.refl _), rfl, fun _ => rfl, rfl,
    rfl, rfl⟩

/-- A step of `LSR` by the immediate `k`. -/
theorem step_lsrImm {s : State} {d n : Fin 32} {sh : Fin 64} {k : Nat} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.lsrImm d n sh))) (hk : sh.val = k) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n >>> UInt64.ofNat k ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  subst hk
  exact step_setX P code hd hc rfl

/-! ## Four bytes stored -/

/-- The run of the four `STRB` of a 32-bit word in X`v` to the bytes 4092 to 4095 above X16, the
higher three shifted down into X`t`: the memory holds the four bytes, X`t` changes, and every
other register, SP, and the UART's state keep their values. -/
theorem run_strb4 {a : UInt64} {v t : Fin 32} {s : State} (ht : t.val < 31)
    (hvt : v ≠ t) (ht16 : t ≠ 16)
    (hcode : CodeAt code a [.strb v 16 4092, .lsrImm t v 8, .strb t 16 4093, .lsrImm t v 16,
      .strb t 16 4094, .lsrImm t v 24, .strb t 16 4095])
    (hpc : s.pc = a) (hmap : ∀ k < 4, P.normal (s.x 16 + UInt64.ofNat (4092 + k)) = true)
    (hU : P.normal P.uart = false) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 7 ∧ s'.sp = s.sp ∧ s'.io = s.io ∧
      (∀ q, q ≠ t → s'.x q = s.x q) ∧
      s'.mem = writeList s.mem (s.x 16 + UInt64.ofNat 4092)
        [(s.x v).toUInt8, (s.x v >>> UInt64.ofNat 8).toUInt8, (s.x v >>> UInt64.ofNat 16).toUInt8,
          (s.x v >>> UInt64.ofNat 24).toUInt8] := by
  have c := fun k (hk : k < 7) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  have c5 := c 5 (by omega)
  have c6 := c 6 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5 c6
  have h16 : (16 : Fin 32).val < 31 := by decide
  have h16t : (16 : Fin 32) ≠ t := Ne.symm ht16
  obtain ⟨s1, r1, p1, x1, sp1, io1, m1⟩ := step_strb P code (s := s) (k := 4092)
    (addr := s.x 16 + UInt64.ofNat 4092) h16 (by rw [hpc]; exact c0) (by decide) rfl
    (hmap 0 (by omega)) hU
  have q1 : s1.pc = after a 1 := by rw [p1, hpc]; simp [after]
  obtain ⟨s2, r2, p2, t2, x2, sp2, m2, io2⟩ := step_lsrImm P code (s := s1) (k := 8) ht
    (by rw [q1]; exact c1) (by decide)
  have q2 : s2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨s3, r3, p3, x3, sp3, io3, m3⟩ := step_strb P code (s := s2) (k := 4093)
    (addr := s.x 16 + UInt64.ofNat 4093) h16 (by rw [q2]; exact c2) (by decide)
    (by rw [x2 16 h16t, x1 16]) (hmap 1 (by omega)) hU
  have q3 : s3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨s4, r4, p4, t4, x4, sp4, m4, io4⟩ := step_lsrImm P code (s := s3) (k := 16) ht
    (by rw [q3]; exact c3) (by decide)
  have q4 : s4.pc = after a 4 := by rw [p4, q3, ← after_succ]
  obtain ⟨s5, r5, p5, x5, sp5, io5, m5⟩ := step_strb P code (s := s4) (k := 4094)
    (addr := s.x 16 + UInt64.ofNat 4094) h16 (by rw [q4]; exact c4) (by decide)
    (by rw [x4 16 h16t, x3 16, x2 16 h16t, x1 16]) (hmap 2 (by omega)) hU
  have q5 : s5.pc = after a 5 := by rw [p5, q4, ← after_succ]
  obtain ⟨s6, r6, p6, t6, x6, sp6, m6, io6⟩ := step_lsrImm P code (s := s5) (k := 24) ht
    (by rw [q5]; exact c5) (by decide)
  have q6 : s6.pc = after a 6 := by rw [p6, q5, ← after_succ]
  obtain ⟨s7, r7, p7, x7, sp7, io7, m7⟩ := step_strb P code (s := s6) (k := 4095)
    (addr := s.x 16 + UInt64.ofNat 4095) h16 (by rw [q6]; exact c6) (by decide)
    (by rw [x6 16 h16t, x5 16, x4 16 h16t, x3 16, x2 16 h16t, x1 16]) (hmap 3 (by omega)) hU
  have hv3 : s3.x v = s.x v := by rw [x3, x2 v hvt, x1]
  have hv5 : s5.x v = s.x v := by rw [x5, x4 v hvt, hv3]
  have a1 : s.x 16 + UInt64.ofNat 4092 + 1 = s.x 16 + UInt64.ofNat 4093 := by
    rw [UInt64.add_assoc, show UInt64.ofNat 4092 + 1 = UInt64.ofNat 4093 by decide]
  have a2 : s.x 16 + UInt64.ofNat 4093 + 1 = s.x 16 + UInt64.ofNat 4094 := by
    rw [UInt64.add_assoc, show UInt64.ofNat 4093 + 1 = UInt64.ofNat 4094 by decide]
  have a3 : s.x 16 + UInt64.ofNat 4094 + 1 = s.x 16 + UInt64.ofNat 4095 := by
    rw [UInt64.add_assoc, show UInt64.ofNat 4094 + 1 = UInt64.ofNat 4095 by decide]
  refine ⟨s7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))),
    by rw [p7, q6, ← after_succ], by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [io7, io6, io5, io4, io3, io2, io1], fun q hq => ?_, ?_⟩
  · rw [x7, x6 q hq, x5, x4 q hq, x3, x2 q hq, x1]
  · rw [m7, m6, m5, m4, m3, m2, m1, t6, t4, t2, hv5, hv3, x1]
    simp only [writeList, a1, a2, a3]

/-! ## The bounds check -/

theorem add_ofNat_sub_four {x : UInt64} {off : Nat} (h : off ≤ 4) :
    x + UInt64.ofNat (4 - off) = x + 4 - UInt64.ofNat off := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat,
    Nat.reducePow] at *
  omega

theorem sub_ofNat_sub_four {x : UInt64} {off : Nat} (h : 4 < off) (h' : off < 4092) :
    x - UInt64.ofNat (off - 4) = x + 4 - UInt64.ofNat off := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat,
    Nat.reducePow] at *
  omega

/-- `bound32Instr off` adds 4 less `off` to X16. -/
theorem exec_bound32Instr {off : Nat} (h : off < 4092) (s : State) :
    exec P (bound32Instr off h) s =
      some { s.setX 16 (s.x 16 + 4 - UInt64.ofNat off) with pc := s.pc + 4 } := by
  have h16 : (16 : Fin 32).val < 31 := by decide
  unfold bound32Instr
  split
  · rename_i h4
    simp only [exec, State.xsp_eq_x h16, State.setXsp_eq_setX h16]
    rw [add_ofNat_sub_four h4]
  · rename_i h4
    simp only [exec, State.xsp_eq_x h16, State.setXsp_eq_setX h16]
    rw [sub_ofNat_sub_four (by omega) h]

/-- The bounds check of a 4-byte access at offset `off` on the address in `r`: the run reaches the
access's fifth instruction when the four bytes lie within the memory, and the stub `tB`
otherwise, changing X16 and the flags alone. -/
theorem run_bounds32 {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {ms : State}
    {a tB : UInt64} {r : Fin 32} {off : Nat} (hoff : off < 4092) {g : Fin 524288}
    (hr : r.val < 31) (hr16 : r ≠ 16)
    (hcode : CodeAt code a [.ldr 16 17 0, bound32Instr off hoff, .subsReg 31 r 16, .bcond 8 g])
    (hg : cbField (after a 3) tB = .ok g) (hpc : ms.pc = a)
    (hsr : StoreRel P cap gts st ms) :
    ∃ s, Reach P code ms s ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.io = ms.io ∧
      (∀ q, q ≠ 16 → s.x q = ms.x q) ∧
      s.pc = if (ms.x r).toNat + off + 4 ≤ st.mem.pages * 65536 then after a 4 else tB := by
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
  let s2 : State := { s1.setX 16 (s1.x 16 + 4 - UInt64.ofNat off) with pc := s1.pc + 4 }
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
  have e1 : LeanExe.A64.exec P (bound32Instr off hoff) s1 = some s2 := exec_bound32Instr P hoff s1
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
  have h16 : s2.x 16 = UInt64.ofNat (st.mem.pages * 65536 - 4 - off) := by
    show (s1.setX 16 (s1.x 16 + 4 - UInt64.ofNat off)).x 16 = _
    rw [State.x_setX_same (by decide)]
    have hs1 : s1.x 16 = S := by
      show (ms.setX 16 S).x 16 = _
      exact State.x_setX_same (by decide)
    rw [hs1]
    show load64 ms.mem (ms.x 17) + 4 - _ = _
    rw [hsr.size]
    have := hsr.pages
    have := hsr.cap_lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      UInt64.toNat_ofNat']
    simp only [Nat.reducePow, UInt64.reduceToNat] at *
    omega
  have hxr : s2.x r = ms.x r := hx2 r hr16
  have hcond : s3.condHolds 8 = !decide ((ms.x r).toNat + off + 4 ≤ st.mem.pages * 65536) := by
    rw [condHolds_8]
    show (decide (s2.x 16 ≤ s2.x r) && !(s2.x r - s2.x 16 == 0)) = _
    rw [hxr, h16]
    have := hsr.pages
    have := hsr.cap_lt
    have hlt := (ms.x r).toNat_lt
    by_cases hc : (ms.x r).toNat + off + 4 ≤ st.mem.pages * 65536
    · have h1 : ¬ (UInt64.ofNat (st.mem.pages * 65536 - 4 - off) ≤ ms.x r ∧
          ms.x r ≠ UInt64.ofNat (st.mem.pages * 65536 - 4 - off)) := by
        rw [UInt64.le_iff_toNat_le, Ne, ← UInt64.toNat_inj, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_true hc]
      by_cases h2 : UInt64.ofNat (st.mem.pages * 65536 - 4 - off) ≤ ms.x r
      · have h3 : ms.x r = UInt64.ofNat (st.mem.pages * 65536 - 4 - off) := by
          exact Classical.byContradiction fun hne => h1 ⟨h2, hne⟩
        rw [h3]
        simp
      · simp [h2]
    · have h1 : UInt64.ofNat (st.mem.pages * 65536 - 4 - off) < ms.x r := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_false hc]
      have h2 : ms.x r - UInt64.ofNat (st.mem.pages * 65536 - 4 - off) ≠ 0 := fun e =>
        absurd ((sub_eq_zero_iff' _ _).mp e) (fun e' => by
          rw [e', UInt64.lt_iff_toNat_lt] at h1
          omega)
      simp [UInt64.le_of_lt h1, h2]
  refine ⟨s4, hreach, ?_, ?_, ?_, fun q hq => ?_, ?_⟩
  · show (s2.setX 31 (s2.x r - s2.x 16)).sp = _
    rw [State.setX_sp]
    show (s1.setX 16 (s1.x 16 + 4 - UInt64.ofNat off)).sp = _
    rw [State.setX_sp]
    show (ms.setX 16 S).sp = _
    exact State.setX_sp
  · show (s2.setX 31 (s2.x r - s2.x 16)).mem = _
    rw [State.setX_mem]
    show (s1.setX 16 (s1.x 16 + 4 - UInt64.ofNat off)).mem = _
    rw [State.setX_mem]
    show (ms.setX 16 S).mem = _
    exact State.setX_mem
  · show (s2.setX 31 (s2.x r - s2.x 16)).io = _
    rw [State.setX_io]
    show (s1.setX 16 (s1.x 16 + 4 - UInt64.ofNat off)).io = _
    rw [State.setX_io]
    show (ms.setX 16 S).io = _
    exact State.setX_io
  · show s3.x q = _
    rw [hx3, hx2 q hq]
  · show (if s3.condHolds 8 then s3.pc + sext 19 g.val * 4 else s3.pc + 4) = _
    rw [hcond, p3]
    by_cases hc : (ms.x r).toNat + off + 4 ≤ st.mem.pages * 65536
    · rw [ite_eq_left hc]
      simp only [decide_eq_true hc, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (after_succ a 3).symm
    · rw [ite_eq_right hc]
      simp only [decide_eq_false hc, Bool.not_false, ite_true]
      exact cbField_target hg

/-- The first four instructions of an access: its bounds check. -/
theorem CodeAt.head4 {a : UInt64} {i0 i1 i2 i3 : Instr} {rest : List Instr}
    (h : CodeAt code a (i0 :: i1 :: i2 :: i3 :: rest)) : CodeAt code a [i0, i1, i2, i3] :=
  ((CodeAt.append (code := code) (l1 := [i0, i1, i2, i3]) (l2 := rest)).mp h).1

/-! ## `i32.load` -/

theorem gen_load32 {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.load32 off) = .ok (is, fin)) :
    ∃ (h : off.toNat < 4092) (g : Fin 524288), curBase ctl + 1 ≤ σ.length ∧
      (σ.head? = some .i32 ∨ σ.head? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, bound32Instr off.toNat h, .subsReg 31 (regOf (σ.length - 1)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 1)), .addImm 16 16 ⟨off.toNat + 4, by omega⟩,
        .ldr (regOf (σ.length - 1)) 16 511,
        .lsrImm (regOf (σ.length - 1)) (regOf (σ.length - 1)) 32] ∧
      fin = some (.i32 :: σ.tail) := by
  unfold genInstr at hg
  by_cases hc : σ.length < curBase ctl + 1 ∨ ¬ (σ.head? = some .i32 ∨ σ.head? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2⟩ := hc'
  by_cases h : off.toNat < 4092
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

theorem sim_load32 (F : Nat) (off : UInt32) : InstrSim P code F (.load32 off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ D _ _
  obtain ⟨h, g, hc1, hty0, hlt, hg, rfl, rfl⟩ := gen_load32 hgen
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
      suffices key : ∀ y : UInt32, (n + off.toNat + 4 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl D (some (.i32 :: σ0)) (after a 8)
            (if n + off.toNat + 4 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough st { sl with values := .i32 (st.mem.read32 y) :: vs }) ms by
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
        run_bounds32 P code (r := regOf σ0.length) h hr hr16 (CodeAt.head4 code hcode) hg hpc
          hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 4 ≤ st.mem.pages * 65536
      · rw [ite_eq_right (by omega)]
        rw [ite_eq_left hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        have c6 := hcode 6 (by simp)
        have c7 := hcode 7 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5 c6 c7
        let s5 : State := { s.setX 16 (s.x 17 + s.x (regOf σ0.length)) with pc := s.pc + 4 }
        have e5 : LeanExe.A64.exec P (.addReg 16 17 (regOf σ0.length)) s = some s5 := rfl
        have p5 : s5.pc = after a 5 := by
          show s.pc + 4 = _
          rw [hpcs, ← after_succ]
        have h16 : s5.x 16 = ms.x 17 + ms.x (regOf σ0.length) := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x 16 = _
          rw [State.x_setX_same (by decide), hxs 17 (by decide), hxs _ hr16]
        let s6 : State :=
          { s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4)) with pc := s5.pc + 4 }
        have e6 : LeanExe.A64.exec P (.addImm 16 16 ⟨off.toNat + 4, by omega⟩) s5 = some s6 := by
          simp only [exec, State.xsp_eq_x (show (16 : Fin 32).val < 31 by decide),
            State.setXsp_eq_setX (show (16 : Fin 32).val < 31 by decide)]
          rfl
        have p6 : s6.pc = after a 6 := by
          show s5.pc + 4 = _
          rw [p5, ← after_succ]
        have h16' : s6.x 16 = ms.x 17 + ms.x (regOf σ0.length) + UInt64.ofNat (off.toNat + 4) := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).x 16 = _
          rw [State.x_setX_same (by decide), h16]
        have hbound : n + off.toNat + 4 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hB : ∀ j : Nat, s6.x 16 + UInt64.ofNat (8 * 511) + UInt64.ofNat j =
            ms.x 17 + UInt64.ofNat (4092 + (n + off.toNat + j)) := by
          intro j
          rw [h16']
          apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
          rw [← hn]
          have := (ms.x 17).toNat_lt
          have := (ms.x (regOf σ0.length)).toNat_lt
          simp only [Nat.reducePow] at *
          omega
        have hB4 : ∀ i, s6.x 16 + UInt64.ofNat (8 * 511) + UInt64.ofNat (4 + i) =
            ms.x 17 + UInt64.ofNat (4096 + (n + off.toNat + i)) := by
          intro i
          rw [hB]
          congr 2
          omega
        have hex7 := exec_ldr_base P (s := s6) (t := regOf σ0.length) (i := 511) (by decide)
          (n := 16) (by decide) (fun k hk => by
            rw [UInt64.ofNat_add, ← UInt64.add_assoc, hB k]
            exact hsr.mapped _ (by unfold areaSize; omega))
        have hmem6 : s6.mem = ms.mem := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).mem = _
          rw [State.setX_mem]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hbyte : ∀ i < 4, s6.mem (s6.x 16 + UInt64.ofNat (8 * 511) + UInt64.ofNat (4 + i)) =
            st.mem.bytes (y.toNat + i) := by
          intro i hi
          rw [hB4, hmem6, hsr.bytes _ (by omega), hy hin]
        have hval : load64 s6.mem (s6.x 16 + UInt64.ofNat (8 * 511)) >>> UInt64.ofNat 32 =
            (st.mem.read32 y).toUInt64 :=
          load64_shr32 (hbyte 0 (by omega)) (hbyte 1 (by omega)) (hbyte 2 (by omega))
            (hbyte 3 (by omega))
        let s7 : State := { s6.setX (regOf σ0.length)
          (load64 s6.mem (s6.x 16 + UInt64.ofNat (8 * 511))) with pc := s6.pc + 4 }
        let s8 : State := { s7.setX (regOf σ0.length)
          (s7.x (regOf σ0.length) >>> UInt64.ofNat 32) with pc := s7.pc + 4 }
        have e8 : LeanExe.A64.exec P
            (.lsrImm (regOf σ0.length) (regOf σ0.length) 32) s7 = some s8 := rfl
        have p7 : s7.pc = after a 7 := by
          show s6.pc + 4 = _
          rw [p6, ← after_succ]
        have hr8 : Reach P code ms s8 :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) e6
              (reach_exec P code (by rw [p6]; exact c6) hex7
                (reach_exec P code (by rw [p7]; exact c7) e8 (.refl _)))))
        have hk8 : ∀ q, q ≠ regOf σ0.length → q ≠ 16 → s8.x q = ms.x q := fun q hq hq16 => by
          show (s7.setX (regOf σ0.length) _).x q = _
          rw [State.x_setX_ne (Ne.symm hq)]
          show (s6.setX (regOf σ0.length) _).x q = _
          rw [State.x_setX_ne (Ne.symm hq)]
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).x q = _
          rw [State.x_setX_ne (Ne.symm hq16)]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x q = _
          rw [State.x_setX_ne (Ne.symm hq16), hxs q hq16]
        have hsp6 : s6.sp = ms.sp := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).sp = _
          rw [State.setX_sp]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        have hio6 : s6.io = ms.io := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).io = _
          rw [State.setX_io]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).io = _
          rw [State.setX_io, houts]
        refine res_outcome P code (v := .i32 (st.mem.read32 y)) (t := .i32) (vs := vs)
          (w := s8.x (regOf σ0.length)) ?_ (show HasType .i32 (.i32 (st.mem.read32 y)) from ⟨⟩)
          hty.2 hinv hsr (by omega) (by omega)
          hstack.pop hr8 ?_ (by rw [hvl]) ?_ (hk8 18 (Ne.symm (regOf_ne_18 _ hlt)) (by decide))
          (hk8 17 (Ne.symm (regOf_ne_17 _ hlt)) (by decide)) ?_ ?_ ?_
        · show (s7.setX (regOf σ0.length) _).x (regOf σ0.length) = _
          rw [State.x_setX_same hr]
          show (s6.setX (regOf σ0.length) _).x (regOf σ0.length) >>> _ = _
          rw [State.x_setX_same hr, hval]
        · show s7.pc + 4 = after a 8
          rw [p7, ← after_succ]
        · intro k hk
          exact hk8 _ (fun e => absurd (regOf_inj k (by omega) _ hlt e) (by omega))
            (regOf_ne_scratch k (by omega))
        · show (s7.setX (regOf σ0.length) _).sp = _
          rw [State.setX_sp]
          show (s6.setX (regOf σ0.length) _).sp = _
          rw [State.setX_sp, hsp6]
        · show (s7.setX (regOf σ0.length) _).mem = _
          rw [State.setX_mem]
          show (s6.setX (regOf σ0.length) _).mem = _
          rw [State.setX_mem, hmem6]
        · show (s7.setX (regOf σ0.length) _).io = _
          rw [State.setX_io]
          show (s6.setX (regOf σ0.length) _).io = _
          rw [State.setX_io, hio6]
      · rw [ite_eq_left (by omega)]
        rw [ite_eq_right hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

/-! ## `i32.store` -/

theorem gen_store32 {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.store32 off) = .ok (is, fin)) :
    ∃ (h : off.toNat < 4092) (g : Fin 524288), E.byteStores = true ∧
      curBase ctl + 2 ≤ σ.length ∧ σ.head? = some .i32 ∧
      (σ[1]? = some .i32 ∨ σ[1]? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, bound32Instr off.toNat h, .subsReg 31 (regOf (σ.length - 2)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 2)),
        .addImm 16 16 ⟨off.toNat + 4, by omega⟩, .strb (regOf (σ.length - 1)) 16 4092,
        .lsrImm 29 (regOf (σ.length - 1)) 8, .strb 29 16 4093,
        .lsrImm 29 (regOf (σ.length - 1)) 16, .strb 29 16 4094,
        .lsrImm 29 (regOf (σ.length - 1)) 24, .strb 29 16 4095] ∧
      fin = some (σ.drop 2) := by
  unfold genInstr at hg
  cases hB : E.byteStores with
  | false => simp [hB, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  | true =>
  simp only [hB, Bool.not_true, Bool.false_eq_true, ite_false] at hg
  by_cases hc : σ.length < curBase ctl + 2 ∨ σ.head? ≠ some .i32 ∨
      ¬ (σ[1]? = some .i32 ∨ σ[1]? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Ne, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2, hc3⟩ := hc'
  by_cases h : off.toNat < 4092
  · by_cases hlt : σ.length - 1 < 26
    · have hlt2 : σ.length - 2 < 26 := by omega
      cases hcb : cbField (after a 3) E.trapBounds with
      | error e => simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind] at hg
      | ok g =>
          simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨h, g, rfl, by omega, hc2, Classical.byContradiction fun hn =>
            hc3 ⟨fun h => hn (.inl h), fun h => hn (.inr h)⟩, hlt, rfl, hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [h, he, bind, Except.bind] at hg
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

/-- The low byte of a 32-bit word's 64-bit word. -/
theorem byte_low (v : UInt32) : v.toUInt64.toUInt8 = (v &&& 0xFF).toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt32.toNat_toUInt64, UInt32.toNat_toUInt8, UInt32.toNat_and,
    UInt32.reduceToNat, and255]
  omega

/-- The four bytes that `run_strb4` stores of a 32-bit word are those of Talos's `write32`. -/
theorem strb4_bytes (v : UInt32) :
    [v.toUInt64.toUInt8, (v.toUInt64 >>> UInt64.ofNat 8).toUInt8,
      (v.toUInt64 >>> UInt64.ofNat 16).toUInt8, (v.toUInt64 >>> UInt64.ofNat 24).toUInt8] =
    [(v &&& 0xFF).toUInt8, ((v >>> 8) &&& 0xFF).toUInt8, ((v >>> 16) &&& 0xFF).toUInt8,
      ((v >>> 24) &&& 0xFF).toUInt8] := by
  rw [byte_low v, byte_shift v 1 (by omega), byte_shift v 2 (by omega), byte_shift v 3 (by omega)]
  rfl

theorem sim_store32 (F : Nat) (off : UInt32) : InstrSim P code F (.store32 off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ D hcl _
  obtain ⟨h, g, hbs, hc1, hty0, hty1, hlt, hg, rfl, rfl⟩ := gen_store32 hgen
  have hU : P.normal P.uart = false := hcl.1 hbs
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
      obtain ⟨vv, rfl⟩ : ∃ vv, v1 = .i32 vv := by
        cases v1 <;> first | exact ⟨_, rfl⟩ | exact hty.1.elim
      have hvv : ms.x (regOf (σ0.length + 1)) = vv.toUInt64 := htop
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      generalize hn : (ms.x (regOf σ0.length)).toNat = n
      suffices key : ∀ y : UInt32, (n + off.toNat + 4 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl D (some σ0) (after a 13)
            (if n + off.toNat + 4 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough { st with mem := st.mem.write32 y vv }
              { sl with values := vs }) ms by
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
        run_bounds32 P code (r := regOf σ0.length) h hr hr16 (CodeAt.head4 code hcode) hg hpc
          hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 4 ≤ st.mem.pages * 65536
      · rw [ite_eq_right (by omega)]
        rw [ite_eq_left hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5
        have cstr : CodeAt code (after a 6) [.strb (regOf (σ0.length + 1)) 16 4092,
            .lsrImm 29 (regOf (σ0.length + 1)) 8, .strb 29 16 4093,
            .lsrImm 29 (regOf (σ0.length + 1)) 16, .strb 29 16 4094,
            .lsrImm 29 (regOf (σ0.length + 1)) 24, .strb 29 16 4095] := fun i hi => by
          have := hcode (6 + i) (by simp at hi ⊢; omega)
          rw [← after_after] at this
          simp at hi
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact this
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
        let s6 : State :=
          { s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4)) with pc := s5.pc + 4 }
        have e6 : LeanExe.A64.exec P (.addImm 16 16 ⟨off.toNat + 4, by omega⟩) s5 = some s6 := by
          simp only [exec, State.xsp_eq_x (show (16 : Fin 32).val < 31 by decide),
            State.setXsp_eq_setX (show (16 : Fin 32).val < 31 by decide)]
          rfl
        have p6 : s6.pc = after a 6 := by
          show s5.pc + 4 = _
          rw [p5, ← after_succ]
        have hk6 : ∀ q, q ≠ 16 → s6.x q = ms.x q := fun q hq => by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).x q = _
          rw [State.x_setX_ne (Ne.symm hq), hk5 q hq]
        have h16' : s6.x 16 = ms.x 17 + ms.x (regOf σ0.length) + UInt64.ofNat (off.toNat + 4) := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).x 16 = _
          rw [State.x_setX_same (by decide), h16]
        have hbound : n + off.toNat + 4 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hB : ∀ j : Nat, s6.x 16 + UInt64.ofNat (4092 + j) =
            ms.x 17 + UInt64.ofNat (4096 + (y.toNat + j)) := by
          intro j
          rw [h16', hy hin]
          apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
          rw [← hn]
          have := (ms.x 17).toNat_lt
          have := (ms.x (regOf σ0.length)).toNat_lt
          simp only [Nat.reducePow] at *
          omega
        have hmem6 : s6.mem = ms.mem := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).mem = _
          rw [State.setX_mem]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hsp6 : s6.sp = ms.sp := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).sp = _
          rw [State.setX_sp]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        have hio6 : s6.io = ms.io := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 4))).io = _
          rw [State.setX_io]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).io = _
          rw [State.setX_io, houts]
        obtain ⟨s', hr', hp', hsp', hio', hk', hmem'⟩ := run_strb4 P code
          (v := regOf (σ0.length + 1)) (t := 29) (s := s6) (by decide) (regOf_ne_29 _ hlt) (by decide) cstr p6
          (fun k hk => by
            rw [hB k]
            exact hsr.mapped _ (by unfold areaSize; omega)) hU
        have hB0 : s6.x 16 + UInt64.ofNat 4092 = ms.x 17 + UInt64.ofNat (4096 + y.toNat) := by
          simpa using hB 0
        have hyn := hy hin
        rw [hk6 _ (regOf_ne_scratch _ hlt), hvv, strb4_bytes, hB0, hmem6] at hmem'
        rw [write32_writeBytes]
        have hr13 : Reach P code ms s' :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) e6 hr'))
        have hks : ∀ q, q ≠ 29 → q ≠ 16 → s'.x q = ms.x q := fun q hq hq16 => by
          rw [hk' q hq, hk6 q hq16]
        have h18' : s'.x 18 = ms.x 18 := hks 18 (by decide) (by decide)
        have h17' : s'.x 17 = ms.x 17 := hks 17 (by decide) (by decide)
        have hsps' : s'.sp = ms.sp := by rw [hsp', hsp6]
        have hlim : (ms.x 17 + UInt64.ofNat (4096 + y.toNat)).toNat + 4 ≤ (ms.x 18).toNat := by
          rw [hsr.toNat_addr (j := 4096 + y.toNat) (by unfold areaSize; omega)]
          have := hsr.below
          unfold areaSize at this
          omega
        have hkeep : ∀ c : UInt64, (ms.x 18).toNat ≤ c.toNat → s'.mem c = ms.mem c := by
          intro c hc
          rw [hmem']
          refine writeList_other _ _ _ _ fun hlt' => ?_
          simp only [List.length_cons, List.length_nil] at hlt'
          have := c.toNat_lt
          rw [UInt64.toNat_sub] at hlt'
          simp only [Nat.reducePow] at *
          omega
        refine .inr ⟨_, rfl, s', hr13, ?_, hsps', ?_, h18', fun c hc => ?_, ?_,
          fun k hk => ?_, hsr.ofWriteList P [_, _, _, _]
            (by simp only [List.length_cons, List.length_nil]; omega) h17' h18' hmem'⟩
        · rw [hp', after_after]
        · rw [hio', hio6]
        · exact hkeep c (by
            have := hinv.frame.limit.2.1
            omega)
        · refine ⟨hstack.pop.pop.congr fun k hk => hks _ (regOf_ne_29 k (by omega))
              (regOf_ne_scratch k (by omega)), ?_, hinv.count, hinv.frame.congr hsps' h18',
            hty.2.2, hinv.ltypes⟩
          intro i hi
          have hi' : i < E.localTypes.length := by rw [← hinv.count]; exact hi
          have hbound' := hinv.bound
          rw [hsps', load64_congr (m := s'.mem) (m' := ms.mem) fun k hk => hkeep _ (by
            have := hinv.frame.limit
            rw [UInt64.toNat_add, toNat_slot, UInt64.toNat_ofNat']
            simp only [Nat.reducePow] at *
            omega)]
          exact hinv.locals i hi
        · exact hks _ (regOf_ne_29 k (by omega)) (regOf_ne_scratch k (by omega))
      · rw [ite_eq_left (by omega)]
        rw [ite_eq_right hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

end LeanExe.A64
