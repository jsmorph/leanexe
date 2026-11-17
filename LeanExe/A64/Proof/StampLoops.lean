import LeanExe.A64.Proof.StampCalls
import LeanExe.Pipeline.Allocation

/-!
The loops of the stamp program under `ProcReachWith`.  `ReadStore` is the store that the calls
before the function keep: related to the machine, written only within the allocator's block, and
holding at the block's start the bytes that the calls returned, with arbitrary bytes after them,
since a reply sets the whole output region of its call.  `ReadStore.write` follows a call's write
into the block.  `run_stampReadLoop` follows the loop that reads the input's descriptor into the
block until a read returns 0, by strong induction on the bytes of the block that remain, and
`run_stampWriteLoop` the loop that writes the function's result to the output's descriptor, by
strong induction on the bytes that remain.  Each records its calls as `ReadLoop` or `WriteLoop`.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies readCall writeCall readData writeData)

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-! ## The store of the block -/

/-- The store that the stamp program keeps before the function: related to the machine, written
only in the block of `N` bytes from `root`, and holding the bytes `D` from `root`. -/
def ReadStore (P : Platform) (cap : Nat) (gts : List ValueType) (st : Store Unit) (root N : Nat)
    (D : List UInt8) (s : State) : Prop :=
  ∃ st', StoreRel P cap gts st' s ∧ LeanExe.Pipeline.WritesWithin st st' root N ∧
    ∀ i < D.length, st'.mem.bytes (root + i) = D.getD i 0

/-- A write of the bytes `O` into the block after the bytes `D` keeps the store of the block,
which then holds `D` and the first `r` bytes of `O`. -/
theorem ReadStore.write {cap : Nat} {gts : List ValueType} {st : Store Unit} {root N : Nat}
    {D O : List UInt8} {s s' : State} (h : ReadStore P cap gts st root N D s)
    (hN : root + N ≤ st.mem.pages * 65536) (hfit : D.length + O.length ≤ N)
    (h17 : s'.x 17 = s.x 17) (h18 : s'.x 18 = s.x 18)
    (hmem : s'.mem = writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (root + D.length))) O)
    {r : Nat} (hr : r ≤ O.length) : ReadStore P cap gts st root N (D ++ O.take r) s' := by
  obtain ⟨st', hsr, hW, hD⟩ := h
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  rw [hW.pages] at hpg
  have hcapN : root + N ≤ cap * 65536 := Nat.le_trans hN (Nat.mul_le_mul_right _ hpg.2)
  have h32 : root + D.length + O.length < 2 ^ 32 := by
    simp only [Nat.reducePow]
    omega
  have hsr' : StoreRel P cap gts (storeBytes st' (root + D.length) O) s' := by
    have hw := StoreRel.kernelWrite P O st' s (root + D.length) hsr (by rw [hW.pages]; omega)
    exact hw.regs h17 h18 (by rw [hmem])
  refine ⟨_, hsr', ?_, fun i hi => ?_⟩
  · obtain ⟨hg1, hpg1, -⟩ := storeBytes_globals st' (root + D.length) O
    refine ⟨hg1.trans hW.globals, hpg1.trans hW.pages, fun a ha => ?_⟩
    rw [storeBytes_bytes st' _ O h32 a, dite_eq_right (by omega), hW.bytes a ha]
  · simp only [List.length_append, List.length_take] at hi
    rw [storeBytes_bytes st' _ O h32 (root + i)]
    by_cases hig : i < D.length
    · rw [dite_eq_right (by omega), hD i hig]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hig]
    · rw [dite_eq_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), List.getElem?_take_of_lt (by omega),
        List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr 1
      omega

/-- A write of the bytes `O` into the block after the bytes `D` changes no byte at or above the
stack's limit. -/
theorem ReadStore.frame {cap : Nat} {gts : List ValueType} {st : Store Unit} {root N : Nat}
    {D O : List UInt8} {s : State} (h : ReadStore P cap gts st root N D s)
    (hN : root + N ≤ st.mem.pages * 65536) (hfit : D.length + O.length ≤ N) :
    ∀ a : UInt64, (s.x 18).toNat ≤ a.toNat →
      writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (root + D.length))) O a = s.mem a := by
  obtain ⟨st', hsr, hW, -⟩ := h
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  rw [hW.pages] at hpg
  have hcapN : root + N ≤ cap * 65536 := Nat.le_trans hN (Nat.mul_le_mul_right _ hpg.2)
  intro a ha
  apply writeList_other
  rcases Nat.eq_zero_or_pos O.length with h0 | h0
  · omega
  have hb := hsr.below
  have hx1 := area_toNat P hsr (j := root + D.length) (by unfold areaSize; omega)
  rw [toNat_sub_le (by unfold areaSize at hb; omega), hx1]
  unfold areaSize at hb
  omega

/-- The bytes that the block holds where `ReadStore` holds `D`, as the machine's memory reads
them. -/
theorem ReadStore.mapped {cap : Nat} {gts : List ValueType} {st : Store Unit} {root N : Nat}
    {D : List UInt8} {s : State} (h : ReadStore P cap gts st root N D s)
    (hN : root + N ≤ st.mem.pages * 65536) :
    ∀ j < N, P.normal (s.x 17 + UInt64.ofNat (4096 + (root + j))) = true := by
  obtain ⟨st', hsr, hW, -⟩ := h
  have hpg := hsr.pages
  rw [hW.pages] at hpg
  have hcapN : root + N ≤ cap * 65536 := Nat.le_trans hN (Nat.mul_le_mul_right _ hpg.2)
  intro j hj
  exact hsr.mapped _ (by unfold areaSize; omega)

/-! ## Branches -/

/-- After a call that returned a value above the count in X2, `CBZ X0`, `SUBS XZR, X0, X2`, and
`B.HI` at `a` reach the target `e` of `B.HI`. -/
theorem run_aboveHi {a e : UInt64} {fz fl : Fin 524288}
    (hc : CodeAt code a [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fl])
    (hfl : cbField (after a 2) e = .ok fl) {s : State} (hpc : s.pc = a) (hlt : s.x 2 < s.x 0) :
    ∃ t, Reach P code s t ∧ t.pc = e ∧ t.io = s.io := by
  have c0 := hc 0 (by simp)
  simp only [List.getElem_cons_zero, after_zero] at c0
  have hne : s.x 0 ≠ 0 := fun h => by
    rw [h, UInt64.lt_iff_toNat_lt] at hlt
    simp at hlt
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0) (cbz_next P hne)
    (.refl _)
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc]; simp [after]
  obtain ⟨t, rt, pt, -, -, -, iot⟩ := run_hiReg P code (x := 0) (y := 2)
    (CodeAt.split code (l1 := [.cbz 0 fz]) hc rfl).2 (by rw [after_after]; exact hfl) p1
  have hlt' : s1.x 2 < s1.x 0 := hlt
  rw [ite_eq_left hlt'] at pt
  exact ⟨t, r1.trans rt, pt, iot⟩

/-- The part of a pass of a read loop after the call, from the `CBZ` at `after H 2`, with the
read's count `r` in X0 and the block's remaining bytes `c`, at least `r`, in X2: a count of 0
reaches `after H 9`, a count below `c` steps X1 and X2 and returns to the loop's head `L`, and a
count of `c` reaches `e64`. -/
theorem run_readTail' {H L e64 e65 : UInt64} {fe fl fr : Fin 524288} {go : Fin 67108864}
    (hc : CodeAt code (after H 2) [.cbz 0 fe, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .cbnz 2 fr, .b go])
    (hfe : cbField (after H 2) (after H 9) = .ok fe) (hfl : cbField (after H 4) e65 = .ok fl)
    (hfr : cbField (after H 7) L = .ok fr) (hgo : bField (after H 8) e64 = .ok go)
    {s : State} (hpc : s.pc = after H 2) {r c : Nat} (hr : r ≤ c) (hc64 : c < 2 ^ 64)
    (h0 : s.x 0 = UInt64.ofNat r) (h2 : s.x 2 = UInt64.ofNat c) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 1 → q ≠ 2 → t.x q = s.x q) ∧
      ((r = 0 ∧ t.pc = after H 9 ∧ t.x 1 = s.x 1 ∧ t.x 2 = s.x 2) ∨
        (0 < r ∧ r < c ∧ t.pc = L ∧ t.x 1 = s.x 1 + UInt64.ofNat r ∧
          t.x 2 = UInt64.ofNat (c - r)) ∨
        (0 < r ∧ r = c ∧ t.pc = e64)) := by
  have c0 := hc 0 (by simp)
  have c5 := hc 5 (by simp)
  have c6 := hc 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c0 c5 c6
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · refine ⟨{ s with pc := after H 9 }, cbz_taken P code (by rw [hpc]; exact c0) hpc hfe
      (by rw [h0]; rfl), rfl, rfl, rfl, fun _ _ _ => rfl, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
  have hr64 : r < 2 ^ 64 := by omega
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h0]; exact ofNat_ne_zero hpos hr64)) (.refl _)
  have p1 : s1.pc = after H 3 := by show s.pc + 4 = _; rw [hpc, ← after_succ]
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c1 c2
  have hhi' : CodeAt code (after H 3) [.subsReg 31 0 2, .bcond 8 fl] :=
    CodeAt.cons.mpr ⟨c1, CodeAt.cons.mpr ⟨by rw [after_after]; exact c2,
      fun i hi => absurd hi (by simp)⟩⟩
  obtain ⟨s2, r2, p2, x2, sp2, mem2, io2⟩ := run_hiReg P code (x := 0) (y := 2) hhi'
    (by rw [after_after]; exact hfl) p1
  have hnlt : ¬ s1.x 2 < s1.x 0 := by
    show ¬ s.x 2 < s.x 0
    rw [h0, h2, ofNat_lt_ofNat hc64 hr64]
    omega
  rw [ite_eq_right hnlt, after_after] at p2
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c3 c4
  obtain ⟨s3, r3, p3, x13, k3, sp3, mem3, io3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p2]; exact c3) (rfl : LeanExe.A64.exec P (.addReg 1 1 0) s2 = _)
  obtain ⟨s4, r4, p4, x24, k4, sp4, mem4, io4⟩ := run_setX P code (d := 2) (by decide)
    (by rw [p3, p2, ← after_succ]; exact c4) (rfl : LeanExe.A64.exec P (.subReg 2 2 0) s3 = _)
  have p4' : s4.pc = after H 7 := by rw [p4, p3, p2, ← after_succ, ← after_succ]
  have hx1 : s4.x 1 = s.x 1 + UInt64.ofNat r := by
    rw [k4 1 (by decide), x13, x2 1, x2 0]
    show s.x 1 + s.x 0 = _
    rw [h0]
  have hx2 : s4.x 2 = UInt64.ofNat (c - r) := by
    rw [x24, k3 2 (by decide), k3 0 (by decide), x2 2, x2 0]
    show s.x 2 - s.x 0 = _
    rw [h0, h2, ofNat_sub_ofNat hr hc64]
  have hk4 : ∀ q : Fin 32, q ≠ 1 → q ≠ 2 → s4.x q = s.x q := fun q h1 h2' => by
    rw [k4 q h2', k3 q h1, x2 q]
    rfl
  have hsp4 : s4.sp = s.sp := by rw [sp4, sp3, sp2]
  have hmem4 : s4.mem = s.mem := by rw [mem4, mem3, mem2]
  have hio4 : s4.io = s.io := by rw [io4, io3, io2]
  let s5 : State := { s4 with pc := if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4 }
  have r5 : Reach P code s4 s5 := reach_exec P code (by rw [p4']; exact c5) rfl (.refl _)
  have r15 : Reach P code s s5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  rcases Nat.lt_or_ge r c with hlt | hge
  · have hne : s4.x 2 ≠ 0 := by rw [hx2]; exact ofNat_ne_zero (by omega) (by omega)
    refine ⟨s5, r15, hsp4, hmem4, hio4, hk4, .inr (.inl ⟨hpos, hlt, ?_, hx1, hx2⟩)⟩
    show (if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4) = L
    rw [ite_eq_left hne, p4']
    exact cbField_target hfr
  · have hrc : r = c := by omega
    have heq : s4.x 2 = 0 := by rw [hx2, show c - r = 0 by omega]; rfl
    have p5 : s5.pc = after H 8 := by
      show (if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4) = _
      rw [ite_eq_right (by simp [heq]), p4', ← after_succ]
    let s6 : State := { s5 with pc := s5.pc + sext 26 go.val * 4 }
    have r6 : Reach P code s5 s6 := reach_exec P code (by rw [p5]; exact c6) rfl (.refl _)
    exact ⟨s6, r15.trans r6, hsp4, hmem4, hio4, hk4, .inr (.inr ⟨hpos, hrc, by
      show s5.pc + sext 26 go.val * 4 = e64
      rw [p5]
      exact bField_target hgo⟩)⟩

/-- The part of a pass of a write loop after the call, from the `CBZ` at `after W 3`, with the
write's count `r`, from 1 to the `c` bytes that remain, in X0 and `c` in X2: X1 and X2 step by
`r`, and the run returns to the loop's head `L`. -/
theorem run_writeTail' {W L e66 : UInt64} {fz fl : Fin 524288} {gb : Fin 67108864}
    (hc : CodeAt code (after W 3) [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .b gb])
    (hfl : cbField (after W 5) e66 = .ok fl) (hgb : bField (after W 8) L = .ok gb)
    {s : State} (hpc : s.pc = after W 3) {r c : Nat} (hr0 : 0 < r) (hr : r ≤ c)
    (hc64 : c < 2 ^ 64) (h0 : s.x 0 = UInt64.ofNat r) (h2 : s.x 2 = UInt64.ofNat c) :
    ∃ t, Reach P code s t ∧ t.pc = L ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 1 → q ≠ 2 → t.x q = s.x q) ∧ t.x 1 = s.x 1 + UInt64.ofNat r ∧
      t.x 2 = UInt64.ofNat (c - r) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c0 c1 c2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c3 c4 c5
  have hr64 : r < 2 ^ 64 := by omega
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h0]; exact ofNat_ne_zero hr0 hr64)) (.refl _)
  have p1 : s1.pc = after W 4 := by show s.pc + 4 = _; rw [hpc, ← after_succ]
  have hhi : CodeAt code (after W 4) [.subsReg 31 0 2, .bcond 8 fl] :=
    CodeAt.cons.mpr ⟨c1, CodeAt.cons.mpr ⟨by rw [after_after]; exact c2,
      fun i hi => absurd hi (by simp)⟩⟩
  obtain ⟨s2, r2, p2, x2, sp2, mem2, io2⟩ := run_hiReg P code (x := 0) (y := 2) hhi
    (by rw [after_after]; exact hfl) p1
  have hnlt : ¬ s1.x 2 < s1.x 0 := by
    show ¬ s.x 2 < s.x 0
    rw [h0, h2, ofNat_lt_ofNat hc64 hr64]
    omega
  rw [ite_eq_right hnlt, after_after] at p2
  obtain ⟨s3, r3, p3, x13, k3, sp3, mem3, io3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p2]; exact c3) (rfl : LeanExe.A64.exec P (.addReg 1 1 0) s2 = _)
  obtain ⟨s4, r4, p4, x24, k4, sp4, mem4, io4⟩ := run_setX P code (d := 2) (by decide)
    (by rw [p3, p2, ← after_succ]; exact c4) (rfl : LeanExe.A64.exec P (.subReg 2 2 0) s3 = _)
  have p4' : s4.pc = after W 8 := by rw [p4, p3, p2, ← after_succ, ← after_succ]
  let s5 : State := { s4 with pc := s4.pc + sext 26 gb.val * 4 }
  have r5 : Reach P code s4 s5 := reach_exec P code (by rw [p4']; exact c5) rfl (.refl _)
  refine ⟨s5, r1.trans (r2.trans (r3.trans (r4.trans r5))), ?_, by rw [sp4, sp3, sp2],
    by rw [mem4, mem3, mem2], by rw [io4, io3, io2], fun q h1 h2' => ?_, ?_, ?_⟩
  · show s4.pc + sext 26 gb.val * 4 = L
    rw [p4']
    exact bField_target hgb
  · show s4.x q = _
    rw [k4 q h2', k3 q h1, x2 q]
    rfl
  · show s4.x 1 = _
    rw [k4 1 (by decide), x13, x2 1, x2 0]
    show s.x 1 + s.x 0 = _
    rw [h0]
  · show s4.x 2 = _
    rw [x24, k3 2 (by decide), k3 0 (by decide), x2 2, x2 0]
    show s.x 2 - s.x 0 = _
    rw [h0, h2, ofNat_sub_ofNat hr hc64]

/-! ## Bytes of reads and writes -/

theorem readBytes_read {d a : UInt64} {c : Nat} (hc : c < 2 ^ 64) {pr out : List UInt8}
    {r : UInt64} (hr : r.toNat ≤ c) :
    LeanExe.Linux.Event.readBytes d ⟨readCall, [d, a, UInt64.ofNat c], [], pr, r, out⟩ =
      out.take r.toNat := by
  unfold LeanExe.Linux.Event.readBytes
  rw [ite_eq_left ⟨rfl, rfl, by
    show r.toNat ≤ (UInt64.ofNat c).toNat
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc]
    exact hr⟩]

theorem writeBytes_write {d a : UInt64} {c : Nat} (hc : c < 2 ^ 64) {inp : List UInt8}
    {r : UInt64} (hr : r.toNat ≤ c) :
    LeanExe.Linux.Event.writeBytes d ⟨writeCall, [d, a, UInt64.ofNat c], [inp], [], r, []⟩ =
      inp.take r.toNat := by
  unfold LeanExe.Linux.Event.writeBytes
  rw [ite_eq_left ⟨rfl, rfl, by
    show r.toNat ≤ (UInt64.ofNat c).toNat
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc]
    exact hr⟩]
  rfl

theorem writeBytes_above {d a : UInt64} {c : Nat} (hc : c < 2 ^ 64) {inp : List UInt8}
    {r : UInt64} (hr : c < r.toNat) :
    LeanExe.Linux.Event.writeBytes d ⟨writeCall, [d, a, UInt64.ofNat c], [inp], [], r, []⟩ =
      [] := by
  unfold LeanExe.Linux.Event.writeBytes
  rw [ite_eq_right fun h => by
    have := h.2.2
    simp only [LeanExe.Linux.arg, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc] at this
    omega]

theorem readList_length (m : UInt64 → UInt8) :
    ∀ (a : UInt64) (n : Nat), (readList m a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by rw [readList, List.length_cons, readList_length m (a + 1) n]

theorem readList_take (m : UInt64 → UInt8) (a : UInt64) {r c : Nat} (h : r ≤ c) :
    (readList m a c).take r = readList m a r := by
  rw [show c = r + (c - r) by omega, readList_add, List.take_left' (readList_length m a r)]

/-! ## The read loop -/

/-- The read loop of the stamp program at `H`, from its head with `c` bytes of the block of `N`
left, the bytes `pre` and those that the trace's reads of `d` returned before them, and the
descriptor `d` in the frame's slot 2.  Each pass loads `d`, reads it into the rest of the block,
and tests the result.  The run reaches `e68` after a read whose result lies above its count;
reaches `e64` when the bytes read fill the block; or leaves the loop at `after H 10` after a read
of a positive count that returned 0, with the block holding the bytes read.  The reads are those
of `ReadLoop` from the block's rest. -/
theorem run_stampReadLoop {H e64 e68 svc : UInt64} {fe f68 fr : Fin 524288}
    {gR g64 : Fin 67108864}
    (hc : CodeAt code H [.ldr 0 31 2, .movz 8 63 0, .bl gR, .cbz 0 fe, .subsReg 31 0 2,
      .bcond 8 f68, .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b g64])
    (hgR : bField (after H 2) svc = .ok gR) (hfe : cbField (after H 3) (after H 10) = .ok fe)
    (hf68 : cbField (after H 5) e68 = .ok f68) (hfr : cbField (after H 8) H = .ok fr)
    (hg64 : bField (after H 9) e64 = .ok g64)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hT : T.find? (fun c => c.arm64 == 63) = some readCall)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (h10 : (after H 10).toNat < 2 ^ 55) (h64 : e64.toNat < 2 ^ 55) (h68 : e68.toNat < 2 ^ 55)
    {cap : Nat} {gts : List ValueType} (st : Store Unit) (root N : Nat)
    (hN : root + N ≤ st.mem.pages * 65536) (pre : List UInt8) (d sp : UInt64)
    (hal : sp % 16 = 0) (htop : sp.toNat < 2 ^ 63)
    (hmap : ∀ j < 24, P.normal (sp + UInt64.ofNat j) = true) :
    ∀ c (p : Proc), (pre ++ readData d (sysEvents p.trace)).length + c = N → 0 < c →
      p.core.pc = H → p.fpcr = fpcrValue → p.core.x 2 = UInt64.ofNat c →
      p.core.x 1 = p.core.x 17 +
        UInt64.ofNat (4096 + (root + (pre ++ readData d (sysEvents p.trace)).length)) →
      p.core.sp = sp → (p.core.x 18).toNat ≤ sp.toNat → load64 p.core.mem (slotAddr sp 2) = d →
      ReadStore P cap gts st root N (pre ++ readData d (sysEvents p.trace)) p.core →
      ∃ p' rs, ProcReachWith T R P code p p' ∧ p'.fpcr = fpcrValue ∧ p'.core.io = p.core.io ∧
        sysEvents p'.trace = sysEvents p.trace ++ rs ∧
        ((p'.core.pc = e68 ∧ ReadLoop d (fun c r => c < r.toNat) (p.core.x 1) c rs) ∨
         (p'.core.pc = e64 ∧ ReadLoop d (fun c r => 0 < c ∧ r.toNat = c) (p.core.x 1) c rs ∧
           (pre ++ readData d (sysEvents p'.trace)).length = N) ∨
         (p'.core.pc = after H 10 ∧
           ReadLoop d (fun c r => 0 < c ∧ r = 0) (p.core.x 1) c rs ∧
           (pre ++ readData d (sysEvents p'.trace)).length < N ∧
           p'.core.x 2 = UInt64.ofNat (N - (pre ++ readData d (sysEvents p'.trace)).length) ∧
           ReadStore P cap gts st root N (pre ++ readData d (sysEvents p'.trace)) p'.core ∧
           (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 30 → p'.core.x q = p.core.x q) ∧
           p'.core.sp = p.core.sp ∧
           (∀ a : UInt64, (p.core.x 18).toNat ≤ a.toNat → p'.core.mem a = p.core.mem a))) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  have hct : CodeAt code (after (after H 1) 2) [.cbz 0 fe, .subsReg 31 0 2, .bcond 8 f68,
      .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b g64] := by
    rw [after_after]
    exact (CodeAt.split code (l1 := [.ldr 0 31 2, .movz 8 63 0, .bl gR]) hc rfl).2
  have hfe' : cbField (after (after H 1) 2) (after (after H 1) 9) = .ok fe := by
    rw [after_after, after_after]; exact hfe
  have hf68' : cbField (after (after H 1) 4) e68 = .ok f68 := by rw [after_after]; exact hf68
  have hfr' : cbField (after (after H 1) 7) H = .ok fr := by rw [after_after]; exact hfr
  have hg64' : bField (after (after H 1) 8) e64 = .ok g64 := by rw [after_after]; exact hg64
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro p hgc hc0 hpc hf h2 h1 hsp h18 hd hst
  generalize hD : pre ++ readData d (sysEvents p.trace) = D at hgc h1 hst
  have hst' := hst
  obtain ⟨st', hsr, hW, -⟩ := hst'
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  rw [hW.pages] at hpg
  have hcapN : root + N ≤ cap * 65536 := Nat.le_trans hN (Nat.mul_le_mul_right _ hpg.2)
  have hc64 : c + 4095 < 2 ^ 64 := by
    simp only [Nat.reducePow] at *
    omega
  have hc64' : c < 2 ^ 64 := by omega
  have hmapc : P.mapped (p.core.x 1) c = true := mapped_of_all P fun i hi => by
    rw [h1, add_ofNat_add, show 4096 + (root + D.length) + i = 4096 + (root + (D.length + i)) by
      omega]
    exact hst.mapped hN _ (by omega)
  -- the load of the descriptor, X8, and the call
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ := run_setX P code (d := 0) (by decide)
    (by rw [hpc]; exact c0) (exec_ldr_sp P (s := p.core) (r := 0) (i := 2) _
      (by rw [hsp]; exact hal) fun j hj => by rw [hsp]; exact hmap _ (by omega))
  obtain ⟨t2, r2, p2, x82, k2, sp2, mem2, io2⟩ := run_movz P code (d := 8) (v := 63) (by decide)
    (by rw [p1, hpc, ← after_one]; exact c1)
  have p2' : t2.pc = after H 2 := by rw [p2, p1, hpc, after_succ H 1, after_one]
  have q1 : ProcReachWith T R P code p { p with core := t2 } :=
    ProcReachWith.of_reach' hdom hf (r1.trans r2) (by rw [p2']; exact hdom _ _ c2)
  have hx0 : t2.x 0 = d := by rw [k2 0 (by decide), x01, hsp, hd]
  have hx1 : t2.x 1 = p.core.x 1 := by rw [k2 1 (by decide), k1 1 (by decide)]
  have hx2 : t2.x 2 = UInt64.ofNat c := by rw [k2 2 (by decide), k1 2 (by decide), h2]
  have hx2n : (t2.x 2).toNat = c := by rw [hx2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64']
  have hmem2 : t2.mem = p.core.mem := by rw [mem2, mem1]
  have hsys := sysCall_read (R := R) (P := P) (p := ({ p with core := t2 } : Proc).call
    (after H 2) svc) (by
      rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
      show P.mapped (t2.x 1) (t2.x 2).toNat = true
      rw [hx1, hx2n]
      exact hmapc)
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_mem] at hsys
  change sysCall R P _ _ = some (Proc.ret _ _ (writeList t2.mem (t2.x 1)
    ((List.range (t2.x 2).toNat).map _)) (.sys ⟨_, [t2.x 0, t2.x 1, t2.x 2], [],
      readList t2.mem (t2.x 1) (t2.x 2).toNat, _, (List.range (t2.x 2).toNat).map _⟩)) at hsys
  rw [hx2n, hx0, hx1, hx2, hmem2] at hsys
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c2 hgR hdom
    (by rw [after_after]; exact hdom _ _ c3) (p := { p with core := t2 }) p2'
    (by show T.find? (fun c => c.arm64 == t2.x 8) = _; rw [x82]; exact hT) rfl hsys
  generalize hRk : R (({ p with core := t2 } : Proc).call (after H 2) svc).trace.length = Rk
    at x0q2 memq2 trq2
  generalize hO : (List.range c).map Rk.bytes = O at memq2 trq2
  have hOl : O.length = c := by rw [← hO]; simp
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hf
  have hio2 : q2.core.io = p.core.io := by rw [ioq2]; show t2.io = _; rw [io2, io1]
  have hev : sysEvents q2.trace = sysEvents p.trace ++ [⟨readCall, [d, p.core.x 1,
      UInt64.ofNat c], [], readList p.core.mem (p.core.x 1) c, Rk.ret, O⟩] := by
    rw [trq2, sysEvents_snoc]
  have pq2' : q2.core.pc = after (after H 1) 2 := by rw [pq2, after_after, after_after]
  have hq2x2 : q2.core.x 2 = UInt64.ofNat c := by rw [kq2 2 (by decide) (by decide), hx2]
  have hq2x : ∀ r : Fin 32, r ≠ 0 → r ≠ 8 → r ≠ 30 → q2.core.x r = p.core.x r :=
    fun r h0 h8 h30 => by
      rw [kq2 r h0 h30]
      show t2.x r = _
      rw [k2 r h8, k1 r h0]
  by_cases hle : Rk.ret.toNat ≤ c
  swap
  · -- a result above the count: the branch to `e68`
    have hlt : q2.core.x 2 < q2.core.x 0 := by
      rw [hq2x2, x0q2, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64']
      omega
    obtain ⟨t, rt, tpc, tio⟩ := run_aboveHi (P := P) (code := code)
      (CodeAt.split code (l1 := [.cbz 0 fe, .subsReg 31 0 2, .bcond 8 f68]) hct rfl).1
      (by rw [after_after, after_after]; exact hf68) pq2' hlt
    exact ⟨{ q2 with core := t }, [_], q1.trans (rq2.trans
      (ProcReachWith.of_reach' hdom fq2' rt (by rw [tpc]; exact h68))), fq2',
      by show t.io = _; rw [tio, hio2], hev, .inl ⟨tpc, rfl, rfl, .inl ⟨rfl, by
        show c < Rk.ret.toNat
        omega⟩⟩⟩
  -- a result within the count
  obtain ⟨t, rt, spt, memt, iot, kt, out⟩ := run_readTail' (P := P) (code := code) hct hfe' hf68'
    hfr' hg64' pq2' hle hc64' (by rw [x0q2, UInt64.ofNat_toNat]) hq2x2
  have hend : t.pc.toNat < 2 ^ 55 := by
    rcases out with ⟨-, e, -, -⟩ | ⟨-, -, e, -, -⟩ | ⟨-, -, e⟩ <;> rw [e]
    · rw [after_after]; exact h10
    · rw [← hpc]; exact hdom _ _ (by rw [hpc]; exact c0)
    · exact h64
  have q4 := ProcReachWith.of_reach' (T := T) (R := R) hdom fq2' rt hend
  have hrd : readData d (sysEvents q2.trace) = readData d (sysEvents p.trace) ++
      O.take Rk.ret.toNat := by
    rw [hev, readData_append, readData_single, readBytes_read hc64' hle]
  have hD' : pre ++ readData d (sysEvents q2.trace) = D ++ O.take Rk.ret.toNat := by
    rw [hrd, ← List.append_assoc, hD]
  have hDl : (D ++ O.take Rk.ret.toNat).length = D.length + Rk.ret.toNat := by
    rw [List.length_append, List.length_take, hOl, Nat.min_eq_left hle]
  have h17t : t.x 17 = p.core.x 17 := by
    rw [kt 17 (by decide) (by decide)]
    exact hq2x 17 (by decide) (by decide) (by decide)
  have h18t : t.x 18 = p.core.x 18 := by
    rw [kt 18 (by decide) (by decide)]
    exact hq2x 18 (by decide) (by decide) (by decide)
  have hmemt : t.mem = writeList p.core.mem (p.core.x 17 + UInt64.ofNat (4096 + (root +
      D.length))) O := by rw [memt, memq2, ← h1]
  have hst2 : ReadStore P cap gts st root N (pre ++ readData d (sysEvents q2.trace)) t := by
    rw [hD']
    exact hst.write hN (by omega) h17t h18t hmemt (by omega)
  have hframe : ∀ a : UInt64, (p.core.x 18).toNat ≤ a.toNat → t.mem a = p.core.mem a :=
    fun a ha => by rw [hmemt]; exact hst.frame hN (by omega) a ha
  have hev1 : ∀ last : Nat → UInt64 → Prop, last c Rk.ret →
      ReadLoop d last (p.core.x 1) c [⟨readCall, [d, p.core.x 1, UInt64.ofNat c], [],
        readList p.core.mem (p.core.x 1) c, Rk.ret, O⟩] :=
    fun last h => ⟨rfl, rfl, .inl ⟨rfl, h⟩⟩
  rcases out with ⟨hr0, tpc, tx1, tx2⟩ | ⟨hrp, hlt, tpc, tx1, tx2⟩ | ⟨hrp, hrc, tpc⟩
  · -- a read that returned 0: the end of the loop
    have hr0' : Rk.ret = 0 := UInt64.toNat_inj.mp hr0
    refine ⟨{ q2 with core := t }, [_], q1.trans (rq2.trans q4), fq2',
      by show t.io = _; rw [iot, hio2], hev, .inr (.inr ⟨by rw [tpc, after_after],
        hev1 _ ⟨hc0, hr0'⟩, ?_, ?_, hst2, fun q h0 h1' h2' h8 h30 => ?_, ?_, hframe⟩)⟩
    · show (pre ++ readData d (sysEvents q2.trace)).length < N
      rw [hD', hDl]
      omega
    · show t.x 2 = _
      rw [tx2, hq2x2, hD', hDl]
      congr 1
      omega
    · show t.x q = _
      rw [kt q h1' h2']
      exact hq2x q h0 h8 h30
    · show t.sp = _
      rw [spt, spq2]
      show t2.sp = _
      rw [sp2, sp1]
  · -- a short read: the loop again
    have ht2 : ({ q2 with core := t } : Proc).core.x 1 = ({ q2 with core := t } : Proc).core.x 17 +
        UInt64.ofNat (4096 + (root + (pre ++ readData d
          (sysEvents ({ q2 with core := t } : Proc).trace)).length)) := by
      show t.x 1 = t.x 17 + _
      rw [tx1, kq2 1 (by decide) (by decide), h17t]
      show t2.x 1 + _ = _
      rw [hx1, h1, add_ofNat_add, hD', hDl]
      congr 2
      omega
    have hsp' : t.sp = sp := by rw [spt, spq2]; show t2.sp = _; rw [sp2, sp1, hsp]
    have hd' : load64 t.mem (slotAddr sp 2) = d := by
      rw [load64_congr (m' := p.core.mem) fun k hk => hframe _ (by
        have := le_slot (sp := sp) (i := 2) (m := 0) (k := k) hk htop (by decide) (by decide)
        omega), hd]
    have hgc' : (pre ++ readData d (sysEvents q2.trace)).length + (c - Rk.ret.toNat) = N := by
      rw [hD', hDl]
      omega
    obtain ⟨p'', rs, q5, hf'', hio'', htr'', res⟩ := ih (c - Rk.ret.toNat) (by omega)
      { q2 with core := t } hgc' (by omega) tpc fq2' tx2 ht2 hsp' (by rw [h18t]; exact h18) hd'
      hst2
    have hx1' : t.x 1 = p.core.x 1 + Rk.ret := by
      rw [tx1, kq2 1 (by decide) (by decide), UInt64.ofNat_toNat]
      show t2.x 1 + _ = _
      rw [hx1]
    refine ⟨p'', ⟨readCall, [d, p.core.x 1, UInt64.ofNat c], [],
      readList p.core.mem (p.core.x 1) c, Rk.ret, O⟩ :: rs, q1.trans (rq2.trans (q4.trans q5)),
      hf'', by rw [hio'']; show t.io = _; rw [iot, hio2], by rw [htr'']; simp [hev], ?_⟩
    have hstep : ∀ last : Nat → UInt64 → Prop,
        ReadLoop d last (t.x 1) (c - Rk.ret.toNat) rs →
        ReadLoop d last (p.core.x 1) c (⟨readCall, [d, p.core.x 1, UInt64.ofNat c], [],
          readList p.core.mem (p.core.x 1) c, Rk.ret, O⟩ :: rs) :=
      fun last h => ⟨rfl, rfl, .inr ⟨hrp, hlt, by rw [← hx1']; exact h⟩⟩
    rcases res with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4, a5, hx'', hsp'', hfr''⟩
    · exact .inl ⟨a1, hstep _ a2⟩
    · exact .inr (.inl ⟨a1, hstep _ a2, a3⟩)
    · refine .inr (.inr ⟨a1, hstep _ a2, a3, a4, a5,
        fun q h0 h1' h2' h8 h30 => ?_, ?_, fun a ha => ?_⟩)
      · rw [hx'' q h0 h1' h2' h8 h30]
        show t.x q = _
        rw [kt q h1' h2']
        exact hq2x q h0 h8 h30
      · rw [hsp'']
        show t.sp = _
        rw [hsp', hsp]
      · rw [hfr'' a (by show (t.x 18).toNat ≤ _; rw [h18t]; exact ha)]
        exact hframe a ha
  · -- the block is full
    refine ⟨{ q2 with core := t }, [_], q1.trans (rq2.trans q4), fq2',
      by show t.io = _; rw [iot, hio2], hev, .inr (.inl ⟨tpc, hev1 _ ⟨hc0, hrc⟩, ?_⟩)⟩
    show (pre ++ readData d (sysEvents q2.trace)).length = N
    rw [hD', hDl]
    omega

/-! ## The write loop -/

/-- The write loop of the stamp program at `W`, from its head with `c` bytes from X1 to write,
all in Normal memory, and the descriptor `fd` in the frame's slot 2.  While bytes remain, each pass
loads `fd`, writes the rest, and tests the result.  A write whose result is 0 or lies above its
count reaches `e74` after writes that took a prefix of the bytes.  Otherwise the run leaves the
loop at `after W 10` after writes that took all of them, with the memory, SP, and every register
but X0, X1, X2, X8, and X30 kept.  The writes are those of `WriteLoop`. -/
theorem run_stampWriteLoop {W e74 svc : UInt64} {fd fz fw : Fin 524288} {gW gb : Fin 67108864}
    (hc : CodeAt code W [.cbz 2 fd, .ldr 0 31 2, .movz 8 64 0, .bl gW, .cbz 0 fz,
      .subsReg 31 0 2, .bcond 8 fw, .addReg 1 1 0, .subReg 2 2 0, .b gb])
    (hfd : cbField W (after W 10) = .ok fd) (hgW : bField (after W 3) svc = .ok gW)
    (hfz : cbField (after W 4) e74 = .ok fz) (hfw : cbField (after W 6) e74 = .ok fw)
    (hgb : bField (after W 9) W = .ok gb)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hT : T.find? (fun c => c.arm64 == 64) = some writeCall)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (h10 : (after W 10).toNat < 2 ^ 55)
    (h74 : e74.toNat < 2 ^ 55) (fdv sp : UInt64) (hal : sp % 16 = 0)
    (hmap : ∀ j < 24, P.normal (sp + UInt64.ofNat j) = true) :
    ∀ c (p : Proc), p.core.pc = W → p.fpcr = fpcrValue → p.core.x 2 = UInt64.ofNat c →
      c + 4095 < 2 ^ 64 → (∀ i < c, P.normal (p.core.x 1 + UInt64.ofNat i) = true) →
      p.core.sp = sp → load64 p.core.mem (slotAddr sp 2) = fdv →
      ∃ p' ws, ProcReachWith T R P code p p' ∧ p'.fpcr = fpcrValue ∧ p'.core.io = p.core.io ∧
        sysEvents p'.trace = sysEvents p.trace ++ ws ∧
        ((p'.core.pc = e74 ∧ WriteLoop fdv true (p.core.x 1) c ws ∧
            ∃ j ≤ c, writeData fdv ws = readList p.core.mem (p.core.x 1) j) ∨
         (p'.core.pc = after W 10 ∧ WriteLoop fdv false (p.core.x 1) c ws ∧
          writeData fdv ws = readList p.core.mem (p.core.x 1) c ∧
          p'.core.mem = p.core.mem ∧ p'.core.sp = p.core.sp ∧
          (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 30 →
            p'.core.x q = p.core.x q))) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4
  have hct : CodeAt code (after (after W 1) 3) [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw,
      .addReg 1 1 0, .subReg 2 2 0, .b gb] := by
    rw [after_after]
    exact (CodeAt.split code (l1 := [.cbz 2 fd, .ldr 0 31 2, .movz 8 64 0, .bl gW]) hc rfl).2
  have hfw' : cbField (after (after W 1) 5) e74 = .ok fw := by rw [after_after]; exact hfw
  have hgb' : bField (after (after W 1) 8) W = .ok gb := by rw [after_after]; exact hgb
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro p hpc hf h2 hc64 hmapc hsp hd
  have hc64' : c < 2 ^ 64 := by omega
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · -- nothing left: the `CBZ` leaves the loop
    have r0 := cbz_taken P code (by rw [hpc]; exact c0) hpc hfd (by rw [h2]; rfl)
    exact ⟨p.goto (after W 10), [], ProcReachWith.of_reach' hdom hf r0 h10, hf, rfl,
      by simp, .inr ⟨rfl, ⟨rfl, rfl⟩, by simp [writeData, readList], rfl, rfl,
        fun _ _ _ _ _ _ => rfl⟩⟩
  -- the `CBZ`, the load of the descriptor, X8, and the call
  let t0 : State := { p.core with pc := p.core.pc + 4 }
  have r0 : Reach P code p.core t0 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h2]; exact ofNat_ne_zero hc0 hc64')) (.refl _)
  have p0 : t0.pc = after W 1 := by show p.core.pc + 4 = _; rw [hpc, after_one]
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ := run_setX P code (d := 0) (by decide)
    (by rw [p0]; exact c1) (exec_ldr_sp P (s := t0) (r := 0) (i := 2) _
      (by show p.core.sp % 16 = 0; rw [hsp]; exact hal)
      fun j hj => by show P.normal (p.core.sp + _) = true; rw [hsp]; exact hmap _ (by omega))
  obtain ⟨t2, r2, p2, x82, k2, sp2, mem2, io2⟩ := run_movz P code (d := 8) (v := 64) (by decide)
    (by rw [p1, p0, ← after_succ]; exact c2)
  have p2' : t2.pc = after W 3 := by rw [p2, p1, p0, ← after_succ, ← after_succ]
  have q1 : ProcReachWith T R P code p { p with core := t2 } :=
    ProcReachWith.of_reach' hdom hf (r0.trans (r1.trans r2)) (by rw [p2']; exact hdom _ _ c3)
  have hx0 : t2.x 0 = fdv := by
    rw [k2 0 (by decide), x01]
    show load64 p.core.mem (slotAddr p.core.sp 2) = _
    rw [hsp, hd]
  have hx1 : t2.x 1 = p.core.x 1 := by rw [k2 1 (by decide), k1 1 (by decide)]; rfl
  have hx2 : t2.x 2 = UInt64.ofNat c := by rw [k2 2 (by decide), k1 2 (by decide)]; exact h2
  have hx2n : (t2.x 2).toNat = c := by rw [hx2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64']
  have hmem2 : t2.mem = p.core.mem := by rw [mem2, mem1]
  have hsys := sysCall_write (R := R) (P := P) (p := ({ p with core := t2 } : Proc).call
    (after W 3) svc) (by
      rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
      show P.mapped (t2.x 1) (t2.x 2).toNat = true
      rw [hx1, hx2n]
      exact mapped_of_all P hmapc)
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_mem] at hsys
  change sysCall R P _ _ = some (Proc.ret _ _ t2.mem (.sys ⟨_, [t2.x 0, t2.x 1, t2.x 2],
    [readList t2.mem (t2.x 1) (t2.x 2).toNat], [], _, []⟩)) at hsys
  rw [hx2n, hx0, hx1, hx2, hmem2] at hsys
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c3 hgW hdom
    (by rw [after_after]; exact hdom _ _ c4) (p := { p with core := t2 }) p2'
    (by show T.find? (fun c => c.arm64 == t2.x 8) = _; rw [x82]; exact hT) rfl hsys
  generalize hRk : (R (({ p with core := t2 } : Proc).call (after W 3) svc).trace.length).ret = v
    at x0q2 trq2
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hf
  have hio2 : q2.core.io = p.core.io := by rw [ioq2]; show t2.io = _; rw [io2, io1]
  have hev : sysEvents q2.trace = sysEvents p.trace ++ [⟨writeCall, [fdv, p.core.x 1,
      UInt64.ofNat c], [readList p.core.mem (p.core.x 1) c], [], v, []⟩] := by
    rw [trq2, sysEvents_snoc]
  have pq2' : q2.core.pc = after (after W 1) 3 := by rw [pq2, after_after, after_after]
  have hq2x2 : q2.core.x 2 = UInt64.ofNat c := by rw [kq2 2 (by decide) (by decide), hx2]
  have hq2x : ∀ r : Fin 32, r ≠ 0 → r ≠ 8 → r ≠ 30 → q2.core.x r = p.core.x r :=
    fun r h0 h8 h30 => by
      rw [kq2 r h0 h30]
      show t2.x r = _
      rw [k2 r h8, k1 r h0]
      rfl
  have hmemq2 : q2.core.mem = p.core.mem := by rw [memq2]
  have hspq2 : q2.core.sp = p.core.sp := by rw [spq2]; show t2.sp = _; rw [sp2, sp1]
  have hev1 : WriteLoop fdv true (p.core.x 1) c [⟨writeCall, [fdv, p.core.x 1, UInt64.ofNat c],
      [readList p.core.mem (p.core.x 1) c], [], v, []⟩] ↔ (v = 0 ∨ c < v.toNat) := by
    constructor
    · rintro ⟨-, -, -, ⟨-, -, h⟩ | ⟨-, -, h⟩⟩
      · exact h
      · exact absurd h (by simp [WriteLoop])
    · intro h
      exact ⟨hc0, rfl, rfl, .inl ⟨rfl, rfl, h⟩⟩
  rcases Nat.eq_zero_or_pos v.toNat with h0 | hpos
  · -- a result of 0: the `CBZ` reaches `e74`
    have hv0 : v = 0 := UInt64.toNat_inj.mp h0
    have r4 := cbz_taken P code (ms := q2.core) (by rw [pq2, after_after]; exact c4)
      (by rw [pq2, after_after]) hfz (by rw [x0q2, hv0])
    exact ⟨_, [_], q1.trans (rq2.trans (ProcReachWith.of_reach' hdom fq2' r4 h74)), fq2', hio2,
      hev, .inl ⟨rfl, hev1.mpr (.inl hv0), 0, Nat.zero_le _, by
        rw [writeData_single, writeBytes_write hc64' (by omega), hv0]
        simp [readList]⟩⟩
  by_cases hle : v.toNat ≤ c
  · -- a write of 1 to `c` bytes: the rest of the pass and the loop
    obtain ⟨t, rt, pt, spt, memt, iot, kt, x1t, x2t⟩ := run_writeTail' (P := P) (code := code) hct
      hfw' hgb' pq2' hpos hle hc64' (by rw [x0q2, UInt64.ofNat_toNat]) hq2x2
    have q4 := ProcReachWith.of_reach' (T := T) (R := R) hdom fq2' rt
      (by rw [pt, ← hpc]; exact hdom _ _ (by rw [hpc]; exact c0))
    have hx1t : t.x 1 = p.core.x 1 + v := by
      rw [x1t, hq2x 1 (by decide) (by decide) (by decide), UInt64.ofNat_toNat]
    obtain ⟨p', ws, q5, hf', hio', htr', res⟩ := ih (c - v.toNat) (by omega)
      { q2 with core := t } pt fq2' x2t (by omega) (fun i hi => by
        show P.normal (t.x 1 + UInt64.ofNat i) = true
        rw [hx1t, ← UInt64.ofNat_toNat (x := v), add_ofNat_add]
        exact hmapc _ (by omega))
      (by show t.sp = _; rw [spt, hspq2, hsp])
      (by show load64 t.mem _ = _; rw [memt, hmemq2]; rw [← hsp]; exact hsp ▸ hd)
    have hio : p'.core.io = p.core.io := by
      rw [hio']
      show t.io = _
      rw [iot, hio2]
    have hwd : writeData fdv [⟨writeCall, [fdv, p.core.x 1, UInt64.ofNat c],
        [readList p.core.mem (p.core.x 1) c], [], v, []⟩] =
        readList p.core.mem (p.core.x 1) v.toNat := by
      rw [writeData_single, writeBytes_write hc64' hle, readList_take _ _ hle]
    have hrl : ∀ j, readList t.mem (t.x 1) j =
        readList p.core.mem (p.core.x 1 + UInt64.ofNat v.toNat) j := fun j => by
      rw [memt, hmemq2, hx1t, UInt64.ofNat_toNat]
    refine ⟨p', ⟨writeCall, [fdv, p.core.x 1, UInt64.ofNat c],
      [readList p.core.mem (p.core.x 1) c], [], v, []⟩ :: ws, q1.trans (rq2.trans (q4.trans q5)),
      hf', hio, by rw [htr']; simp [hev], ?_⟩
    have hstep : ∀ fails : Bool, WriteLoop fdv fails (t.x 1) (c - v.toNat) ws →
        WriteLoop fdv fails (p.core.x 1) c (⟨writeCall, [fdv, p.core.x 1, UInt64.ofNat c],
          [readList p.core.mem (p.core.x 1) c], [], v, []⟩ :: ws) :=
      fun fails h => ⟨hc0, rfl, rfl, .inr ⟨hpos, hle, by rw [← hx1t]; exact h⟩⟩
    rcases res with ⟨hpc', hw, j, hj, hout'⟩ | ⟨hpc', hw, hout', hmem', hsp', hx'⟩
    · refine .inl ⟨hpc', hstep _ hw, v.toNat + j, by omega, ?_⟩
      rw [show (_ :: ws) = [_] ++ ws from rfl, writeData_append, hwd, hout', hrl,
        ← readList_add]
    · refine .inr ⟨hpc', hstep _ hw, ?_, ?_, ?_, ?_⟩
      · rw [show (_ :: ws) = [_] ++ ws from rfl, writeData_append, hwd, hout', hrl,
          ← readList_add, Nat.add_sub_cancel' hle]
      · rw [hmem']
        show t.mem = _
        rw [memt, hmemq2]
      · rw [hsp']
        show t.sp = _
        rw [spt, hspq2]
      · intro q h0' h1 h2' h8 h30
        rw [hx' q h0' h1 h2' h8 h30]
        show t.x q = _
        rw [kt q h1 h2']
        exact hq2x q h0' h8 h30
  · -- a result above the count: `B.HI` reaches `e74`
    have hlt : q2.core.x 2 < q2.core.x 0 := by
      rw [hq2x2, x0q2, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64']
      omega
    obtain ⟨t, rt, tpc, tio⟩ := run_aboveHi (P := P) (code := code)
      (CodeAt.split code (l1 := [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw]) hct rfl).1
      (by rw [after_after, after_after]; exact hfw) pq2' hlt
    exact ⟨{ q2 with core := t }, [_], q1.trans (rq2.trans
      (ProcReachWith.of_reach' hdom fq2' rt (by rw [tpc]; exact h74))), fq2',
      by show t.io = _; rw [tio, hio2], hev, .inl ⟨tpc, hev1.mpr (.inr (by omega)), 0,
        Nat.zero_le _, by rw [writeData_single, writeBytes_above hc64' (by omega)]; rfl⟩⟩

end LeanExe.A64
