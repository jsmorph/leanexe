module

public import Verified.ShimA64.Stubs
public import LeanExe.A64.Proof.WasiClocks

@[expose] public section

/-!
The stubs of `clock_time_get` and `random_get` against the shim's `clockInvoke` and
`randomInvoke`, first as runs of the process from a stub's entry on one platform and then on the
shim's machine.  `StubEnd` states what such a run gives for a result of the host function: a
return to X30 with the result's values and a state that holds its store, or the trap stub for the
shim's trap, each with the process's trace extended by the layer events that the result's world
appended, and with the memory kept outside the guest's memory and a region, the timespec for the
clock.  `clockStub_run` and `randomStub_run` prove it for every store and arguments, with the
replies of the process's next calls; `randomLoop_run` follows the loop of `random_get` by
induction on the bytes that remain, as `randomLoop` does.

`clockStub_sim` and `randomStub_sim` prove `Machine.StubSim` on `shimMachine`: they move the store
relation from `modulePlatform` to `wasiPlatform`, take the stub's run, and `stubResult_of_end`
restores the machine's relation, the trace's relation `TraceRel` from the run's events and the
scratch's relation `ScratchHolds` from the run's memory frame, since neither call opens nor closes
a descriptor.  The stack's limit lies above the scratch by the machine's relation, so the
timespec's bytes lie below SP.

The facts about bytes and words that the proofs use come first: `writeList_at` and
`load64_writeList` read back bytes that a call wrote, `store64_writeList` states a word's store as
the store of its bytes by `byteOf`, `leBytes_eight` states those bytes as those of `leBytes`, and
`clock_quotient_iff` states the stub's test against the quotient of `UDIV` as the specification's
test of the time's range.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

/-! ## Bytes and words -/

/-- Byte `k` of the bytes `bs` written from `a`. -/
theorem writeList_at (m : UInt64 → UInt8) : ∀ (bs : List UInt8) (a : UInt64) (k : Nat),
    k < bs.length → bs.length < 2 ^ 64 → writeList m a bs (a + UInt64.ofNat k) = bs.getD k 0
  | [], _, _, h, _ => absurd h (by simp)
  | b :: bs, a, 0, _, hl => by
    simp only [List.length_cons] at hl
    rw [add_ofNat_zero, writeList, writeList_other _ bs (a + 1) a ?_]
    · simp [store8]
    · have ha := a.toNat_lt
      simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat, Nat.reducePow] at hl ⊢
      omega
  | b :: bs, a, k + 1, hk, hl => by
    simp only [List.length_cons] at hk hl
    rw [writeList, ← LeanExe.Linux.succ_ofNat, writeList_at _ bs (a + 1) k (by omega) (by omega)]
    simp

/-- The word at byte `j` of the bytes `bs` written from `a`. -/
theorem load64_writeList (m : UInt64 → UInt8) (bs : List UInt8) (a : UInt64) {j : Nat}
    (hj : j + 8 ≤ bs.length) (hl : bs.length < 2 ^ 64) :
    load64 (writeList m a bs) (a + UInt64.ofNat j) = leWord ((bs.drop j).take 8) := by
  apply load64_bytes
  intro k hk
  rw [byteOf_leWord (by simp) hk, add_ofNat_add, writeList_at m bs a (j + k) (by omega) hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, ite_eq_left hk]

/-- A word's store is the store of its eight bytes, the lowest first. -/
theorem store64_writeList (m : UInt64 → UInt8) (a v : UInt64) :
    store64 m a v = writeList m a ((List.range 8).map (LeanExe.A64.byteOf v)) := by
  funext b
  by_cases h : b - a < 8
  · have hk : (b - a).toNat < 8 := by
      rw [UInt64.lt_iff_toNat_lt] at h
      simpa using h
    have hb : b = a + UInt64.ofNat (b - a).toNat := by
      rw [UInt64.ofNat_toNat]
      apply UInt64.toNat_inj.mp
      have := a.toNat_lt
      have := b.toNat_lt
      simp only [UInt64.toNat_add, UInt64.toNat_sub, Nat.reducePow] at *
      omega
    rw [hb, store64_byteOf _ _ _ hk, writeList_at _ _ _ _ (by simpa using hk) (by simp)]
    simp [hk]
  · rw [store64_other _ _ _ _ h, writeList_other _ _ _ _ (by
      rw [UInt64.lt_iff_toNat_lt] at h
      simpa using h)]

/-- The bytes of `leBytes 8 t` for a value below `2^64` are those of the word. -/
theorem leBytes_eight {t : Nat} (ht : t < 2 ^ 64) :
    (leBytes 8 t).data.data.toList = (List.range 8).map (LeanExe.A64.byteOf (UInt64.ofNat t)) := by
  simp only [leBytes, bytesOfList, List.toList_toArray]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  apply UInt8.toNat_inj.mp
  rw [byteOf_toNat _ hk, UInt64.toNat_ofNat_of_lt' ht]
  simp [Verified.Wasi.byteOf, Nat.pow_mul]

/-- The 16 bytes from `T` after stores of 0 at `T` and `T + 8` are zeros. -/
theorem readList_cleared (m : UInt64 → UInt8) (T : UInt64) :
    readList (store64 (store64 m T 0) (T + UInt64.ofNat 8) 0) T 16 = List.replicate 16 0 := by
  have h : ∀ j < 16, store64 (store64 m T 0) (T + UInt64.ofNat 8) 0 (T + UInt64.ofNat j) = 0 := by
    intro j hj
    by_cases hlo : j < 8
    · rw [store64_other _ _ _ _ ?_, store64_byteOf _ _ _ hlo]
      · simp [LeanExe.A64.byteOf]
      · rw [UInt64.lt_iff_toNat_lt]
        have := T.toNat_lt
        simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat,
          Nat.reducePow] at *
        omega
    · rw [show T + UInt64.ofNat j = T + UInt64.ofNat 8 + UInt64.ofNat (j - 8) by
        rw [add_ofNat_add]; congr 2; omega, store64_byteOf _ _ _ (by omega)]
      simp [LeanExe.A64.byteOf]
  have := readList_eq (store64 (store64 m T 0) (T + UInt64.ofNat 8) 0) T (List.replicate 16 0)
    fun j hj => by
      have hj' : j < 16 := by simpa using hj
      rw [h j hj', List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hj']
      rfl
  simpa using this

/-- Bytes outside the 16 from `T` keep their values through the clock's writes there. -/
theorem timespec_other (m : UInt64 → UInt8) (T : UInt64) (bs : List UInt8) (hl : bs.length = 16)
    {b : UInt64} (hb : ¬ (b - T).toNat < 16) :
    writeList (store64 (store64 m T 0) (T + UInt64.ofNat 8) 0) T bs b = m b := by
  rw [writeList_other _ _ _ _ (by omega), store64_other _ _ _ _ ?_, store64_other _ _ _ _ ?_]
  · rw [UInt64.lt_iff_toNat_lt]
    simpa using (show ¬ (b - T).toNat < 8 by omega)
  · rw [UInt64.lt_iff_toNat_lt]
    have := T.toNat_lt
    have := b.toNat_lt
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat,
      Nat.reducePow] at *
    omega

/-! ## The time's arithmetic -/

/-- The stub's test of the seconds against `⌊(2^64 − 1 − nsec) / 10^9⌋` is the negation of the
specification's test that the time lies below `2^64` with the seconds below `2^63`. -/
theorem clock_quotient_iff {sec nsec : UInt64} (hn : nsec.toNat < 10 ^ 9) :
    (0 - nsec - 1) / 1000000000 < sec ↔
      ¬ (sec.toNat < 2 ^ 63 ∧ sec.toNat * 10 ^ 9 + nsec.toNat < 2 ^ 64) := by
  have hq : ((0 - nsec - 1) / 1000000000).toNat = (2 ^ 64 - 1 - nsec.toNat) / 10 ^ 9 := by
    rw [UInt64.toNat_div]
    congr 1
    simp only [UInt64.toNat_sub, UInt64.reduceToNat, Nat.reducePow] at *
    omega
  rw [UInt64.lt_iff_toNat_lt, hq, Nat.div_lt_iff_lt_mul (by decide)]
  simp only [Nat.reducePow] at *
  omega

/-- The time that the stub stores. -/
theorem clock_time_toNat {sec nsec : UInt64} (hn : nsec.toNat < 10 ^ 9)
    (h : ¬ (0 - nsec - 1) / 1000000000 < sec) :
    (nsec + sec * 1000000000).toNat = sec.toNat * 10 ^ 9 + nsec.toNat := by
  have hr := not_not.mp ((clock_quotient_iff hn).not.mp h)
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat, Nat.reducePow] at *
  omega

/-- `Linux.isError` of a nonzero result is its negation's lying at most 4095. -/
theorem isError_iff_ne {r : UInt64} (h : r ≠ 0) : Linux.isError r = true ↔ 0 - r ≤ 4095 := by
  have h' : r.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  simp only [Linux.isError, decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_sub,
    UInt64.reduceToNat]
  have := r.toNat_lt
  simp only [Nat.reducePow] at *
  omega

/-! ## The store relation -/

/-- The store relation holds after code that keeps X17, X18, and the area's bytes. -/
theorem StoreRel.congrArea {P : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s s' : State} (h : StoreRel P cap gts st s) (h17 : s'.x 17 = s.x 17)
    (h18 : s'.x 18 = s.x 18)
    (hmem : ∀ j < areaSize cap,
      s'.mem (s.x 17 + UInt64.ofNat j) = s.mem (s.x 17 + UInt64.ofNat j)) :
    StoreRel P cap gts st s' := by
  have hgl := h.types.length
  have hg := h.glen
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk =>
      hmem k (by unfold areaSize; omega)]
    exact h.size
  · intro i hi
    rw [h17, load64_congr (m := s'.mem) (m' := s.mem) fun k hk => by
      rw [add_ofNat_add]
      exact hmem _ (by unfold areaSize; omega)]
    exact h.globals i hi
  · intro j hj
    rw [h17, hmem _ (by unfold areaSize; omega)]
    exact h.bytes j hj
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

/-- The store relation keeps no part of the store's host state or of the store's fields other
than its memory, globals, and caps. -/
theorem StoreRel.answered {P : Platform} {cap : Nat} {gts : List ValueType}
    {st : Store (Observed LinuxWorld)} {s : State} (h : StoreRel P cap gts st s)
    (l : List Linux.Event) (e : Wasi.Event) :
    StoreRel P cap gts (answered st st.mem l e) s :=
  StoreRel.withHost h _

/-! ## A stub's end -/

/-- The memory `m'` keeps the bytes of `m` outside the guest's memory of `cap` pages in the area
at `area` and outside the `n` bytes from `T`. -/
def KeptOutside (area : UInt64) (cap : Nat) (T : UInt64) (n : Nat) (m m' : UInt64 → UInt8) :
    Prop :=
  ∀ b : UInt64, ¬ (b - (area + UInt64.ofNat 4096)).toNat < cap * 65536 → ¬ (b - T).toNat < n →
    m' b = m b

/-- What a stub's run from the process `q` gives for the result of its host function from the
store `st`, with results of the types `rs`: a return to X30 with the result's values and a state
that holds its store, or the trap stub for the shim's trap.  The process's trace gains the layer
events `l` that the result's world appended, each of which `Ev` admits, and the memory keeps its
bytes outside the guest's memory and the `n` bytes from `T`. -/
def StubEnd (R : Linux.Replies) (P : Platform) (code : UInt64 → Option UInt32) (S : Shared)
    (rs : List ValueType) (Ev : Linux.Event → Prop) (T : UInt64) (n : Nat)
    (st : Store (Observed LinuxWorld)) (q : Proc) : HostResult (Observed LinuxWorld) → Prop
  | .Return vs st' => ∃ q' l, ProcRunWith Linux.table R P code q q' ∧
      Returned rs vs q.core q'.core ∧ StoreRel P S.cap S.globalTypes st' q'.core ∧
      q'.fpcr = fpcrValue ∧ q'.core.x 17 = q.core.x 17 ∧
      st'.host.world.events = st.host.world.events ++ l ∧ q'.trace = q.trace ++ l.map .sys ∧
      (∀ e ∈ l, Ev e) ∧ KeptOutside (q.core.x 17) S.cap T n q.core.mem q'.core.mem
  | .Trap st' msg => ∃ q' l, ProcRunWith Linux.table R P code q q' ∧ q'.core.io = q.core.io ∧
      msg = shimTrap ∧ q'.core.pc = S.trapUnreachable ∧ q'.fpcr = fpcrValue ∧
      st'.host.world.events = st.host.world.events ++ l ∧ q'.trace = q.trace ++ l.map .sys ∧
      (∀ e ∈ l, Ev e) ∧ KeptOutside (q.core.x 17) S.cap T n q.core.mem q'.core.mem
  | .Throw _ _ _ => False

/-- The address of byte `k` from the guest's byte `p`. -/
theorem guest_addr' (area : UInt64) (p : UInt32) (k : Nat) :
    area + p.toUInt64 + UInt64.ofNat (4096 + k) = area + UInt64.ofNat (4096 + (p.toNat + k)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
  omega

/-- An address at least `n` bytes above `a`, without wrapping, lies outside the `n` bytes from
`a`. -/
theorem sub_not_lt {a b : UInt64} {n : Nat} (h : a.toNat + n ≤ b.toNat) : ¬ (b - a).toNat < n := by
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  omega

/-- An address below `a` lies outside the `n` bytes from `a` when `a` lies at least `n` below
`2^64`. -/
theorem sub_not_lt_below {a b : UInt64} {n : Nat} (h : b.toNat < a.toNat)
    (ha : a.toNat + n ≤ 2 ^ 64) : ¬ (b - a).toNat < n := by
  have := b.toNat_lt
  simp only [UInt64.toNat_sub, Nat.reducePow] at *
  omega

theorem ofNat_not_lt {x : UInt64} {n : Nat} (h : ¬ x.toNat < n) (hn : n < 2 ^ 64) :
    ¬ x < UInt64.ofNat n := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hn]
  exact h

section Run

/-! ## `clock_time_get` -/

variable {R : Linux.Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-- The stub of `clock_time_get` from its entry, with the clock in X0, the time's pointer in X2,
the store `st` in the area at X17, the timespec 1,040 bytes into the scratch that follows the area,
its 16 bytes Normal memory, and the scratch's first 1,056 bytes below the stack's limit, ends as
`clockInvoke` of the replies `R'` answers, when the reply of the world's next call is that of the
process's next call.  The trace gains at most the clock's event, and the memory changes only in
the guest's memory and the timespec. -/
theorem clockStub_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {S : Shared}
    {a svc en : UInt64} {scratch : Nat} {is : List Instr}
    (hg : clockStub a svc S.trapUnreachable en scratch = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (L : ShimLayout) (R' : Linux.Replies) (st : Store (Observed LinuxWorld)) (q : Proc)
    (id : UInt32) (precision : UInt64) (ptr : UInt32)
    (hpc : q.core.pc = a) (hstk : StackOk P q.core)
    (hsr : StoreRel P S.cap S.globalTypes st q.core) (hf : q.fpcr = fpcrValue)
    (x0 : q.core.x 0 = id.toUInt64) (x2 : q.core.x 2 = ptr.toUInt64)
    (hscr : areaSize S.cap ≤ scratch)
    (hT : L.timespec = q.core.x 17 + UInt64.ofNat (scratch + 1040))
    (hlim : (q.core.x 17).toNat + scratch + 1056 ≤ (q.core.x 18).toNat)
    (hmapT : ∀ k < 16, P.normal (L.timespec + UInt64.ofNat k) = true)
    (hR : R' st.host.world.events.length = R q.trace.length) :
    StubEnd R P code S [.i32] (· = clockEvent L id.toUInt64 (R' st.host.world.events.length))
      L.timespec 16 st q (clockInvoke L R' st [.i32 id, .i64 precision, .i32 ptr]) := by
  obtain ⟨g1, g4, g6, g18, g26, g32, g40, gs, g42, hg1, hg4, hg6, hgs, hg18, hg26, hg32, hg40,
    hg42, rfl⟩ := clockStub_ok hg
  have cA := CodeAt.split code hcode (n := 46) (by simp [clockTimeCode, movImm])
  have cB := CodeAt.split code cA.1 (n := 18) (by simp [movImm])
  have cC := CodeAt.split code cB.1 (n := 17) (by simp [movImm])
  have cD := CodeAt.split code cC.1 (n := 8) (by simp)
  have cbl : code (after a 17) = some (encode (.bl gs)) := by
    simpa [after_zero] using cC.2 0 (by simp)
  have cnext : code (after a 18) = some (encode (.cbnz 0 g18)) := by
    simpa [after_zero, clockTimeCode] using cB.2 0 (by simp [clockTimeCode])
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hlimit := hstk.limit
  have hbelow := hsr.below
  have hp32 := ptr.toNat_lt
  have hid32 := id.toNat_lt
  have h17lt := (q.core.x 17).toNat_lt
  have h18lt := (q.core.x 18).toNat_lt
  unfold areaSize at hscr hbelow
  have hmap17 : ∀ k < 8, P.normal (q.core.x 17 + UInt64.ofNat k) = true := fun k hk =>
    hsr.mapped k (by unfold areaSize; omega)
  obtain ⟨u1, r1, sp1, m1, io1, k1, h1⟩ := run_clockHead P code cD.1 cA.2 hg1 hg4 hg6 hpc hmap17
  have hsize : (load64 q.core.mem (q.core.x 17)).toNat = st.mem.pages * 65536 - 8 := by
    rw [hsr.size, UInt64.toNat_ofNat_of_lt' (show _ < 2 ^ 64 by omega)]
  have hcheck : (3 < q.core.x 0 ∨ load64 q.core.mem (q.core.x 17) < q.core.x 2) ↔
      ¬ (id.toNat < 4 ∧ ptr.toNat + 8 ≤ st.mem.pages * 65536 ∧ ptr.toNat + 8 < 2 ^ 32) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt, hsize, x0, x2, UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt64]
    have : st.mem.pages * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    simp only [UInt64.reduceToNat, Nat.reducePow] at *
    omega
  have e17 : u1.x 17 = q.core.x 17 := k1 17 (by decide) (by decide) (by decide)
  have e18 : u1.x 18 = q.core.x 18 := k1 18 (by decide) (by decide) (by decide)
  unfold clockInvoke
  dsimp only
  by_cases hbad : 3 < q.core.x 0 ∨ load64 q.core.mem (q.core.x 17) < q.core.x 2
  · rw [ite_eq_left hbad] at h1
    rw [ite_eq_right (hcheck.mp hbad)]
    dsimp only [StubEnd]
    exact ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1, io1, rfl, h1, hf, by simp,
      by simp, by simp, fun b _ _ => by show u1.mem b = _; rw [m1]⟩
  rw [ite_eq_right hbad] at h1
  have hok : id.toNat < 4 ∧ ptr.toNat + 8 ≤ st.mem.pages * 65536 ∧ ptr.toNat + 8 < 2 ^ 32 :=
    Classical.not_not.mp fun h => hbad (hcheck.mpr h)
  rw [ite_eq_left hok]
  have hhiIff : 1 < q.core.x 0 ↔ ¬ id.toNat < 2 := by
    rw [UInt64.lt_iff_toNat_lt, x0, UInt32.toNat_toUInt64]
    simp only [UInt64.reduceToNat]
    omega
  by_cases hhi : 1 < q.core.x 0
  · rw [ite_eq_left hhi] at h1
    obtain ⟨p1, x01⟩ := h1
    rw [ite_eq_right (hhiIff.mp hhi)]
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1,
      ⟨p1, sp1, e18, io1, fun b _ => by show u1.mem b = _; rw [m1], by simp,
        ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩,
      StoreRel.answered (hsr.regs e17 e18 m1) _ _, hf, e17, rfl, by simp, by simp,
      fun b _ _ => by show u1.mem b = _; rw [m1]⟩
    simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show u1.x 0 = (8 : UInt64).toUInt32.toUInt64
    rw [x01]
    rfl
  rw [ite_eq_right hhi] at h1
  obtain ⟨p1, x01, x191⟩ := h1
  have hlo : id.toNat < 2 := Classical.not_not.mp fun h => hhi (hhiIff.mpr h)
  rw [ite_eq_left hlo]
  -- the call's setup
  have eT : ∀ k, u1.x 17 + UInt64.ofNat scratch + UInt64.ofNat (1040 + k) =
      L.timespec + UInt64.ofNat k := fun k => by
    rw [e17, hT, add_ofNat_add, add_ofNat_add, Nat.add_assoc]
  obtain ⟨u2, r2, p2, sp2, io2, x202, x12, x82, k2, m2⟩ := run_clockCall P code cD.2 p1
    (fun k hk => by rw [eT]; exact hmapT k hk)
  have hG : u2.x 20 + UInt64.ofNat 1040 = L.timespec := by
    rw [x202, e17, hT, add_ofNat_add]
  have h1048 : u2.x 20 + UInt64.ofNat 1048 = L.timespec + UInt64.ofNat 8 := by
    rw [← hG, add_ofNat_add]
  have u2x1 : u2.x 1 = L.timespec := by rw [x12, hG]
  have u2x0 : u2.x 0 = id.toUInt64 := by
    rw [k2 0 (by decide) (by decide) (by decide), x01, x0]
  have u2mem : u2.mem =
      store64 (store64 q.core.mem L.timespec 0) (L.timespec + UInt64.ofNat 8) 0 := by
    rw [m2, m1, hG, h1048]
  have u2keep : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 19 → r ≠ 20 →
      u2.x r = q.core.x r := fun r h0 h1 h8 h9 h19 h20 => by
    rw [k2 r h1 h8 h20, k1 r h0 h9 h19]
  -- the call
  have hTab : Linux.table.find? (fun c => c.arm64 == ({ q with core := u2 } : Proc).core.x 8) =
      some Linux.clockGettimeCall := by
    show Linux.table.find? (fun c => c.arm64 == u2.x 8) = _
    rw [x82]
    exact table_clock
  have hmapC : P.mapped ((({ q with core := u2 } : Proc).call (after a 17) svc).core.x 1) 16 =
      true := by
    rw [Proc.call_x _ _ _ (by decide)]
    show P.mapped (u2.x 1) 16 = true
    rw [u2x1]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    exact hmapT i hi
  have hnext : (after (after a 17) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    exact hdom _ _ cnext
  obtain ⟨q3, rq3, p3, x03, x303, k3, sp3, m3, io3, f3, tr3⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl hgs hdom hnext
      (p := { q with core := u2 }) p2 hTab rfl (sysCall_clockGettime hmapC)
  change q3.core.x 0 = (R q.trace.length).ret at x03
  change q3.core.mem = writeList u2.mem (u2.x 1) ((List.range 16).map (R q.trace.length).bytes)
    at m3
  change q3.trace = q.trace ++ [A64.Event.sys ⟨Linux.clockGettimeCall, [u2.x 0, u2.x 1], [],
    readList u2.mem (u2.x 1) 16, (R q.trace.length).ret,
    (List.range 16).map (R q.trace.length).bytes⟩] at tr3
  have hrl : readList u2.mem (u2.x 1) 16 = List.replicate 16 0 := by
    rw [u2mem, u2x1, readList_cleared]
  have hev : (⟨Linux.clockGettimeCall, [u2.x 0, u2.x 1], [], readList u2.mem (u2.x 1) 16,
      (R q.trace.length).ret, (List.range 16).map (R q.trace.length).bytes⟩ : Linux.Event) =
      clockEvent L id.toUInt64 (R' st.host.world.events.length) := by
    rw [hrl, u2x0, u2x1, hR]
    rfl
  rw [hev] at tr3
  rw [u2x1] at m3
  have hret : (clockEvent L id.toUInt64 (R' st.host.world.events.length)).ret =
      (R q.trace.length).ret := by simp [clockEvent, hR]
  have hout : (clockEvent L id.toUInt64 (R' st.host.world.events.length)).output =
      (List.range 16).map (R q.trace.length).bytes := by simp [clockEvent, hR]
  rw [hret, hout]
  generalize clockEvent L id.toUInt64 (R' st.host.world.events.length) = E at tr3 ⊢
  generalize R q.trace.length = rr at x03 m3 ⊢
  generalize hout : (List.range 16).map rr.bytes = out at m3 ⊢
  have hlen : out.length = 16 := by rw [← hout]; simp
  -- facts of the state after the call
  have q3x : ∀ r : Fin 32, r ≠ 0 → r ≠ 30 → q3.core.x r = u2.x r := fun r h0 h30 => k3 r h0 h30
  have q3x20 : q3.core.x 20 = u2.x 20 := q3x 20 (by decide) (by decide)
  have q3x17 : q3.core.x 17 = q.core.x 17 := by
    rw [q3x 17 (by decide) (by decide), u2keep 17 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have q3x18 : q3.core.x 18 = q.core.x 18 := by
    rw [q3x 18 (by decide) (by decide), u2keep 18 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have q3x19 : q3.core.x 19 = q.core.x 30 := by
    rw [q3x 19 (by decide) (by decide), k2 19 (by decide) (by decide) (by decide), x191]
  have q3x2 : q3.core.x 2 = ptr.toUInt64 := by
    rw [q3x 2 (by decide) (by decide), u2keep 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), x2]
  have q3sp : q3.core.sp = q.core.sp := by
    rw [sp3]
    show u2.sp = _
    rw [sp2, sp1]
  have q3io : q3.core.io = q.core.io := by
    rw [io3]
    show u2.io = _
    rw [io2, io1]
  have hf3 : q3.fpcr = fpcrValue := by rw [f3]; exact hf
  have hTn : (L.timespec).toNat = (q.core.x 17).toNat + scratch + 1040 := by
    rw [hT, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have a4096 : (q.core.x 17 + UInt64.ofNat 4096).toNat = (q.core.x 17).toNat + 4096 := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  have hkeep3 : KeptOutside (q.core.x 17) S.cap L.timespec 16 q.core.mem q3.core.mem :=
    fun b _ hb => by rw [m3, u2mem, timespec_other _ _ _ hlen hb]
  have habove3 : ∀ b : UInt64, q.core.sp.toNat ≤ b.toNat → q3.core.mem b = q.core.mem b :=
    fun b hb => by rw [m3, u2mem, timespec_other _ _ _ hlen (sub_not_lt (by omega))]
  have hsr3 : StoreRel P S.cap S.globalTypes st q3.core :=
    StoreRel.congrArea hsr q3x17 q3x18 fun j hj => by
      unfold areaSize at hj
      rw [m3, u2mem, timespec_other _ _ _ hlen
        (sub_not_lt_below ?_ (by simp only [Nat.reducePow]; omega))]
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
      omega
  -- the result
  have hq3pc : q3.core.pc = after a 18 := by rw [p3, after_after]
  have hmapT' : ∀ k < 16, P.normal (q3.core.x 20 + UInt64.ofNat (1040 + k)) = true :=
    fun k hk => by
      rw [q3x20, ← add_ofNat_add, hG]
      exact hmapT k hk
  have hmapP' : ∀ k < 8, P.normal (q3.core.x 17 + q3.core.x 2 + UInt64.ofNat (4096 + k)) = true :=
    fun k hk => by
      rw [q3x17, q3x2, guest_addr']
      have := Nat.mul_le_mul_right 65536 hpg.2
      exact hsr.mapped _ (by unfold areaSize; omega)
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ :=
    run_clockTime P code cB.2 hg18 hg26 hg32 hg40 hg42 hen hq3pc hmapT' hmapP'
  have hsec : load64 q3.core.mem (q3.core.x 20 + UInt64.ofNat 1040) = leWord (out.take 8) := by
    have := load64_writeList u2.mem out L.timespec (j := 0) (by omega) (by rw [hlen]; decide)
    rw [add_ofNat_zero, List.drop_zero] at this
    rw [m3, q3x20, hG, this]
  have hnsec : load64 q3.core.mem (q3.core.x 20 + UInt64.ofNat 1048) =
      leWord ((out.drop 8).take 8) := by
    rw [m3, q3x20, h1048,
      load64_writeList u2.mem out L.timespec (by omega) (by rw [hlen]; decide)]
  rw [x03, hsec, hnsec, q3x17, q3x2, q3x19] at ht
  obtain ⟨hsecN, -⟩ := leWord_toNat (out.take 8) (by simp)
  obtain ⟨hnsN, -⟩ := leWord_toNat ((out.drop 8).take 8) (by simp)
  generalize leWord (out.take 8) = SEC at ht hsecN
  generalize leWord ((out.drop 8).take 8) = NSEC at ht hnsN
  have hrch : ProcRunWith Linux.table R P code q { q3 with core := t } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf (r1.trans r2))
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq3 hf3) (ProcRunWith.ofReach hf3 rt))
  have htr : ({ q3 with core := t } : Proc).trace = q.trace ++ [E].map A64.Event.sys := by
    show q3.trace = _
    rw [tr3]
    rfl
  have tsp : t.sp = q.core.sp := by rw [spt, q3sp]
  have tio : t.io = q.core.io := by rw [iot, q3io]
  have t17 : t.x 17 = q3.core.x 17 := x17t
  have t18 : t.x 18 = q3.core.x 18 := x18t
  have hres : ∀ (v : UInt64) (vs : List Value), vs = [.i32 v.toUInt32] → t.x 0 = v →
      v.toNat < 2 ^ 32 → StackRel t (vs.take [ValueType.i32].length) := by
    intro v vs hvs hx hv
    subst hvs
    refine ⟨by simp, fun k hk => ?_⟩
    simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show t.x 0 = v.toUInt32.toUInt64
    rw [hx]
    apply UInt64.toNat_inj.mp
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
    omega
  unfold clockReply
  dsimp only
  rw [← hsecN, ← hnsN]
  by_cases hr0 : rr.ret = 0
  · rw [ite_eq_left hr0] at ht
    rw [ite_eq_left hr0]
    have hnIff : 999999999 < NSEC ↔ ¬ NSEC.toNat < 10 ^ 9 := by
      rw [UInt64.lt_iff_toNat_lt]
      simp only [UInt64.reduceToNat]
      omega
    by_cases hn : 999999999 < NSEC
    · rw [ite_eq_left hn] at ht
      obtain ⟨pt, mt⟩ := ht
      rw [ite_eq_right (hnIff.mp hn)]
      dsimp only [placeReply, sysAnswer, sysResult, StubEnd]
      exact ⟨{ q3 with core := t }, [E], hrch, tio, rfl, pt, hf3, rfl, htr, by simp,
        fun b h1 h2 => by show t.mem b = _; rw [mt]; exact hkeep3 b h1 h2⟩
    rw [ite_eq_right hn] at ht
    have hn' : NSEC.toNat < 10 ^ 9 := Classical.not_not.mp fun h => hn (hnIff.mpr h)
    rw [ite_eq_left hn']
    by_cases hq : (0 - NSEC - 1) / 1000000000 < SEC
    · rw [ite_eq_left hq] at ht
      obtain ⟨pt, x0t, mt⟩ := ht
      rw [ite_eq_right ((clock_quotient_iff hn').mp hq)]
      rw [show placeReply st.mem (fun outputs => [(ptr, outputs.headD Bytes.empty)])
        (.returned 61 [zeros 8]) = st.mem from rfl]
      dsimp only [sysAnswer, sysResult, StubEnd]
      refine ⟨{ q3 with core := t }, [E], hrch,
        ⟨pt, tsp, by rw [t18, q3x18], tio, fun b hb => ?_, by simp, hres 61 _ rfl x0t (by decide),
          by simp [Typed, HasType]⟩,
        StoreRel.answered (hsr3.regs t17 t18 mt) _ _, hf3, by rw [t17, q3x17], rfl, htr,
        by simp, fun b h1 h2 => ?_⟩
      · show t.mem b = _
        rw [mt]
        exact habove3 b (by simpa using hb)
      · show t.mem b = _
        rw [mt]
        exact hkeep3 b h1 h2
    · rw [ite_eq_right hq] at ht
      obtain ⟨pt, x0t, mt⟩ := ht
      have hrange := Classical.not_not.mp ((clock_quotient_iff hn').not.mp hq)
      rw [ite_eq_left hrange]
      have htime := clock_time_toNat hn' hq
      have hbytes : (leBytes 8 (SEC.toNat * 10 ^ 9 + NSEC.toNat)).data.data.toList =
          (List.range 8).map (LeanExe.A64.byteOf (NSEC + SEC * 1000000000)) := by
        rw [leBytes_eight (by omega), ← htime, UInt64.ofNat_toNat]
      rw [show placeReply st.mem (fun outputs => [(ptr, outputs.headD Bytes.empty)])
        (.returned 0 [leBytes 8 (SEC.toNat * 10 ^ 9 + NSEC.toNat)]) =
          st.mem.writeBytes ptr.toNat
            ((List.range 8).map (LeanExe.A64.byteOf (NSEC + SEC * 1000000000))) by
        rw [← hbytes]
        rfl]
      dsimp only [sysAnswer, sysResult, StubEnd]
      have hA : q.core.x 17 + ptr.toUInt64 + UInt64.ofNat 4096 =
          q.core.x 17 + UInt64.ofNat (4096 + ptr.toNat) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64, Nat.reducePow]
        omega
      have hAn : (q.core.x 17 + UInt64.ofNat (4096 + ptr.toNat)).toNat =
          (q.core.x 17).toNat + 4096 + ptr.toNat := by
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
        have := Nat.mul_le_mul_right 65536 hpg.2
        omega
      have hmemt : t.mem = writeList q3.core.mem (q3.core.x 17 + UInt64.ofNat (4096 + ptr.toNat))
          ((List.range 8).map (LeanExe.A64.byteOf (NSEC + SEC * 1000000000))) := by
        rw [mt, store64_writeList, hA, q3x17]
      have hother : ∀ b : UInt64,
          ¬ (b - (q.core.x 17 + UInt64.ofNat (4096 + ptr.toNat))).toNat < 8 →
          t.mem b = q3.core.mem b := fun b hb => by
        rw [hmemt, q3x17, writeList_other _ _ _ _ (by simpa using hb)]
      have hpg' := Nat.mul_le_mul_right 65536 hpg.2
      refine ⟨{ q3 with core := t }, [E], hrch,
        ⟨pt, tsp, by rw [t18, q3x18], tio, fun b hb => ?_, by simp, hres 0 _ rfl x0t (by decide),
          by simp [Typed, HasType]⟩,
        StoreRel.withHost (StoreRel.ofWriteList P _ hsr3 (by simp; omega) t17 t18 hmemt) _, hf3,
        by rw [t17, q3x17], rfl, htr, by simp, fun b h1 h2 => ?_⟩
      · show t.mem b = _
        have hb' : q.core.sp.toNat ≤ b.toNat := by simpa using hb
        rw [hother b (sub_not_lt (by omega)), habove3 b hb']
      · show t.mem b = _
        rw [hother b ?_, hkeep3 b h1 h2]
        have := b.toNat_lt
        simp only [UInt64.toNat_sub, a4096, hAn, Nat.reducePow] at h1 ⊢
        omega
  · rw [ite_eq_right hr0] at ht
    obtain ⟨mt, ht⟩ := ht
    rw [ite_eq_right hr0]
    by_cases he : 0 - rr.ret ≤ 4095
    · rw [ite_eq_left he] at ht
      obtain ⟨pt, x0t⟩ := ht
      rw [ite_eq_left ((isError_iff_ne hr0).mpr he)]
      rw [show placeReply st.mem (fun outputs => [(ptr, outputs.headD Bytes.empty)])
        (.returned (errnoOf (0 - rr.ret)) [zeros 8]) = st.mem by
        simp [placeReply, (errnoOf_valid _).2]]
      dsimp only [sysAnswer, sysResult, StubEnd]
      refine ⟨{ q3 with core := t }, [E], hrch,
        ⟨pt, tsp, by rw [t18, q3x18], tio, fun b hb => ?_, by simp,
          hres _ _ rfl (by rw [x0t, errnoOf_lookup])
            (by have := (errnoOf_valid (0 - rr.ret)).1; omega),
          by simp [Typed, HasType]⟩,
        StoreRel.answered (hsr3.regs t17 t18 mt) _ _, hf3, by rw [t17, q3x17], rfl, htr,
        by simp, fun b h1 h2 => ?_⟩
      · show t.mem b = _
        rw [mt]
        exact habove3 b (by simpa using hb)
      · show t.mem b = _
        rw [mt]
        exact hkeep3 b h1 h2
    · rw [ite_eq_right he] at ht
      rw [ite_eq_right (fun h => he ((isError_iff_ne hr0).mp h))]
      dsimp only [placeReply, sysAnswer, sysResult, StubEnd]
      exact ⟨{ q3 with core := t }, [E], hrch, tio, rfl, ht, hf3, rfl, htr, by simp,
        fun b h1 h2 => by show t.mem b = _; rw [mt]; exact hkeep3 b h1 h2⟩

/-! ## `random_get` -/

/-- A `getrandom` of `random_get`'s loop writes within every size that holds its buffer. -/
theorem randomEvent_writesLinear (L : ShimLayout) (mem : Mem) {pointer n size : Nat}
    (r : Linux.Reply) (small : pointer + n < 2 ^ 64) (address : pointer + n ≤ size) :
    WritesLinear L size (randomEvent L mem (UInt64.ofNat pointer) n r) := by
  intro g member
  simp only [randomEvent, outputs_getrandom, List.mem_singleton] at member
  subst member
  rw [offset_base, UInt64.toNat_ofNat_of_lt' (show pointer < 2 ^ 64 by omega),
    UInt64.toNat_ofNat_of_lt' (show n < 2 ^ 64 by omega)]
  exact address

/-- Every event of `random_get`'s loop is a `getrandom` whose output region lies within every
size that holds the buffer. -/
theorem randomLoop_events (L : ShimLayout) (R' : Linux.Replies) (pointer length : Nat)
    {size : Nat} (hfit : pointer + length ≤ size) (small : pointer + length < 2 ^ 64) :
    ∀ (remaining done : Nat) (filled : List UInt8) (mem : Mem) (k : Nat),
      length - done = remaining → ∀ e ∈ (randomLoop L R' pointer length done filled mem k).2.1,
        e.call = Linux.getrandomCall ∧ WritesLinear L size e := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | _ remaining ih =>
  intro done filled mem k hrem e he
  rw [randomLoop] at he
  by_cases more : done < length
  · simp only [more, ↓reduceDIte] at he
    have hev : (randomEvent L mem (UInt64.ofNat (pointer + done)) (length - done) (R' k)).call =
        Linux.getrandomCall ∧ WritesLinear L size
          (randomEvent L mem (UInt64.ofNat (pointer + done)) (length - done) (R' k)) :=
      ⟨rfl, randomEvent_writesLinear L mem (R' k) (by omega) (by omega)⟩
    split at he
    · rcases List.mem_cons.mp he with rfl | he
      · exact hev
      · exact ih _ (by omega) _ _ _ _ rfl e he
    · obtain rfl := List.mem_singleton.mp he
      exact hev
  · simp only [more, ↓reduceDIte] at he
    cases he

/-- What the loop of the stub of `random_get` gives from the process `p` at the loop's head for
the result `x` of `randomLoop`: for a returned reply, a return to `ret` with its errno in X0, a
state that holds the store with the loop's memory, and SP, X17, X18, and the UART's state kept;
for a trap, the trap stub with the shim's trap.  The trace gains the loop's events, and the memory
changes only in the guest's memory. -/
def LoopEnd (R : Linux.Replies) (P : Platform) (code : UInt64 → Option UInt32) (S : Shared)
    (ret : UInt64) (st : Store (Observed LinuxWorld)) (p : Proc)
    (x : Mem × List Linux.Event × Transfer (List Bytes)) : Prop :=
  match x.2.2 with
  | .returned errno _ => ∃ p', ProcRunWith Linux.table R P code p p' ∧ p'.core.pc = ret ∧
      p'.core.x 0 = errno ∧ errno.toNat < 2 ^ 32 ∧ p'.core.sp = p.core.sp ∧
      p'.core.io = p.core.io ∧ p'.core.x 17 = p.core.x 17 ∧ p'.core.x 18 = p.core.x 18 ∧
      p'.fpcr = fpcrValue ∧ StoreRel P S.cap S.globalTypes { st with mem := x.1 } p'.core ∧
      p'.trace = p.trace ++ x.2.1.map .sys ∧
      KeptOutside (p.core.x 17) S.cap 0 0 p.core.mem p'.core.mem
  | .trapped msg _ => ∃ p', ProcRunWith Linux.table R P code p p' ∧
      p'.core.pc = S.trapUnreachable ∧ msg = shimTrap ∧ p'.core.io = p.core.io ∧
      p'.fpcr = fpcrValue ∧ p'.trace = p.trace ++ x.2.1.map .sys ∧
      KeptOutside (p.core.x 17) S.cap 0 0 p.core.mem p'.core.mem

/-- A pass of the loop that reaches the loop's head again composes with the loop's end from
there. -/
theorem LoopEnd.cons (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {S : Shared}
    {ret : UInt64} {st : Store (Observed LinuxWorld)} {p p'' : Proc} {e : Linux.Event}
    {rest : Mem × List Linux.Event × Transfer (List Bytes)}
    (hr : ProcRunWith Linux.table R P code p p'') (htr : p''.trace = p.trace ++ [.sys e])
    (hsp : p''.core.sp = p.core.sp) (hio : p''.core.io = p.core.io)
    (h17 : p''.core.x 17 = p.core.x 17) (h18 : p''.core.x 18 = p.core.x 18)
    (hkeep : KeptOutside (p.core.x 17) S.cap 0 0 p.core.mem p''.core.mem)
    (h : LoopEnd R P code S ret st p'' rest) :
    LoopEnd R P code S ret st p (rest.1, e :: rest.2.1, rest.2.2) := by
  unfold LoopEnd at h ⊢
  dsimp only at h ⊢
  have htrace : ∀ p' : Proc, p'.trace = p''.trace ++ rest.2.1.map .sys →
      p'.trace = p.trace ++ (e :: rest.2.1).map .sys := fun p' h' => by
    rw [h', htr]
    simp
  have hkeep' : ∀ p' : Proc, KeptOutside (p''.core.x 17) S.cap 0 0 p''.core.mem p'.core.mem →
      KeptOutside (p.core.x 17) S.cap 0 0 p.core.mem p'.core.mem := fun p' h' b h1 h2 => by
    rw [h17] at h'
    rw [h' b h1 h2, hkeep b h1 h2]
  split at h
  · obtain ⟨p', r', pc', x0', lt', sp', io', x17', x18', f', sr', tr', k'⟩ := h
    exact ⟨p', ProcRunWith.trans hdom hr r', pc', x0', lt', by rw [sp', hsp], by rw [io', hio],
      by rw [x17', h17], by rw [x18', h18], f', sr', htrace p' tr', hkeep' p' k'⟩
  · obtain ⟨p', r', pc', msg', io', f', tr', k'⟩ := h
    exact ⟨p', ProcRunWith.trans hdom hr r', pc', msg', by rw [io', hio], f', htrace p' tr',
      hkeep' p' k'⟩

/-- The loop of the stub of `random_get` from its head at `after a 11`, with the address of the
bytes that remain in X20, their count in X21, the return address `ret` in X19, and the store with
the loop's memory `mem` in the area at X17, ends as `randomLoop` of the loop's state gives, when
the replies of the world's calls from `k` are those of the process's next calls. -/
theorem randomLoop_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {S : Shared}
    {a svc en : UInt64} {g15 g30 : Fin 67108864} {g17 g18 g21 g28 : Fin 524288}
    (hcall : CodeAt code (after a 11) [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0,
      .movz 8 278 0, .bl g15])
    (hres : CodeAt code (after a 16) [.subsReg 31 0 21, .bcond 8 g17, .cbz 0 g18,
      .subReg 21 21 0, .addReg 20 20 0, .cbnz 21 g21, .movz 0 0 0, .ret 19])
    (htail : CodeAt code (after a 26) [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g28,
      .orrReg 0 31 12, .bl g30, .ret 19])
    (hg15 : bField (after a 15) svc = .ok g15)
    (hg17 : cbField (after a 17) (after a 26) = .ok g17)
    (hg18 : cbField (after a 18) S.trapUnreachable = .ok g18)
    (hg21 : cbField (after a 21) (after a 11) = .ok g21)
    (hg28 : cbField (after a 28) S.trapUnreachable = .ok g28)
    (hg30 : bField (after a 30) en = .ok g30)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (L : ShimLayout) (R' : Linux.Replies) (st : Store (Observed LinuxWorld)) (ptr length : Nat)
    (hfit : ptr + length ≤ st.mem.pages * 65536) (ret : UInt64) :
    ∀ (remaining done : Nat) (filled : List UInt8) (mem : Mem) (k : Nat) (p : Proc),
      length - done = remaining → done < length → mem.pages = st.mem.pages →
      p.core.pc = after a 11 → p.fpcr = fpcrValue →
      StoreRel P S.cap S.globalTypes { st with mem := mem } p.core →
      L.base = p.core.x 17 + UInt64.ofNat 4096 →
      p.core.x 20 = p.core.x 17 + UInt64.ofNat (4096 + (ptr + done)) →
      p.core.x 21 = UInt64.ofNat (length - done) → p.core.x 19 = ret →
      (∀ j, R' (k + j) = R (p.trace.length + j)) →
      LoopEnd R P code S ret st p (randomLoop L R' ptr length done filled mem k) := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | _ remaining ih =>
  intro done filled mem k p hrem hmore hpages hpc hf hsr hbase x20 x21 x19 hR
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hbelow := hsr.below
  have h17lt := (p.core.x 17).toNat_lt
  have h18lt := (p.core.x 18).toNat_lt
  unfold areaSize at hbelow
  simp only at hpg
  rw [hpages] at hpg
  have hpg' := Nat.mul_le_mul_right 65536 hpg.2
  have hn32 : length - done < 2 ^ 32 := by omega
  -- the call
  have c4 : CodeAt code (after a 11) [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0,
      .movz 8 278 0] := by
    simpa [after_zero] using CodeAt.drop_take code hcall 0 4 (by simp)
  have cbl : code (after a 15) = some (encode (.bl g15)) := by
    simpa [after_after] using hcall 4 (by simp)
  have cnext : ∃ w, code (after a 16) = some w := ⟨_, by simpa [after_zero] using hres 0 (by simp)⟩
  obtain ⟨u1, r1, p1, sp1, m1, io1, x01, x11, x21', x81, k1⟩ := run_randomCall P code c4 hpc
  have u1x0 : u1.x 0 = p.core.x 17 + UInt64.ofNat (4096 + (ptr + done)) := by rw [x01, x20]
  have u1x1 : (u1.x 1).toNat = length - done := by
    rw [x11, x21, UInt64.toNat_ofNat_of_lt' (show length - done < 2 ^ 64 by omega)]
  have hTab : Linux.table.find? (fun c => c.arm64 == ({ p with core := u1 } : Proc).core.x 8) =
      some Linux.getrandomCall := by
    show Linux.table.find? (fun c => c.arm64 == u1.x 8) = _
    rw [x81]
    exact table_random
  have hmapG : P.mapped ((({ p with core := u1 } : Proc).call (after a 15) svc).core.x 0)
      ((({ p with core := u1 } : Proc).call (after a 15) svc).core.x 1).toNat = true := by
    rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
    show P.mapped (u1.x 0) (u1.x 1).toNat = true
    rw [u1x0, u1x1]
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [add_ofNat_add]
    exact hsr.mapped _ (by unfold areaSize; omega)
  have hnext : (after (after a 15) 1).toNat < 2 ^ 55 := by
    rw [after_after]
    obtain ⟨w, hw⟩ := cnext
    exact hdom _ _ hw
  obtain ⟨q2, rq2, p2, x02, x302, k2, sp2, m2, io2, f2, tr2⟩ :=
    run_callSvc (T := Linux.table) (R := R) (P := P) (code := code) hsvc cbl hg15 hdom hnext
      (p := { p with core := u1 }) p1 hTab rfl (sysCall_getrandom hmapG)
  change q2.core.x 0 = (R p.trace.length).ret at x02
  change q2.core.mem = writeList u1.mem (u1.x 0)
    ((List.range (u1.x 1).toNat).map (R p.trace.length).bytes) at m2
  change q2.trace = p.trace ++ [A64.Event.sys ⟨Linux.getrandomCall, [u1.x 0, u1.x 1, u1.x 2], [],
    readList u1.mem (u1.x 0) (u1.x 1).toNat, (R p.trace.length).ret,
    (List.range (u1.x 1).toNat).map (R p.trace.length).bytes⟩] at tr2
  have hRk : R' k = R p.trace.length := by simpa using hR 0
  have hrl : readList u1.mem (u1.x 0) (length - done) =
      mem.readBytes (ptr + done) (length - done) := by
    rw [m1, u1x0, readList_bytes P hsr (length - done) (ptr + done) (by omega), memBytes_readBytes]
  have hev : (⟨Linux.getrandomCall, [u1.x 0, u1.x 1, u1.x 2], [],
      readList u1.mem (u1.x 0) (u1.x 1).toNat, (R p.trace.length).ret,
      (List.range (u1.x 1).toNat).map (R p.trace.length).bytes⟩ : Linux.Event) =
      randomEvent L mem (UInt64.ofNat (ptr + done)) (length - done) (R' k) := by
    rw [u1x1, hrl, hRk, x21', u1x0, x11, x21]
    simp only [randomEvent, hbase, add_ofNat_add,
      UInt64.toNat_ofNat_of_lt' (show ptr + done < 2 ^ 64 by omega)]
  rw [hev] at tr2
  rw [u1x1, u1x0, m1] at m2
  rw [← hRk] at x02 m2
  generalize hE : randomEvent L mem (UInt64.ofNat (ptr + done)) (length - done) (R' k) = E at tr2
  have hsr2 : StoreRel P S.cap S.globalTypes
      { st with
        mem := (mem.writeBytes (ptr + done) ((List.range (length - done)).map (R' k).bytes)) }
      q2.core :=
    StoreRel.ofWriteList P _ hsr (by simp; omega)
      (by rw [k2 17 (by decide) (by decide)]; show u1.x 17 = _; rw [k1 17 (by decide)
        (by decide) (by decide) (by decide)])
      (by rw [k2 18 (by decide) (by decide)]; show u1.x 18 = _; rw [k1 18 (by decide)
        (by decide) (by decide) (by decide)]) m2
  -- the result
  have q2x : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 30 → q2.core.x r = p.core.x r :=
    fun r h0 h1 h2 h8 h30 => by
      rw [k2 r h0 h30]
      exact k1 r h0 h1 h2 h8
  have hq2pc : q2.core.pc = after a 16 := by rw [p2, after_after]
  obtain ⟨t, rt, spt, mt, iot, x17t, x18t, x19t, ht⟩ :=
    run_randomResult P code hres htail hg17 hg18 hg21 hg28 hg30 hen hq2pc
  have q2x21 : q2.core.x 21 = UInt64.ofNat (length - done) := by
    rw [q2x 21 (by decide) (by decide) (by decide) (by decide) (by decide), x21]
  have q2x20 : q2.core.x 20 = p.core.x 17 + UInt64.ofNat (4096 + (ptr + done)) := by
    rw [q2x 20 (by decide) (by decide) (by decide) (by decide) (by decide), x20]
  have q2x19 : q2.core.x 19 = ret := by
    rw [q2x 19 (by decide) (by decide) (by decide) (by decide) (by decide), x19]
  have q2x17 : q2.core.x 17 = p.core.x 17 :=
    q2x 17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have q2x18 : q2.core.x 18 = p.core.x 18 :=
    q2x 18 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [x02, q2x21, q2x20, q2x19] at ht
  have hf2 : q2.fpcr = fpcrValue := by rw [f2]; exact hf
  have hrch : ProcRunWith Linux.table R P code p { q2 with core := t } :=
    ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1)
      (ProcRunWith.trans hdom (ProcRunWith.ofWith rq2 hf2) (ProcRunWith.ofReach hf2 rt))
  have htrt : ({ q2 with core := t } : Proc).trace = p.trace ++ [.sys E] := tr2
  have tsp : t.sp = p.core.sp := by rw [spt, sp2]; show u1.sp = _; rw [sp1]
  have tio : t.io = p.core.io := by rw [iot, io2]; show u1.io = _; rw [io1]
  have t17 : t.x 17 = p.core.x 17 := by rw [x17t, q2x17]
  have t18 : t.x 18 = p.core.x 18 := by rw [x18t, q2x18]
  have hkeep : KeptOutside (p.core.x 17) S.cap 0 0 p.core.mem t.mem := fun b h1 _ => by
    rw [mt, m2, writeList_other _ _ _ _ ?_]
    simp only [List.length_map, List.length_range]
    have := b.toNat_lt
    have h4096 : (p.core.x 17 + UInt64.ofNat 4096).toNat = (p.core.x 17).toNat + 4096 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    have hA : (p.core.x 17 + UInt64.ofNat (4096 + (ptr + done))).toNat =
        (p.core.x 17).toNat + 4096 + (ptr + done) := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    simp only [UInt64.toNat_sub, h4096, hA] at h1 ⊢
    omega
  have hsrt : StoreRel P S.cap S.globalTypes
      { st with
        mem := (mem.writeBytes (ptr + done) ((List.range (length - done)).map (R' k).bytes)) }
      t :=
    hsr2.regs (by rw [t17, q2x17]) (by rw [t18, q2x18]) mt
  generalize hr : R' k = r at hsr2 hsrt x02 ht hE
  have hn64 : (UInt64.ofNat (length - done)).toNat = length - done :=
    UInt64.toNat_ofNat_of_lt' (show length - done < 2 ^ 64 by omega)
  -- the specification's step
  rw [randomLoop]
  simp only [hmore, ↓reduceDIte]
  rw [hr, hE]
  by_cases hgt : UInt64.ofNat (length - done) < r.ret
  · rw [ite_eq_left hgt] at ht
    have hnot : ¬ (0 < r.ret.toNat ∧ r.ret.toNat < length - done) := by
      rw [UInt64.lt_iff_toNat_lt, hn64] at hgt
      omega
    rw [dite_eq_right hnot]
    unfold randomLast
    rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hn64] at hgt; omega)]
    by_cases he : 0 - r.ret ≤ 4095
    · rw [ite_eq_left he] at ht
      obtain ⟨pt, x0t⟩ := ht
      rw [ite_eq_left ((isError_iff (by rw [hn64]; omega) hgt).mpr he)]
      unfold LoopEnd
      dsimp only
      exact ⟨{ q2 with core := t }, hrch, pt, by show t.x 0 = _; rw [x0t, errnoOf_lookup],
        by have := (errnoOf_valid (0 - r.ret)).1; omega, tsp, tio, t17, t18, hf2, hsrt,
        by rw [htrt]; rfl, hkeep⟩
    · rw [ite_eq_right he] at ht
      rw [ite_eq_right (fun h => he ((isError_iff (by rw [hn64]; omega) hgt).mp h))]
      unfold LoopEnd
      dsimp only
      exact ⟨{ q2 with core := t }, hrch, ht, rfl, tio, hf2, by rw [htrt]; rfl, hkeep⟩
  rw [ite_eq_right hgt] at ht
  have hle : r.ret.toNat ≤ length - done := by
    rw [UInt64.lt_iff_toNat_lt, hn64] at hgt
    omega
  by_cases h0 : r.ret = 0
  · rw [ite_eq_left h0] at ht
    have hnot : ¬ (0 < r.ret.toNat ∧ r.ret.toNat < length - done) := by
      rw [h0]
      simp
    rw [dite_eq_right hnot]
    unfold randomLast
    rw [ite_eq_right (by rw [h0]; simp; omega), ite_eq_right (by rw [h0]; decide)]
    unfold LoopEnd
    dsimp only
    exact ⟨{ q2 with core := t }, hrch, ht, rfl, tio, hf2, by rw [htrt]; rfl, hkeep⟩
  rw [ite_eq_right h0] at ht
  have hpos : 0 < r.ret.toNat := by
    have : r.ret.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    omega
  have hsubN : (UInt64.ofNat (length - done) - r.ret).toNat = length - done - r.ret.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn64]; exact hle), hn64]
  by_cases hz : UInt64.ofNat (length - done) - r.ret = 0
  · rw [ite_eq_left hz] at ht
    obtain ⟨pt, x0t⟩ := ht
    have heq : r.ret.toNat = length - done := by
      have := congrArg UInt64.toNat hz
      rw [hsubN] at this
      simp at this
      omega
    rw [dite_eq_right (by omega)]
    unfold randomLast
    rw [ite_eq_left heq]
    unfold LoopEnd
    dsimp only
    exact ⟨{ q2 with core := t }, hrch, pt, x0t, by decide, tsp, tio, t17, t18, hf2, hsrt,
      by rw [htrt]; rfl, hkeep⟩
  rw [ite_eq_right hz] at ht
  obtain ⟨pt, x20t, x21t⟩ := ht
  have hlt : r.ret.toNat < length - done := by
    have : (UInt64.ofNat (length - done) - r.ret).toNat ≠ 0 :=
      fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
    rw [hsubN] at this
    omega
  rw [dite_eq_left ⟨hpos, hlt⟩]
  refine LoopEnd.cons hdom hrch htrt tsp tio t17 t18 hkeep ?_
  refine ih (length - (done + r.ret.toNat)) (by omega) (done + r.ret.toNat) _ _ (k + 1)
    { q2 with core := t } rfl (by omega) (by simp [Mem.writeBytes, hpages]) pt hf2 hsrt
    (by rw [t17]; exact hbase) ?_ ?_ (by rw [x19t, q2x19]) ?_
  · show t.x 20 = t.x 17 + _
    rw [x20t, t17]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  · show t.x 21 = _
    rw [x21t]
    apply UInt64.toNat_inj.mp
    rw [hsubN, UInt64.toNat_ofNat_of_lt' (show length - (done + r.ret.toNat) < 2 ^ 64 by omega)]
    omega
  · intro j
    rw [htrt]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [show k + 1 + j = k + (j + 1) by omega, hR (j + 1)]
    congr 1
    omega

/-- The stub of `random_get` from its entry, with the buffer's pointer in X0, its length in X1,
the store `st` in the area at X17, and the guest's byte 0 4096 bytes above X17, ends as
`randomInvoke` of the replies `R'` answers, when the replies of the world's calls from its next
are those of the process's next calls.  Each event that the trace gains is a `getrandom` whose
output region lies within the cap's memory, and the memory changes only in the guest's memory. -/
theorem randomStub_run (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {S : Shared}
    {a svc en : UInt64} {is : List Instr}
    (hg : randomStub a svc S.trapUnreachable en = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (L : ShimLayout) (R' : Linux.Replies) (st : Store (Observed LinuxWorld)) (q : Proc)
    (ptr len : UInt32) (hpc : q.core.pc = a) (hstk : StackOk P q.core)
    (hsr : StoreRel P S.cap S.globalTypes st q.core) (hf : q.fpcr = fpcrValue)
    (x0 : q.core.x 0 = ptr.toUInt64) (x1 : q.core.x 1 = len.toUInt64)
    (hbase : L.base = q.core.x 17 + UInt64.ofNat 4096)
    (hR : ∀ j, R' (st.host.world.events.length + j) = R (q.trace.length + j)) :
    StubEnd R P code S [.i32]
      (fun e => e.call = Linux.getrandomCall ∧ WritesLinear L (S.cap * 65536) e) 0 0 st q
      (randomInvoke L R' st [.i32 ptr, .i32 len]) := by
  obtain ⟨g4, g5, g17, g18, g21, g28, gs, g30, hg4, hg5, hgs, hg17, hg18, hg21, hg28, hg30, rfl⟩ :=
    randomStub_ok hg
  have cA := CodeAt.split code hcode (n := 26) (by simp)
  have cB := CodeAt.split code cA.1 (n := 16) (by simp)
  have cC := CodeAt.split code cB.1 (n := 15) (by simp)
  have cD := CodeAt.split code cC.1 (n := 11) (by simp)
  have hcall : CodeAt code (after a 11) [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0,
      .movz 8 278 0, .bl gs] := by
    have := (CodeAt.append (code := code)).mpr ⟨cD.2, by simpa [after_after] using cC.2⟩
    simpa using this
  have hres : CodeAt code (after a 16) [.subsReg 31 0 21, .bcond 8 g17, .cbz 0 g18,
      .subReg 21 21 0, .addReg 20 20 0, .cbnz 21 g21, .movz 0 0 0, .ret 19] := by
    simpa [after_zero] using CodeAt.drop_take code cB.2 0 8 (by simp)
  have hzero : CodeAt code (after a 24) [.movz 0 0 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cB.2 8 2 (by simp)
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hlimit := hstk.limit
  have hbelow := hsr.below
  have h17lt := (q.core.x 17).toNat_lt
  have hp32 := ptr.toNat_lt
  have hl32 := len.toNat_lt
  unfold areaSize at hbelow
  have hpg' := Nat.mul_le_mul_right 65536 hpg.2
  have hmap17 : ∀ k < 8, P.normal (q.core.x 17 + UInt64.ofNat k) = true := fun k hk =>
    hsr.mapped k (by unfold areaSize; omega)
  obtain ⟨u1, r1, sp1, m1, io1, k1, h1⟩ := run_randomHead P code cD.1 hzero hg4 hg5 hpc hmap17
  have hsize : (load64 q.core.mem (q.core.x 17) + 8).toNat = st.mem.pages * 65536 := by
    rw [hsr.size, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (show _ < 2 ^ 64 by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have hcheck : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 0 + q.core.x 1 ↔
      ¬ (ptr.toNat + len.toNat ≤ st.mem.pages * 65536 ∧ ptr.toNat + len.toNat < 2 ^ 32) := by
    rw [UInt64.lt_iff_toNat_lt, hsize, x0, x1, UInt64.toNat_add, UInt32.toNat_toUInt64,
      UInt32.toNat_toUInt64]
    have : st.mem.pages * 65536 ≤ 65535 * 65536 := Nat.mul_le_mul_right _ (by omega)
    omega
  have e17 : u1.x 17 = q.core.x 17 :=
    k1 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have e18 : u1.x 18 = q.core.x 18 :=
    k1 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold randomInvoke
  dsimp only
  by_cases hbad : load64 q.core.mem (q.core.x 17) + 8 < q.core.x 0 + q.core.x 1
  · rw [ite_eq_left hbad] at h1
    rw [ite_eq_right (hcheck.mp hbad)]
    dsimp only [StubEnd]
    exact ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1, io1, rfl, h1, hf, by simp,
      by simp, by simp, fun b _ _ => by show u1.mem b = _; rw [m1]⟩
  rw [ite_eq_right hbad] at h1
  have hok : ptr.toNat + len.toNat ≤ st.mem.pages * 65536 ∧ ptr.toNat + len.toNat < 2 ^ 32 :=
    Classical.not_not.mp fun h => hbad (hcheck.mpr h)
  rw [ite_eq_left hok]
  have hkeepAll : ∀ (q' : Proc) (m : UInt64 → UInt8),
      KeptOutside (q.core.x 17) S.cap 0 0 q.core.mem m → q'.core.mem = m →
      MemFrame q.core.sp 0 q.core q'.core := fun q' m hk hm b hb => by
    rw [hm]
    refine hk b (sub_not_lt ?_) (by simp)
    have : (q.core.x 17 + UInt64.ofNat 4096).toNat = (q.core.x 17).toNat + 4096 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    simp only [Nat.mul_zero, Nat.add_zero] at hb
    omega
  by_cases hz : q.core.x 1 = 0
  · rw [ite_eq_left hz] at h1
    obtain ⟨p1, x01⟩ := h1
    have hlen0 : len.toNat = 0 := by
      rw [x1] at hz
      simpa using congrArg UInt64.toNat hz
    rw [hlen0]
    rw [randomLoop]
    simp only [show ¬ (0 < 0) by omega, ↓reduceDIte]
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨{ q with core := u1 }, [], ProcRunWith.ofReach hf r1,
      ⟨p1, sp1, e18, io1, fun b _ => by show u1.mem b = _; rw [m1], by simp,
        ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩,
      StoreRel.answered (hsr.regs e17 e18 m1) _ _, hf, e17, by simp [answered, LinuxWorld.answer],
      by simp, by simp, fun b _ _ => by show u1.mem b = _; rw [m1]⟩
    simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show u1.x 0 = (0 : UInt64).toUInt32.toUInt64
    rw [x01]
    rfl
  rw [ite_eq_right hz] at h1
  obtain ⟨p1, x191, x201, x211⟩ := h1
  have hlenpos : 0 < len.toNat := by
    rw [x1] at hz
    have : len.toUInt64.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp (by simpa using e))
    simpa using Nat.pos_of_ne_zero this
  have hloop := randomLoop_run (R := R) (P := P) hdom hcall hres cA.2 hgs hg17 hg18 hg21 hg28
    hg30 hsvc hen L R' st ptr.toNat len.toNat hok.1 (q.core.x 30) _ 0 [] st.mem
    st.host.world.events.length { q with core := u1 } rfl hlenpos rfl p1 hf
    (hsr.regs e17 e18 m1) (by rw [hbase]; show _ = u1.x 17 + _; rw [e17])
    (by
      show u1.x 20 = u1.x 17 + _
      rw [x201, e17, x0]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt32.toNat_toUInt64]
      omega)
    (by show u1.x 21 = _; rw [x211, x1]; apply UInt64.toNat_inj.mp; simp)
    x191 (fun j => hR j)
  have hev := randomLoop_events L R' ptr.toNat len.toNat (size := S.cap * 65536)
    (by omega) (by omega) _ 0 [] st.mem st.host.world.events.length rfl
  generalize randomLoop L R' ptr.toNat len.toNat 0 [] st.mem st.host.world.events.length = x
    at hloop hev ⊢
  obtain ⟨mx, lx, rx⟩ := x
  unfold LoopEnd at hloop
  dsimp only at hloop hev ⊢
  cases rx with
  | returned errno outs =>
    obtain ⟨p', r', pc', x0', lt', sp', io', x17', x18', f', sr', tr', k'⟩ := hloop
    change KeptOutside (u1.x 17) S.cap 0 0 u1.mem p'.core.mem at k'
    rw [e17] at k'
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨p', lx, ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1) r',
      ⟨pc', by rw [sp']; exact sp1, by rw [x18']; exact e18, by rw [io']; exact io1,
        hkeepAll p' p'.core.mem ?_ rfl, by simp,
        ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩,
      StoreRel.withHost sr' _, f', by rw [x17']; exact e17, rfl, tr', hev, ?_⟩
    · intro b h1 h2
      rw [k' b h1 h2]
      show u1.mem b = _
      rw [m1]
    · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      show p'.core.x 0 = errno.toUInt32.toUInt64
      rw [x0']
      apply UInt64.toNat_inj.mp
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
      omega
    · intro b h1 h2
      rw [k' b h1 h2]
      show u1.mem b = _
      rw [m1]
  | trapped msg outs =>
    obtain ⟨p', r', pc', msg', io', f', tr', k'⟩ := hloop
    change KeptOutside (u1.x 17) S.cap 0 0 u1.mem p'.core.mem at k'
    rw [e17] at k'
    dsimp only [sysAnswer, sysResult, StubEnd]
    refine ⟨p', lx, ProcRunWith.trans hdom (ProcRunWith.ofReach hf r1) r',
      by rw [io']; exact io1, msg', pc', f', rfl, tr', hev, ?_⟩
    intro b h1 h2
    rw [k' b h1 h2]
    show u1.mem b = _
    rw [m1]

end Run

/-! ## The stubs on the shim's machine -/

/-- The store relation on a platform that maps more. -/
theorem StoreRel.toLe {P P' : Platform} {cap : Nat} {gts : List ValueType} {α : Type}
    {st : Store α} {s : State} (h : StoreRel P cap gts st s) (hP : P.Le P') :
    StoreRel P' cap gts st s :=
  ⟨h.caps, h.cap_lt, h.glen, h.pages, h.size, h.types, h.globals, h.bytes,
    fun j hj => hP.normal _ (h.mapped j hj), h.below⟩

/-- The store relation of `st` at `s'` on the platform on which another store's relation at a
state with the same X17 maps the area. -/
theorem StoreRel.ofArea {P P' : Platform} {cap : Nat} {gts : List ValueType} {α β : Type}
    {st : Store α} {st' : Store β} {s s' : State} (h : StoreRel P' cap gts st s')
    (h0 : StoreRel P cap gts st' s) (h17 : s'.x 17 = s.x 17) : StoreRel P cap gts st s' :=
  ⟨h.caps, h.cap_lt, h.glen, h.pages, h.size, h.types, h.globals, h.bytes,
    fun j hj => by rw [h17]; exact h0.mapped j hj, h.below⟩

theorem StackOk.toLe {P P' : Platform} {s : State} (h : StackOk P s) (hP : P.Le P') :
    StackOk P' s :=
  ⟨h.aligned, h.limit, fun j hj => hP.normal _ (h.below j hj)⟩

theorem WritesLinear.mono {L : ShimLayout} {size size' : Nat} {e : Linux.Event}
    (h : WritesLinear L size e) (hs : size ≤ size') : WritesLinear L size' e :=
  fun g hg => Nat.le_trans (h g hg) hs

/-- The scratch's relation with the scratch's first 1,040 bytes and every byte from `2^32` up
kept. -/
theorem ScratchHolds.keepMem {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {m m' : UInt64 → UInt8} (h : ScratchHolds G I sp₀ top events m)
    (hm : ∀ j < 1040, m' (G.base + UInt64.ofNat j) = m (G.base + UInt64.ofNat j))
    (hhigh : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → m' a = m a) :
    ScratchHolds G I sp₀ top events m' := by
  refine ⟨?_, h.stack.congr hhigh, ?_, fun d hd => ?_⟩
  · rw [← h.saved]
    exact load64_congr fun k hk => hm k (by omega)
  · rw [← h.preopen]
    exact hm 8 (by decide)
  · rw [← h.held d hd]
    exact hm (16 + d) (by unfold descriptorLimit at hd; omega)

/-- The scratch's relation after layer events that neither open nor close a descriptor. -/
theorem ScratchHolds.quietAll {G : Scratch} {I : Launch} {sp₀ top : UInt64}
    {events : List Linux.Event} {m : UInt64 → UInt8} (h : ScratchHolds G I sp₀ top events m) :
    ∀ (l : List Linux.Event), (∀ e ∈ l, e.call.opens = false ∧ e.call ≠ Linux.closeCall) →
      ScratchHolds G I sp₀ top (events ++ l) m := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rw [List.append_nil]; exact h
  | append_singleton l e ih =>
    intro hl
    rw [← List.append_assoc]
    have he := hl e (by simp)
    exact ScratchHolds.quiet (ih fun x hx => hl x (by simp [hx])) (by rw [he.1]; simp) he.2

theorem typed_clock {args : List Value} (hlen : args.length = 3)
    (hty : Typed [.i32, .i64, .i32] args) :
    ∃ (id : UInt32) (precision : UInt64) (ptr : UInt32),
      args = [.i32 id, .i64 precision, .i32 ptr] := by
  match args, hlen, hty with
  | [v0, v1, v2], _, ⟨t0, t1, t2, _⟩ =>
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := by
      cases v0 <;> first | exact ⟨_, rfl⟩ | exact t0.elim
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i64 a := by
      cases v1 <;> first | exact ⟨_, rfl⟩ | exact t1.elim
    obtain ⟨a2, rfl⟩ : ∃ a, v2 = .i32 a := by
      cases v2 <;> first | exact ⟨_, rfl⟩ | exact t2.elim
    exact ⟨a0, a1, a2, rfl⟩

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- What a stub's end gives on the shim's machine: a return or a trap of `StubResult`, from a run
of the process that `StubEnd` states on `wasiPlatform`, when every event that the run adds is a
call that neither opens nor closes a descriptor and writes as `TraceRel` requires, and the memory
keeps the scratch's first 1,040 bytes and every byte from `2^32` up. -/
theorem stubResult_of_end {S : Shared} {n : Nat} {rs : List ValueType}
    {Ev : Linux.Event → Prop} {T : UInt64} {m : Nat} {st : Store (Observed LinuxWorld)} {q : Proc}
    (hsr : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR S.cap
      S.globalTypes st q)
    (hEv : ∀ e, Ev e → e.call.opens = false ∧ e.call ≠ Linux.closeCall ∧
      WritesNative (shimLayout L.area G) size e)
    (hkeep : ∀ m' : UInt64 → UInt8, KeptOutside (q.core.x 17) S.cap T m q.core.mem m' →
      (∀ j < 1040, m' (G.base + UInt64.ofNat j) = q.core.mem (G.base + UInt64.ofNat j)) ∧
      ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → m' a = q.core.mem a)
    {r : HostResult (Observed LinuxWorld)}
    (h : StubEnd R (wasiPlatform L sp₀ top) code S rs Ev T m st q r) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubResult S n rs
      r q := by
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  refine .inr ?_
  cases r with
  | Return vs st' =>
    obtain ⟨q', l, hrch, hret, hsr', hf', h17', hev, htr', hEv', hkp⟩ := h
    have hsame := hkeep _ hkp
    refine ⟨q', hrch, hret, StoreRel.ofArea hsr' hst h17', hf', by rw [h17']; exact h17,
      by rw [show q'.core.x 18 = q.core.x 18 from hret.x18]; exact hgap, ⟨?_, ?_⟩, ?_⟩
    · show q'.trace = _
      rw [htr', htr.1, hev]
      simp
    · intro e he
      rw [hev] at he
      rcases List.mem_append.mp he with he | he
      · exact htr.2 e he
      · exact (hEv e (hEv' e he)).2.2
    · show ScratchHolds G I sp₀ top st'.host.world.events q'.core.mem
      rw [hev]
      exact (ScratchHolds.keepMem hK hsame.1 hsame.2).quietAll l
        fun e he => ⟨(hEv e (hEv' e he)).1, (hEv e (hEv' e he)).2.1⟩
  | Trap st' msg =>
    obtain ⟨q', l, hrch, hio, hmsg, hpc, hf', hev, htr', hEv', -⟩ := h
    subst hmsg
    refine ⟨q', hrch, hio, .inr (.inr (.inr ⟨rfl, hpc⟩)), hf', ?_, ?_⟩
    · show q'.trace = _
      rw [htr', htr.1, hev]
      simp
    · intro e he
      rw [hev] at he
      rcases List.mem_append.mp he with he | he
      · exact htr.2 e he
      · exact (hEv e (hEv' e he)).2.2
  | Throw _ _ _ => exact h.elim

/-- A byte at or above the area's end lies outside the guest's memory, and a byte below `T` or at
least `n` bytes above it lies outside the `n` bytes from `T`, so `KeptOutside` keeps it. -/
theorem kept_scratch {area T b : UInt64} {cap n : Nat} {m m' : UInt64 → UInt8}
    (h : KeptOutside area cap T n m m') (hb : area.toNat + areaSize cap ≤ b.toNat)
    (hT : b.toNat < T.toNat ∨ T.toNat + n ≤ b.toNat)
    (harea : area.toNat + areaSize cap < 2 ^ 64) (hT64 : T.toNat + n ≤ 2 ^ 64) : m' b = m b := by
  have h4096 : (area + UInt64.ofNat 4096).toNat = area.toNat + 4096 := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    unfold areaSize at harea
    omega
  unfold areaSize at hb
  refine h b (sub_not_lt (by rw [h4096]; omega)) ?_
  rcases hT with hT | hT
  · exact sub_not_lt_below hT hT64
  · exact sub_not_lt hT

/-- `sysFn` of `clock_time_get` invokes `clockInvoke`. -/
theorem sysInvoke_clock (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies) :
    sysInvoke F L I R Call.clockTimeGet = clockInvoke L R := by
  simp only [sysInvoke, ↓reduceIte]

/-- `sysFn` of `random_get` invokes `randomInvoke`. -/
theorem sysInvoke_random (F : OpenFlags) (L : ShimLayout) (I : Launch) (R : Linux.Replies) :
    sysInvoke F L I R Call.randomGet = randomInvoke L R := by
  simp (config := { decide := true }) only [sysInvoke, ↓reduceIte]

/-- The stub of `clock_time_get` stands for the shim's `clock_time_get`, when the area and the
scratch lie in the data segment. -/
theorem clockStub_sim (S : Shared) (n : Nat) {ck svc en : UInt64} {is : List Instr}
    (hg : clockStub ck svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code ck is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i64, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.clockTimeGet)
      ck := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = ck at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨id, precision, ptr, rfl⟩ := typed_clock hlen hty
  have x0 : q.core.x 0 = id.toUInt64 := hregs 0 (by simp)
  have x2 : q.core.x 2 = ptr.toUInt64 := hregs 2 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, hgap, htr, -⟩ := hsr'
  change q.core.x 17 = L.area at h17
  change L.area.toNat + areaSize S.cap + scratchSize ≤ (q.core.x 18).toNat at hgap
  have hPP := modulePlatform_le_wasi L G sp₀ top
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      Call.clockTimeGet).invoke st [.i32 id, .i64 precision, .i32 ptr] =
      clockInvoke (shimLayout L.area G) (fun j => R (l₀.length + j)) st
        [.i32 id, .i64 precision, .i32 ptr] := by
    have e : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
        Call.clockTimeGet).invoke = sysInvoke arm64Flags (shimLayout L.area G) I
          (fun j => R (l₀.length + j)) Call.clockTimeGet := rfl
    rw [e, sysInvoke_clock]
  rw [hinv]
  have hLA := hL
  unfold scratchSize at hdata hgap
  have hGn : G.base.toNat = L.area.toNat + areaSize S.cap := by
    rw [hGb, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at hLA ⊢
    omega
  have hTn : (shimLayout L.area G).timespec.toNat = G.base.toNat + 1040 := by
    show (G.base + 1040).toNat = _
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat, Nat.reducePow] at hLA ⊢
    omega
  have hT : (shimLayout L.area G).timespec =
      q.core.x 17 + UInt64.ofNat (areaSize S.cap + 1040) := by
    apply UInt64.toNat_inj.mp
    rw [hTn, hGn, h17, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at hLA ⊢
    omega
  have hlim : (q.core.x 17).toNat + areaSize S.cap + 1056 ≤ (q.core.x 18).toNat := by
    rw [h17]
    omega
  have hmapT : ∀ k < 16, (wasiPlatform L sp₀ top).normal
      ((shimLayout L.area G).timespec + UInt64.ofNat k) = true := by
    intro k hk
    apply (elfPlatform_le_wasi L sp₀ top).normal
    have e : ((shimLayout L.area G).timespec + UInt64.ofNat k).toNat =
        G.base.toNat + 1040 + k := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat', hTn]
      simp only [Nat.reducePow] at hLA ⊢
      omega
    simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le]
    rw [e, hGn]
    omega
  have hR : (fun j => R (l₀.length + j)) st.host.world.events.length = R q.trace.length := by
    simp only [htr.1, List.length_map, List.length_append]
  have hrun := clockStub_run (P := wasiPlatform L sp₀ top) hdom hg hcode hsvc hen
    (shimLayout L.area G) (fun j => R (l₀.length + j)) st q id precision ptr hpc
    (StackOk.toLe hstk hPP) (StoreRel.toLe hst hPP) hf x0 x2 (Nat.le_refl _) hT hlim hmapT hR
  refine stubResult_of_end hsr (fun e he => ?_) (fun m' hkp => ⟨fun j hj => ?_, fun a ha => ?_⟩)
    hrun
  · subst he
    exact ⟨rfl, fun h => absurd h (by decide : Linux.clockGettimeCall ≠ Linux.closeCall),
      .inr (.inl ⟨rfl, outputs_clock _ _⟩)⟩
  · have e : (G.base + UInt64.ofNat j).toNat = G.base.toNat + j := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow] at hLA ⊢
      omega
    exact kept_scratch hkp (by rw [e, hGn, h17]; omega) (.inl (by rw [e, hTn]; omega))
      (by rw [h17]; simp only [Nat.reducePow] at hLA ⊢; omega)
      (by rw [hTn]; simp only [Nat.reducePow] at hLA ⊢; omega)
  · exact kept_scratch hkp (by rw [h17]; omega) (.inr (by rw [hTn]; omega))
      (by rw [h17]; simp only [Nat.reducePow] at hLA ⊢; omega)
      (by rw [hTn]; simp only [Nat.reducePow] at hLA ⊢; omega)

/-- The stub of `random_get` stands for the shim's `random_get`, when the area and the scratch
lie in the data segment and the machine's bound on writes holds the cap's memory. -/
theorem randomStub_sim (S : Shared) (n : Nat) {rn svc en : UInt64} {is : List Instr}
    (hg : randomStub rn svc S.trapUnreachable en = .ok is)
    (hcode : CodeAt code rn is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem) (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) Call.randomGet)
      rn := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = rn at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨ptr, len, rfl⟩ := typed_i32x2 hlen hty
  have x0 : q.core.x 0 = ptr.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = len.toUInt64 := hregs 1 (by simp)
  have hsr' := hsr
  obtain ⟨hst, hf, h17, -, htr, -⟩ := hsr'
  change q.core.x 17 = L.area at h17
  have hPP := modulePlatform_le_wasi L G sp₀ top
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      Call.randomGet).invoke st [.i32 ptr, .i32 len] =
      randomInvoke (shimLayout L.area G) (fun j => R (l₀.length + j)) st [.i32 ptr, .i32 len] := by
    have e : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
        Call.randomGet).invoke = sysInvoke arm64Flags (shimLayout L.area G) I
          (fun j => R (l₀.length + j)) Call.randomGet := rfl
    rw [e, sysInvoke_random]
  rw [hinv]
  have hLA := hL
  unfold scratchSize at hdata
  have hR : ∀ j, (fun j => R (l₀.length + j)) (st.host.world.events.length + j) =
      R (q.trace.length + j) := by
    intro j
    simp only [htr.1, List.length_map, List.length_append, Nat.add_assoc]
  have hrun := randomStub_run (P := wasiPlatform L sp₀ top) hdom hg hcode hsvc hen
    (shimLayout L.area G) (fun j => R (l₀.length + j)) st q ptr len hpc (StackOk.toLe hstk hPP)
    (StoreRel.toLe hst hPP) hf x0 x1 (by rw [h17]; rfl) hR
  have hlow : (q.core.x 17).toNat + areaSize S.cap < 2 ^ 64 := by
    rw [h17]
    simp only [Nat.reducePow] at hLA ⊢
    omega
  refine stubResult_of_end hsr (fun e he => ⟨by rw [he.1]; rfl, by rw [he.1]; decide,
    .inl (he.2.mono hsize)⟩) (fun m' hkp => ⟨fun j hj => ?_, fun a ha => ?_⟩) hrun
  · have e : (G.base + UInt64.ofNat j).toNat = L.area.toNat + areaSize S.cap + j := by
      rw [hGb, add_ofNat_add, UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow] at hLA ⊢
      omega
    exact kept_scratch hkp (by rw [e, h17]; omega) (.inr (by simp)) hlow (by simp)
  · exact kept_scratch hkp (by rw [h17]; simp only [Nat.reducePow] at hLA ha ⊢; omega)
      (.inr (by simp)) hlow (by simp)

/-- The call of `shimCalls` whose import is the import of a stub of `clockStubs` is the stub's
call. -/
theorem clockStubs_call :
    ∀ s ∈ clockStubs, ∀ c ∈ shimCalls, ABI.callImport c = s.decl → c = s.call := by
  decide

/-- The code of a stub of `clockStubs` at `a`, generated with the routine `SVC #0; RET` at `svc`,
the trap stub, the routine of errnos at `en`, and the scratch `areaSize S.cap` bytes above the
area, stands for the shim's function of the call `c` of `shimCalls` whose import is the stub's,
when the area and the scratch lie in the data segment and the cap's linear memory within the
machine's `size` bytes. -/
theorem clockStubs_sim {s : FlatStub} (hs : s ∈ clockStubs) {c : Call} (hc : c ∈ shimCalls)
    (hd : ABI.callImport c = s.decl) (S : Shared) (n : Nat) {a svc en : UInt64}
    {is : List Instr} (hg : s.gen a svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code a is) (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hen : CodeAt code en errnoRoutine) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem) (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      s.decl.params s.decl.results
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) c) a := by
  obtain rfl := clockStubs_call s hs c hc hd
  simp only [clockStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact clockStub_sim S n hg hcode hsvc hen hGb hdata
  · exact randomStub_sim S n hg hcode hsvc hen hGb hdata hsize

end Verified.ShimA64
