module

public import LeanExe.A64.Proof.LinuxImage
public import LeanExe.A64.Proof.LinuxCalls
public import LeanExe.A64.Stamp
public import LeanExe.A64.Proof.StampRuns

@[expose] public section

/-!
The runtime of the stamp executable around its program, for the Linux call layer's rule.
`genStampElf` checks that the stack's room and the stamp routine's frame of `stampFrame pin pout`
bytes stay below 2^32 and builds the executable with `genElfWith`, whose layout reserves 16 bytes
of `main`'s frame below the stack's top, so it passes the room `room + (stampFrame pin pout - 16)`.
`stamp_main` applies `elfWith_main` to the executable and lifts its runs, which make no call, into
`ProcReachWith` for every table of calls and every set of replies.  From the entry, a run reaches
`main` in a process that meets the premises of the stamp routine's theorem, with the stack's
premises stated for the routine's frame, and from `main`'s return address or the exit word a run
reaches `SVC #0` with X8 at 94, the call of `exit_group`.  `stamp_bytes_run_any` joins
`stamp_main` to the program's theorem in the form `StampRunsAny`: from the entry, a run over
`LeanExe.Linux.table` reaches `exit_group` with only the Linux call layer's events in its trace,
`ProcReachWith.trace_sys`, and with the events of `StampEvents`.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies)

/-- The layout of the stamp executable, and an empty layout when the generator fails. -/
def stampLayout (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) (pin pout : List UInt8) :
    ElfLayout :=
  match genStampElf m k inMax room cap pin pout with
  | .ok (_, L) => L
  | .error _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- `genStampElf` unpacked: the bound on the stack and the executable of `genElfWith`. -/
theorem genStampElf_ok {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {pin pout : List UInt8} {r : List UInt8 × ElfLayout}
    (h : genStampElf m k inMax room cap pin pout = .ok r) :
    room.toNat + stampFrame pin pout < 2 ^ 32 ∧
      genElfWith (fun rd _ base => genStampProgram m k inMax (after rd 1) base room cap pin pout)
        m (room + UInt64.ofNat (stampFrame pin pout - 16)) cap = .ok r := by
  unfold genStampElf at h
  by_cases hb : room.toNat + stampFrame pin pout < 2 ^ 32
  · simp only [bind, Except.bind, hb] at h
    exact ⟨hb, h⟩
  · simp only [bind, Except.bind, hb, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at h
    cases h

/-- The runtime of the stamp executable around its program, given the kernel's check `hk` of the
file `nb` and the file's program headers `hseg`.  From a process whose memory holds the file as the
loader places it, with the program counter at the entry and no event in the trace, the run reaches
`main` in a process `p0` that meets the premises of the stamp routine's theorem for the program
`is`, the code map, the routine `SVC #0; RET` at `svcRetAddr`, the exit word, and the area, and
leaves the UART's state as it was.  From every process that the run reaches at `main`'s return
address or at the exit word, it reaches `SVC #0` with X8 at 94, the call of `exit_group`, keeping
X0, the trace, and the UART's state.  Every run is one of `ProcReachWith` for the table `T` and the
replies `R`.  The code map holds the words from the entry through the program's end, and the
platform's Normal memory is the data segment. -/
theorem stamp_main {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {pin pout : List UInt8} {nb len : Nat}
    (hk : bytesOk (genStampElf m k inMax room cap pin pout) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (stampLayout m k inMax room cap pin pout))
    (hroom : room.toNat % 16 = 0) (T : List Call) (R : Replies) (p : Proc)
    (hl : ElfLoaded (byteAt nb) p.core.mem) (hpc : p.core.pc = elfEntry) (htr : p.trace = [])
    {L' : ElfLayout} (hL' : L' = stampLayout m k inMax room cap pin pout)
    {code' : UInt64 → Option UInt32}
    (hcode' : code' = fetchFrom p.core.mem elfEntry (elfWords L')) :
    ∃ (is : List Instr) (p0 : Proc),
      genStampProgram m k inMax svcRetAddr elfExitWord room cap pin pout = .ok is ∧
      CodeAt code' (after elfExitWord 1) is ∧ OpsAt code' svcRetAddr [.svc, .ins (.ret 30)] ∧
      (∀ a w, code' a = some w → a.toNat < 2 ^ 55) ∧ elfExitWord.toNat < 2 ^ 55 ∧
      ProcReachWith T R (elfPlatform L') code' p p0 ∧ p0.core.pc = after elfExitWord 1 ∧
      p0.fpcr = fpcrValue ∧ p0.trace = [] ∧ (p0.core.x 30).toNat < 2 ^ 55 ∧
      p0.core.sp % 16 = 0 ∧ p0.core.sp.toNat ≤ 2 ^ 63 ∧
      (∀ j < room.toNat + stampFrame pin pout, (elfPlatform L').normal
        (p0.core.sp - UInt64.ofNat (stampFrame pin pout) - room + UInt64.ofNat j) = true) ∧
      p0.core.x 17 = L'.area ∧
      (∀ j < areaSize cap, p0.core.mem (L'.area + UInt64.ofNat j) = areaByte m.initialStore j) ∧
      (∀ j < areaSize cap, (elfPlatform L').normal (L'.area + UInt64.ofNat j) = true) ∧
      L'.area.toNat + areaSize cap + room.toNat + stampFrame pin pout ≤ p0.core.sp.toNat ∧
      (elfPlatform L').normal (elfPlatform L').uart = false ∧ p0.core.io = p.core.io ∧
      ∀ q : Proc, ProcReachWith T R (elfPlatform L') code' p q →
        (q.core.pc = p0.core.x 30 ∨ q.core.pc = elfExitWord) →
        ∃ q', ProcReachWith T R (elfPlatform L') code' p q' ∧
          code' q'.core.pc = some svcWord ∧ q'.core.x 8 = 94 ∧ q'.core.x 0 = q.core.x 0 ∧
          q'.trace = q.trace ∧ q'.core.io = q.core.io := by
  subst hcode' hL'
  obtain ⟨bytes, L, hg, -, hbyte⟩ := of_bytesOk hk
  have hL : stampLayout m k inMax room cap pin pout = L := by simp only [stampLayout, hg]
  rw [hL] at hseg ⊢
  obtain ⟨hb, hg'⟩ := genStampElf_ok hg
  have hF : stampFrame pin pout % 16 = 0 ∧ 32 ≤ stampFrame pin pout := by
    unfold stampFrame
    omega
  have hF64 : (UInt64.ofNat (stampFrame pin pout)).toNat = stampFrame pin pout :=
    toNat_ofNat_lt (by omega)
  have hr : (room + UInt64.ofNat (stampFrame pin pout - 16)).toNat =
      room.toNat + (stampFrame pin pout - 16) := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  obtain ⟨is, p0, hp, hprogC, hrd, -, hdom, hbase', hpm, pc0, f0, tr0, h30, hal, htop, hstk,
    h17, hdata, hamap, habove, hU, hio0, hexit⟩ :=
    elfWith_main hg' hbyte hseg (by rw [hr]; omega) p hl hpc htr rfl
  rw [hr] at hstk habove
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have e1 : (p0.core.sp - 16).toNat = p0.core.sp.toNat - 16 :=
    toNat_sub_le (by rw [h16]; omega)
  have e2 : (p0.core.sp - UInt64.ofNat (stampFrame pin pout)).toNat =
      p0.core.sp.toNat - stampFrame pin pout := by
    rw [toNat_sub_le (a := p0.core.sp) (by rw [hF64]; omega), hF64]
  have hsp : p0.core.sp - 16 - (room + UInt64.ofNat (stampFrame pin pout - 16)) =
      p0.core.sp - UInt64.ofNat (stampFrame pin pout) - room := by
    apply UInt64.toNat_inj.mp
    rw [toNat_sub_le (a := p0.core.sp - 16) (b := room + UInt64.ofNat (stampFrame pin pout - 16))
        (by rw [e1, hr]; omega),
      toNat_sub_le (a := p0.core.sp - UInt64.ofNat (stampFrame pin pout)) (b := room)
        (by rw [e2]; omega), e1, e2, hr]
    omega
  refine ⟨is, p0, hp, hprogC, OpsAt.drop (l1 := [.ins (.movz 8 63 0)]) hrd, hdom, hbase',
    hpm.toWith T R, pc0, f0, tr0, h30, hal, htop, fun j hj => ?_, h17, hdata, hamap,
    by omega, hU, hio0, fun q hq hqpc => ?_⟩
  · rw [← hsp]
    exact hstk j (by omega)
  · obtain ⟨q', r', rest⟩ := hexit q hqpc
    exact ⟨q', hq.trans (r'.toWith T R), rest⟩

/-! ## The executable -/

/-- A step of `istep` keeps the trace. -/
theorem istep_trace {P : Platform} {code : UInt64 → Option UInt32} {p q : Proc}
    (h : istep P code p = some q) : q.trace = p.trace := by
  unfold istep at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          rfl
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
                rfl
              · cases h
            · cases h

/-- A step of `pstepWith` appends at most one event, an event of the Linux call layer. -/
theorem pstepWith_trace_sys {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} {p q : Proc} (h : pstepWith T R P code p = some q)
    (hp : p.trace = (sysEvents p.trace).map Event.sys) :
    q.trace = (sysEvents q.trace).map Event.sys := by
  unfold pstepWith at h
  split at h
  · split at h
    · split at h
      · cases h
      · unfold sysCall at h
        split at h
        · cases h
          show p.trace ++ [Event.sys _] = (sysEvents (p.trace ++ [Event.sys _])).map Event.sys
          rw [sysEvents_snoc, List.map_append, ← hp]
          rfl
        · cases h
    · cases h
  · rw [istep_trace h]
    exact hp

/-- Every event of a run of `pstepWith` from a trace of the layer's events is an event of the
Linux call layer. -/
theorem ProcReachWith.trace_sys {T : List Call} {R : Replies} {P : Platform}
    {code : UInt64 → Option UInt32} :
    ∀ {p q : Proc}, ProcReachWith T R P code p q →
      p.trace = (sysEvents p.trace).map Event.sys → q.trace = (sysEvents q.trace).map Event.sys
  | _, _, .refl _, hp => hp
  | _, _, .next hs r, hp => ProcReachWith.trace_sys r (pstepWith_trace_sys hs hp)

/-- The theorem of an executable of `genStampElf` from its entry to `exit_group` for every set of
replies, given the kernel's check `hk` of the file `nb`, the file's program headers `hseg`, and the
program's theorem `hprog` in the form `StampRunsAny`.  From a process whose memory holds the file
as the loader places it, with the program counter at the entry and no event in the trace, a run of
`ProcReachWith` over `LeanExe.Linux.table` reaches `SVC #0` with X8 at 94, the call of
`exit_group`, leaving the UART's state as it was, with only events of the Linux call layer in its
trace.  For some address `sp` of the top of `main`'s frame, the status in X0 is 0 and the events
are those of `StampEvents` for a run that returned, or the events are those of `StampEvents` for a
run that reached the exit word with the status in X0. -/
theorem stamp_bytes_run_any {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat}
    {pin pout : List UInt8} {nb len : Nat}
    (hk : bytesOk (genStampElf m k inMax room cap pin pout) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (stampLayout m k inMax room cap pin pout))
    (hroom : room.toNat % 16 = 0) {Out : List UInt8 → List UInt8}
    {Tr : List UInt8 → UInt64 → Prop} (hprog : StampRunsAny m k inMax room cap pin pout Out Tr)
    (R : Replies) (p : Proc) (hl : ElfLoaded (byteAt nb) p.core.mem) (hpc : p.core.pc = elfEntry)
    (htr : p.trace = []) :
    ∃ p', ProcReachWith LeanExe.Linux.table R
        (elfPlatform (stampLayout m k inMax room cap pin pout))
        (fetchFrom p.core.mem elfEntry (elfWords (stampLayout m k inMax room cap pin pout))) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords (stampLayout m k inMax room cap pin pout))
        p'.core.pc = some svcWord ∧ p'.core.x 8 = 94 ∧ p'.core.io = p.core.io ∧
      p'.trace = (sysEvents p'.trace).map Event.sys ∧
      ∃ sp : UInt64,
        (p'.core.x 0 = 0 ∧ StampEvents sp inMax pin pout Out Tr none (sysEvents p'.trace)) ∨
          StampEvents sp inMax pin pout Out Tr (some (p'.core.x 0)) (sysEvents p'.trace) := by
  obtain ⟨is, p0, hp, hprogC, hsvc, hdom, hbase', hpm, pc0, f0, tr0, h30, hal, htop, hstk, h17,
    hdata, hamap, habove, hU, hio0, hexit⟩ :=
    stamp_main hk hseg hroom LeanExe.Linux.table R p hl hpc htr rfl rfl
  obtain ⟨q, rq, ioq, out⟩ := hprog _ R _ svcRetAddr elfExitWord _ hp hprogC hsvc hdom hbase' p0
    pc0 f0 tr0 h30 hal htop hstk h17 hdata hamap habove hU
  have hpcq : q.core.pc = p0.core.x 30 ∨ q.core.pc = elfExitWord := by
    rcases out with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  obtain ⟨q', r', c', x8', x0', tr', io'⟩ := hexit q (hpm.trans rq) hpcq
  refine ⟨q', r', c', x8', (io'.trans ioq).trans hio0,
    ProcReachWith.trace_sys r' (by rw [htr]; rfl), p0.core.sp, ?_⟩
  rw [x0', tr']
  rcases out with ⟨-, h0, ev⟩ | ⟨-, ev⟩
  · exact .inl ⟨h0, ev⟩
  · exact .inr ev

end LeanExe.A64
