import LeanExe.A64.Proof.LinuxImage
import LeanExe.A64.Proof.LinuxCalls
import LeanExe.A64.Stamp

/-!
The runtime of the stamp executable around its program, for the Linux call layer's rule.
`genStampElf` checks that the stack's room and the stamp routine's frame of `stampFrame pin pout`
bytes stay below 2^32 and builds the executable with `genElfWith`, whose layout reserves 16 bytes
of `main`'s frame below the stack's top, so it passes the room `room + (stampFrame pin pout - 16)`.
`stamp_main` applies `elfWith_main` to the executable and lifts its runs, which make no call, into
`ProcReachWith` for every table of calls and every set of replies.  From the entry, a run reaches
`main` in a process that meets the premises of the stamp routine's theorem, with the stack's
premises stated for the routine's frame, and from `main`'s return address or the exit word a run
reaches `SVC #0` with X8 at 94, the call of `exit_group`.
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

end LeanExe.A64
