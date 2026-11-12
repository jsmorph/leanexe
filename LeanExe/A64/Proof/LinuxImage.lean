import LeanExe.A64.Proof.LinuxRuns
import LeanExe.A64.Proof.Addr
import LeanExe.A64.Proof.StartupCode
import LeanExe.A64.File

/-!
The theorem of a Linux executable of `genSysElf`, from the process's first instruction to its
`exit_group`.  The premise on memory is `ElfLoaded` of the file: for each `PT_LOAD` header that
`elfSegments` reads from the file, memory holds the segment's file bytes from its address and zeros
up to its memory size, as Linux's ELF loader places them.  The kernel's check `bytesOk` makes the
file's bytes those of the generator, so the text segment holds the runtime and the program and the
data segment the area's prefix and zeros.  From the entry, with any registers but the program
counter, any `FPCR`, and an empty trace, the runtime writes `FPCR`, sets X17 and SP, and calls
`main`, whose run `SysBytesRuns` gives; `main` returns to the exit, which the trap stubs reach
through the exit word, and the exit sets X8 to 94 at `SVC #0`.  `elf_bytes_run` states the result
for the code map of the words from the entry through the program's end and the platform of the
data segment.
-/

namespace LeanExe.A64

open Wasm

/-! ## The generator's output -/

/-- `genElfWith` unpacked: the program, the layout, the bounds, the runtime, and the bytes. -/
theorem gen_elfWith {gp : UInt64 → UInt64 → UInt64 → GenM (List Instr)} {m : Module}
    {room : UInt64} {cap : Nat} {bytes : List UInt8} {L : ElfLayout}
    (hg : genElfWith gp m room cap = .ok (bytes, L)) :
    ∃ prog rt, gp sysReadAddr sysWriteAddr elfExitWord = .ok prog ∧
      L = elfLayoutOf prog.length m cap room ∧
      elfBase.toNat + L.dataOff + L.dataMem < 2 ^ 32 ∧ areaPrefix m ≤ areaSize cap ∧
      sysRuntime L = .ok rt ∧
      bytes = elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
        (loadHeader 6 L.dataOff L.area L.dataFile L.dataMem ++ (opBytes rt ++ (imageBytes prog ++
          (List.replicate (L.dataOff - L.codeEnd) 0 ++ areaPrefixBytes m))))) := by
  unfold genElfWith at hg
  cases hp : gp sysReadAddr sysWriteAddr elfExitWord with
  | error e => rw [hp] at hg; cases hg
  | ok prog => ?_
  rw [hp] at hg
  by_cases hr : elfBase.toNat + (elfLayoutOf prog.length m cap room).dataOff +
      (elfLayoutOf prog.length m cap room).dataMem < 2 ^ 32 ∧ areaPrefix m ≤ areaSize cap
  · simp only [bind, Except.bind, hr] at hg
    cases hs : sysRuntime (elfLayoutOf prog.length m cap room) with
    | error e => rw [hs] at hg; cases hg
    | ok rt =>
        rw [hs] at hg
        simp only [pure, Except.pure] at hg
        injection hg with hg1
        injection hg1 with hb hL
        subst hL
        exact ⟨prog, rt, rfl, rfl, hr.1, hr.2, hs, hb.symm⟩
  · simp only [bind, Except.bind, hr, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at hg
    cases hg

/-- `sysRuntime` unpacked: the instructions of the addresses and the branches' fields. -/
theorem sysRuntime_ok {L : ElfLayout} {rt : List Op} (h : sysRuntime L = .ok rt) :
    ∃ ar stk call back, addrOf 17 (after elfEntry 2) L.area = .ok ar ∧
      addrOf 1 (after elfEntry 4) L.stackTop = .ok stk ∧
      bField (after elfEntry 7) (after elfExitWord 1) = .ok call ∧
      bField elfExitWord (after elfEntry 8) = .ok back ∧
      rt = ([Instr.movz 1 0x200 1, msrOf .fpcr 1] ++ ar ++ stk ++
        ([.addImm 31 1 0, .bl call, .movz 8 94 0] : List Instr)).map .ins ++ [.svc, .ins (.b 0)] ++
        [.ins (.movz 8 63 0), .svc, .ins (.ret 30), .ins (.movz 8 64 0), .svc, .ins (.ret 30),
          .ins (.b back)] := by
  unfold sysRuntime at h
  cases h1 : addrOf 17 (after elfEntry 2) L.area with
  | error e => simp [h1, bind, Except.bind] at h
  | ok ar =>
  cases h2 : addrOf 1 (after elfEntry 4) L.stackTop with
  | error e => simp [h1, h2, bind, Except.bind] at h
  | ok stk =>
  cases h3 : bField (after elfEntry 7) (after elfExitWord 1) with
  | error e => simp [h1, h2, h3, bind, Except.bind] at h
  | ok call =>
  cases h4 : bField elfExitWord (after elfEntry 8) with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind] at h
  | ok back =>
  simp only [h1, h2, h3, h4, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  exact ⟨ar, stk, call, back, rfl, rfl, rfl, rfl, h.symm⟩

/-! ## Code words from memory -/

theorem length_opBytes (ops : List Op) : (opBytes ops).length = 4 * ops.length := by
  induction ops with
  | nil => rfl
  | cons o ops ih =>
      simp only [opBytes, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih]
      simp [wordBytes]
      omega

theorem getElem_opBytes (ops : List Op) (i k : Nat) (hi : i < ops.length) (hk : k < 4) :
    (opBytes ops)[4 * i + k]'(by rw [length_opBytes]; omega) =
      (wordBytes ops[i].word)[k]'(by simp [wordBytes]; omega) := by
  induction ops generalizing i with
  | nil => simp at hi
  | cons o ops ih =>
      cases i with
      | zero =>
          simp only [opBytes, List.flatMap_cons]
          rw [List.getElem_append_left (by simp [wordBytes]; omega)]
          simp
      | succ i =>
          simp only [opBytes, List.flatMap_cons]
          rw [List.getElem_append_right (by simp [wordBytes]; omega)]
          have := ih i (by simpa using hi)
          simp only [opBytes] at this
          simp only [List.getElem_cons_succ]
          rw [← this]
          congr 1
          simp [wordBytes]
          omega

theorem opBytes_append (a b : List Op) : opBytes (a ++ b) = opBytes a ++ opBytes b := by
  simp [opBytes]

theorem imageBytes_eq_opBytes (is : List Instr) : imageBytes is = opBytes (is.map .ins) := by
  simp [imageBytes, opBytes, Op.word, List.flatMap_map]

/-- A memory that holds the bytes of `ops` from `a` gives a map of code words that holds `ops` at
`a`. -/
theorem opsAt_fetchFrom {m : UInt64 → UInt8} {a : UInt64} {ops : List Op}
    (hn : 4 * ops.length < 2 ^ 64)
    (hm : ∀ j (hj : j < (opBytes ops).length), m (a + UInt64.ofNat j) = (opBytes ops)[j]) :
    OpsAt (fetchFrom m a ops.length) a ops := by
  intro i hi
  have hd : (after a i - a).toNat = 4 * i := by
    rw [after, UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_mul, UInt64.toNat_ofNat']
    have e4 : (4 : UInt64).toNat = 4 := rfl
    rw [e4]
    simp only [Nat.reducePow] at hn ⊢
    omega
  simp only [fetchFrom, hd]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  congr 1
  apply load32_wordBytes
  intro k hk
  have := hm (4 * i + k) (by rw [length_opBytes]; omega)
  rw [getElem_opBytes ops i k hi hk] at this
  rw [← this]
  congr 1
  rw [after, UInt64.add_assoc]
  congr 1
  rw [UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

theorem OpsAt.drop {code : UInt64 → Option UInt32} {a : UInt64} {l1 l2 : List Op}
    (h : OpsAt code a (l1 ++ l2)) : OpsAt code (after a l1.length) l2 := fun i hi => by
  have := h (l1.length + i) (by simp; omega)
  rw [after_after]
  simpa [List.getElem_append_right] using this

theorem OpsAt.take {code : UInt64 → Option UInt32} {a : UInt64} {l1 l2 : List Op}
    (h : OpsAt code a (l1 ++ l2)) : OpsAt code a l1 := fun i hi => by
  have := h i (by simp; omega)
  simpa [List.getElem_append_left hi] using this

theorem OpsAt.codeAt {code : UInt64 → Option UInt32} {a : UInt64} {is : List Instr}
    (h : OpsAt code a (is.map .ins)) : CodeAt code a is := fun i hi => by
  have := h i (by simpa using hi)
  simpa [Op.word] using this

/-! ## The layout -/

/-- The layout of the executable of `genSysElf`, and an empty layout when the generator fails. -/
def elfLayout (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) : ElfLayout :=
  match genSysElf m k inMax room cap with
  | .ok (_, L) => L
  | .error _ => ⟨0, 0, 0, 0, 0, 0⟩

/-- The two program headers of an executable with layout `L`. -/
def elfSegmentsOf (L : ElfLayout) : List ElfSegment :=
  [⟨1, 5, 0, elfBase.toNat, L.codeEnd, L.codeEnd⟩,
    ⟨1, 6, L.dataOff, L.area.toNat, L.dataFile, L.dataMem⟩]

/-- The number of code words of an executable with layout `L`, from the entry through the
program's end. -/
def elfWords (L : ElfLayout) : Nat := (L.codeEnd - 176) / 4

/-- A step of `MSR FPCR, Xt` sets the process's `FPCR`. -/
theorem pstep_fpcr {K : Kernel} {P : Platform} {code : UInt64 → Option UInt32} {p : Proc}
    {t : Fin 32} (hc : code p.core.pc = some (encode (msrOf .fpcr t))) :
    pstep K P code p = some { p.goto (p.core.pc + 4) with fpcr := p.core.x t } := by
  unfold pstep
  rw [hc]
  simp only [encode_ne_svcWord, ↓reduceIte, decode_encode]
  rfl

theorem elfHeader_length (e : UInt64) : (elfHeader e).length = 64 := by
  simp [elfHeader, bytes16, bytes64, wordBytes]

theorem loadHeader_length (fl : UInt32) (off : Nat) (v : UInt64) (fi me : Nat) :
    (loadHeader fl off v fi me).length = 56 := by
  simp [loadHeader, bytes64, wordBytes]

/-- A map of code words from `a` holds words only below `a + 4 N`. -/
theorem fetchFrom_dom {m : UInt64 → UInt8} {a : UInt64} {N : Nat} (h : a.toNat + 4 * N < 2 ^ 55) :
    ∀ b w, fetchFrom m a N b = some w → b.toNat < 2 ^ 55 := by
  intro b w hb
  unfold fetchFrom at hb
  split at hb
  · rename_i hc
    have e : b = a + (b - a) := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
    rw [e, UInt64.toNat_add]
    have := a.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  · cases hb

/-- The theorem of an executable of `genSysElf` from its entry to `exit_group`, given the kernel's
check `hk` of the file `nb`, the file's program headers `hseg`, and the program's theorem in the
form `SysBytesRuns`.  From a process whose memory holds the file as the loader places it, with the
program counter at the entry and no event in the trace, for a kernel none of whose calls fails:
when standard input holds at most `inMax` bytes, the process reaches `SVC #0` with X8 at 94, the
call of `exit_group`, after it writes `Out` of the input with status 0 in X0, or with a status that
`T` allows and nothing written; when it holds more, with status 64 and nothing written.  The run
leaves the UART's state as it was.  The code map holds the words from the entry through the
program's end, and the platform's Normal memory is the data segment. -/
theorem elf_bytes_run {m : Module} {k : Nat} {inMax room : UInt64} {cap : Nat} {nb len : Nat}
    (hk : bytesOk (genSysElf m k inMax room cap) nb len = true)
    (hseg : elfSegments (byteAt nb) = elfSegmentsOf (elfLayout m k inMax room cap))
    (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat)
    {Out : List UInt8 → List UInt8} {T : List UInt8 → UInt64 → Prop}
    (hprog : SysBytesRuns m k inMax room cap Out T) (K : Kernel) (p : Proc)
    (hl : ElfLoaded (byteAt nb) p.core.mem) (hpc : p.core.pc = elfEntry) (htr : p.trace = [])
    (hok : ∀ k, K.fail k = none) :
    (K.input.length ≤ inMax.toNat → ∃ p', ProcReach K (elfPlatform (elfLayout m k inMax room cap))
        (fetchFrom p.core.mem elfEntry (elfWords (elfLayout m k inMax room cap))) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords (elfLayout m k inMax room cap)) p'.core.pc =
        some svcWord ∧ p'.core.x 8 = 94 ∧
      ((p'.core.x 0 = 0 ∧ stdoutOf p'.trace = Out K.input) ∨
        (T K.input (p'.core.x 0) ∧ stdoutOf p'.trace = [])) ∧ p'.core.io = p.core.io) ∧
    (inMax.toNat < K.input.length → ∃ p', ProcReach K (elfPlatform (elfLayout m k inMax room cap))
        (fetchFrom p.core.mem elfEntry (elfWords (elfLayout m k inMax room cap))) p p' ∧
      fetchFrom p.core.mem elfEntry (elfWords (elfLayout m k inMax room cap)) p'.core.pc =
        some svcWord ∧ p'.core.x 8 = 94 ∧ p'.core.x 0 = 64 ∧ stdoutOf p'.trace = [] ∧
      p'.core.io = p.core.io) := by
  obtain ⟨bytes, L, hg, hlen, hbyte⟩ := of_bytesOk hk
  have hL : elfLayout m k inMax room cap = L := by simp only [elfLayout, hg]
  rw [hL] at hseg ⊢
  obtain ⟨prog, rt, hp, hLeq, hbound, hpre, hrt, hbytes⟩ := gen_elfWith hg
  obtain ⟨ar, stk, call, back, har, hstk, hcall, hback, hrteq⟩ := sysRuntime_ok hrt
  have har2 := addrOf_length har
  have hstk2 := addrOf_length hstk
  have hrtl : rt.length = 18 := by
    rw [hrteq]
    simp [har2, hstk2]
  -- the layout
  have hce : L.codeEnd = 176 + 4 * (18 + prog.length) := by rw [hLeq]; rfl
  have hdo : L.dataOff = roundUp L.codeEnd 65536 := by rw [hLeq]; rfl
  have hdo1 : L.codeEnd ≤ L.dataOff := by rw [hdo]; unfold roundUp; omega
  have hdo2 : L.dataOff % 65536 = 0 := by rw [hdo]; unfold roundUp; omega
  have hdm : L.dataMem = areaSize cap + room.toNat + 16 := by rw [hLeq]; rfl
  have hdf : L.dataFile = areaPrefix m := by rw [hLeq]; rfl
  have hbase : elfBase.toNat = 4194304 := rfl
  have hentry : elfEntry.toNat = 4194480 := rfl
  have harea0 : L.area = elfBase + UInt64.ofNat L.dataOff := by rw [hLeq]; rfl
  have htop0 : L.stackTop = elfBase + UInt64.ofNat (L.dataOff + L.dataMem) := by rw [hLeq]; rfl
  rw [hbase] at hbound
  have harea : L.area.toNat = 4194304 + L.dataOff := by
    rw [harea0, UInt64.toNat_add, toNat_ofNat_lt (by omega), hbase]
    omega
  have htop : L.stackTop.toNat = 4194304 + L.dataOff + L.dataMem := by
    rw [htop0, UInt64.toNat_add, toNat_ofNat_lt (by omega), hbase]
    omega
  have hasz : areaSize cap % 16 = 0 := by unfold areaSize; omega
  -- the code
  generalize hops : rt ++ prog.map Op.ins = ops
  have hopsl : ops.length = 18 + prog.length := by rw [← hops]; simp [hrtl]
  have hwords : elfWords L = ops.length := by
    unfold elfWords
    rw [hce, hopsl]
    omega
  rw [hwords]
  generalize hcode : fetchFrom p.core.mem elfEntry ops.length = code
  have hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55 := by
    rw [← hcode]
    exact fetchFrom_dom (by rw [hentry]; omega)
  have hpre' : (elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
      loadHeader 6 L.dataOff L.area L.dataFile L.dataMem)).length = 176 := by
    simp [elfHeader, loadHeader, bytes16, bytes64, wordBytes]
  have hbytes' : bytes = (elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
      loadHeader 6 L.dataOff L.area L.dataFile L.dataMem)) ++ (opBytes ops ++
      (List.replicate (L.dataOff - L.codeEnd) 0 ++ areaPrefixBytes m)) := by
    rw [hbytes, ← hops, opBytes_append, imageBytes_eq_opBytes]
    simp only [List.append_assoc]
  have hopb := length_opBytes ops
  -- the text segment
  have hblen : bytes.length = 176 + 4 * ops.length + (L.dataOff - L.codeEnd) + areaPrefix m := by
    rw [hbytes']
    simp only [List.length_append, List.length_replicate, elfHeader_length, loadHeader_length,
      hopb, areaPrefixBytes_length]
    omega
  have htext : ∀ j < L.codeEnd, p.core.mem (UInt64.ofNat (4194304 + j)) = byteAt nb j := by
    intro j hj
    have := hl ⟨1, 5, 0, elfBase.toNat, L.codeEnd, L.codeEnd⟩
      (by rw [hseg]; simp [elfSegmentsOf]) rfl j hj
    dsimp only at this
    rw [if_pos hj, Nat.zero_add, hbase] at this
    exact this
  have hcm : ∀ j (hj : j < (opBytes ops).length),
      p.core.mem (elfEntry + UInt64.ofNat j) = (opBytes ops)[j] := by
    intro j hj
    have e : elfEntry + UInt64.ofNat j = UInt64.ofNat (4194304 + (176 + j)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, hentry, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
      omega
    rw [e, htext _ (by omega), hbyte (176 + j) (by rw [hblen]; omega)]
    simp only [hbytes']
    rw [List.getElem_append_right (by rw [hpre']; omega)]
    simp only [hpre', Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hj]
  have hopsAt : OpsAt code elfEntry ops := by
    rw [← hcode]
    exact opsAt_fetchFrom (by omega) hcm
  -- the data segment
  have hdata : ∀ j < areaSize cap,
      p.core.mem (L.area + UInt64.ofNat j) = areaByte m.initialStore j := by
    intro j hj
    have := hl ⟨1, 6, L.dataOff, L.area.toNat, L.dataFile, L.dataMem⟩
      (by rw [hseg]; simp [elfSegmentsOf]) rfl j (by show j < L.dataMem; rw [hdm]; omega)
    dsimp only at this
    have e : L.area + UInt64.ofNat j = UInt64.ofNat (L.area.toNat + j) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
      omega
    rw [e, this]
    by_cases hj' : j < L.dataFile
    · rw [if_pos hj', hbyte _ (by rw [hblen]; rw [hdf] at hj'; omega)]
      have hbytesD : bytes = ((elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
          loadHeader 6 L.dataOff L.area L.dataFile L.dataMem)) ++ (opBytes ops ++
          List.replicate (L.dataOff - L.codeEnd) 0)) ++ areaPrefixBytes m := by
        rw [hbytes']
        simp only [List.append_assoc]
      have hfirst : ((elfHeader elfEntry ++ (loadHeader 5 0 elfBase L.codeEnd L.codeEnd ++
          loadHeader 6 L.dataOff L.area L.dataFile L.dataMem)) ++ (opBytes ops ++
          List.replicate (L.dataOff - L.codeEnd) 0)).length = L.dataOff := by
        simp only [List.length_append, List.length_replicate, hopb, elfHeader_length,
          loadHeader_length]
        omega
      rw [List.getElem_of_eq hbytesD, List.getElem_append_right (by rw [hfirst]; omega)]
      have hg' := areaPrefixBytes_getElem m j (by rw [← hdf]; exact hj')
      simp only [hfirst, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem (by rw [areaPrefixBytes_length, ← hdf]; exact hj')] at hg'
      exact Option.some.inj hg'
    · rw [if_neg hj', areaByte_tail m j (by rw [← hdf]; omega)]
  -- the runtime's words
  have hrtOps : OpsAt code elfEntry rt := by
    rw [← hops] at hopsAt
    exact OpsAt.take hopsAt
  rw [hrteq] at hrtOps
  have hA := OpsAt.take hrtOps
  have hinstr := OpsAt.codeAt (OpsAt.take hA)
  have hAl : (([Instr.movz 1 0x200 1, msrOf .fpcr 1] ++ ar ++ stk ++
      ([.addImm 31 1 0, .bl call, .movz 8 94 0] : List Instr)).map Op.ins).length = 9 := by
    simp [har2, hstk2]
  have hsv := OpsAt.drop hA
  rw [hAl] at hsv
  have csvc : code (after elfEntry 9) = some svcWord := by
    have := hsv 0 (by simp)
    simpa [Op.word, after_zero] using this
  have hC := OpsAt.drop hrtOps
  have hCl : ((([Instr.movz 1 0x200 1, msrOf .fpcr 1] ++ ar ++ stk ++
      ([.addImm 31 1 0, .bl call, .movz 8 94 0] : List Instr)).map Op.ins) ++
      [Op.svc, .ins (.b 0)]).length = 11 := by
    simp [har2, hstk2]
  rw [hCl] at hC
  have hC' : OpsAt code (after elfEntry 11) ([.ins (.movz 8 63 0), .svc, .ins (.ret 30)] ++
      [.ins (.movz 8 64 0), .svc, .ins (.ret 30), .ins (.b back)]) := hC
  have hrd : OpsAt code sysReadAddr [.ins (.movz 8 63 0), .svc, .ins (.ret 30)] :=
    OpsAt.take hC'
  have hwr' := OpsAt.drop hC'
  have hwr : OpsAt code sysWriteAddr [.ins (.movz 8 64 0), .svc, .ins (.ret 30)] := by
    have := OpsAt.take (l1 := [.ins (.movz 8 64 0), .svc, .ins (.ret 30)])
      (l2 := [.ins (.b back)]) hwr'
    simpa [after_after, sysWriteAddr] using this
  have cback : code elfExitWord = some (encode (.b back)) := by
    have := hwr' 3 (by simp)
    simpa [after_after, elfExitWord, Op.word] using this
  have cexit : code (after elfEntry 8) = some (encode (.movz 8 94 0)) := by
    have := hinstr 8 (by simp [har2, hstk2])
    simpa [har2, hstk2, List.getElem_append_right] using this
  -- the program's words
  have hprogC : CodeAt code (after elfExitWord 1) prog := by
    rw [← hops] at hopsAt
    have := OpsAt.drop hopsAt
    rw [hrtl, show after elfEntry 18 = after elfExitWord 1 by
      rw [elfExitWord, after_after]] at this
    exact OpsAt.codeAt this
  -- Normal memory and bounds
  have hnorm : ∀ a : UInt64, L.area.toNat ≤ a.toNat → a.toNat < L.area.toNat + L.dataMem →
      (elfPlatform L).normal a = true := by
    intro a h1 h2
    simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le]
    exact ⟨h1, h2⟩
  have hU : (elfPlatform L).normal (elfPlatform L).uart = false := by
    simp only [elfPlatform, decide_eq_false_iff_not, UInt64.le_iff_toNat_le, not_and]
    intro h
    simp at h
    omega
  have hbnd : ∀ i : Nat, i ≤ 18 + prog.length → (after elfEntry i).toNat < 2 ^ 55 := by
    intro i hi
    rw [after, UInt64.toNat_add, UInt64.toNat_mul, hentry, toNat_ofNat_lt (by omega)]
    simp only [show (4 : UInt64).toNat = 4 from rfl, Nat.reducePow]
    omega
  -- the first two steps: FPCR
  have c0 := hinstr 0 (by simp)
  have c1 := hinstr 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.cons_append,
    List.getElem_cons_zero, after_zero] at c0 c1
  let s1 : State := { p.core.setX 1 (UInt64.ofNat (512 : Fin 65536).val <<<
    UInt64.ofNat (16 * (1 : Fin 4).val)) with pc := p.core.pc + 4 }
  have hs1pc : s1.pc = after elfEntry 1 := by show p.core.pc + 4 = _; rw [hpc, after_one]
  have st1 := pstep_at (K := K) (P := elfPlatform L) (code := code) (p := p)
    (c := s1) (by rw [hpc]; exact c0) (.inl rfl) rfl (by rw [hs1pc]; exact hbnd 1 (by omega))
  have st2 := pstep_fpcr (K := K) (P := elfPlatform L) (code := code) (p := { p with core := s1 })
    (t := 1) (by show code s1.pc = _; rw [hs1pc]; exact c1)
  have hfp2 : s1.x 1 = fpcrValue := by
    show s1.x 1 = _
    rw [State.x_withPc]
    rw [State.x_setX_same (by decide)]
    rfl
  generalize hp2 : ({ ({ p with core := s1 } : Proc).goto (s1.pc + 4) with
    fpcr := s1.x 1 } : Proc) = p2 at st2
  have p2f : p2.fpcr = fpcrValue := by rw [← hp2]; exact hfp2
  have p2pc : p2.core.pc = after elfEntry 2 := by
    rw [← hp2]
    show s1.pc + 4 = _
    rw [hs1pc, ← after_succ]
  have p2tr : p2.trace = [] := by rw [← hp2]; exact htr
  have p2mem : p2.core.mem = p.core.mem := by
    rw [← hp2]
    show s1.mem = _
    exact State.setX_mem
  have p2io : p2.core.io = p.core.io := by
    rw [← hp2]
    show s1.io = _
    exact State.setX_io
  -- X17, SP, and the call of `main`
  have hs3 := CodeAt.split code hinstr (n := 6) (by simp [har2, hstk2])
  have hs2 := CodeAt.split code hs3.1 (n := 4) (by simp [har2])
  have hs1 := CodeAt.split code hs2.1 (n := 2) rfl
  obtain ⟨u1, ru1, pu1, x17u1, ku1, spu1, memu1, iou1⟩ :=
    run_addrOf (elfPlatform L) code har (by decide) hs1.2 p2pc
  obtain ⟨u2, ru2, pu2, x1u2, ku2, spu2, memu2, iou2⟩ :=
    run_addrOf (elfPlatform L) code hstk (by decide) hs2.2 (by rw [pu1, after_after])
  have ca := (CodeAt.cons.mp hs3.2).1
  have cb := (CodeAt.cons.mp (CodeAt.cons.mp hs3.2).2).1
  rw [after_after] at cb
  let u3 : State := { u2.setXsp 31 (u2.xsp 1 + UInt64.ofNat 0) with pc := u2.pc + 4 }
  have pu2' : u2.pc = after elfEntry 6 := by rw [pu2, after_after]
  let u4 : State := { u3.setX 30 (u3.pc + 4) with pc := u3.pc + sext 26 call.val * 4 }
  have pu3 : u3.pc = after elfEntry 7 := by show u2.pc + 4 = _; rw [pu2', ← after_succ]
  have ru4 : Reach (elfPlatform L) code p2.core u4 := ru1.trans (ru2.trans
    (reach_exec _ code (by rw [pu2']; exact ca) rfl
      (reach_exec _ code (by rw [pu3]; exact cb) rfl (.refl _))))
  have pu4 : u4.pc = after elfExitWord 1 := by
    show u3.pc + sext 26 call.val * 4 = _
    rw [pu3]
    exact bField_target hcall
  have hbase' : elfExitWord.toNat < 2 ^ 55 := hbnd 17 (by omega)
  have qm := ProcReach.of_reach' (K := K) hdom p2f ru4
    (by rw [pu4, elfExitWord, after_after]; exact hbnd 18 (by omega))
  have hsp3 : u3.sp = L.stackTop := by
    show (u2.setXsp 31 (u2.xsp 1 + UInt64.ofNat 0)).sp = _
    unfold State.setXsp
    rw [if_neg (by decide), State.xsp_eq_x (by decide), x1u2]
    exact add_ofNat_zero _
  have hsp4 : u4.sp = L.stackTop := by
    show (u3.setX 30 (u3.pc + 4)).sp = _
    rw [State.setX_sp, hsp3]
  have hx304 : u4.x 30 = after elfEntry 8 := by
    rw [State.x_withPc, State.x_setX_same (by decide), pu3, ← after_succ]
  have hx174 : u4.x 17 = L.area := by
    rw [State.x_withPc, State.x_setX_ne (by decide)]
    show u2.x 17 = _
    rw [ku2 17 (by decide), x17u1]
  have hmem4 : u4.mem = p.core.mem := by
    show (u3.setX 30 (u3.pc + 4)).mem = _
    rw [State.setX_mem]
    show u2.mem = _
    rw [memu2, memu1, p2mem]
  have hio4 : u4.io = p.core.io := by
    show (u3.setX 30 (u3.pc + 4)).io = _
    rw [State.setX_io]
    show u2.io = _
    rw [iou2, iou1, p2io]
  -- the program
  have htopv : L.stackTop.toNat = L.area.toNat + areaSize cap + room.toNat + 16 := by
    rw [htop, harea, hdm]
    omega
  have hst := hprog (elfPlatform L) K code sysReadAddr sysWriteAddr elfExitWord L.area hp hprogC
    hrd hwr hdom hbase' { p2 with core := u4 } pu4 p2f p2tr
    (by rw [hx304]; exact hbnd 8 (by omega))
    (by
      show u4.sp % 16 = 0
      rw [hsp4]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, htopv]
      show _ = 0
      simp only [show (16 : UInt64).toNat = 16 from rfl]
      omega)
    hroom' (by show u4.sp.toNat ≤ 2 ^ 63; rw [hsp4, htopv]; omega)
    (fun j hj => by
      show (elfPlatform L).normal (u4.sp - 16 - room + UInt64.ofNat j) = true
      have e : (u4.sp - 16 - room + UInt64.ofNat j).toNat = L.area.toNat + areaSize cap + j := by
        rw [hsp4, UInt64.toNat_add, toNat_ofNat_lt (by omega),
          toNat_sub_le (by rw [toNat_sub_le (by show 16 ≤ L.stackTop.toNat; omega)]; simp; omega),
          toNat_sub_le (by show 16 ≤ L.stackTop.toNat; omega)]
        simp only [show (16 : UInt64).toNat = 16 from rfl]
        omega
      exact hnorm _ (by rw [e]; omega) (by rw [e, hdm]; omega))
    hx174 (fun j hj => by show u4.mem _ = _; rw [hmem4]; exact hdata j hj)
    (fun j hj => hnorm _ (by
        rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
        omega) (by
        rw [UInt64.toNat_add, toNat_ofNat_lt (by omega), hdm]
        omega))
    (by show L.area.toNat + areaSize cap + room.toNat + 16 ≤ u4.sp.toNat; rw [hsp4, htopv])
    hU hok
  -- the exit
  have exitRun : ∀ q : Proc, ProcReach K (elfPlatform L) code p q → q.core.pc = after elfEntry 8 →
      ∃ q', ProcReach K (elfPlatform L) code p q' ∧
        code q'.core.pc = some svcWord ∧ q'.core.x 8 = 94 ∧ q'.core.x 0 = q.core.x 0 ∧
        q'.trace = q.trace ∧ q'.core.io = q.core.io := by
    intro q hq hqpc
    let v : State := { q.core.setX 8 (UInt64.ofNat (94 : Fin 65536).val <<<
      UInt64.ofNat (16 * (0 : Fin 4).val)) with pc := q.core.pc + 4 }
    have pv : v.pc = after elfEntry 9 := by
      show q.core.pc + 4 = _
      rw [hqpc, ← after_succ]
    have sv := pstep_at (K := K) (P := elfPlatform L) (code := code) (p := q) (c := v)
      (by rw [hqpc]; exact cexit) (.inl rfl) rfl (by rw [pv]; exact hbnd 9 (by omega))
    refine ⟨{ q with core := v }, hq.trans (.single sv), by show code v.pc = _; rw [pv]; exact csvc,
      ?_, ?_, rfl, State.setX_io⟩
    · show (q.core.setX 8 (UInt64.ofNat (94 : Fin 65536).val <<<
        UInt64.ofNat (16 * (0 : Fin 4).val))).x 8 = 94
      rw [State.x_setX_same (by decide), movz_value]
      rfl
    · show (q.core.setX 8 (UInt64.ofNat (94 : Fin 65536).val <<<
        UInt64.ofNat (16 * (0 : Fin 4).val))).x 0 = _
      rw [State.x_setX_ne (by decide)]
  have baseRun : ∀ q : Proc, ProcReach K (elfPlatform L) code p q → q.core.pc = elfExitWord →
      ∃ q', ProcReach K (elfPlatform L) code p q' ∧
        code q'.core.pc = some svcWord ∧ q'.core.x 8 = 94 ∧ q'.core.x 0 = q.core.x 0 ∧
        q'.trace = q.trace ∧ q'.core.io = q.core.io := by
    intro q hq hqpc
    let v : State := { q.core with pc := q.core.pc + sext 26 back.val * 4 }
    have pv : v.pc = after elfEntry 8 := by
      show q.core.pc + sext 26 back.val * 4 = _
      rw [hqpc]
      exact bField_target hback
    have sv := pstep_at (K := K) (P := elfPlatform L) (code := code) (p := q) (c := v)
      (by rw [hqpc]; exact cback) (.inl rfl) rfl (by rw [pv]; exact hbnd 8 (by omega))
    obtain ⟨q', r', c', x8', x0', tr', io'⟩ := exitRun { q with core := v }
      (hq.trans (.single sv)) pv
    exact ⟨q', r', c', x8', x0', tr', io'⟩
  have hpm : ProcReach K (elfPlatform L) code p { p2 with core := u4 } :=
    .next st1 (.next st2 (by rw [← hp2] at qm ⊢; exact qm))
  refine ⟨fun hlen' => ?_, fun hlong => ?_⟩
  · obtain ⟨q, rq, out, ioq⟩ := hst.1 hlen'
    rcases out with ⟨pcq, x0q, outq⟩ | ⟨pcq, tq, outq⟩
    · obtain ⟨q', r', c', x8', x0', tr', io'⟩ :=
        exitRun q (hpm.trans rq) (by rw [pcq]; exact hx304)
      exact ⟨q', r', c', x8', .inl ⟨by rw [x0', x0q], by rw [tr', outq]⟩,
        (io'.trans ioq).trans hio4⟩
    · obtain ⟨q', r', c', x8', x0', tr', io'⟩ := baseRun q (hpm.trans rq) pcq
      exact ⟨q', r', c', x8', .inr ⟨by rw [x0']; exact tq, by rw [tr', outq]⟩,
        (io'.trans ioq).trans hio4⟩
  · obtain ⟨q, rq, pcq, x0q, outq, ioq⟩ := hst.2 hlong
    obtain ⟨q', r', c', x8', x0', tr', io'⟩ := baseRun q (hpm.trans rq) pcq
    exact ⟨q', r', c', x8', by rw [x0', x0q], by rw [tr', outq], (io'.trans ioq).trans hio4⟩

end LeanExe.A64
