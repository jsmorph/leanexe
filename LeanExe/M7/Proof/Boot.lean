import LeanExe.M7.Boot
import LeanExe.M7.Proof.Main

/-!
Reset, the image's bytes, and the run of a program from reset.  `Reset code vtor b` is a state
that reset gives from the vector table at `vtor` (DDI 0403E.e section B1.5.5): SP holds word 0 of
the table with bits 1 and 0 clear, and the program counter word 1 with bit 0 clear, where bit 0 of
word 1, which reset copies to EPSR.T, is set, since the model executes Thumb code only.  LR holds
0xFFFFFFFF, the trace is empty, and no device read has happened.  r0 to r12, the flags, and memory
are arbitrary.  `FileAt code n len org` states that the code map holds from `org` the `len`
bytes of the number `n` that `file_nat%` reads from a file, two at each even offset, the lower at
the lower address, as the processor fetches halfwords (DDI 0403E.e section A3.3.1).

`boot_image` turns the kernel's check `bootFileOk` of an image into the words of its vector table
and its instructions, each at its address in the code map.  `boot_run` runs the image from reset:
the initialization, which `InitRuns` describes by the device accesses that it appends to the
trace, then `main_run` of `LeanExe/M7/Proof/Main.lean`.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph LeanExe.Pipeline LeanExe.Requests LeanExe.FileNat

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Reset and the code map -/

/-- The word at `a` of the code map, its lower halfword at `a`. -/
def codeWord (code : UInt32 → Option UInt16) (a : UInt32) : Option UInt32 :=
  match code a, code (a + 2) with
  | some lo, some hi => some (lo.toUInt32 ||| hi.toUInt32 <<< 16)
  | _, _ => none

/-- A state that reset gives from the vector table at `vtor`. -/
structure Reset (code : UInt32 → Option UInt16) (vtor : UInt32) (b : State) : Prop where
  sp : ∃ w, codeWord code vtor = some w ∧ b.sp = w &&& 0xFFFFFFFC
  pc : ∃ w, codeWord code (vtor + 4) = some w ∧ w % 2 = 1 ∧ b.pc = w &&& 0xFFFFFFFE
  lr : b.lr = 0xFFFFFFFF
  trace : b.trace = []
  reads : b.reads = 0

/-- The halfword of bytes `j` and `j + 1` of the number `n`, the lower byte first. -/
def halfAt (n j : Nat) : UInt16 :=
  UInt16.ofNat ((byteAt n j).toNat + 256 * (byteAt n (j + 1)).toNat)

/-- The code map holds from `org` the `len` bytes of the number `n`. -/
def FileAt (code : UInt32 → Option UInt16) (n len : Nat) (org : UInt32) : Prop :=
  ∀ j, 2 * j + 2 ≤ len → code (org + UInt32.ofNat (2 * j)) = some (halfAt n (2 * j))

/-! ## Bytes, halfwords, and words -/

theorem length_halfBytes : ∀ hs : List UInt16, (hs.flatMap halfBytes).length = 2 * hs.length
  | [] => rfl
  | h :: hs => by
      rw [List.flatMap_cons, List.length_append, length_halfBytes hs, List.length_cons]
      simp only [halfBytes, List.length_cons, List.length_nil]
      omega

theorem getElem?_halfBytes : ∀ (hs : List UInt16) (k : Nat) (hk : k < hs.length),
    (hs.flatMap halfBytes)[2 * k]? = some hs[k].toUInt8 ∧
      (hs.flatMap halfBytes)[2 * k + 1]? = some (hs[k] >>> 8).toUInt8
  | [], _, hk => absurd hk (by simp)
  | h :: hs, 0, _ => ⟨rfl, rfl⟩
  | h :: hs, k + 1, hk => by
      have ih := getElem?_halfBytes hs k (by simp at hk; omega)
      rw [List.flatMap_cons, show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
        show 2 * k + 1 + 1 + 1 = 2 * k + 1 + 1 + 1 from rfl]
      simp only [halfBytes, List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact ih

theorem half_of_bytes (h : UInt16) :
    UInt16.ofNat (h.toUInt8.toNat + 256 * (h >>> 8).toUInt8.toNat) = h := by
  apply UInt16.toNat_inj.mp
  have hl := h.toNat_lt
  have e : (h >>> 8).toNat = h.toNat / 256 := by
    rw [UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  rw [UInt16.toNat_ofNat', UInt16.toNat_toUInt8, UInt16.toNat_toUInt8, e]
  simp only [Nat.reducePow] at *
  omega

theorem byteAt_of_getElem? {l : List UInt8} {j : Nat} {b : UInt8} (h : l[j]? = some b) :
    byteAt (natOfBytes l) j = b := by
  obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.mp h
  rw [byteAt_natOfBytes l j hj, e]

/-- A code map that holds the bytes of a file holds the halfwords whose bytes the file holds. -/
theorem halfsAt_of_file {hs : List UInt16} {n len : Nat} {org : UInt32}
    (hn : natOfBytes (hs.flatMap halfBytes) = n) (hl : (hs.flatMap halfBytes).length = len)
    (hf : FileAt code n len org) : HalfsAt code org hs := by
  intro k hk
  rw [length_halfBytes] at hl
  obtain ⟨e0, e1⟩ := getElem?_halfBytes hs k hk
  rw [hf k (by omega), halfAt, ← hn, byteAt_of_getElem? e0, byteAt_of_getElem? e1,
    half_of_bytes]

theorem word_of_halfs (w : UInt32) :
    w.toUInt16.toUInt32 ||| (w >>> 16).toUInt16.toUInt32 <<< 16 = w := by
  apply UInt32.toNat_inj.mp
  have hw := toNat_lt32 w
  have e1 : (w >>> 16).toUInt16.toUInt32.toNat = w.toNat / 65536 := by
    have e : (w >>> 16).toNat = w.toNat / 65536 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      rfl
    rw [UInt16.toNat_toUInt32, UInt32.toNat_toUInt16, e]
    simp only [Nat.reducePow]
    omega
  rw [UInt32.toNat_or, toNat_shiftLeft32 _ 16 16 rfl (by decide)
      (by rw [e1]; simp only [Nat.reducePow]; omega), e1,
    UInt16.toNat_toUInt32, UInt32.toNat_toUInt16, or_add_shift (by simp only [Nat.reducePow]; omega)]
  simp only [Nat.reducePow]
  omega

theorem codeWord_of_halfs {a w : UInt32} {rest : List UInt16}
    (h : HalfsAt code a (wordHalfs w ++ rest)) : codeWord code a = some w := by
  have h0 := h 0 (by simp [wordHalfs])
  have h1 := h 1 (by simp [wordHalfs])
  have e0 : code a = some w.toUInt16 := by
    rw [show a = a + UInt32.ofNat (2 * 0) by rw [Nat.mul_zero, show UInt32.ofNat 0 = 0 from rfl,
      UInt32.add_zero]]
    exact h0
  have e1 : code (a + 2) = some (w >>> 16).toUInt16 := h1
  unfold codeWord
  rw [e0, e1]
  exact congrArg some (word_of_halfs w)

/-! ## The image -/

theorem length_table (B : Boot) (h : 2 ≤ B.entries) : B.table.length = B.entries := by
  simp only [Boot.table, List.length_cons, List.length_replicate]
  omega

theorem length_wordHalfs : ∀ ws : List UInt32, (ws.flatMap wordHalfs).length = 2 * ws.length
  | [] => rfl
  | w :: ws => by
      rw [List.flatMap_cons, List.length_append, length_wordHalfs ws, List.length_cons]
      simp only [wordHalfs, List.length_cons, List.length_nil]
      omega

/-- The kernel's check of an image whose table has at least two words and whose initialization
consists of 32-bit forms gives the generator's program at the base, the initialization at the
reset entry, and the table's first two words, the initial SP and the reset entry with bit 0
set. -/
theorem boot_image {B : Boot} {m : Module} {k : Nat} {s0 : List UInt64} {limit dev : UInt32}
    {n len : Nat} (hent : 2 ≤ B.entries) (hw : B.init.all Instr.wide = true)
    (hk : bootFileOk B (bootProgram B m k s0 limit dev) n len = true)
    (hf : FileAt code n len B.org) :
    ∃ prog, genProgram m k s0 B.base limit dev udivmod64 = .ok prog ∧ CodeAt code B.base prog ∧
      CodeAt code B.reset B.init ∧ codeWord code B.org = some B.sp ∧
      codeWord code (B.org + 4) = some (B.reset ||| 1) := by
  unfold bootFileOk at hk
  split at hk
  · rename_i is hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨hn, hl⟩ := hk
    unfold bootProgram at hb
    simp only [except_bind_ok, except_pure_ok] at hb
    obtain ⟨prog, hprog, rfl⟩ := hb
    have hh := halfsAt_of_file (code := code) hn hl hf
    unfold bootHalfs at hh
    obtain ⟨ht, hc⟩ := HalfsAt.append.mp hh
    have hloop : B.org + UInt32.ofNat (2 * (B.table.flatMap wordHalfs).length) = B.loop := by
      rw [length_wordHalfs, length_table B hent, Boot.loop, after_eq,
        show 2 * (2 * B.entries) = 4 * B.entries by omega]
    rw [hloop] at hc
    have hc' : CodeAt code B.loop (Instr.bTo (-4) :: (B.init ++ prog)) := hc
    obtain ⟨-, hc2⟩ := CodeAt.cons.mp hc'
    rw [show (Instr.bTo (-4)).size = 4 from rfl,
      show B.loop + UInt32.ofNat 4 = B.reset by rw [Boot.loop, Boot.reset]; addr_after] at hc2
    obtain ⟨hci, hcp⟩ := CodeAt.append.mp hc2
    rw [codeSize_of_wide hw, show B.reset + UInt32.ofNat (4 * B.init.length) = B.base by
      rw [Boot.reset, Boot.base]; addr_after] at hcp
    refine ⟨prog, hprog, hcp, hci, ?_, ?_⟩
    · simp only [Boot.table, List.flatMap_cons] at ht
      exact codeWord_of_halfs (by simpa only [List.append_assoc] using ht)
    · simp only [Boot.table, List.flatMap_cons] at ht
      have ht2 := (HalfsAt.append.mp ht).2
      rw [show (wordHalfs B.sp).length = 2 from rfl] at ht2
      exact codeWord_of_halfs ht2
  · cases hk

/-! ## The run from reset -/

/-- The initialization `init`, placed at the program counter, runs to its end with the device
accesses `t0` appended to the trace and SP and the read count unchanged. -/
def InitRuns (P : Platform) (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (init : List Instr) (t0 : List Access) : Prop :=
  ∀ s : State, CodeAt code s.pc init → ∃ t, Reach P σ code s t ∧
    t.pc = s.pc + UInt32.ofNat (4 * init.length) ∧ t.sp = s.sp ∧ t.trace = s.trace ++ t0 ∧
    t.reads = s.reads

/-- The image of step `k` of `m`, whose bytes the kernel's check `hk` finds in the code map, run
from reset: the initialization appends `t0` to the trace, and `main` reaches the loop's head after
`N` windows with their accesses appended, the windows reading `σ` from its start.  The table lies
at a multiple of 4, its initial SP is a multiple of 4 above the outgoing area, and every state
whose SP lies at the outgoing area has the stack that `StackOk` states. -/
theorem boot_run {G : Type} [Scalar G] {m : Module} {k : Nat} {s0 : List UInt64}
    {limit dev : UInt32} {B : Boot} {n len : Nat} {words : G → List UInt64}
    (hwords : ∀ g, Scalar.values g = (words g).map Value.i64)
    (hlen : ∀ g, (words g).length = s0.length) {tick : G → UInt64 → G × UInt64}
    {Pre : G × UInt64 → Heap → Store Unit → Prop}
    {Post : G × UInt64 → Heap → Store Unit → Heap → Store Unit → Prop}
    (himpl : ImplementsA false m k (fun x : G × UInt64 => tick x.1 x.2) Pre Post)
    (hPre : ∀ x heap st, Pre x heap st) (hm : m.imports = []) (hcov : reachCovered m k = true)
    (hdev : DevWindow P dev) {st : Store Unit} {heap : Heap} (hat : heap.At st)
    (hcap : st.memoryCap m 0 ≤ 65535)
    (hent : 2 ≤ B.entries) (hw : B.init.all Instr.wide = true)
    (hk : bootFileOk B (bootProgram B m k s0 limit dev) n len = true)
    (hf : FileAt code n len B.org) (horg : B.org.toNat % 4 = 0) {t0 : List Access}
    (hinit : InitRuns P σ code B.init t0) (hsp : B.sp.toNat % 4 = 0)
    (hfit : 8 * (s0.length + 1) ≤ B.sp.toNat)
    (hstk : ∀ s : State, s.sp = B.sp - UInt32.ofNat (8 * (s0.length + 1)) →
      StackOk P limit (s0.length + 1) (stackBound m k) s)
    (g0 : G) (hs0 : words g0 = s0) (b : State) (hb : Reset code B.org b) (N : Nat) :
    ∃ t, Reach P σ code b t ∧ t.pc = after B.base (mainStart s0) ∧
      t.trace = t0 ++ windows (reqTrace (devBus dev) tick g0 σ) N := by
  obtain ⟨prog, hprog, hcp, hci, hw0, hw1⟩ := boot_image hent hw hk hf
  obtain ⟨w0, e0, hbsp⟩ := hb.sp
  obtain ⟨w1, e1, -, hbpc⟩ := hb.pc
  rw [hw0, Option.some.injEq] at e0
  rw [hw1, Option.some.injEq] at e1
  subst e0 e1
  have hev : (B.reset).toNat % 2 = 0 := by
    rw [Boot.reset]
    exact even_after (by omega) _
  rw [or1_and _ hev] at hbpc
  rw [and_align hsp] at hbsp
  rw [← hbpc] at hci
  obtain ⟨t1, r1, p1, sp1, tr1, rd1⟩ := hinit b hci
  have hp1 : t1.pc = B.base := by
    rw [p1, hbpc, Boot.reset, Boot.base]
    addr_after
  have hsp1 : t1.sp = B.sp := sp1.trans hbsp
  obtain ⟨t, rt, pt, trt⟩ := main_run (P := P) (σ := σ) (code := code) hwords hlen himpl hPre hm
    hprog hcp (by rw [Boot.base]; exact even_after (by omega) _) hcov hdev hat hcap g0 hs0 t1 hp1
    (by rw [hsp1]; exact hsp) (by rw [hsp1]; exact hfit) (hstk _ (by rw [← hsp1])) N
  refine ⟨t, r1.trans rt, pt, ?_⟩
  rw [trt, tr1, rd1, hb.trace, hb.reads, List.nil_append]
  rfl

end LeanExe.M7
