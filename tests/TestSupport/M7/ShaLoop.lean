import TestSupport.M7.ShaStep
import TestSupport.M7.ShaImages
import TestSupport.M7.ShaSpec
import TestSupport.M7.QemuLoop
import LeanExe.M7.Proof.Board
import LeanExe.Proof.AreaHeap
import LeanExe.Requests.Reads

/-!
The loop theorems of the SHA-256 steps through the Cortex-M7 back end, from reset: `sha_loop` of
`shaUsart3Tick` on the NUCLEO-F767ZI in the layout `boardBoot`, and `shaQemu_loop` of
`shaCmsdkTick` on QEMU's `mps2-an500` in the layout `qemuBoot`, both of
`tests/TestSupport/M7/ShaImages.lean`.  Each instantiates the run of a program with an area,
`Nucleo.areaBoard_run` or `setupBoot_run`, with the step's call fact `sha_stepCall` or
`shaCmsdk_stepCall` of `tests/TestSupport/M7/ShaStep.lean`, whose invariant `ShaInv` holds of the
store with the area's cap, `initStore`, by `sha_initStore` or `shaCmsdk_initStore`.  For every
sequence `σ` of the values that device reads return, every number `N` of windows, every code map
that holds the bytes of a file whose kernel check passes, and every state that reset gives, the
model reaches the loop's head with the initialization's accesses followed by those of the first
`N` windows.

`sha_digests` states what the windows of either step compute, for any UART whose step `shaAbs`
relates to the framing: the bytes that they write to the transmit register begin the 32-byte
digests of the blocks that the bytes that they read from the receive register encode, digest `i`
being the SHA-256 digest of FIPS 180-4 of the bytes of blocks 0 to `i`, for fewer than 2^62
windows.  It composes `sha_windows_prefix` of `tests/TestSupport/M7/Sha.lean` with `shaSpec_fips`
of `tests/TestSupport/M7/ShaSpec.lean`, and `frame_reads` and `decode_lengths` of
`LeanExe/Requests/Reads.lean` bound the blocks below 2^55: the windows read at most one byte for
every two windows, and each block takes 64 of the bytes read.  `sha_digests_bytes` states the
digests over the bytes read, by `decode_take`: one digest for each 64 bytes, digest `i` that of the
first `64 (i + 1)` bytes.  `sha_prefix` and `sha_bytes` join them to `sha_loop`, and
`shaQemu_prefix` joins `sha_digests` to `shaQemu_loop`.  `sha_loop_runs` states that the board's
run never stops, `sha_requests` that every request names `USART_ISR`, `USART_RDR`, or `USART_TDR`,
and `sha_confined` that the run's accesses lie in RCC, GPIOD, and USART3.
-/

namespace TestSupport.M7.Sha

open Wasm LeanExe.M7 LeanExe.Requests LeanExe.Pipeline TestSupport.M7 TestSupport.M7.ShaImages
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding Library.Hashing.Sha256

/-- The step's module fits the area that the setup writes. -/
theorem sha_setupOk : setupOk shaStepCompiled.module areaPages = true := by
  decide +kernel

/-- The heap of `initialHeap` lies at the store with the area's cap in which the step's module
starts, and `ShaInv` holds there. -/
theorem sha_initStore :
    (Verified.initialHeap shaStepCompiled.tables).At
        (LeanExe.initStore shaStepCompiled.module areaPages) ∧
      ShaInv (Verified.initialHeap shaStepCompiled.tables)
        (LeanExe.initStore shaStepCompiled.module areaPages) := by
  obtain ⟨hAt, -, -⟩ : Verified.Ready shaStepCompiled.module shaStepCompiled.tables
      (Verified.initialHeap shaStepCompiled.tables) shaStepCompiled.module.initialStore :=
    Verified.Ready.initial rfl shaStepCompiled.initial
  exact ⟨LeanExe.heapAt_initStore hAt _, shaInv_initial.1,
    LeanExe.borrowed_initStore shaInv_initial.2 _⟩

/-- The SHA-256 step `shaUsart3Tick` from `shaInit` on the board, from reset: for every sequence
`σ` of the values that device reads return and every number `N` of windows, the model reaches the
loop's head of `main` with the initialization's accesses followed by those of the first `N`
windows, whose reads take the values of `σ` after the initialization's 11, from every state that
reset gives from the vector table at `0x00200000` of a code map that holds in flash the bytes of
the number `n` of length `len`, whose kernel check `hk` passes. -/
theorem sha_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) :
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.pc = boardHead ∧
      s.trace = initTrace Nucleo.init σ ++
        windows (reqTrace (devBus Nucleo.devBase) shaUsart3Tick shaInit
          (fun j => σ (j + initReads Nucleo.init))) N :=
  Nucleo.areaBoard_run (words := shaWords) (fun _ => rfl) sha_stepCall rfl sha_covered sha_setupOk
    sha_initStore.1 sha_initStore.2 hk (by rw [sha_stack]; decide) shaInit rfl hf b hb N

/-- The SHA-256 step's run on the board succeeds for every number of steps. -/
theorem sha_loop_runs {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) :
    ∀ j, ∃ t, run Nucleo.platform σ code j b = some t :=
  Nucleo.areaBoard_runs (words := shaWords) (fun _ => rfl) sha_stepCall rfl sha_covered
    sha_setupOk sha_initStore.1 sha_initStore.2 hk (by rw [sha_stack]; decide) shaInit rfl hf b hb

/-- Every request of `shaUsart3Tick` names `USART_ISR`, index `0x1207`, `USART_RDR`, index
`0x1209`, or `USART_TDR`, index `0x120A`. -/
theorem sha_requests (s : ShaFrame) (v : UInt64) :
    reqReg (shaUsart3Tick s v).2 = 0x1207 ∨ reqReg (shaUsart3Tick s v).2 = 0x1209 ∨
      reqReg (shaUsart3Tick s v).2 = 0x120A := by
  have e1 : reqReg (LeanExe.Native.readReq 0x1207) = 0x1207 := reqReg_readReq (by decide)
  have e2 : reqReg (LeanExe.Native.readReq 0x1209) = 0x1209 := reqReg_readReq (by decide)
  have e3 : ∀ x, reqReg (LeanExe.Native.writeReq 0x120A x) = 0x120A :=
    fun x => reqReg_writeReq x (by decide)
  simp only [shaUsart3Tick, shaStepWith, shaPhases]
  repeat' split
  all_goals simp [e1, e2, e3]

/-- The accesses of the trace of `sha_loop`: the initialization's lie in RCC, GPIOD, or USART3,
and the windows' are accesses of `USART_ISR`, `USART_RDR`, and `USART_TDR`. -/
theorem sha_confined (σ : Nat → UInt32) (N : Nat) :
    (∀ e ∈ initTrace Nucleo.init σ, Nucleo.InitBlock e.addr) ∧
      ∀ e ∈ windows (reqTrace (devBus Nucleo.devBase) shaUsart3Tick shaInit
          (fun j => σ (j + initReads Nucleo.init))) N,
        e.addr = Nucleo.usartIsr ∨ e.addr = Nucleo.usartRdr ∨ e.addr = Nucleo.usartTdr :=
  ⟨Nucleo.init_confined σ, Nucleo.windows_confined sha_requests shaInit _ N⟩

/-- The windows of a step that `shaAbs` relates to the framing over the UART `u` read at most one
byte from the receive register for every two windows. -/
theorem sha_reads {α : Type} (B : Bus α) {u : Uart} {tick : ShaFrame → UInt64 → ShaFrame × UInt64}
    (habs : ∀ f v, frameTick u 8 4 (shaSpec roundConstants) (shaAbs f) v =
      (shaAbs (tick f v).1, (tick f v).2))
    (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
    (hrs : u.rx ≠ u.status) (σ : Nat → UInt32) (n : Nat) :
    2 * (dataIn B u (windows (reqTrace B tick shaInit σ) n)).length ≤ n := by
  rw [← reqTrace_map shaAbs habs]
  exact frame_reads (kin := 8) (kout := 4) (mach := shaSpec roundConstants) (m0 := sha0) B u hrx
    htx hs hrs σ n

/-- A digest record of four words is its 32 bytes. -/
theorem digestVec_bytes {ws : List UInt64} (h4 : ws.length = 4) :
    (digestVec ws).toList.map UInt8.toUInt64 = recordBytes ws := by
  have hw : ∀ x ∈ ws, (wordBytes x 8).length = 8 := fun x _ => length_wordBytes x 8
  have hl : (recordBytes ws).length = 32 := by
    simp only [recordBytes, length_flatMap8 _ ws hw, h4]
  apply List.ext_getElem
  · simp [digestVec, hl]
  · intro j h1 h2
    simp only [digestVec, List.getElem_map, Vector.getElem_toList, Vector.getElem_ofFn]
    obtain ⟨q, r, rfl, hr⟩ : ∃ q r, j = 8 * q + r ∧ r < 8 := ⟨j / 8, j % 8, by omega, by omega⟩
    have hq : q < ws.length := by omega
    have hb := wordBytes_lt ws[q] r hr
    rw [← getElem!_pos (recordBytes ws) (8 * q + r) h2, recordBytes,
      getElem!_flatMap8 (fun w => wordBytes w 8) ws hw hq hr]
    apply UInt64.toNat_inj.mp
    rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
    exact Nat.mod_eq_of_lt hb

/-- The 32-byte digests of the blocks `recs`: digest `i` is the record machine's answer to block
`i`. -/
theorem outBytes_digests (recs : List (List UInt64)) (hn : recs.length < 2 ^ 58) :
    outBytes (shaSpec roundConstants) sha0 recs =
      ((machRun (shaSpec roundConstants) sha0 recs).2.map digestVec).flatMap
        fun d => d.toList.map UInt8.toUInt64 := by
  rw [outBytes, List.flatMap_map]
  apply List.flatMap_congr
  intro ws hws
  rw [machRun_sha recs hn] at hws
  simp only [List.mem_map] at hws
  obtain ⟨i, -, rfl⟩ := hws
  exact (digestVec_bytes rfl).symm

/-- For a step `tick` that `shaAbs` relates to the framing over the UART `u` and fewer than 2^62
windows from `shaInit`, the bytes that the windows write to the transmit register begin the 32-byte
digests `ds` of the blocks `recs` of 8 words that the bytes that they read from the receive
register encode, one for each block, where digest `i` is, as a 256-bit value, the SHA-256 digest of
FIPS 180-4 of the bytes of blocks 0 to `i`. -/
theorem sha_digests {α : Type} (B : Bus α) {u : Uart}
    {tick : ShaFrame → UInt64 → ShaFrame × UInt64}
    (habs : ∀ f v, frameTick u 8 4 (shaSpec roundConstants) (shaAbs f) v =
      (shaAbs (tick f v).1, (tick f v).2))
    (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
    (hrs : u.rx ≠ u.status) (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62) :
    let w := windows (reqTrace B tick shaInit σ) N
    let recs := (decode 8 (dataIn B u w)).recs
    ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
      (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
        SHS.SHA256.sha256
          (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
      dataOut B u w <+: ds.flatMap fun d => d.toList.map UInt8.toUInt64 := by
  intro w recs
  obtain ⟨h8, -, -, hlen⟩ := decode_lengths (kin := 8) (by decide) (dataIn B u w)
  have h8' : ∀ r ∈ recs, r.length = 8 := h8
  have hlen' : recs.length * (8 * 8) + (decode 8 (dataIn B u w)).words.length * 8 +
      (decode 8 (dataIn B u w)).nbyte = (dataIn B u w).length := hlen
  have hrd : 2 * (dataIn B u w).length ≤ N := sha_reads B habs hrx htx hs hrs σ N
  have hr55 : recs.length < 2 ^ 55 := by omega
  have hout := machRun_sha recs (by omega)
  refine ⟨(machRun (shaSpec roundConstants) sha0 recs).2.map digestVec, ?_, ?_, ?_⟩
  · simp only [List.length_map, hout, List.length_range]
  · intro i hi
    have hi' : i < recs.length := by
      simp only [List.length_map, hout, List.length_range] at hi; exact hi
    obtain ⟨h, e⟩ := shaSpec_fips recs h8' hr55 i hi'
    refine ⟨h, ?_⟩
    rw [List.getElem_map, ← getElem!_pos]
    exact e
  · rw [← outBytes_digests recs (by omega)]
    exact sha_windows_prefix B habs hrx htx hs hrs σ N

/-- `sha_digests` over the bytes read: the digests number one for each 64 bytes read, and digest
`i` is the SHA-256 digest of the first `64 (i + 1)` bytes read. -/
theorem sha_digests_bytes {α : Type} (B : Bus α) {u : Uart}
    {tick : ShaFrame → UInt64 → ShaFrame × UInt64}
    (habs : ∀ f v, frameTick u 8 4 (shaSpec roundConstants) (shaAbs f) v =
      (shaAbs (tick f v).1, (tick f v).2))
    (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
    (hrs : u.rx ≠ u.status) (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62) :
    let w := windows (reqTrace B tick shaInit σ) N
    let bs := dataIn B u w
    ∃ ds : List (Vector UInt8 32), ds.length = bs.length / 64 ∧
      (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
        SHS.SHA256.sha256 (bytesToBitMessage (byteArrayOf (bs.take (64 * (i + 1))))) h) ∧
      dataOut B u w <+: ds.flatMap fun d => d.toList.map UInt8.toUInt64 := by
  intro w bs
  obtain ⟨ds, hl, hd, hp⟩ := sha_digests B habs hrx htx hs hrs σ N hN
  have hb : ∀ b ∈ bs, b.toNat < 256 := dataIn_lt B u w
  refine ⟨ds, hl.trans (decode_length (by decide) bs), fun i hi => ?_, hp⟩
  obtain ⟨h, e⟩ := hd i hi
  have et : ((decode 8 bs).recs.take (i + 1)).flatMap recordBytes = bs.take (64 * (i + 1)) :=
    decode_take (by decide) hb (by rw [← hl]; omega)
  exact ⟨_, e.trans (sha256_congr (congrArg (fun l => bytesToBitMessage (byteArrayOf l)) et) h)⟩

/-- The SHA-256 step on the board from reset: the run reaches the initialization's accesses
followed by the accesses `w` of the first `N` windows, for fewer than 2^62 windows, and the bytes
that `w` writes to `USART_TDR` begin the 32-byte digests `ds` of the blocks `recs` of 8 words that
the bytes that `w` reads from `USART_RDR` encode, one for each block, where digest `i` is, as a
256-bit value, the SHA-256 digest of FIPS 180-4 of the bytes of blocks 0 to `i`. -/
theorem sha_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) (hN : N < 2 ^ 62) :
    let w := windows (reqTrace (devBus Nucleo.devBase) shaUsart3Tick shaInit
      (fun j => σ (j + initReads Nucleo.init))) N
    let recs := (decode 8 (dataIn (devBus Nucleo.devBase) shaUsart3 w)).recs
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.init σ ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256
            (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
        dataOut (devBus Nucleo.devBase) shaUsart3 w <+:
          ds.flatMap fun d => d.toList.map UInt8.toUInt64 := by
  intro w recs
  obtain ⟨s, r, -, tr⟩ := sha_loop hk hf b hb N
  exact ⟨s, r, tr, sha_digests (devBus Nucleo.devBase) shaUsart3Tick_abs (by decide) (by decide)
    (by decide) (by decide) _ N hN⟩

/-- `sha_prefix` over the bytes read: the bytes that `w` writes to `USART_TDR` begin the 32-byte
digests `ds`, one for each 64 bytes that `w` reads from `USART_RDR`, where digest `i` is, as a
256-bit value, the SHA-256 digest of FIPS 180-4 of the first `64 (i + 1)` bytes read. -/
theorem sha_bytes {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk boardBoot boardProgram n len = true) (hf : Nucleo.Flash code n len)
    (b : State) (hb : Reset code Nucleo.flashItcm b) (N : Nat) (hN : N < 2 ^ 62) :
    let w := windows (reqTrace (devBus Nucleo.devBase) shaUsart3Tick shaInit
      (fun j => σ (j + initReads Nucleo.init))) N
    let bs := dataIn (devBus Nucleo.devBase) shaUsart3 w
    ∃ s, Reach Nucleo.platform σ code b s ∧ s.trace = initTrace Nucleo.init σ ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = bs.length / 64 ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256 (bytesToBitMessage (byteArrayOf (bs.take (64 * (i + 1))))) h) ∧
        dataOut (devBus Nucleo.devBase) shaUsart3 w <+:
          ds.flatMap fun d => d.toList.map UInt8.toUInt64 := by
  intro w bs
  obtain ⟨s, r, -, tr⟩ := sha_loop hk hf b hb N
  exact ⟨s, r, tr, sha_digests_bytes (devBus Nucleo.devBase) shaUsart3Tick_abs (by decide)
    (by decide) (by decide) (by decide) _ N hN⟩

/-- The CMSDK step's module fits the area that the setup writes. -/
theorem shaCmsdk_setupOk : setupOk shaCmsdkCompiled.module areaPages = true := by
  decide +kernel

/-- `sha_initStore` for the CMSDK step's module. -/
theorem shaCmsdk_initStore :
    (Verified.initialHeap shaCmsdkCompiled.tables).At
        (LeanExe.initStore shaCmsdkCompiled.module areaPages) ∧
      ShaInv (Verified.initialHeap shaCmsdkCompiled.tables)
        (LeanExe.initStore shaCmsdkCompiled.module areaPages) := by
  obtain ⟨hAt, -, -⟩ : Verified.Ready shaCmsdkCompiled.module shaCmsdkCompiled.tables
      (Verified.initialHeap shaCmsdkCompiled.tables) shaCmsdkCompiled.module.initialStore :=
    Verified.Ready.initial rfl shaCmsdkCompiled.initial
  exact ⟨LeanExe.heapAt_initStore hAt _, shaCmsdkInv_initial.1,
    LeanExe.borrowed_initStore shaCmsdkInv_initial.2 _⟩

/-- The SHA-256 step `shaCmsdkTick` from `shaInit` on `mps2-an500`, from QEMU's reset: for every
sequence `σ` of the values that device reads return and every number `N` of windows, the model
reaches the loop's head of `main` with UART0's initialization and the accesses of the first `N`
windows in its trace, from every state that reset gives from the vector table at 0 of a code map
that holds the bytes of the number `n` of length `len`, whose kernel check `hk` passes. -/
theorem shaQemu_loop {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk qemuBoot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) shaCmsdkTick shaInit σ) N :=
  setupBoot_run (B := Qemu.boot) (words := shaWords) (fun _ => rfl) shaCmsdk_stepCall rfl
    shaCmsdk_covered shaCmsdk_setupOk Qemu.area_ram (Nat.le_of_eq Nucleo.areaEnd_toNat.symm)
    Qemu.devWindow shaCmsdk_initStore.1 shaCmsdk_initStore.2 (by decide) (by decide) hk hf
    (by decide) (Qemu.initRuns σ code) (by decide) (by decide)
    (fun s hs => by rw [shaCmsdk_stack]; exact Qemu.stackOk_of (by decide) (by decide) s hs)
    shaInit rfl b hb N

/-- The SHA-256 step on `mps2-an500` from QEMU's reset: the run reaches UART0's initialization
followed by the accesses `w` of the first `N` windows, for fewer than 2^62 windows, and the bytes
that `w` writes to UART0's data register begin the 32-byte digests `ds` of the blocks `recs` of 8
words that the bytes that `w` reads from it encode, one for each block, where digest `i` is, as a
256-bit value, the SHA-256 digest of FIPS 180-4 of the bytes of blocks 0 to `i`. -/
theorem shaQemu_prefix {σ : Nat → UInt32} {code : UInt32 → Option UInt16} {n len : Nat}
    (hk : bootFileOk qemuBoot qemuProgram n len = true) (hf : FileAt code n len 0) (b : State)
    (hb : Reset code 0 b) (N : Nat) (hN : N < 2 ^ 62) :
    let w := windows (reqTrace (devBus Qemu.devBase) shaCmsdkTick shaInit σ) N
    let recs := (decode 8 (dataIn (devBus Qemu.devBase) shaCmsdk w)).recs
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256
            (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
        dataOut (devBus Qemu.devBase) shaCmsdk w <+:
          ds.flatMap fun d => d.toList.map UInt8.toUInt64 := by
  intro w recs
  obtain ⟨s, r, -, tr⟩ := shaQemu_loop hk hf b hb N
  exact ⟨s, r, tr, sha_digests (devBus Qemu.devBase) shaCmsdkTick_abs (by decide) (by decide)
    (by decide) (by decide) σ N hN⟩

end TestSupport.M7.Sha
