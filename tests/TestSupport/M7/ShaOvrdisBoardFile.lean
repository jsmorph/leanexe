import TestSupport.M7.ShaLoop

/-!
The kernel's check of the image of the SHA-256 step `shaUsart3Tick` for the NUCLEO-F767ZI with the
initialization `initOvrdis`, which `m7-windows sha-ovrdis-board` writes, `sha-ovrdis.bin`, and the
theorems over that file.  `tests/baremetal/m7-board.sh check sha-ovrdis` elaborates this file in
the directory of the image, so that `file_nat%` and `file_size%` read it, and no build target
includes it.  The image differs from `sha.bin` in its initialization, which writes `OVRDIS` to
`USART_CR3` before the write of `USART_CR1` that sets UE, and in the addresses that follow it.

`shaOvrdis_board` states what `sha_board` of `tests/TestSupport/M7/ShaBoardFile.lean` states, with
the accesses of `initOvrdis` in place of those of `init`, and `shaOvrdis_board_runs` states that
the run never stops.  The theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset, or an NRST reset with the debug registers at
their power-on values, with BOOT0 low and BOOT_ADD0 0x0080, software watchdogs (OPTCR 0xFFFFAAFD),
and no interrupt, NMI, debug halt, debugger access, or DMA during the run.
-/

namespace TestSupport.M7.ShaOvrdisBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Sha TestSupport.M7.ShaImages
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding

def shaOvrdisBytes : Nat := file_nat% "sha-ovrdis.bin"
def shaOvrdisSize : Nat := file_size% "sha-ovrdis.bin"

/-- The file holds the bytes of the SHA-256 step's image with the initialization `initOvrdis`. -/
theorem shaOvrdis_file :
    bootFileOk ovrdisBoot ovrdisProgram shaOvrdisBytes shaOvrdisSize = true := by
  decide +kernel

/-- The SHA-256 step on the NUCLEO-F767ZI from reset, over the image file with the initialization
`initOvrdis`: for every sequence `σ` of the values that device reads return, every number `N` of
windows below 2^62, every code map that holds the file's bytes in flash from `0x08000000` and from
`0x00200000`, and every state that reset gives from the vector table at `0x00200000`, the model
reaches the accesses of `initOvrdis` followed by the accesses `w` of the first `N` windows of
`shaUsart3Tick` from `shaInit`, whose reads take the values of `σ` after the initialization's 11.
The bytes that `w` writes to `USART_TDR` begin the 32-byte digests `ds` of the blocks of 8 words
that the bytes that `w` reads from `USART_RDR` encode, one for each block, where digest `i` is, as
a 256-bit value, the SHA-256 digest of FIPS 180-4 §6.2 of the bytes of blocks 0 to `i`. -/
theorem shaOvrdis_board (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62)
    (code : UInt32 → Option UInt16) (hf : Flash code shaOvrdisBytes shaOvrdisSize) (b : State)
    (hb : Reset code flashItcm b) :
    let w := windows (reqTrace (devBus devBase) shaUsart3Tick shaInit
      (fun k => σ (k + initReads initOvrdis))) N
    let recs := (decode 8 (dataIn (devBus devBase) shaUsart3 w)).recs
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace initOvrdis σ ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256
            (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
        dataOut (devBus devBase) shaUsart3 w <+: ds.flatMap fun d => d.toList.map UInt8.toUInt64 :=
  shaOvrdis_prefix shaOvrdis_file hf b hb N hN

/-- The run of `shaOvrdis_board` succeeds for every number of steps. -/
theorem shaOvrdis_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code shaOvrdisBytes shaOvrdisSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  shaOvrdis_loop_runs shaOvrdis_file hf b hb

end TestSupport.M7.ShaOvrdisBoardFile

#print axioms TestSupport.M7.ShaOvrdisBoardFile.shaOvrdis_board
#print axioms TestSupport.M7.ShaOvrdisBoardFile.shaOvrdis_board_runs
#print axioms TestSupport.M7.ShaOvrdisBoardFile.shaOvrdis_file
#print axioms TestSupport.M7.Sha.shaOvrdis_loop
#print axioms TestSupport.M7.Sha.shaOvrdis_loop_runs
#print axioms TestSupport.M7.Sha.shaOvrdis_prefix
#print axioms TestSupport.M7.Sha.shaOvrdis_confined
#print axioms LeanExe.M7.Nucleo.areaBoardWith_run
#print axioms LeanExe.M7.Nucleo.areaBoardWith_runs
#print axioms LeanExe.M7.Nucleo.initOvrdis_ok
#print axioms LeanExe.M7.Nucleo.initOvrdis_confined
