import TestSupport.M7.ShaLoop

/-!
The kernel's check of the image of the SHA-256 step `shaUsart3Tick` for the NUCLEO-F767ZI that
`m7-windows sha-board` writes, `sha.bin`, and the theorems over that file.
`tests/baremetal/m7-board.sh check sha` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on the layout `areaBoot` of the step's module, whose setup holds the nonzero words of
the area's prefix as immediates, among them the round constants, and on the module, the index 13,
and the initial state `shaInit`, and checks that the file's bytes are those of the vector table and
the instructions.

`sha_board` states, for every code map that holds the file's bytes in flash at both of its
addresses, every state that reset gives, every sequence of the values that device reads return,
and every number of windows below 2^62, that the run reaches the initialization's accesses
followed by the accesses of those windows, and that the bytes that the run writes to `USART_TDR`
begin the 32-byte digests of the blocks of 64 bytes that it reads from `USART_RDR`, digest `i` being
the SHA-256 digest of FIPS 180-4 of blocks 0 to `i`.  `sha_board_bytes` states the digests over the
bytes read, with no records: one digest for each 64 bytes, digest `i` that of the first
`64 (i + 1)` bytes.  `sha_board_runs` states that the run never stops.  The theorems hold of the processor under the run conditions of
`LeanExe/M7/Proof/Board.lean`: a power-on reset with BOOT0 low and BOOT_ADD0 0x0080, software
watchdogs (OPTCR 0xFFFFAAFD), and no interrupt, NMI, debug halt, debugger access, or DMA during
the run.
-/

namespace TestSupport.M7.ShaBoardFile

open LeanExe.M7 LeanExe.M7.Nucleo LeanExe.Requests TestSupport.M7.Sha TestSupport.M7.ShaImages
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding

def shaBytes : Nat := file_nat% "sha.bin"
def shaSize : Nat := file_size% "sha.bin"

/-- The file holds the bytes of the SHA-256 step's image. -/
theorem sha_file : bootFileOk boardBoot boardProgram shaBytes shaSize = true := by
  decide +kernel

/-- The SHA-256 step on the NUCLEO-F767ZI from reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows below 2^62, every code map
that holds the file's bytes in flash from `0x08000000` and from `0x00200000`, and every state that
reset gives from the vector table at `0x00200000`, the model reaches the initialization's accesses
followed by the accesses `w` of the first `N` windows of `shaUsart3Tick` from `shaInit`, whose
reads take the values of `σ` after the initialization's 11.  The bytes that `w` writes to
`USART_TDR` begin the 32-byte digests `ds` of the blocks of 8 words that the bytes that `w` reads
from `USART_RDR` encode, one for each block, where digest `i` is, as a 256-bit value, the SHA-256
digest of FIPS 180-4 §6.2 of the bytes of blocks 0 to `i`. -/
theorem sha_board (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62) (code : UInt32 → Option UInt16)
    (hf : Flash code shaBytes shaSize) (b : State) (hb : Reset code flashItcm b) :
    let w := windows (reqTrace (devBus devBase) shaUsart3Tick shaInit
      (fun k => σ (k + initReads init))) N
    let recs := (decode 8 (dataIn (devBus devBase) shaUsart3 w)).recs
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace init σ ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256
            (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
        dataOut (devBus devBase) shaUsart3 w <+: ds.flatMap fun d => d.toList.map UInt8.toUInt64 :=
  sha_prefix sha_file hf b hb N hN

/-- `sha_board` over the bytes `bs` that the windows read from `USART_RDR`: the bytes that `w`
writes to `USART_TDR` begin the 32-byte digests `ds`, one for each 64 bytes of `bs`, where digest
`i` is, as a 256-bit value, the SHA-256 digest of FIPS 180-4 §6.2 of the first `64 (i + 1)` bytes
of `bs`. -/
theorem sha_board_bytes (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62)
    (code : UInt32 → Option UInt16) (hf : Flash code shaBytes shaSize) (b : State)
    (hb : Reset code flashItcm b) :
    let w := windows (reqTrace (devBus devBase) shaUsart3Tick shaInit
      (fun k => σ (k + initReads init))) N
    let bs := dataIn (devBus devBase) shaUsart3 w
    ∃ s, Reach platform σ code b s ∧ s.trace = initTrace init σ ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = bs.length / 64 ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256 (bytesToBitMessage (byteArrayOf (bs.take (64 * (i + 1))))) h) ∧
        dataOut (devBus devBase) shaUsart3 w <+: ds.flatMap fun d => d.toList.map UInt8.toUInt64 :=
  sha_bytes sha_file hf b hb N hN

/-- The SHA-256 step's run from reset over the image file succeeds for every number of steps. -/
theorem sha_board_runs (σ : Nat → UInt32) (code : UInt32 → Option UInt16)
    (hf : Flash code shaBytes shaSize) (b : State) (hb : Reset code flashItcm b) :
    ∀ k, ∃ t, run platform σ code k b = some t :=
  sha_loop_runs sha_file hf b hb

end TestSupport.M7.ShaBoardFile

#print axioms TestSupport.M7.ShaBoardFile.sha_board
#print axioms TestSupport.M7.ShaBoardFile.sha_board_bytes
#print axioms TestSupport.M7.ShaBoardFile.sha_board_runs
#print axioms TestSupport.M7.ShaBoardFile.sha_file
#print axioms TestSupport.M7.Sha.sha_loop
#print axioms TestSupport.M7.Sha.sha_loop_runs
#print axioms TestSupport.M7.Sha.sha_prefix
#print axioms TestSupport.M7.Sha.sha_bytes
#print axioms TestSupport.M7.Sha.sha_requests
#print axioms TestSupport.M7.Sha.sha_confined
#print axioms TestSupport.M7.Sha.sha_initStore
#print axioms TestSupport.M7.Sha.shaSpec_fips
#print axioms TestSupport.M7.Sha.sha_windows_prefix
#print axioms TestSupport.M7.sha_step
#print axioms LeanExe.Requests.frame_reads
#print axioms LeanExe.Requests.decode_lengths
#print axioms LeanExe.Requests.decode_take
#print axioms LeanExe.M7.Nucleo.areaBoard_run
#print axioms LeanExe.M7.Nucleo.areaBoard_runs
