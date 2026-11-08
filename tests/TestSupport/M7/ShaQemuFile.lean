import TestSupport.M7.ShaLoop

/-!
The kernel's check of the image of the SHA-256 step `shaCmsdkTick` for QEMU's `mps2-an500` that
`m7-windows sha-qemu` writes, `sha-cmsdk-qemu.bin`, and the theorems over that file.
`tests/baremetal/m7-qemu.sh sha` elaborates this file in the directory of the image, so that
`file_nat%` and `file_size%` read it, and no build target includes it.  The kernel evaluates
`bootProgram` on QEMU's layout with the setup of the step's area before UART0's initialization and
on the module, the index 13, and the initial state `shaInit`, and checks that the file's bytes are
those of the vector table and the instructions.  `sha_qemu` states the loop theorem for every code
map that holds the file's bytes from address 0, where QEMU loads the image, and `sha_qemu_prefix`
that the bytes that the run writes to UART0's data register begin the 32-byte digests of the
blocks of 64 bytes that it reads from that register, digest `i` being the SHA-256 digest of FIPS
180-4 of blocks 0 to `i`, for fewer than 2^62 windows.
-/

namespace TestSupport.M7.ShaQemuFile

open LeanExe.M7 LeanExe.Requests TestSupport.M7.Sha TestSupport.M7.ShaImages
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding

def shaBytes : Nat := file_nat% "sha-cmsdk-qemu.bin"
def shaSize : Nat := file_size% "sha-cmsdk-qemu.bin"

/-- The file holds the bytes of the SHA-256 step's image for QEMU. -/
theorem sha_file : bootFileOk qemuBoot qemuProgram shaBytes shaSize = true := by
  decide +kernel

/-- The SHA-256 step on `mps2-an500` from QEMU's reset, over the image file: for every sequence `σ`
of the values that device reads return, every number `N` of windows, every code map that holds
the file's bytes from address 0, and every state that reset gives from the vector table at 0, the
model reaches the loop's head of `main` with the trace of UART0's initialization followed by the
accesses of the first `N` windows of `shaCmsdkTick` from the state `shaInit`. -/
theorem sha_qemu (σ : Nat → UInt32) (N : Nat) (code : UInt32 → Option UInt16)
    (hf : FileAt code shaBytes shaSize 0) (b : State) (hb : Reset code 0 b) :
    ∃ s, Reach Qemu.platform σ code b s ∧ s.pc = qemuHead ∧
      s.trace = Qemu.initTrace ++
        windows (reqTrace (devBus Qemu.devBase) shaCmsdkTick shaInit σ) N :=
  shaQemu_loop sha_file hf b hb N

/-- The SHA-256 step's digests on `mps2-an500` from QEMU's reset, over the image file, for fewer
than 2^62 windows. -/
theorem sha_qemu_prefix (σ : Nat → UInt32) (N : Nat) (hN : N < 2 ^ 62)
    (code : UInt32 → Option UInt16) (hf : FileAt code shaBytes shaSize 0) (b : State)
    (hb : Reset code 0 b) :
    let w := windows (reqTrace (devBus Qemu.devBase) shaCmsdkTick shaInit σ) N
    let recs := (decode 8 (dataIn (devBus Qemu.devBase) shaCmsdk w)).recs
    ∃ s, Reach Qemu.platform σ code b s ∧ s.trace = Qemu.initTrace ++ w ∧
      ∃ ds : List (Vector UInt8 32), ds.length = recs.length ∧
        (∀ i (hi : i < ds.length), ∃ h, digestBitVec ds[i] =
          SHS.SHA256.sha256
            (bytesToBitMessage (byteArrayOf ((recs.take (i + 1)).flatMap recordBytes))) h) ∧
        dataOut (devBus Qemu.devBase) shaCmsdk w <+:
          ds.flatMap fun d => d.toList.map UInt8.toUInt64 :=
  shaQemu_prefix sha_file hf b hb N hN

end TestSupport.M7.ShaQemuFile

#print axioms TestSupport.M7.ShaQemuFile.sha_qemu
#print axioms TestSupport.M7.ShaQemuFile.sha_qemu_prefix
#print axioms TestSupport.M7.ShaQemuFile.sha_file
#print axioms TestSupport.M7.Sha.shaQemu_loop
#print axioms TestSupport.M7.Sha.shaQemu_prefix
#print axioms TestSupport.M7.Sha.shaCmsdk_initStore
#print axioms TestSupport.M7.shaCmsdk_step
