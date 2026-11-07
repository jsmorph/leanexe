import LeanExe.A64.Gen
import LeanExe.M7.Boot
import TestSupport.M7.Crc
import TestSupport.M7.Qemu

/-!
The image of the CRC-32 step `crcCmsdkTick`, function 5 of `crcCmsdkCompiled.module`, for QEMU's
`mps2-an500`, from the state `crcInit`, which no theorem covers.  The image holds the vector table
and UART0's initialization of `tests/TestSupport/M7/Qemu.lean`, the setup of the area, and the
generator's program with the stack's limit at the area's end.  `m7-windows crc-qemu` writes it,
and `tests/baremetal/m7-qemu.sh crc` runs it under QEMU against `tests/baremetal/uart_crc.py`.

The setup `areaSetup` is test code, outside the generator and its theorems: it clears the area
from `areaHeader` to `areaEnd` a word at a time, with the loop `CMP r0, r1; BCS done; STR r2,
[r0]; ADD r0, r0, r3; B loop` and r2 at 0 and r3 at 4, and then stores each nonzero word of
`areaPrefixBytes` of `LeanExe/A64/Gen.lean` at its place in the area, with `MOVW`, and `MOVT` when
the word's upper half is nonzero, into r0 and `STR r0, [r1, #(4j mod 4096)]` for word `j`, where r1
holds the base of the area's 4,096 bytes that hold word `j` and is set again for each such block.
The words of the area that the prefix does not cover are 0, as `areaBytes` has them.
-/

namespace TestSupport.M7.CrcImages

open LeanExe.M7 TestSupport.M7.Crc

/-- The words of the bytes `bs`, four bytes each, the lowest first. -/
def wordsOf : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24) ::
        wordsOf rest
  | _ => []

/-- The stores of the nonzero words `ws` from word `j` of the area on, when r1 holds the base of
the area's block of 4,096 bytes `blk`, if any. -/
def prefixStores : Nat → Option Nat → List UInt32 → List Instr
  | _, _, [] => []
  | j, blk, w :: ws =>
      if w = 0 then prefixStores (j + 1) blk ws
      else
        let b := j / 1024
        (if blk = some b then [] else movWord 1 (areaHeader + UInt32.ofNat (4096 * b))) ++
          movConst 0 w.toNat ++ [.str 0 1 (field 4096 (4 * (j % 1024)))] ++
          prefixStores (j + 1) (some b) ws

/-- The setup of the area for the module `m`: the clear of the area and the stores of the nonzero
words of its first bytes. -/
def areaSetup (m : Wasm.Module) : List Instr :=
  movWord 0 areaHeader ++ movWord 1 areaEnd ++
    [.movImm 2 0, .movImm 3 4, .cmpReg 0 1, .bcondTo 2 12, .str 2 0 0, Instr.addLsl 0 0 0 3 0,
      .bTo (-20)] ++
    prefixStores 0 none (wordsOf (LeanExe.A64.areaPrefixBytes m))

/-- The image's layout: QEMU's vector table and SP, and UART0's initialization followed by the
setup of the area. -/
def boot : Boot := { Qemu.boot with init := Qemu.init ++ areaSetup crcCmsdkCompiled.module }

/-- The image's instructions from the self-loop on. -/
def program : GenM (List Instr) :=
  bootProgram boot crcCmsdkCompiled.module 5 [crcInit] areaEnd Qemu.devBase

/-- The bytes of the image. -/
def image : GenM (List UInt8) := do
  return bootBytes boot (← program)

/-- The address of the loop's head of `main`. -/
def loopHead : UInt32 := after boot.base (mainStart [crcInit])

end TestSupport.M7.CrcImages
