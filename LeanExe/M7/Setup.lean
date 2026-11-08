import LeanExe.Area
import LeanExe.M7.Boot

/-!
The setup of the area of a module's store in the Cortex-M7's memory, which an image with linear
memory runs after the self-loop and before the board's initialization.  The area lies at a fixed
address `area` with the layout of `LeanExe/Area.lean`: the memory's size less 8, the globals from
byte 8, and the memory's bytes from byte 4096.  Reset leaves memory arbitrary, so the setup first
clears the area's `areaSize cap` bytes with a loop of word stores, and then stores each nonzero
word of the area's prefix `areaPrefixBytes m` as a constant.  The prefix's words reach memory as
immediates of `MOVW` and `MOVT`, which the kernel's check of the image compares with the file.  A
copy from flash would need loads from flash, which stop the model.

`clearLoop` takes r0 from the area's address to its end in r1, storing r2, which holds 0, and
adding r3, which holds 4.  `storeWords` gives, for each nonzero word `i` of the prefix,
`movConst 0` of the word and `STR r0, [r1, #(4 * (i % 1024))]`, after a `movConst 1` of the
address of the 4 KiB block that holds the word whenever r1 does not hold it yet, since the offset
of `STR` reaches 4,095 bytes.  `Boot.setup` places a setup before a layout's initialization.
-/

namespace LeanExe.M7

open Wasm

/-- The condition CS, unsigned higher or same. -/
def condCS : Fin 14 := 2

/-- The words of the bytes `bs`, four bytes each, the lowest first; fewer than four bytes at the
end give no word. -/
def wordsOf : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24) ::
        wordsOf rest
  | [] | [_] | [_, _] | [_, _, _] => []

/-- `CMP r0, r1`, `B<CS>.W` to the instruction after the loop, `STR r2, [r0]`, `ADD r0, r0, r3`,
and `B.W` back to the `CMP`. -/
def clearLoop : List Instr :=
  [.cmpReg 0 1, .bcondTo condCS 12, .str 2 0 0, .addReg 0 0 0 3 0 0, .bTo (-20)]

/-- The stores of the nonzero words `ws` from word `i` of the area at the address `area`, where
r1 holds `area + 4096 * q` when `cur` is `some q`. -/
def storeWords (area : Nat) : Nat → Option Nat → List UInt32 → List Instr
  | _, _, [] => []
  | i, cur, w :: ws =>
      if w = 0 then storeWords area (i + 1) cur ws
      else
        (if cur = some (i / 1024) then [] else movConst 1 (area + 4096 * (i / 1024))) ++
          movConst 0 w.toNat ++ [.str 0 1 (field 4096 (4 * (i % 1024)))] ++
          storeWords area (i + 1) (some (i / 1024)) ws

/-- The setup of the area at `area` of the store of `m` with a memory of `cap` pages: r0 to r3 for
`clearLoop` over the area's `areaSize cap` bytes, the loop, and the stores of the nonzero words of
the area's prefix. -/
def setupCode (area : UInt32) (cap : Nat) (m : Module) : List Instr :=
  movConst 0 area.toNat ++ movConst 1 (area.toNat + areaSize cap) ++ [.movImm 2 0, .movImm 3 4] ++
    clearLoop ++ storeWords area.toNat 0 none (wordsOf (areaPrefixBytes m))

/-- The store of `m` fits an area of `cap` pages that the setup can write: the memory fits, the
prefix lies inside the area, and the globals are at most 511 numbers of type `i32` or `i64`. -/
def setupOk (m : Module) (cap : Nat) : Bool :=
  areaOk m cap && decide (areaPrefix m ≤ areaSize cap) &&
    match globalTypesOf m with
    | some gts => decide (gts.length ≤ 511) && gts.all intType
    | none => false

/-- The layout `B` with the setup `su` before its initialization: the reset entry names the
setup, which falls through to the initialization. -/
def Boot.setup (B : Boot) (su : List Instr) : Boot := { B with init := su ++ B.init }

end LeanExe.M7
