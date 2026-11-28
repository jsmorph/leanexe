module

public import Demos.BignumCalc.Message
public import TestSupport.Host

@[expose] public section

/-!
The cases of the calculator's module `bignumCalc` in the form of `tests/verified/run.sh`: each
message's line from `calcSpec` in native Lean, through `calcLine`, whose message and line hold one
byte to a word, `calcWords`, the bare-metal entry, whose message is packed eight bytes to a word
with its length and whose line is packed the same way, and `calcBytes`, the Image's entry.  The
messages are among those of `tests/bignum-calc/messages.mjs`: every operation on small and large
operands, zero divisors, operands outside the grammar, names of no operation, wrong numbers of
spaces, empty parts, bytes that belong to an operand, the empty message, and, for `calcWords`, a
length above 65,536 bytes.
-/

namespace TestSupport.BignumCalc.Cases

open Demos.BignumCalc
open TestSupport.Host

/-- The bytes of a string. -/
def bytes (s : String) : List UInt8 := s.toList.map Char.toUInt8

def wordsOf (b : List UInt8) : List UInt64 := b.map UInt8.toUInt64

/-- Bytes packed eight to a word, the lowest first, with zeros after the last. -/
def packed (b : List UInt8) : List UInt64 :=
  (List.range ((b.length + 7) / 8)).map fun k =>
    (List.range 8).foldl (fun w i => w ||| ((b.getD (8 * k + i) 0).toUInt64 <<< (8 * i).toUInt64)) 0

def hexByte (x : UInt8) : String :=
  let d := fun (n : Nat) => "0123456789abcdef".toList[n]!
  String.ofList [d (x.toNat / 16), d (x.toNat % 16)]

def hex (b : List UInt8) : String := String.join (b.map hexByte)

/-- A decimal text of `n` digits whose first digit is not 0. -/
def digits (n seed : Nat) : String :=
  String.ofList ((List.range n).map fun i =>
    Char.ofNat (48 + if i = 0 then 1 + seed % 9 else (seed * 31 + 17 * i) % 10))

def messages : List String :=
  ["neg 0", "neg -5", "neg 12345678901234567890", "cmp 3 5", "cmp -1 -1", "cmp 10 -10",
    "add 1 2", "add -7 7", "add 18446744073709551615 1", "sub 0 1", "sub 4294967296 1",
    "mul 123 -456", "mul 99999999999 99999999999", "tdiv -7 2", "tmod -7 2", "ediv -7 2",
    "emod -7 2", "ediv 7 -2", "emod -7 -2", "tdiv -6 -3", "tdiv 5 0", "tmod 5 0", "ediv -5 0",
    "emod -5 0", "tdiv x 0", "add 1 x", "add -0 1", "add 007 1", "add +1 1", "add  1",
    "add 1 ", " add 1 2", "add 1 2 3", "foo 1 2", "ADD 1 2", "neg", "neg ", "", "add 1 2\n",
    "add\t1 2", "cmp 1 2 ",
    s!"mul {digits 300 1} -{digits 300 2}", s!"ediv {digits 500 3} -{digits 200 4}",
    s!"emod -{digits 500 5} {digits 31 6}", s!"sub {digits 40 7} {digits 41 8}",
    s!"add -{digits 600 9} {digits 600 10}", s!"tdiv {digits 400 11} {digits 400 12}"]

def bignumCalc : IO Unit := do
  for m in messages do
    let b := bytes m
    let l := calcSpec b
    line "bignumCalc" "calcLine" "array-u64" [arrU (wordsOf b)] (arrOut (wordsOf l))
    line "bignumCalc" "calcWords" "array-u64" [arrU (packed b), u b.length.toUInt64]
      (arrOut (packed l))
    line "bignumCalc" "calcBytes" "bytes" [s!"bytes:{hex b}"] (hex l)
  line "bignumCalc" "calcWords" "array-u64" [arrU (packed (bytes "add 1 2")), u 65537]
    (arrOut (packed (bytes "4")))

end TestSupport.BignumCalc.Cases
