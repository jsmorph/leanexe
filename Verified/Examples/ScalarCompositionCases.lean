import Verified.Examples.ScalarComposition
import Examples.Host

namespace Verified.Examples.ScalarComposition

def cases : IO Unit := do
  let words : List UInt64 := [0, 1, 7, 0x7fffffffffffffff, 0x8000000000000000,
    0xfffffffffffffffe, 0xffffffffffffffff]
  for x in words do
    for y in words do
      IO.println s!"scalarcomposition|divide|i64|i64:{x} i64:{y}|{divide x y}|0|0"
      IO.println s!"scalarcomposition|choose|i64|i64:{x} i64:{y}|{choose x y}|0|0"
  for n in ([0, 1, 2, 7, 998, 999, 1000, 4096] : List UInt64) do
    for acc in ([0, 13, 0xffffffffffffffff] : List UInt64) do
      IO.println s!"scalarcomposition|sum|i64|i64:{n} i64:{acc}|{sum n acc}|0|0"
    IO.println s!"scalarcomposition|shiftedSum|i64|i64:{n}|{shiftedSum n}|0|0"
  for bits in ([0, 0x8000000000000000, 1, 0x8000000000000001, 0x3ff0000000000000,
      0xbff8000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
      0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000] : List UInt64) do
    let x := Float.ofBits bits
    IO.println s!"scalarcomposition|scale|f64|f64:{x.toBits}|{(scale x).toBits}|0|0"
    IO.println s!"scalarcomposition|twice|f64|f64:{x.toBits}|{(twice x).toBits}|0|0"
  for bits in ([0, 0x80000000, 1, 0x80000001, 0x3fc00000, 0xbfc00000,
      0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x7fc00000] : List UInt64) do
    let x := Float32.ofBits bits.toUInt32
    IO.println s!"scalarcomposition|round32|f32|f32:{x.toBits}|{(round32 x).toBits}|0|0"
    IO.println s!"scalarcomposition|bits32|i64|i64:{bits}|{bits32 bits}|0|0"

end Verified.Examples.ScalarComposition
