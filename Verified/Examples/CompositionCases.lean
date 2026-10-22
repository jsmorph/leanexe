import Verified.Examples.Composition
import TestSupport.Host

namespace Verified.Examples.Composition

def cases : IO Unit := do
  let words : List UInt64 := [0, 1, 7, 0x7fffffffffffffff, 0x8000000000000000,
    0xfffffffffffffffe, 0xffffffffffffffff]
  for x in words do
    for y in words do
      IO.println s!"composition|add|i64|i64:{x} i64:{y}|{CompositionBase.add x y}|0|0"
      IO.println s!"composition|wordCaller|i64|i64:{x} i64:{y}|{wordCaller x y}|0|0"
  for bits in ([0, 0x8000000000000000, 1, 0x8000000000000001, 0x3ff0000000000000,
      0xbff8000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
      0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000] : List UInt64) do
    let x := Float.ofBits bits
    IO.println s!"composition|scale|f64|f64:{x.toBits}|{(CompositionBase.scale x).toBits}|0|0"
    IO.println s!"composition|floatCaller|f64|f64:{x.toBits}|{(floatCaller x).toBits}|0|0"

end Verified.Examples.Composition
