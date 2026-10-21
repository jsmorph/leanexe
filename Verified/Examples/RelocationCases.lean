import Verified.Examples.Relocation
import Verified.Examples.ScalarCompositionCases

namespace Verified.Examples.Relocation

def cases : IO Unit := do
  ScalarComposition.casesFor "relocation"
  for x in ([0, 1, 7, 0x7fffffffffffffff, 0x8000000000000000,
      0xfffffffffffffffe, 0xffffffffffffffff] : List UInt64) do
    IO.println s!"relocation|seed|i64|i64:{x}|{seed x}|0|0"
  for n in ([0, 1, 2, 7, 998, 999, 1000, 4096] : List UInt64) do
    IO.println s!"relocation|callBoth|i64|i64:{n}|{callBoth n}|0|0"

end Verified.Examples.Relocation
