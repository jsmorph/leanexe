import Library.Numerics.Bounds.Program
import Library.Numerics.Limiters.Minmod.Program
import Library.Numerics.Reductions.Word.Program
import Library.Arrays.Search.Program
import TestSupport.Host

namespace TestSupport.LibraryCases

open TestSupport.Host Library.Numerics.Bounds

private def checked (name : String) (args : List String) (result : Checked) : IO Unit :=
  line "libbounds" name "list:i64,f64" args s!"{result.status} {result.value.toBits}"

def cases : IO Unit := do
  for xs in wordArrays do
    let values := xs.toArray
    line "libwordreductions" "productArray" "i64" [arrU xs]
      (toString (Library.Numerics.Reductions.Word.productArray values))
    line "libwordreductions" "xorArray" "i64" [arrU xs]
      (toString (Library.Numerics.Reductions.Word.xorArray values))
    for count in [0, xs.length.toUInt64, xs.length.toUInt64 + 1] do
      line "libsearch" "firstZero" "i64" [arrU xs, u count]
        (toString (Library.Arrays.Search.firstZero values count))
  for a in specialFloats do
    for up in [false, true] do
      let direction := u (if up then 1 else 0)
      checked "endpoint" [direction, fl a] (endpoint up a)
      checked "outSqrt" [direction, fl a] (outSqrt up a)
      for b in specialFloats do
        let args := [direction, fl a, fl b]
        checked "outAdd" args (outAdd up a b)
        checked "outSub" args (outSub up a b)
        checked "outMul" args (outMul up a b)
        checked "outDiv" args (outDiv up a b)
    for b in specialFloats do
      line "libminmod" "minmod" "f64" [fl a, fl b]
        (toString (Library.Numerics.Limiters.Minmod.minmod a b).toBits)

end TestSupport.LibraryCases
