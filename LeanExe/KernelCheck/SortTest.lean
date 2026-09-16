import LeanExe.KernelCheck.Sort

namespace LeanExe.KernelCheck.SortTest

-- Pin the interpretation of the first concrete universe levels to Lean.
example : Sort 1 := Sort 0
example : Sort 2 := Sort 1
example : Sort 3 := Sort 2

#guard checkSort 0 1 == 0
#guard checkSort 0 0 == 1
#guard checkSort 1 2 == 0
#guard checkSort 1 1 == 1
#guard checkSort 0 2 == 1
#guard checkSort 42 43 == 0
#guard checkSort 9223372036854775807 9223372036854775808 == 0
#guard checkSort 18446744073709551614 18446744073709551615 == 0
#guard checkSort 18446744073709551614 0 == 1
#guard checkSort 18446744073709551615 0 == 2
#guard checkSort 18446744073709551615 18446744073709551615 == 2

end LeanExe.KernelCheck.SortTest
