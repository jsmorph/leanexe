import Lean

namespace Project.WGSL.ArithmeticChoice

def select (fused : Bool) (separateWord fusedWord : UInt32) : UInt32 :=
  if fused then fusedWord else separateWord

theorem select_false (separateWord fusedWord : UInt32) :
    select false separateWord fusedWord = separateWord := rfl

theorem select_true (separateWord fusedWord : UInt32) :
    select true separateWord fusedWord = fusedWord := rfl

#print axioms select_false
#print axioms select_true
end Project.WGSL.ArithmeticChoice
