import LeanExe.KernelCheck.Application

namespace LeanExe.KernelCheck

example (p q r : Prop) (f : p → q) (g : q → r) (hp : p) : r := g (f hp)
example (A : Type) (P : A → Type) (f : (x : A) → P x) (x : A) : P x := f x
#guard checkApplication #[0,0,0,4,0,0] 1 0 100 == 1

end LeanExe.KernelCheck
