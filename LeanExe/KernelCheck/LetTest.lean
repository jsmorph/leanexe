import LeanExe.KernelCheck.Let

namespace LeanExe.KernelCheck

example (p : Prop) (hp : p) : p := let h : p := hp; h
example : Prop → Prop := let A : Type := Prop; fun (x : A) => x
#guard checkLet #[0,1,0,0,0,0,1,0,0,3,0,2,5,1,3] 4 0 100 == 0
-- Incorrect unused value: let x : Prop := Prop; Prop.
#guard checkLet #[0,1,0,0,0,0,3,1,1,5,1,2] 3 0 100 == 1

end LeanExe.KernelCheck
