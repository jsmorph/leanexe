import LeanExe.KernelCheck.Conversion

namespace LeanExe.KernelCheck

example : Prop → Prop := fun (p : (fun A : Type => A) Prop) => p
example : (Prop → Prop) → Prop → Prop :=
  fun (f : (fun A : Type => A) (Prop → Prop)) p => f p

end LeanExe.KernelCheck
