import Verified.WGSL.Dispatch

namespace Verified.WGSL

structure Compiled (source : Verified.Expr S Γ (.array e)) where
  count : Verified.Expr S Γ .word
  element : Verified.Expr S (.word :: Γ) (.elem e)
  shape : source = .build count element
  kernel : Kernel count element

def compile : (source : Verified.Expr S Γ (.array e)) → Option (Compiled source)
  | .build count element => (compileKernel count element).map fun kernel =>
      ⟨count, element, rfl, kernel⟩
  | _ => none

variable {source : Verified.Expr S Γ (.array e)}

def Compiled.module (c : Compiled source) : LeanExe.WGSL.Module := c.kernel.module
def Compiled.spec (c : Compiled source) : LeanExe.WGSL.Spec := c.kernel.toKernelPlan.spec
def Compiled.args (c : Compiled source) (env : Verified.Env Γ) : List LeanExe.WGSL.Arg :=
  c.kernel.params.args env
def Compiled.encode (c : Compiled source) : e.denote → UInt64 := c.kernel.output.encode

theorem Compiled.dispatch_eq (c : Compiled source) (funs : Funs S) (env : Verified.Env Γ) (n : Nat)
    (fits : c.spec.Fits (c.args env) n)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * n)
    (hL0 : output[0]? = some (UInt32.ofNat n)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : n ≤ count) (h32 : count ≤ 2 ^ 32) :
    c.module.dispatch ((c.args env).map LeanExe.WGSL.Arg.buffer) output count =
        some (LeanExe.WGSL.arrayWords ((source.denote funs env).map c.encode)) ∧
      c.module.RaceFree ((c.args env).map LeanExe.WGSL.Arg.buffer) output.size count := by
  have hValue := congrArg (fun expr => expr.denote funs env) c.shape
  have h := c.kernel.dispatch_eq funs env n fits output hOut hL0 hL1 count hCover h32
  simpa only [Compiled.module, Compiled.args, Compiled.encode, hValue] using h

end Verified.WGSL
