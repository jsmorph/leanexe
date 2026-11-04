import Verified.PTX.Kernel

/-!
`compile` translates a source expression that is a build into a PTX kernel, or gives `none`.
`Compiled.executions_eq` states the launch theorem of `Kernel.executions_eq` for the source array.
-/

namespace Verified.PTX

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

def Compiled.module (c : Compiled source) : LeanExe.PTX.Module := c.kernel.module
def Compiled.spec (c : Compiled source) : LeanExe.Source.Spec := c.kernel.toKernelPlan.spec
def Compiled.args (c : Compiled source) (env : Verified.Env Γ) : List LeanExe.Source.Arg :=
  c.kernel.params.args env
def Compiled.encode (c : Compiled source) : e.denote → UInt64 := c.kernel.output.encode

theorem Compiled.executions_eq (c : Compiled source) (funs : Funs S) (env : Verified.Env Γ)
    (value : Array e.denote) (meaning : source.denote funs env = value) (n : Nat)
    (fits : c.spec.Fits (c.args env) n)
    (ys : Array UInt64) (hys : ys.size = n) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : n ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    let L := LeanExe.PTX.buildLaunch c.module (c.args env) n ys blocks block
    (∃ E, L.Consistent E) ∧ ∀ E, L.Consistent E →
      L.NoDataRace E ∧ (∀ g, g < blocks * block → (L.events (E.oracle g) g).2 = true) ∧
        ∀ i, i < n + 1 →
          (#[UInt64.ofNat n] ++ value.map c.encode)[i]? = some (E.observed i) := by
  have hValue : source.denote funs env = (Verified.Expr.build c.count c.element).denote funs env :=
    congrArg (fun expr => expr.denote funs env) c.shape
  have h := c.kernel.executions_eq funs env n fits ys hys blocks block hb hb32 hbl hcover
    hthreads
  rw [← meaning, hValue]
  exact h

end Verified.PTX
