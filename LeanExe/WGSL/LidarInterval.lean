import LeanExe.WGSL.SceneMap
import LeanExe.WGSL.LidarOblique

namespace LeanExe.WGSL.LidarInterval
open UInt

/-- A conservative one-grid-unit inner rectangle. -/
def innerWord (i : Nat) : Expr :=
  if i % 4 < 2 then .add (.read .scene i) (.lit 1)
  else .sub (.read .scene i) (.lit 1)

/-- A conservative one-grid-unit outer rectangle. -/
def outerWord (i : Nat) : Expr :=
  if i % 4 < 2 then .sub (.read .scene i) (.lit 1)
  else .add (.read .scene i) (.lit 1)

def inner : Expr := LidarOblique.kernel.mapScene innerWord
def outer : Expr := LidarOblique.kernel.mapScene outerWord

theorem inner_checked : inner.Checked 4095 := by decide
theorem outer_checked : outer.Checked 4095 := by decide

theorem inner_exact (input : Input) (bounded : input.Bounded 4095) :
    inner.eval32 input = LidarOblique.kernel.eval (input.mapScene innerWord) := by
  rw [exact32 inner input 4095 bounded inner_checked]
  exact eval_mapScene _ _ _

theorem outer_exact (input : Input) (bounded : input.Bounded 4095) :
    outer.eval32 input = LidarOblique.kernel.eval (input.mapScene outerWord) := by
  rw [exact32 outer input 4095 bounded outer_checked]
  exact eval_mapScene _ _ _

end LeanExe.WGSL.LidarInterval
