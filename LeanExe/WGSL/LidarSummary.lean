import LeanExe.WGSL.Lidar

namespace LeanExe.WGSL.LidarSummary
open UInt

/-- Finite mask decoding avoids adding bit operations to the integer subset. -/
def selected (i : Nat) : Expr :=
  (List.range 16).foldr (fun mask rest =>
    if mask / 2^i % 2 = 1 then .choose (.eq (.read .params 3) (.lit mask)) (.lit 1) rest
    else rest) (.lit 0)

def miss : Expr := .add (.read .params 2) (.lit 1)

def distance (i : Nat) : Expr := .choose (selected i) (.read .scene i) miss

def count (i : Nat) : Expr :=
  .choose (.both (selected i) (.le (.read .scene i) (.read .params 2))) (.lit 8192) (.lit 0)

/-- One compact summary word: hit count in the high bits, nearest selected
distance (or range+1 for no selected hit) in the low 13 bits. -/
def kernel : Expr :=
  .add (.add (count 0) (.add (count 1) (.add (count 2) (count 3))))
    (.min (distance 0) (.min (distance 1) (.min (distance 2) (distance 3))))

theorem checked : kernel.Checked 4096 := by decide

theorem exact (input : Input) (bounded : input.Bounded 4096) :
    kernel.eval32 input = kernel.eval input := exact32 _ _ _ bounded checked

end LeanExe.WGSL.LidarSummary
