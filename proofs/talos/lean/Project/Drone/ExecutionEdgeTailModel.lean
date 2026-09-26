import Project.Drone.ExecutionScalar
import Project.ProofKit.ScalarTransitionU64

namespace Project.Drone.Execution
open Wasm Project.ProofKit LeanExe.Examples.Drone
open ScalarTransition

def durationExpr : Expr .u64 :=
  .bin .divU (.const 33600) (.bin .divU (.get 10) (.const 5))

def clearanceExpr (z r w other : Nat) : Expr .u64 :=
  .ite (.ltU
    (.bin .mul (.bin .mul (.const 3) (.get 10)) (.bin .sub (.get z) (.get r)))
    (.bin .mul (.bin .mul (.const 2) (.get w)) (.bin .sub (.get other) (.get r))))
    (.const 0) durationExpr

def movingTailExpr : Expr .u64 :=
  .ite (.ltU (.const 8000) (.bin .mul (.bin .mul (.const 3) (.get 9)) (.get 10)))
    (.const 0)
    (.ite (.ltU (.const 160000)
      (.bin .mul (.bin .mul (.bin .mul (.const 6) (.get 9)) (.get 10)) (.get 10)))
      (.const 0)
      (.ite (.not (.ltU (.get 1) (.get 0)))
        (clearanceExpr 2 0 4 1) (clearanceExpr 3 1 5 0)))

def movingTailValue (r0 r1 z0 z1 u v dh : UInt64) : UInt64 :=
  if 8000 < 3*dh*(u+v) then 0
  else if 160000 < 6*dh*(u+v)*(u+v) then 0
  else if r0 ≤ r1 then
    if 3*(u+v)*(z0-r0) < 2*u*(r1-r0) then 0 else 33600/((u+v)/5)
  else
    if 3*(u+v)*(z1-r1) < 2*v*(r0-r1) then 0 else 33600/((u+v)/5)

def movingTailWords (r0 r1 z0 z1 u v dh : UInt64) : U64State :=
  { params := [r0, r1, z0, z1, u, v],
    locals := [z0, z1, dh, dh, u+v, 0, u*u, v*v, 0, 0, 0, 0, 0] }

def movingTailState (r0 r1 z0 z1 u v dh : UInt64) : State :=
  (movingTailWords r0 r1 z0 z1 u v dh).toState

end Project.Drone.Execution
