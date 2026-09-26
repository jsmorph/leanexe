import Project.ClobFindBest.FrozenHelpers
import Project.ProofKit.PackedFloatFrame
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers

def fbFrame (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat)
    (best : Option Nat) (tag payload done : UInt64) (scratch : List Value) : Locals :=
  { params := [.i64 fuel, .i64 owner, .i64 ptr, .i64 taker.oid, .i64 taker.otrader,
      .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty, .i64 (UInt64.ofNat k),
      .i64 (optionTag best), .i64 (optionPayload best)],
    locals := [.i64 tag, .i64 payload, .i64 done] ++ scratch,
    values := [] }

def fbInv (initial : Store Unit) (owner ptr : UInt64) (os : List OrderL)
    (taker : OrderL) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ k : Nat, k ≤ os.length ∧
  ∃ fuel tag payload done : UInt64, ∃ scratch : List Value,
    scratch.length = 44 ∧
    frame = fbFrame fuel owner ptr taker k (bestPrefixL os taker k) tag payload done scratch ∧
    ((done = 0 ∧ fuel = UInt64.ofNat (os.length+1-k)) ∨
      (done = 1 ∧ k = os.length ∧ tag = optionTag (bestPrefixL os taker os.length) ∧
        payload = optionPayload (bestPrefixL os taker os.length)))

def fbMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: _ :: .i64 done :: _ =>
      2*fuel.toNat + (if done = 0 then 1 else 0)
  | _, _ => 0

def loopCode : Wasm.Program :=
  match (func7[2]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

def stepCode : Wasm.Program :=
  match (loopCode[14]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

end Project.ClobFindBest.Frozen.Loop
