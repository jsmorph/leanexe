import Project.ClobFindBest.Helpers
import Project.ProofKit.PackedFloatFrame
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Helpers

def fbFrame (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat)
    (best : Option Nat) (tag payload done : UInt64) (scratch : List Value) : Locals :=
  { params := [.i64 fuel, .i64 owner, .i64 ptr, .i64 taker.oid, .i64 taker.otrader,
      .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty, .i64 (UInt64.ofNat k),
      .i64 (optionTag best), .i64 (optionPayload best)],
    locals := [.i64 0, .i64 tag, .i64 payload, .i64 done] ++ scratch,
    values := [] }

def fbInv (initial : Store Unit) (owner ptr : UInt64) (os : List OrderL)
    (taker : OrderL) : AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ k : Nat, k ≤ os.length ∧
  ∃ fuel tag payload done : UInt64, ∃ scratch : List Value,
    scratch.length = 52 ∧
    frame = fbFrame fuel owner ptr taker k (bestPrefixL os taker k) tag payload done scratch ∧
    ((done = 0 ∧ fuel = UInt64.ofNat (os.length+1-k)) ∨
      (done = 1 ∧ k = os.length ∧ tag = optionTag (bestPrefixL os taker os.length) ∧
        payload = optionPayload (bestPrefixL os taker os.length)))

def fbMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: _ :: _ :: .i64 done :: _ =>
      2*fuel.toNat + (if done = 0 then 1 else 0)
  | _, _ => 0

def loopCode : Wasm.Program :=
  match (func7[4]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => body
  | _ => []

def stepCode : Wasm.Program :=
  match (loopCode[14]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.iff _ _ body _ _ _) => body
  | _ => []

def advanceCode : Wasm.Program := stepCode.drop 65

def advanceScratch (scratch : List Value) (owner ptr : UInt64) (taker : OrderL)
    (k : Nat) (selected : Option Nat) : List Value :=
  scratch |>.set 28 (.i64 owner) |>.set 29 (.i64 ptr)
    |>.set 30 (.i64 taker.oid) |>.set 31 (.i64 taker.otrader)
    |>.set 32 (.i64 taker.oside) |>.set 33 (.i64 taker.oprice) |>.set 34 (.i64 taker.oqty)
    |>.set 49 (.i64 (UInt64.ofNat k)) |>.set 50 (.i64 1)
    |>.set 51 (.i64 (UInt64.ofNat (k+1))) |>.set 35 (.i64 (UInt64.ofNat (k+1)))
    |>.set 36 (.i64 (optionTag selected)) |>.set 37 (.i64 (optionPayload selected))
    |>.set 38 (.i64 owner) |>.set 39 (.i64 ptr)
    |>.set 40 (.i64 taker.oid) |>.set 41 (.i64 taker.otrader)
    |>.set 42 (.i64 taker.oside) |>.set 43 (.i64 taker.oprice) |>.set 44 (.i64 taker.oqty)
    |>.set 45 (.i64 (UInt64.ofNat (k+1)))
    |>.set 46 (.i64 (optionTag selected)) |>.set 47 (.i64 (optionPayload selected))
    |>.set 48 (.i64 0)

theorem advanceScratch_length (scratch : List Value) (owner ptr : UInt64) (taker : OrderL)
    (k : Nat) (selected : Option Nat) :
    (advanceScratch scratch owner ptr taker k selected).length = scratch.length := by
  simp only [advanceScratch, List.length_set]

end Project.ClobFindBest.Loop
