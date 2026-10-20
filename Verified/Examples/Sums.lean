import Verified.Reflect.Command
import Examples.Shape.Flat

namespace Verified.Examples.Sums

open LeanExe.Pipeline Examples.Shape

instance : Inhabited Shape := ⟨.circle 0⟩

def read (xs : Array Shape) (i : UInt64) : Shape := xs[i.toNat]!

def replace (xs : Array Shape) (i : UInt64) (s : Shape) : Array Shape := xs.set! i.toNat s

def push (xs : Array Shape) (s : Shape) : Array Shape := xs.push s

def areaSum (xs : Array Shape) : Float := xs.foldl (fun acc s => acc + s.area) 0

def spin (n : UInt64) (s : Shape) : Shape := LeanExe.loop n s fun _ p => p.grow

inductive Mode where
  | raw | rounded
  deriving DecidableEq

instance : Flat Mode UInt64 := ⟨fun | .raw => 0 | .rounded => 9⟩

inductive Packet where
  | value (x : Float32) (mode : Mode)
  | word (x : UInt64)
  | empty

instance : Flat Packet (UInt64 × Float32 × Mode × UInt64) := ⟨fun
  | .value x mode => (0, x, mode, 0)
  | .word x => (1, 0, .raw, x)
  | .empty => (2, 0, .raw, 0)⟩

def packetRead : Packet → Float32
  | .value x mode => if mode == .raw then x else LeanExe.Float32.nearest x
  | .word x => x.toFloat32
  | .empty => -0.0

def packetTurn : Packet → Packet
  | .value x mode => .value (-x) (if mode == .raw then .rounded else .raw)
  | .word x => .word (x + 1)
  | .empty => .value 1.25 .rounded

def packetDefault (p : Packet) : UInt64 :=
  match p with
  | .word x => x
  | other => (packetRead other).toBits.toUInt64

def packetMake (k : UInt64) (x : Float32) (w : UInt64) : Packet :=
  if k = 0 then .value x .raw else if k = 1 then .word w else .empty

verified_compile compiled := [Shape.area, Shape.ofWords, Shape.scale, Shape.width, Shape.grow,
  Shape.normalize, totalArea, read, replace, push, areaSum, spin, packetRead, packetTurn,
  packetDefault, packetMake]

#print axioms compiled.bytes
#print axioms compiled.areaSum.bound_eq
#print axioms compiled.push.trapFree

end Verified.Examples.Sums
