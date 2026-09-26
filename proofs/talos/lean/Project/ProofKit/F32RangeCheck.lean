import Interpreter.Wasm.IEEE32

namespace Project.ProofKit.F32RangeCertificate

def addition (a b : UInt32) (bound : Nat) : Bool :=
  Wasm.IEEE32.isFinite a && Wasm.IEEE32.isFinite b && bound ≤ 276 &&
    decide ((Wasm.IEEE32.scaledValue a + Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound)

def subtraction (a b : UInt32) (bound : Nat) : Bool :=
  Wasm.IEEE32.isFinite a && Wasm.IEEE32.isFinite b && bound ≤ 276 &&
    decide ((Wasm.IEEE32.scaledValue a - Wasm.IEEE32.scaledValue b).natAbs < 2 ^ bound)

def multiplication (a b : UInt32) (bound : Nat) : Bool :=
  Wasm.IEEE32.isFinite a && Wasm.IEEE32.isFinite b && 173 ≤ bound && bound ≤ 425 &&
    decide (Wasm.IEEE32.scaledMagnitude a * Wasm.IEEE32.scaledMagnitude b < 2 ^ bound)

def division (a b : UInt32) (bound : Nat) : Bool :=
  Wasm.IEEE32.isFinite a && Wasm.IEEE32.isFinite b && 24 ≤ bound && bound ≤ 275 &&
    Wasm.IEEE32.scaledMagnitude b != 0 &&
    decide (Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude b * 2 ^ bound)

def squareRoot (a : UInt32) (bound : Nat) : Bool :=
  Wasm.IEEE32.isFinite a && !Wasm.IEEE32.sign a && 24 ≤ bound && bound ≤ 274 &&
    decide (Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ 2 ^ (2 * bound))

def lowerAbsolute (a : UInt32) (numerator denominator : Nat) : Bool :=
  0 < numerator && 0 < denominator &&
    decide (numerator * 2 ^ 149 ≤ Wasm.IEEE32.scaledMagnitude a * denominator)

def rescaling (a reduced : UInt32) (squares : Nat) : Bool :=
  decide ((2 ^ squares : Int) * Wasm.IEEE32.scaledValue reduced = Wasm.IEEE32.scaledValue a)

end Project.ProofKit.F32RangeCertificate
