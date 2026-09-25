import Project.ProofKit.F32RangeCheck

namespace Project.ProofKit.F32SumRangeCertificate

def checkedPrefix (input : Nat → UInt32) (bound : Nat) : Nat → UInt32 × Bool
  | 0 => (0, true)
  | count + 1 =>
    let previous := checkedPrefix input bound count
    (Wasm.IEEE32.add previous.1 (input count),
      previous.2 && F32RangeCertificate.addition previous.1 (input count) bound)

def maximum (input : Nat → UInt32) : Nat → UInt32 × Nat
  | 0 => (0, 0)
  | count + 1 =>
    let previous := maximum input count
    (Wasm.IEEE32.add previous.1 (input count),
      max previous.2 (Wasm.IEEE32.scaledValue previous.1 + Wasm.IEEE32.scaledValue (input count)).natAbs)

def bound (input : Nat → UInt32) (count : Nat) : Nat := (maximum input count).2.log2 + 1

end Project.ProofKit.F32SumRangeCertificate
