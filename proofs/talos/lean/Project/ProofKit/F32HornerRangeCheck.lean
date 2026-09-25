import LeanExe.Float32
import Project.ProofKit.F32RangeCheck

namespace Project.ProofKit.F32HornerRangeCertificate

def checkedPrefix (input initial : UInt32) (coefficient : Nat → UInt32)
    (mulBound addBound : Nat) : Nat → UInt32 × Bool
  | 0 => (initial, true)
  | count + 1 =>
    let previous := checkedPrefix input initial coefficient mulBound addBound count
    let product := LeanExe.Float32.mulBits previous.1 input
    (LeanExe.Float32.addBits product (coefficient count), previous.2 &&
      F32RangeCertificate.multiplication previous.1 input mulBound &&
      F32RangeCertificate.addition product (coefficient count) addBound)

end Project.ProofKit.F32HornerRangeCertificate
