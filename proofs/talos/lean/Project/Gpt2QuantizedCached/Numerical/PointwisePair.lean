import Project.Gpt2CachedStep.PointwiseError

namespace Project.Gpt2QuantizedCached.Numerical.PointwisePair
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open Gpt2CachedStep

structure AddRanges (ql qr rl rr : ByteArray) (i qb rb : Nat) : Prop where
  qLeft : CodeLib.IEEE32.Finite (word ql i)
  qRight : CodeLib.IEEE32.Finite (word qr i)
  rLeft : CodeLib.IEEE32.Finite (word rl i)
  rRight : CodeLib.IEEE32.Finite (word rr i)
  qUpper : qb ≤ 276
  rUpper : rb ≤ 276
  qRange : (Wasm.IEEE32.scaledValue (word ql i) + Wasm.IEEE32.scaledValue (word qr i)).natAbs < 2 ^ qb
  rRange : (Wasm.IEEE32.scaledValue (word rl i) + Wasm.IEEE32.scaledValue (word rr i)).natAbs < 2 ^ rb

theorem add_error (ql qr rl rr : ByteArray) (i qb rb : Nat)
    (hqi : i < ql.size / 4) (hri : i < rl.size / 4) (leftError rightError : ℝ)
    (h : AddRanges ql qr rl rr i qb rb)
    (hl : |value (word ql i) - value (word rl i)| ≤ leftError)
    (hr : |value (word qr i) - value (word rr i)| ≤ rightError) :
    |value (word (addRows ql qr) i) - value (word (addRows rl rr) i)| ≤
      F32AdditionBounds.epsilon qb + (leftError + rightError) + F32AdditionBounds.epsilon rb := by
  rw [PointwiseError.add_source ql qr i hqi, PointwiseError.add_source rl rr i hri]
  exact F32PairError.add _ _ _ _ leftError rightError qb rb h.qLeft h.qRight h.rLeft h.rRight
    h.qUpper h.rUpper h.qRange h.rRange hl hr

structure GeluRanges (qi ri : ByteArray) (i : Nat) (qb rb : GeluForwardError.Bounds) : Prop where
  qFinite : CodeLib.IEEE32.Finite (word qi i)
  rFinite : CodeLib.IEEE32.Finite (word ri i)
  qRange : ¬F32Order.absBits (word qi i) > 0x41000000 → GeluForwardError.Ranges (F32Order.absBits (word qi i)) qb
  rRange : ¬F32Order.absBits (word ri i) > 0x41000000 → GeluForwardError.Ranges (F32Order.absBits (word ri i)) rb

theorem gelu_error (qi ri : ByteArray) (i : Nat) (hqi : i < qi.size / 4) (hri : i < ri.size / 4)
    (inputError : ℝ) (qb rb : GeluForwardError.Bounds) (h : GeluRanges qi ri i qb rb)
    (he : |value (word qi i) - value (word ri i)| ≤ inputError) :
    |value (word (activate qi) i) - value (word (activate ri) i)| ≤
      GeluForwardError.error (word qi i) qb + 4 * inputError + GeluForwardError.error (word ri i) rb := by
  rw [PointwiseError.activate_source qi i hqi, PointwiseError.activate_source ri i hri]
  have hq := GeluForwardError.reference_error (word qi i) (value (word ri i)) inputError qb h.qFinite h.qRange he
  have hr := GeluForwardError.source_error (word ri i) rb h.rFinite h.rRange
  exact F32ErrorPropagation.compare _ _ _ _ _ hq.2 hr.2

#print axioms add_error
#print axioms gelu_error
end Project.Gpt2QuantizedCached.Numerical.PointwisePair
