/-! This module writes the CIC decimation filter of order 3, decimation 8, and differential delay 1
in the verified compiler's dialect, in the block form of `Cascade.lean`: three integrator passes
over the whole input, a decimation pass, and three comb passes over the decimated list.  Each pass
is a fold over its input array whose state holds a word and the result so far, and each step pushes
at most one word onto the result, which grows in place.  The words wrap modulo `2^64`, as `cascade`
at `UInt64` does, and `Proof.lean` proves that `cic` computes `cascade 3 8 1` on every input
array. -/

namespace Library.Numerics.Filters.Cic

/-- An integrator pass: element `t` of the result is the sum of the elements `0` to `t` of `xs`.
The state holds the sum so far. -/
def integratePass (xs : Array UInt64) : Array UInt64 :=
  (xs.foldl (fun (state : UInt64 × Array UInt64) x =>
    let sum := state.1 + x
    (sum, state.2.push sum)) ((0 : UInt64), (#[] : Array UInt64))).2

/-- Decimation by 8: elements `7`, `15`, `23`, and so on of `xs`, the last of each complete block of
8.  The state holds the position of the next element in its block, from 0 to 7. -/
def decimatePass (xs : Array UInt64) : Array UInt64 :=
  (xs.foldl (fun (state : UInt64 × Array UInt64) x =>
    if state.1 == 7 then ((0 : UInt64), state.2.push x) else (state.1 + 1, state.2))
    ((0 : UInt64), (#[] : Array UInt64))).2

/-- A comb of differential delay 1: element `m` of the result is element `m` of `xs` minus element
`m − 1`, with 0 before element 0.  The state holds the previous element. -/
def combPass (xs : Array UInt64) : Array UInt64 :=
  (xs.foldl (fun (state : UInt64 × Array UInt64) x =>
    (x, state.2.push (x - state.1))) ((0 : UInt64), (#[] : Array UInt64))).2

/-- The CIC decimation filter of order 3, decimation 8, and differential delay 1 on the samples
`xs`. -/
def cic (xs : Array UInt64) : Array UInt64 :=
  combPass (combPass (combPass (decimatePass (integratePass (integratePass (integratePass xs))))))

end Library.Numerics.Filters.Cic
