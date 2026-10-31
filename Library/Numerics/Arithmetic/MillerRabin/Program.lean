import LeanExe.Dialect.Loop

/-! Modular exponentiation and the strong probable-prime test.  `addMod` adds two residues modulo
`m` without overflow, by subtracting `m - b` when the sum would reach `m`.  `mulMod` multiplies by
the binary method on the bits of the second factor, from the most significant down, so that every
intermediate value is a residue.  `powMod` is Algorithm A of TAOCP §4.6.3, the right-to-left binary
method, over the 64 bits of the exponent.  `test` is Algorithm P of §4.5.4: it removes the factors
2 of `n - 1`, raises the base to the odd part `q`, and squares the result up to `k - 1` times,
looking for `n - 1`. -/

namespace Library.Numerics.Arithmetic.MillerRabin

/-- `a + b` modulo `m`, for `a, b < m`. -/
def addMod (a b m : UInt64) : UInt64 := if m - b ≤ a then a - (m - b) else a + b

/-- `a * b` modulo `m`, for `a < m`: the bits of `b` from the most significant down double the
partial product and add `a`. -/
def mulMod (a b m : UInt64) : UInt64 :=
  LeanExe.loop 64 (0 : UInt64) fun i r =>
    if (b >>> (63 - i)) &&& 1 = 1 then addMod (addMod r r m) a m else addMod r r m

/-- Algorithm A: `x^n` modulo `m`.  `s.1` is the product `Y` and `s.2` the power `Z` of the
base. -/
def powMod (x n m : UInt64) : UInt64 :=
  if m = 0 then 0
  else
    (LeanExe.loop 64 (1 % m, x % m) fun i s =>
      (if (n >>> i) &&& 1 = 1 then mulMod s.1 s.2 m else s.1, mulMod s.2 s.2 m)).1

/-- The number of factors 2 of `x`, for `x > 0`: the number of low bits that are 0. -/
def twos (x : UInt64) : UInt64 :=
  LeanExe.loop 64 (0 : UInt64) fun i k => if k = i ∧ (x >>> i) &&& 1 = 0 then k + 1 else k

/-- Algorithm P: 1 when `n` is a strong probable prime to the base `x`.  `k` is the number of
factors 2 of `n - 1`, and `y` is the base raised to the odd part of `n - 1`. -/
def test (n x : UInt64) : UInt64 :=
  if n % 2 = 0 ∨ n < 3 then 0
  else
    let k := twos (n - 1)
    let y := powMod x ((n - 1) >>> k) n
    if y = 1 ∨ y = n - 1 then 1
    else
      (LeanExe.loop 63 (y, (0 : UInt64)) fun j s =>
        if j + 1 < k ∧ s.2 = 0 then (mulMod s.1 s.1 n, if mulMod s.1 s.1 n = n - 1 then 1 else 0)
        else s).2

end Library.Numerics.Arithmetic.MillerRabin
