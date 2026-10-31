import Library.Numerics.Arithmetic.BinaryGcd.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the binary GCD. -/

namespace Library.Numerics.Arithmetic.BinaryGcd

open TestSupport.Host

/-- The arguments of the verified compiler's cases, each also with its arguments swapped.  The
chosen pairs are 0 with odd and even words, ones, `2^64 - 1`, powers of 2 and their neighbors, pairs
with a common power of 2, equal pairs, `(48, 18)` and `(1071, 462)`, the consecutive Fibonacci
numbers `F₉₃` and `F₉₂`, the largest consecutive pair that fits in a word, and `F₈₃` and `F₈₂`.
The fold runs 91 times from `[F₂, F₁]`, so its head is `F₉₃`.  Of the 60 generated pairs, a third
are arbitrary words, a third are arbitrary words shifted left by up to 16 and 12 bits, and a third
are numbers below `10^6` multiplied by `2^20`. -/
def gcdInputs : List (UInt64 × UInt64) :=
  let half : UInt64 := 9223372036854775808
  let fib := (List.range 91).foldl (fun (acc : List UInt64) _ =>
    match acc with
    | a :: b :: _ => (a + b) :: acc
    | _ => acc) [1, 1]
  let chosen : List (UInt64 × UInt64) :=
    [(0, 0), (0, 1), (0, maxU), (0, 6), (0, half), (0, 12 * 2 ^ 40), (1, 1), (1, maxU), (maxU, maxU), (maxU, maxU - 1), (half, half),
      (half, 1), (half, 6), (half, 3 * 2 ^ 40), (48, 18), (1071, 462), (2 ^ 63 - 1, 2 ^ 62),
      (12157665459056928801, 7540113804746346429), (3 * 2 ^ 20, 5 * 2 ^ 21), (2 ^ 32, 2 ^ 31 * 3),
      (fib.head!, fib.tail.head!), (fib[10]!, fib[11]!), (7 * 2 ^ 60, 7 * 2 ^ 59)]
  let random := (List.range 60).map fun i =>
    let a := rw (3 * i + 500)
    let b := rw (3 * i + 501)
    if i % 3 = 0 then (a <<< (UInt64.ofNat (i % 17)), b <<< (UInt64.ofNat (i % 13)))
    else if i % 3 = 1 then (a % 1000000 * 2 ^ 20, b % 1000000 * 2 ^ 20) else (a, b)
  (chosen ++ random).flatMap fun (a, b) => [(a, b), (b, a)]

end Library.Numerics.Arithmetic.BinaryGcd
