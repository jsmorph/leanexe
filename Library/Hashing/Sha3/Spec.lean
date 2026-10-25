/-! SHA-3 of FIPS 202, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*,
August 2015, transcribed from §2.3, §3, §4, §5, §6, and Appendix B.1.  A string is a list of bits
with `X[0]` first.  A state array of §3.1 is a function of its coordinates.  θ, π, and χ give
their output bit by bit, as the steps of Algorithms 1, 3, and 4 that range over all triples do,
and ρ and ι follow the loops of Algorithms 2 and 6.  The standard's `m mod n` takes integers,
negative ones among them, to the integer in `[0, n)`, which `modFin` returns as an index.
Compiled code computes `keccakP`, Algorithm 7 on state arrays, as `keccakPRun`, which holds the
state between rounds as the array of its bits; the `csimp` theorem `keccakP_eq_run` proves them
equal. -/

namespace Library.Hashing.Sha3.Spec

/-- A string of bits (§2.3), `X[0]` first. -/
abbrev Bits := List Bool

/-- `0^s` (§2.3). -/
def zeros (s : Nat) : Bits := List.replicate s false

/-- `Trunc_s(X)` (§2.3): the bits `X[0]` to `X[s - 1]`. -/
def trunc (s : Nat) (X : Bits) : Bits := X.take s

/-- `X ⊕ Y` (§2.3), for strings of equal length. -/
def xor (X Y : Bits) : Bits := List.zipWith (· ^^ ·) X Y

/-- `m mod n` (§2.3) as an index below `n`: the integer `r` with `0 ≤ r < n` for which `m - r` is
a multiple of `n`. -/
def modFin (m : Int) (n : Nat) (h : 0 < n) : Fin n :=
  ⟨(m % n).toNat, by
    have h0 : (0 : Int) < n := by exact_mod_cast h
    have := Int.emod_lt_of_pos m h0
    have := Int.emod_nonneg m (Int.ne_of_gt h0)
    omega⟩

/-! ## 3.1 State -/

/-- The lane size `w = 2^ℓ` of Table 1. -/
def laneSize (ℓ : Nat) : Nat := 2 ^ ℓ

/-- The width `b = 25 w` of Table 1. -/
def width (ℓ : Nat) : Nat := 25 * laneSize ℓ

theorem laneSize_pos (ℓ : Nat) : 0 < laneSize ℓ := Nat.two_pow_pos ℓ

/-- `m mod 5`. -/
def mod5 (m : Int) : Fin 5 := modFin m 5 (by decide)

/-- `m mod w`. -/
def modW (ℓ : Nat) (m : Int) : Fin (laneSize ℓ) := modFin m (laneSize ℓ) (laneSize_pos ℓ)

/-- A state array (§3.1): the bit `A[x, y, z]` for `0 ≤ x < 5`, `0 ≤ y < 5`, and `0 ≤ z < w`. -/
abbrev StateArray (ℓ : Nat) := Fin 5 → Fin 5 → Fin (laneSize ℓ) → Bool

/-- The state array of a string `S` of `b` bits (§3.1.2): `A[x, y, z] = S[w(5y + x) + z]`. -/
def toStateArray (ℓ : Nat) (S : Bits) : StateArray ℓ :=
  fun x y z => S.getD (laneSize ℓ * (5 * y.val + x.val) + z.val) false

/-- `Lane(i, j)` (§3.1.3): `A[i, j, 0] || A[i, j, 1] || … || A[i, j, w - 1]`. -/
def lane {ℓ : Nat} (A : StateArray ℓ) (i j : Fin 5) : Bits :=
  (List.finRange (laneSize ℓ)).map (A i j)

/-- `Plane(j)` (§3.1.3): `Lane(0, j) || Lane(1, j) || … || Lane(4, j)`. -/
def plane {ℓ : Nat} (A : StateArray ℓ) (j : Fin 5) : Bits :=
  (List.finRange 5).flatMap fun i => lane A i j

/-- The string of a state array (§3.1.3): `Plane(0) || Plane(1) || … || Plane(4)`. -/
def toBits {ℓ : Nat} (A : StateArray ℓ) : Bits := (List.finRange 5).flatMap (plane A)

/-! ## 3.2 Step mappings -/

/-- `θ(A)`, Algorithm 1. -/
def theta {ℓ : Nat} (A : StateArray ℓ) : StateArray ℓ :=
  -- Step 1.
  let C (x : Fin 5) (z : Fin (laneSize ℓ)) : Bool :=
    A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z
  -- Step 2.
  let D (x : Fin 5) (z : Fin (laneSize ℓ)) : Bool :=
    C (mod5 (x.val - 1 : Int)) z ^^ C (mod5 (x.val + 1 : Int)) (modW ℓ (z.val - 1 : Int))
  -- Step 3.
  fun x y z => A x y z ^^ D x z

/-- The lanes `(x, y)` of step 3 of Algorithm 2, in the order of `t` from 0 to 23, each with the
amount `(t + 1)(t + 2)/2` that step 3a subtracts from `z`.  Step 2 starts at `(1, 0)`, and step
3b moves to `(y, (2x + 3y) mod 5)`. -/
def rhoSteps : List (Fin 5 × Fin 5 × Nat) :=
  ((List.range 24).foldl
    (fun (acc : List (Fin 5 × Fin 5 × Nat) × Fin 5 × Fin 5) t =>
      let (steps, x, y) := acc
      (steps ++ [(x, y, (t + 1) * (t + 2) / 2)], y, mod5 (2 * x.val + 3 * y.val : Int)))
    ([], 1, 0)).1

/-- `ρ(A)`, Algorithm 2. -/
def rho {ℓ : Nat} (A : StateArray ℓ) : StateArray ℓ :=
  -- Step 1 sets lane (0, 0), and step 3a sets the lanes of `rhoSteps`.
  let A' : StateArray ℓ := fun x y z => if x = 0 ∧ y = 0 then A 0 0 z else false
  rhoSteps.foldl
    (fun A' (s : Fin 5 × Fin 5 × Nat) =>
      let (x, y, k) := s
      fun x' y' z => if x' = x ∧ y' = y then A x y (modW ℓ (z.val - k : Int)) else A' x' y' z)
    A'

/-- `π(A)`, Algorithm 3. -/
def pi {ℓ : Nat} (A : StateArray ℓ) : StateArray ℓ :=
  fun x y z => A (mod5 (x.val + 3 * y.val : Int)) x z

/-- `χ(A)`, Algorithm 4.  The product of two bits is their conjunction. -/
def chi {ℓ : Nat} (A : StateArray ℓ) : StateArray ℓ :=
  fun x y z =>
    A x y z ^^ ((A (mod5 (x.val + 1 : Int)) y z ^^ true) && A (mod5 (x.val + 2 : Int)) y z)

/-- `rc(t)`, Algorithm 5. -/
def rc (t : Int) : Bool :=
  let k := (t % 255).toNat
  -- Step 1.
  if k = 0 then true
  else
    -- Steps 2 and 3.
    let R := (List.range k).foldl
      (fun (R : Bits) _ =>
        let R := false :: R
        let R := R.set 0 (R.getD 0 false ^^ R.getD 8 false)
        let R := R.set 4 (R.getD 4 false ^^ R.getD 8 false)
        let R := R.set 5 (R.getD 5 false ^^ R.getD 8 false)
        let R := R.set 6 (R.getD 6 false ^^ R.getD 8 false)
        trunc 8 R)
      [true, false, false, false, false, false, false, false]
    -- Step 4.
    R.getD 0 false

/-- The lane value `RC` of Algorithm 6, steps 2 and 3. -/
def roundConstant (ℓ : Nat) (ir : Int) : Bits :=
  (List.range (ℓ + 1)).foldl
    (fun RC (j : Nat) => RC.set (2 ^ j - 1) (rc ((j : Int) + 7 * ir))) (zeros (laneSize ℓ))

/-- Steps 1 and 4 of Algorithm 6 for the lane value `RC`. -/
def addRoundConstant {ℓ : Nat} (RC : Bits) (A : StateArray ℓ) : StateArray ℓ :=
  fun x y z => if x = 0 ∧ y = 0 then A 0 0 z ^^ RC.getD z.val false else A x y z

/-- `ι(A, i_r)`, Algorithm 6. -/
def iota {ℓ : Nat} (A : StateArray ℓ) (ir : Int) : StateArray ℓ :=
  addRoundConstant (roundConstant ℓ ir) A

/-! ## 3.3 KECCAK-p[b, n_r] -/

/-- `Rnd(A, i_r) = ι(χ(π(ρ(θ(A)))), i_r)`. -/
def rnd {ℓ : Nat} (A : StateArray ℓ) (ir : Int) : StateArray ℓ :=
  iota (chi (pi (rho (theta A)))) ir

/-- The bits of a state array in the order of §3.1.2, `T[w(5y + x) + z] = A[x, y, z]`, in which
`keccakPRun` holds the state between rounds. -/
def table {ℓ : Nat} (A : StateArray ℓ) : Array Bool :=
  Array.ofFn fun i : Fin (width ℓ) =>
    A ⟨i.val / laneSize ℓ % 5, Nat.mod_lt _ (by decide)⟩
      ⟨i.val / laneSize ℓ / 5, by
        have := i.isLt
        unfold width at this
        have h : i.val / laneSize ℓ < 25 :=
          (Nat.div_lt_iff_lt_mul (laneSize_pos ℓ)).mpr (by omega)
        omega⟩
      ⟨i.val % laneSize ℓ, Nat.mod_lt _ (laneSize_pos ℓ)⟩

/-- The state array whose bits a `table` holds. -/
def ofTable {ℓ : Nat} (T : Array Bool) : StateArray ℓ :=
  fun x y z => T.getD (laneSize ℓ * (5 * y.val + x.val) + z.val) false

/-- `KECCAK-p[b, n_r](S)`, Algorithm 7, for `b = 25 · 2^ℓ`. -/
def keccakP (ℓ nr : Nat) (S : Bits) : Bits :=
  -- Step 1.
  let A := toStateArray ℓ S
  -- Step 2: for `i_r` from `12 + 2ℓ - n_r` to `12 + 2ℓ - 1`.
  let A := (List.range nr).foldl (fun A (k : Nat) => rnd A ((12 + 2 * ℓ : Int) - nr + k)) A
  -- Steps 3 and 4.
  toBits A

/-- `keccakP` as compiled code computes it, by `keccakP_eq_run`.  The state between rounds is its
`table`, and each round computes `RC` once, so that a round reads each bit of the round before
from an array. -/
def keccakPRun (ℓ nr : Nat) (S : Bits) : Bits :=
  let T := (List.range nr).foldl
    (fun T (k : Nat) =>
      let RC := roundConstant ℓ ((12 + 2 * ℓ : Int) - nr + k)
      table (addRoundConstant RC (chi (pi (rho (theta (ofTable (ℓ := ℓ) T)))))))
    (table (toStateArray ℓ S))
  toBits (ofTable (ℓ := ℓ) T)

/-- A table determines its state array. -/
theorem ofTable_table {ℓ : Nat} (A : StateArray ℓ) : ofTable (table A) = A := by
  funext x y z
  have hw := laneSize_pos ℓ
  have hz := z.isLt
  have hx := x.isLt
  have hy := y.isLt
  have hi : laneSize ℓ * (5 * y.val + x.val) + z.val < width ℓ := by
    have h := Nat.mul_le_mul_left (laneSize ℓ) (show 5 * y.val + x.val + 1 ≤ 25 by omega)
    rw [Nat.mul_add_one] at h
    unfold width
    omega
  have hdiv : (laneSize ℓ * (5 * y.val + x.val) + z.val) / laneSize ℓ = 5 * y.val + x.val := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hz, Nat.zero_add]
  simp only [ofTable, table, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, dite_true,
    Option.getD_some]
  congr
  · rw [hdiv]; omega
  · rw [hdiv]; omega
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]

/-- Compiled code computes `keccakP` as `keccakPRun`. -/
@[csimp] theorem keccakP_eq_run : @keccakP = @keccakPRun := by
  funext ℓ nr S
  have key : ∀ (L : List Nat) (A : StateArray ℓ),
      ofTable (L.foldl (fun T (k : Nat) =>
          let RC := roundConstant ℓ ((12 + 2 * ℓ : Int) - nr + k)
          table (addRoundConstant RC (chi (pi (rho (theta (ofTable (ℓ := ℓ) T)))))))
        (table A)) = L.foldl (fun A (k : Nat) => rnd A ((12 + 2 * ℓ : Int) - nr + k)) A := by
    intro L
    induction L with
    | nil => exact ofTable_table
    | cons k L ih =>
      intro A
      simp only [List.foldl_cons, ofTable_table]
      exact ih _
  simp only [keccakP, keccakPRun]
  rw [key]

/-! ## 4 Sponge construction -/

/-- Steps 8 to 10 of Algorithm 8 from the state `S` and the output `Z`, with at most `k` passes.
For `0 < r` and an `f` whose strings have at least `r` bits, a pass appends `r` bits, so
`d / r + 1` passes reach `d ≤ len(Z)`. -/
def squeeze (f : Bits → Bits) (r d : Nat) : Nat → Bits → Bits → Bits
  | 0, _, Z => trunc d Z
  | k + 1, S, Z =>
    -- Step 8.
    let Z := Z ++ trunc r S
    -- Steps 9 and 10.
    if d ≤ Z.length then trunc d Z else squeeze f r d k (f S) Z

/-- `SPONGE[f, pad, r](N, d)`, Algorithm 8, for an `f` on strings of `b` bits. -/
def sponge (f : Bits → Bits) (pad : Nat → Nat → Bits) (b r : Nat) (N : Bits) (d : Nat) : Bits :=
  -- Steps 1 to 4.
  let P := N ++ pad r N.length
  let n := P.length / r
  let c := b - r
  let block (i : Nat) : Bits := (P.drop (i * r)).take r
  -- Steps 5 and 6.
  let S := (List.range n).foldl (fun S i => f (xor S (block i ++ zeros c))) (zeros b)
  -- Steps 7 to 10.
  squeeze f r d (d / r + 1) S []

/-! ## 5 KECCAK -/

/-- `pad10*1(x, m)`, Algorithm 9. -/
def pad101 (x m : Nat) : Bits :=
  let j := ((-(m : Int) - 2) % (x : Int)).toNat
  [true] ++ zeros j ++ [true]

/-- `KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 - c](N, d)` (§5.2). -/
def keccak (c : Nat) (N : Bits) (d : Nat) : Bits :=
  sponge (keccakP 6 24) pad101 1600 (1600 - c) N d

/-! ## 6 SHA-3 functions -/

/-- `SHA3-224(M) = KECCAK[448](M || 01, 224)` (§6.1). -/
def sha3_224 (M : Bits) : Bits := keccak 448 (M ++ [false, true]) 224

/-- `SHA3-256(M) = KECCAK[512](M || 01, 256)` (§6.1). -/
def sha3_256 (M : Bits) : Bits := keccak 512 (M ++ [false, true]) 256

/-- `SHA3-384(M) = KECCAK[768](M || 01, 384)` (§6.1). -/
def sha3_384 (M : Bits) : Bits := keccak 768 (M ++ [false, true]) 384

/-- `SHA3-512(M) = KECCAK[1024](M || 01, 512)` (§6.1). -/
def sha3_512 (M : Bits) : Bits := keccak 1024 (M ++ [false, true]) 512

/-- `SHAKE128(M, d) = KECCAK[256](M || 1111, d)` (§6.2). -/
def shake128 (M : Bits) (d : Nat) : Bits := keccak 256 (M ++ [true, true, true, true]) d

/-- `SHAKE256(M, d) = KECCAK[512](M || 1111, d)` (§6.2). -/
def shake256 (M : Bits) (d : Nat) : Bits := keccak 512 (M ++ [true, true, true, true]) d

/-- `RawSHAKE128(J, d) = KECCAK[256](J || 11, d)` (§6.3). -/
def rawShake128 (J : Bits) (d : Nat) : Bits := keccak 256 (J ++ [true, true]) d

/-- `RawSHAKE256(J, d) = KECCAK[512](J || 11, d)` (§6.3). -/
def rawShake256 (J : Bits) (d : Nat) : Bits := keccak 512 (J ++ [true, true]) d

/-! ## B.1 Conversion functions -/

/-- The value of a hexadecimal digit (Appendix B): `0` to `9`, and `A` to `F` for ten to fifteen.
Lower-case letters, which the CAVP files use, have the same values, and every other character has
the value 0. -/
def hexValue (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else 0

/-- The hexadecimal digit of a value below 16 (Appendix B). -/
def hexDigit (v : Nat) : Char := "0123456789ABCDEF".toList.getD v '0'

/-- `h2b(H, n)`, Algorithm 10, for a string `H` of `2m` hexadecimal digits and `n ≤ 8m`. -/
def h2b (H : String) (n : Nat) : Bits :=
  let digits := H.toList.map hexValue
  let m := digits.length / 2
  -- Steps 2 and 3: `h_i = 16 H_{2i} + H_{2i+1}`, whose bit `b_{ij}` of value `2^j` is `T[8i + j]`.
  let T := (List.range m).flatMap fun i =>
    let h := 16 * digits.getD (2 * i) 0 + digits.getD (2 * i + 1) 0
    (List.range 8).map fun j => h.testBit j
  -- Step 4.
  trunc n T

/-- `b2h(S)`, Algorithm 11. -/
def b2h (S : Bits) : String :=
  -- Steps 1 and 2.
  let n := S.length
  let T := S ++ zeros ((8 - n % 8) % 8)
  let m := (n + 7) / 8
  -- Steps 3 and 4: `h_i` has the bit `T[8i + j]` of value `2^j`.
  let h (i : Nat) : Nat :=
    (List.range 8).foldl (fun acc j => acc + if T.getD (8 * i + j) false then 2 ^ j else 0) 0
  -- Step 5.
  String.ofList ((List.range m).flatMap fun i => [hexDigit (h i / 16), hexDigit (h i % 16)])

/-! ## Checks of the transcription -/

/-- The offsets of Table 2, the amounts of `rhoSteps`, by lane. -/
theorem rhoSteps_table2 : rhoSteps = [
    (1, 0, 1), (0, 2, 3), (2, 1, 6), (1, 2, 10), (2, 3, 15), (3, 3, 21), (3, 0, 28), (0, 1, 36),
    (1, 3, 45), (3, 1, 55), (1, 4, 66), (4, 4, 78), (4, 0, 91), (0, 3, 105), (3, 4, 120),
    (4, 3, 136), (3, 2, 153), (2, 2, 171), (2, 0, 190), (0, 4, 210), (4, 2, 231), (2, 4, 253),
    (4, 1, 276), (1, 1, 300)] := by
  decide

/-- Step 3 of Algorithm 2 sets each lane other than (0, 0) exactly once and never sets (0, 0). -/
theorem rhoSteps_lanes :
    (rhoSteps.map fun s => (s.1, s.2.1)).Nodup ∧ (∀ s ∈ rhoSteps, ¬(s.1 = 0 ∧ s.2.1 = 0)) ∧
      ∀ x ∈ List.finRange 5, ∀ y ∈ List.finRange 5,
        (x = 0 ∧ y = 0) ∨ (x, y) ∈ rhoSteps.map fun s => (s.1, s.2.1) := by
  rw [rhoSteps_table2]
  decide

/-- The alternate definition of SHAKE128 (§6.3). -/
theorem shake128_eq (M : Bits) (d : Nat) : shake128 M d = rawShake128 (M ++ [true, true]) d := by
  simp [shake128, rawShake128]

/-- The alternate definition of SHAKE256 (§6.3). -/
theorem shake256_eq (M : Bits) (d : Nat) : shake256 M d = rawShake256 (M ++ [true, true]) d := by
  simp [shake256, rawShake256]

end Library.Hashing.Sha3.Spec
