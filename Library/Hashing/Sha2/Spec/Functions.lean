--#--
import Library.Hashing.Sha2.Spec.Notation
set_option autoImplicit true
--#--

namespace SHS --#
/-!
# 4. FUNCTIONS AND CONSTANTS

## 4.1 Functions

This section defines the functions that are used by each of the algorithms. Although
the SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256 algorithms all use
similar functions, their descriptions are separated into sections for SHA-224 and
SHA-256 (Sec. 4.1.2) and for SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (Sec. 4.1.3),
since the input and output for these functions are words of different sizes. Each of
the algorithms include $Ch(x, y, z)$ and $Maj(x, y, z)$ functions; the exclusive-OR
operation ($\oplus$) in these functions may be replaced by a bitwise OR operation
($\vee$) and produce identical results.
-/

/-!
### 4.1.1 SHA-1 Functions

SHA-1 uses a sequence of logical functions, $f_0, f_1, \ldots, f_{79}$. Each function
$f_t$, where $0 \leq t \leq 79$, operates on three 32-bit words, $x$, $y$, and $z$, and
produces a 32-bit word as output. The function $f_t(x, y, z)$ is defined as follows:
-/

namespace SHA1 --#

/-- A SHA-1 word: 32 bits. -/ --#
scoped notation "Word" => BitVec 32 --#
/-- A SHA-1 message block: 16 words (512 bits). -/ --#
scoped notation "Block" => Vector (BitVec 32) 16 --#
/-- A SHA-1 hash value: 5 words (160 bits). -/ --#
scoped notation "HashValue" => Vector (BitVec 32) 5 --#
/-- A SHA-1 message schedule: 80 words. -/ --#
scoped notation "Schedule" => Vector (BitVec 32) 80 --#

/-! <!-- eqn:4.1 --> -/

/-- FIPS-180-4 §4.1.1: SHA-1 logical function `f_t(x, y, z)`. -/ --#
def f (t : Nat) (x y z : Word) : Word :=
  if t ≤ 19 then /- Ch(x, y, z) -/ (x ∧ y) ⊕ (¬x ∧ z)
  else if t ≤ 39 then /- Parity(x, y, z) -/ x ⊕ y ⊕ z
  else if t ≤ 59 then /- Maj(x, y, z) -/ (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)
  else /- Parity(x, y, z) -/ x ⊕ y ⊕ z

end SHA1 --#

/-!
### 4.1.2 SHA-224 and SHA-256 Functions

SHA-224 and SHA-256 both use six logical functions, where *each function operates on
32-bit words*, which are represented as $x$, $y$, and $z$. The result of each function
is a new 32-bit word.
-/

namespace SHA256 --#

/-- A SHA-256 word: 32 bits. -/ --#
scoped notation "Word" => BitVec 32 --#
/-- A SHA-256 message block: 16 words (512 bits). -/ --#
scoped notation "Block" => Vector (BitVec 32) 16 --#
/-- A SHA-256 hash value: 8 words (256 bits). -/ --#
scoped notation "HashValue" => Vector (BitVec 32) 8 --#
/-- A SHA-256 message schedule: 64 words. -/ --#
scoped notation "Schedule" => Vector (BitVec 32) 64 --#

/-! <!-- eqn:4.2 --> -/

/-- FIPS-180-4 §4.1.2 (4.2): `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/ --#
def Ch (x y z : Word) : Word := (x ∧ y) ⊕ (¬x ∧ z)

/-! <!-- eqn:4.3 --> -/

/-- FIPS-180-4 §4.1.2 (4.3): `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/ --#
def Maj (x y z : Word) : Word := (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)

/-! <!-- eqn:4.4 --> -/

/-- FIPS-180-4 §4.1.2 (4.4): `Σ₀⁽²⁵⁶⁾(x) = ROTR² x ⊕ ROTR¹³ x ⊕ ROTR²² x`. -/ --#
def bigSigma0 (x : Word) : Word := ROTR 2 x ⊕ ROTR 13 x ⊕ ROTR 22 x

/-! <!-- eqn:4.5 --> -/

/-- FIPS-180-4 §4.1.2 (4.5): `Σ₁⁽²⁵⁶⁾(x) = ROTR⁶ x ⊕ ROTR¹¹ x ⊕ ROTR²⁵ x`. -/ --#
def bigSigma1 (x : Word) : Word := ROTR 6 x ⊕ ROTR 11 x ⊕ ROTR 25 x

/-! <!-- eqn:4.6 --> -/

/-- FIPS-180-4 §4.1.2 (4.6): `σ₀⁽²⁵⁶⁾(x) = ROTR⁷ x ⊕ ROTR¹⁸ x ⊕ SHR³ x`. -/ --#
def smallSigma0 (x : Word) : Word := ROTR 7 x ⊕ ROTR 18 x ⊕ SHR 3 x

/-! <!-- eqn:4.7 --> -/

/-- FIPS-180-4 §4.1.2 (4.7): `σ₁⁽²⁵⁶⁾(x) = ROTR¹⁷ x ⊕ ROTR¹⁹ x ⊕ SHR¹⁰ x`. -/ --#
def smallSigma1 (x : Word) : Word := ROTR 17 x ⊕ ROTR 19 x ⊕ SHR 10 x

end SHA256 --#

/-!
### 4.1.3 SHA-384, SHA-512, SHA-512/224 and SHA-512/256 Functions

SHA-384, SHA-512, SHA-512/224 and SHA-512/256 use six logical functions, where *each
function operates on 64-bit words*, which are represented as $x$, $y$, and $z$. The
result of each function is a new 64-bit word.
-/

namespace SHA512 --#

/-- A SHA-512 word: 64 bits. -/ --#
scoped notation "Word" => BitVec 64 --#
/-- A SHA-512 message block: 16 words (1024 bits). -/ --#
scoped notation "Block" => Vector (BitVec 64) 16 --#
/-- A SHA-512 hash value: 8 words (512 bits). -/ --#
scoped notation "HashValue" => Vector (BitVec 64) 8 --#
/-- A SHA-512 message schedule: 80 words. -/ --#
scoped notation "Schedule" => Vector (BitVec 64) 80 --#

/-! <!-- eqn:4.8 --> -/

/-- FIPS-180-4 §4.1.3 (4.8): `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)` (64-bit). -/ --#
def Ch (x y z : Word) : Word := (x ∧ y) ⊕ (¬x ∧ z)

/-! <!-- eqn:4.9 --> -/

/-- FIPS-180-4 §4.1.3 (4.9): `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)` (64-bit). -/ --#
def Maj (x y z : Word) : Word := (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)

/-! <!-- eqn:4.10 --> -/

/-- FIPS-180-4 §4.1.3 (4.10): `Σ₀⁽⁵¹²⁾(x) = ROTR²⁸ x ⊕ ROTR³⁴ x ⊕ ROTR³⁹ x`. -/ --#
def bigSigma0 (x : Word) : Word := ROTR 28 x ⊕ ROTR 34 x ⊕ ROTR 39 x

/-! <!-- eqn:4.11 --> -/

/-- FIPS-180-4 §4.1.3 (4.11): `Σ₁⁽⁵¹²⁾(x) = ROTR¹⁴ x ⊕ ROTR¹⁸ x ⊕ ROTR⁴¹ x`. -/ --#
def bigSigma1 (x : Word) : Word := ROTR 14 x ⊕ ROTR 18 x ⊕ ROTR 41 x

/-! <!-- eqn:4.12 --> -/

/-- FIPS-180-4 §4.1.3 (4.12): `σ₀⁽⁵¹²⁾(x) = ROTR¹ x ⊕ ROTR⁸ x ⊕ SHR⁷ x`. -/ --#
def smallSigma0 (x : Word) : Word := ROTR 1 x ⊕ ROTR 8 x ⊕ SHR 7 x

/-! <!-- eqn:4.13 --> -/

/-- FIPS-180-4 §4.1.3 (4.13): `σ₁⁽⁵¹²⁾(x) = ROTR¹⁹ x ⊕ ROTR⁶¹ x ⊕ SHR⁶ x`. -/ --#
def smallSigma1 (x : Word) : Word := ROTR 19 x ⊕ ROTR 61 x ⊕ SHR 6 x

end SHA512 --#

/-!
## 4.2 Constants

### 4.2.1 SHA-1 Constants

SHA-1 uses a sequence of eighty constant 32-bit words, $K_0, K_1, \ldots, K_{79}$,
which are given by
-/

namespace SHA1 --#

/-! <!-- eqn:4.14 --> -/

/-- FIPS-180-4 §4.2.1 (4.14): SHA-1 round constants `K_t`. -/ --#
def K (t : Nat) : Word :=
  if t ≤ 19 then 0x5a827999
  else if t ≤ 39 then 0x6ed9eba1
  else if t ≤ 59 then 0x8f1bbcdc
  else 0xca62c1d6

end SHA1 --#

/-!
### 4.2.2 SHA-224 and SHA-256 Constants

SHA-224 and SHA-256 use the same sequence of sixty-four constant 32-bit words,
$K_0^{\{256\}}, K_1^{\{256\}}, \ldots, K_{63}^{\{256\}}$. These words represent the first
thirty-two bits of the fractional parts of the cube roots of the first sixty-four
prime numbers. In hex, these constant words are (from left to right)
-/

namespace SHA256 --#

/-- FIPS-180-4 §4.2.2: SHA-224/SHA-256 round constants `K⁽²⁵⁶⁾_t`. -/ --#
def K : Schedule := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

end SHA256 --#

/-!
### 4.2.3 SHA-384, SHA-512, SHA-512/224 and SHA-512/256 Constants

SHA-384, SHA-512, SHA-512/224 and SHA-512/256 use the same sequence of eighty constant
64-bit words, $K_0^{\{512\}}, K_1^{\{512\}}, \ldots, K_{79}^{\{512\}}$. These words
represent the first sixty-four bits of the fractional parts of the cube roots of the
first eighty prime numbers. In hex, these constant words are (from left to right)
-/

namespace SHA512 --#

/-- FIPS-180-4 §4.2.3: SHA-384/SHA-512/SHA-512/t round constants `K⁽⁵¹²⁾_t`. -/ --#
def K : Schedule := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

end SHA512 --#

end SHS --#
