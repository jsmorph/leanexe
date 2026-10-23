--#--
import Library.Hashing.Sha2.Spec.HashAlgorithms
set_option autoImplicit true
--#--

namespace SHS --#
/-!
These words were obtained by taking the first sixty-four bits of the fractional parts
of the square roots of the first eight prime numbers.

### 5.3.6 SHA-512/t

"SHA-512/$t$" is the general name for a $t$-bit hash function based on SHA-512 whose
output is truncated to $t$ bits. Each hash function requires a distinct initial hash
value. This section provides a procedure for determining the initial value for
SHA-512/$t$ for a given value of $t$.

For SHA-512/$t$, $t$ is any positive integer without a leading zero such that
$t < 512$, and $t$ is not 384. For example: $t$ is 256, but not 0256, and
"SHA-512/$t$" is "SHA-512/256" (an 11 character long ASCII string), which is equivalent
to `53 48 41 2D 35 31 32 2F 32 35 36` in hexadecimal.

The initial hash value $H^{(0)}$ for SHA-512/$t$ is generated as follows: each word
of the SHA-512 IV (§5.3.5) is XOR-ed with $\texttt{a5a5a5a5a5a5a5a5}$ to obtain a
temporary IV $H^{(0)\prime\prime}$, and $H^{(0)}$ is then
SHA-512("SHA-512/$t$") using $H^{(0)\prime\prime}$ as the IV.
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.3.6: generic SHA-512/t IV generator. -/ --#
def H0_t (t : {t : Nat // 0 < t ∧ t < 512 ∧ t ≠ 384}) : HashValue :=
  -- Build H'' by XOR-ing each word of the SHA-512 IV with 0xa5a5a5a5a5a5a5a5.
  let H'' := H0_512.map (· ⊕ (0xa5a5a5a5a5a5a5a5 : Word))
  -- Run SHA-512 on the ASCII string "SHA-512/t" using H'' as the initial IV.
  let M := Message.fromString s!"SHA-512/{t}"
  let blocks := parse (pad M)
  blocks.foldl compress H''

end SHA512 --#

/-!
SHA-512/224 ($t = 224$) and SHA-512/256 ($t = 256$) are **approved** hash algorithms.
Other SHA-512/$t$ hash algorithms with different $t$ values may be specified in
[SP 800-107] in the future as the need arises. Below are the IVs for SHA-512/224
and SHA-512/256.

#### 5.3.6.1 SHA-512/224

For SHA-512/224, the initial hash value, $H^{(0)}$, shall consist of the
following eight 64-bit words, in hex:
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.3.6.1: SHA-512/224 initial hash value (precomputed via `H0_t 224`). -/ --#
def H0_512_224 : HashValue := #v[
  0x8C3D37C819544DA2, 0x73E1996689DCD4D6, 0x1DFAB7AE32FF9C82, 0x679DD514582F9FCF,
  0x0F6D2B697BD44DA8, 0x77E36F7304C48942, 0x3F9D85A86A1D36C8, 0x1112E6AD91D692A1
]

end SHA512 --#

/-!
These words were obtained by executing the *SHA-512/t IV Generation Function* with $t = 224$.
-/

namespace SHA512 --#

theorem H0_512_224_correct : H0_t 224 = H0_512_224
--#--
  := by decide +kernel
--#--

end SHA512 --#

/-!
#### 5.3.6.2 SHA-512/256

For SHA-512/256, the initial hash value, $H^{(0)}$, shall consist of the
following eight 64-bit words, in hex:
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.3.6.2: SHA-512/256 initial hash value (precomputed via `H0_t 256`). -/ --#
def H0_512_256 : HashValue := #v[
  0x22312194FC2BF72C, 0x9F555FA3C84C64C2, 0x2393B86B6F53B151, 0x963877195940EABD,
  0x96283EE2A88EFFE3, 0xBE5E1E2553863992, 0x2B0199FC2C85B8AA, 0x0EB72DDC81C52CA2
]

end SHA512 --#

/-!
These words were obtained by executing the *SHA-512/t IV Generation Function* with $t = 256$.
-/

namespace SHA512 --#

theorem H0_512_256_correct : H0_t 256 = H0_512_256
--#--
  := by decide +kernel
--#--

end SHA512 --#

end SHS --#
