--#--
import Library.Hashing.Sha2.Spec.Preprocessing
set_option autoImplicit true

-- Bounds discharge for `Vector` accessors used inside the `for h : t in [a:b] do`
-- ranges below.  Range membership (`Std.Legacy.Range`) carries `.lower` / `.upper`
-- accessors that pin `start ≤ t < stop`; we extract them and let `grind` close
-- the ensuing arithmetic goal (e.g. `t < 80`, `t - 16 < 80`).
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)
              | (grind [Nat.and_le_right])))
--#--

namespace SHS --#
/-!
# 6. SECURE HASH ALGORITHMS

In the following sections, the hash algorithms are not described in ascending order of
size. SHA-256 is described before SHA-224 because the specification for SHA-224 is
identical to SHA-256, except that different initial hash values are used, and the final
hash value is truncated to 224 bits for SHA-224. The same is true for SHA-512, SHA-384,
SHA-512/224 and SHA-512/256, except that the final hash value is truncated to 224 bits
for SHA-512/224, 256 bits for SHA-512/256 or 384 bits for SHA-384.

For each of the secure hash algorithms, there may exist alternate computation methods
that yield identical results; one example is the alternative SHA-1 computation
described in Sec. 6.1.3. Such alternate methods may be implemented in conformance to
this standard.

## 6.1 SHA-1

SHA-1 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The algorithm uses 1) a message schedule of eighty 32-bit words,
2) five working variables of 32 bits each, and 3) a hash value of five 32-bit words.
The final result of SHA-1 is a 160-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{79}$. The five
working variables are labeled $a$, $b$, $c$, $d$, and $e$. The words of the hash value
are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_4^{(i)}$, which will hold the initial hash
value, $H^{(0)}$, replaced by each successive intermediate hash value (after each
message block is processed), $H^{(i)}$, and ending with the final hash value,
$H^{(N)}$. SHA-1 also uses a single temporary word, $T$.

### 6.1.1 SHA-1 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.1.
2. The message is padded and parsed as specified in Section 5.

### 6.1.2 SHA-1 Hash Computation

The SHA-1 hash computation uses functions and constants previously defined in
Sec. 4.1.1 and Sec. 4.2.1, respectively. Addition ($+$) is performed modulo $2^{32}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order, using
the following steps:

-/

namespace SHA1 --#

/-- FIPS-180-4 §6.1.2 step 1: SHA-1 message schedule (16-word block → 80 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 80 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 79: W_t = ROTL^1(W_{t-3} ⊕ W_{t-8} ⊕ W_{t-14} ⊕ W_{t-16})
  for h : t in [16:80] do
    W[t] := ROTL 1 (W[t-3] ⊕ W[t-8] ⊕ W[t-14] ⊕ W[t-16])
  W

/-!  -/

/-- FIPS-180-4 §6.1.2 steps 2-4: SHA-1 block compression updating the 5-word state. -/ --#
def compress (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. Prepare the message schedule {W_t}
  let W := schedule M
  -- Step 2. Initialize the five working variables a, b, c, d, e with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let T := ROTL 5 a + f t b c d + e + K t + W[t]
    e := d
    d := c
    c := ROTL 30 b
    b := a
    a := T
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[a + H[0], b + H[1], c + H[2], d + H[3], e + H[4]]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 160-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)}$$
-/

/-- FIPS-180-4 §6.1: SHA-1 hash of a message `M` (length < 2⁶⁴ bits) → 160-bit digest. -/ --#
@[nolint unusedArguments] --#
def sha1 (M : Message) (_h : M.length < 2 ^ 64) : Digest 160 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4]

end SHA1 --#

/-!
### 6.1.3 Alternate Method for Computing a SHA-1 Message Digest

The SHA-1 hash computation method described in Sec. 6.1.2 assumes that the message
schedule $W_0, W_1, \ldots, W_{79}$ is implemented as an array of eighty 32-bit words.
This is efficient from the standpoint of the minimization of execution time, since the
addresses of $W_{t-3}, \ldots, W_{t-16}$ in step (2) of Sec. 6.1.2 are easily computed.

However, if memory is limited, an alternative is to regard $\{W_t\}$ as a circular
queue that may be implemented using an array of sixteen 32-bit words,
$W_0, W_1, \ldots, W_{15}$. The alternate method that is described in this section
yields the same message digest as the SHA-1 computation method described in Sec. 6.1.2.
Although this alternate method saves sixty-four 32-bit words of storage, it is likely
to lengthen the execution time due to the increased complexity of the address
computations for the $\{W_t\}$ in step (3).

For this alternate SHA-1 method, let $MASK = \texttt{0000000f}$ (in hex). As in
Sec. 6.1.1, addition is performed modulo $2^{32}$. Assuming that the preprocessing as
described in Sec. 6.1.1 has been performed, the processing of $M^{(i)}$ is as follows:

-/

namespace SHA1 --#

/-- FIPS-180-4 §6.1.3: SHA-1 alternate compression using a 16-word circular schedule. -/ --#
def compress_alt (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. For t = 0 to 15: W_t = M_t^(i).  Note: the SHA-1 alternate method's
  -- circular schedule has only 16 words; we therefore use `Block` (size 16) here
  -- in place of the 80-word `Schedule` used by the standard method.
  let mut W : Block := M
  -- Step 2. Initialize the five working variables a, b, c, d, e with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let s := t &&& 0xf
    if t ≥ 16 then
      W[s] := ROTL 1 (W[(s+13) % 16] ⊕ W[(s+8) % 16] ⊕ W[(s+2) % 16] ⊕ W[s])
    let T := ROTL 5 a + f t b c d + e + K t + W[s]
    e := d
    d := c
    c := ROTL 30 b
    b := a
    a := T
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[a + H[0], b + H[1], c + H[2], d + H[3], e + H[4]]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 160-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)}$$
-/

/-- FIPS-180-4 §6.1.3: SHA-1 hash via the alternate (circular schedule) method. -/ --#
@[nolint unusedArguments] --#
def sha1_alt (M : Message) (_h : M.length < 2 ^ 64) : Digest 160 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress_alt H0
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4]

/-!
The FIPS 180-4 §6.1.3 prose claims that this alternate method yields the
same digest as the standard method (Sec. 6.1.2).  That equivalence is
**not formalized in this spec.**  `SHA1.sha1_alt` is provided as a
literate translation of the FIPS text and is not consumed by any other
definition or theorem; only the standard `SHA1.sha1` (above) is part of
the verified pipeline.
-/

end SHA1 --#

/-!
## 6.2 SHA-256

SHA-256 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The algorithm uses 1) a message schedule of sixty-four 32-bit
words, 2) eight working variables of 32 bits each, and 3) a hash value of eight 32-bit
words. The final result of SHA-256 is a 256-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{63}$. The eight
working variables are labeled $a$, $b$, $c$, $d$, $e$, $f$, $g$, and $h$. The words of
the hash value are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_7^{(i)}$, which will hold
the initial hash value, $H^{(0)}$, replaced by each successive intermediate hash value
(after each message block is processed), $H^{(i)}$, and ending with the final hash
value, $H^{(N)}$. SHA-256 also uses two temporary words, $T_1$ and $T_2$.

### 6.2.1 SHA-256 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.3.
2. The message is padded and parsed as specified in Section 5.

### 6.2.2 SHA-256 Hash Computation

The SHA-256 hash computation uses functions and constants previously defined in
Sec. 4.1.2 and Sec. 4.2.2, respectively. Addition ($+$) is performed modulo $2^{32}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order,
using the following steps:

-/

namespace SHA256 --#

/-- FIPS-180-4 §6.2.2 step 1: SHA-256 message schedule (16-word block → 64 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 64 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 63: W_t = σ_1^(256)(W_{t-2}) + W_{t-7} + σ_0^(256)(W_{t-15}) + W_{t-16}
  for h : t in [16:64] do
    W[t] := smallSigma1 W[t-2] + W[t-7] + smallSigma0 W[t-15] + W[t-16]
  W

/-!  -/

/-- FIPS-180-4 §6.2.2 steps 2-4: SHA-256 block compression updating the 8-word state. -/ --#
def compress (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. Prepare the message schedule {W_t}
  let W := schedule M
  -- Step 2. Initialize the eight working variables a..h with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  let mut f := H[5]
  let mut g := H[6]
  let mut h := H[7]
  -- Step 3. For t = 0 to 63
  for h : t in [0:64] do
    let T1 := h + bigSigma1 e + Ch e f g + K[t] + W[t]
    let T2 := bigSigma0 a + Maj a b c
    h := g
    g := f
    f := e
    e := d + T1
    d := c
    c := b
    b := a
    a := T1 + T2
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[
    a + H[0], b + H[1], c + H[2], d + H[3],
    e + H[4], f + H[5], g + H[6], h + H[7]
  ]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 256-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \|
  H_4^{(N)} \| H_5^{(N)} \| H_6^{(N)} \| H_7^{(N)}$$
-/

/-- FIPS-180-4 §6.2: SHA-256 hash of a message `M` (length < 2⁶⁴ bits) → 256-bit digest. -/ --#
@[nolint unusedArguments] --#
def sha256 (M : Message) (_h : M.length < 2 ^ 64) : Digest 256 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_256
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6] ++ H[7]

end SHA256 --#

/-!
## 6.3 SHA-224

SHA-224 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{64}$. The function is defined in the exact same manner as SHA-256
(Section 6.2), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.2; and
2. The 224-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 224 bits:

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)} \| H_6^{(N)}$$
-/

namespace SHA256 --#

/-- FIPS-180-4 §6.3: SHA-224 hash — SHA-256 with `H0_224` IV, truncated to 224 bits. -/ --#
@[nolint unusedArguments] --#
def sha224 (M : Message) (_h : M.length < 2 ^ 64) : Digest 224 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_224
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6]

end SHA256 --#

/-!
## 6.4 SHA-512

SHA-512 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm uses 1) a message schedule of eighty 64-bit words,
2) eight working variables of 64 bits each, and 3) a hash value of eight 64-bit words.
The final result of SHA-512 is a 512-bit message digest.

The words of the message schedule are labeled $W_0, W_1, \ldots, W_{79}$. The eight
working variables are labeled $a$, $b$, $c$, $d$, $e$, $f$, $g$, and $h$. The words of
the hash value are labeled $H_0^{(i)}, H_1^{(i)}, \ldots, H_7^{(i)}$, which will hold
the initial hash value, $H^{(0)}$, replaced by each successive intermediate hash value
(after each message block is processed), $H^{(i)}$, and ending with the final hash
value, $H^{(N)}$. SHA-512 also uses two temporary words, $T_1$ and $T_2$.

### 6.4.1 SHA-512 Preprocessing

1. Set the initial hash value, $H^{(0)}$, as specified in Sec. 5.3.5.
2. The message is padded and parsed as specified in Section 5.

### 6.4.2 SHA-512 Hash Computation

The SHA-512 hash computation uses functions and constants previously defined in
Sec. 4.1.3 and Sec. 4.2.3, respectively. Addition ($+$) is performed modulo $2^{64}$.

Each message block, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$, is processed in order,
using the following steps:
-/

namespace SHA512 --#

/-- FIPS-180-4 §6.4.2 step 1: SHA-512 message schedule (16-word block → 80 words). -/ --#
def schedule (M : Block) : Schedule := Id.run do
  let mut W : Schedule := Vector.replicate 80 default
  -- For 0 ≤ t ≤ 15:  W_t = M_t^(i)
  for h : t in [0:16] do
    W[t] := M[t]
  -- For 16 ≤ t ≤ 79: W_t = σ_1^(512)(W_{t-2}) + W_{t-7} + σ_0^(512)(W_{t-15}) + W_{t-16}
  for h : t in [16:80] do
    W[t] := smallSigma1 W[t-2] + W[t-7] + smallSigma0 W[t-15] + W[t-16]
  W

/-!  -/

/-- FIPS-180-4 §6.4.2 steps 2-4: SHA-512 block compression updating the 8-word state. -/ --#
def compress (H : HashValue) (M : Block) : HashValue := Id.run do
  -- Step 1. Prepare the message schedule {W_t}
  let W := schedule M
  -- Step 2. Initialize the eight working variables a..h with H^(i-1)
  let mut a := H[0]
  let mut b := H[1]
  let mut c := H[2]
  let mut d := H[3]
  let mut e := H[4]
  let mut f := H[5]
  let mut g := H[6]
  let mut h := H[7]
  -- Step 3. For t = 0 to 79
  for h : t in [0:80] do
    let T1 := h + bigSigma1 e + Ch e f g + K[t] + W[t]
    let T2 := bigSigma0 a + Maj a b c
    h := g
    g := f
    f := e
    e := d + T1
    d := c
    c := b
    b := a
    a := T1 + T2
  -- Step 4. Compute the i-th intermediate hash value H^(i)
  #v[
    a + H[0], b + H[1], c + H[2], d + H[3],
    e + H[4], f + H[5], g + H[6], h + H[7]
  ]

/-!
After repeating steps one through four a total of $N$ times (i.e., after processing
$M^{(N)}$), the resulting 512-bit message digest of the message, $M$, is

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)} \|
  H_6^{(N)} \| H_7^{(N)}$$
-/

/-- FIPS-180-4 §6.4: SHA-512 hash of a message `M` (length < 2¹²⁸ bits) → 512-bit digest. -/ --#
@[nolint unusedArguments] --#
def sha512 (M : Message) (_h : M.length < 2 ^ 128) : Digest 512 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_512
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5] ++ H[6] ++ H[7]

end SHA512 --#

/-!
## 6.5 SHA-384

SHA-384 may be used to hash a message, $M$, having a length of $\ell$ bits, where
$0 \le \ell < 2^{128}$. The algorithm is defined in the exact same manner as SHA-512
(Sec. 6.4), with the following two exceptions:

1. The initial hash value, $H^{(0)}$, shall be set as specified in Sec. 5.3.4; and
2. The 384-bit message digest is obtained by truncating the final hash value,
   $H^{(N)}$, to its left-most 384 bits:

$$H_0^{(N)} \| H_1^{(N)} \| H_2^{(N)} \| H_3^{(N)} \| H_4^{(N)} \| H_5^{(N)}$$
-/

namespace SHA512 --#

/-- FIPS-180-4 §6.5: SHA-384 hash — SHA-512 with `H0_384` IV, truncated to 384 bits. -/ --#
@[nolint unusedArguments] --#
def sha384 (M : Message) (_h : M.length < 2 ^ 128) : Digest 384 :=
  let blocks := parse (pad M)
  let H := blocks.foldl compress H0_384
  H[0] ++ H[1] ++ H[2] ++ H[3] ++ H[4] ++ H[5]

end SHA512 --#

end SHS --#
