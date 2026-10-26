--#--
import Library.Hashing.Sha2.Spec.Functions
set_option autoImplicit true
--#--

namespace SHS --#
/-!
# 5. PREPROCESSING

Preprocessing consists of three steps: padding the message, $M$ (Sec. 5.1), parsing
the message into message blocks (Sec. 5.2), and setting the initial hash value,
$H^{(0)}$ (Sec. 5.3).

## 5.1 Padding the Message

The purpose of this padding is to ensure that the padded message is a multiple of 512
or 1024 bits, depending on the algorithm. Padding can be inserted before hash
computation begins on a message, or at any other time during the hash computation prior
to processing the block(s) that will contain the padding.

### 5.1.1 SHA-1, SHA-224 and SHA-256

Suppose that the length of the message, $M$, is $\ell$ bits. Append the bit "1" to the
end of the message, followed by $k$ zero bits, where $k$ is the smallest, non-negative
solution to the equation $\ell + 1 + k \equiv 448 \mod 512$. Then append the 64-bit
block that is equal to the number $\ell$ expressed using a binary representation. For
example, the (8-bit ASCII) message "abc" has length $8 \times 3 = 24$, so the
message is padded with a one bit, then $448 - (24 + 1) = 423$ zero bits, and then the
message length, to become the 512-bit padded message

```
                                  423       64
                                 ┌─┴─┐  ┌───┴───┐
01100001  01100010  01100011  1  00…00  00…011000
└───┬──┘  └───┬──┘  └───┬──┘               └──┬─┘
   "a"       "b"       "c"                 l = 24
```

The length of the padded message should now be a multiple of 512 bits.
-/

namespace SHA256 --#

/-- FIPS-180-4 §5.1.1: SHA-1, SHA-224, SHA-256 padding to a 512-bit-multiple length. -/ --#
def pad (M : Message) : Message :=
  -- Length of the message M is ℓ bits.
  let ℓ := M.length
  -- k is the smallest non-negative solution to ℓ + 1 + k ≡ 448 (mod 512).
  let k := min { k < 512 | ℓ + 1 + k ≡ 448 [MOD 512] }
  -- Append "1", k zero bits, and the 64-bit binary representation of ℓ.
  M ++ [true] ++ List.replicate k false ++ (List.range 64).reverse.map ℓ.testBit

end SHA256 --#

--#--
namespace SHA1
/-- FIPS-180-4 §5.1.1: SHA-1 padding (identical to SHA-256's). -/ --#
def pad : Message → Message := SHA256.pad
end SHA1
--#--

/-
### 5.1.2 SHA-384, SHA-512, SHA-512/224 and SHA-512/256

Suppose the length of the message $M$, in bits, is $\ell$ bits. Append the bit "1" to
the end of the message, followed by $k$ zero bits, where $k$ is the smallest
non-negative solution to the equation $\ell + 1 + k \equiv 896 \mod 1024$. Then append
the 128-bit block that is equal to the number $\ell$ expressed using a binary
representation. For example, the (8-bit ASCII) message "abc" has length
$8 \times 3 = 24$, so the message is padded with a one bit, then
$896 - (24 + 1) = 871$ zero bits, and then the message length, to become the 1024-bit
padded message

```
                                  871      128
                                 ┌─┴─┐  ┌───┴───┐
01100001  01100010  01100011  1  00…00  00…011000
└───┬──┘  └───┬──┘  └───┬──┘               └──┬─┘
   "a"       "b"       "c"                 l = 24
```

The length of the padded message should now be a multiple of 1024 bits.
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.1.2: SHA-384, SHA-512, SHA-512/t padding to a 1024-bit-multiple length. -/ --#
def pad (M : Message) : Message :=
  -- Length of the message M is ℓ bits.
  let ℓ := M.length
  -- k is the smallest non-negative solution to ℓ + 1 + k ≡ 896 (mod 1024).
  let k := min { k < 1024 | ℓ + 1 + k ≡ 896 [MOD 1024] }
  -- Append "1", k zero bits, and the 128-bit binary representation of ℓ.
  M ++ [true] ++ List.replicate k false ++ (List.range 128).reverse.map ℓ.testBit

end SHA512 --#

/-!
## 5.2 Parsing the Message

The message and its padding must be parsed into $N$ *m*-bit blocks.

### 5.2.1 SHA-1, SHA-224 and SHA-256

For SHA-1, SHA-224 and SHA-256, the message and its padding are parsed into $N$ 512-bit
blocks, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$. Since the 512 bits of the input block may
be expressed as sixteen 32-bit words, the first 32 bits of message block $i$ are
denoted $M_0^{(i)}$, the next 32 bits are $M_1^{(i)}$, and so on up to $M_{15}^{(i)}$.
-/

namespace SHA256 --#

/-- FIPS-180-4 §5.2.1: parse a padded SHA-1/SHA-224/SHA-256 message into 16-word blocks. -/ --#
def parse (M : Message) : Array Block :=
  -- Split into 512-bit blocks, then split each block into sixteen 32-bit words.
  -- A spec-conforming input padded by §5.1.1 yields exactly 16 words per block;
  -- the `getD 0` total fallback only fires on malformed (mis-padded) input.
  M.toChunks 512 |>.toArray |>.map fun b =>
    let words := b.toChunks 32 |>.map Word.fromBits |>.toArray
    Vector.ofFn (n := 16) fun i => words[i]?.getD 0

end SHA256 --#

--#--
namespace SHA1

/-- FIPS-180-4 §5.2.1: SHA-1 message parsing (identical to SHA-256's). -/ --#
def parse : Message → Array Block := SHA256.parse

end SHA1
--#--

/-!
### 5.2.2 SHA-384, SHA-512, SHA-512/224 and SHA-512/256

For SHA-384, SHA-512, SHA-512/224 and SHA-512/256, the message and its padding are
parsed into $N$ 1024-bit blocks, $M^{(1)}, M^{(2)}, \ldots, M^{(N)}$. Since the 1024
bits of the input block may be expressed as sixteen 64-bit words, the first 64 bits of
message block $i$ are denoted $M_0^{(i)}$, the next 64 bits are $M_1^{(i)}$, and so on
up to $M_{15}^{(i)}$.
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.2.2: parse a padded SHA-384/SHA-512/SHA-512/t message into 16-word blocks. -/ --#
def parse (M : Message) : Array Block :=
  -- Split into 1024-bit blocks, then split each block into sixteen 64-bit words.
  -- A spec-conforming input padded by §5.1.2 yields exactly 16 words per block;
  -- the `getD 0` total fallback only fires on malformed (mis-padded) input.
  M.toChunks 1024 |>.toArray |>.map fun b =>
    let words := b.toChunks 64 |>.map Word.fromBits |>.toArray
    Vector.ofFn (n := 16) fun i => words[i]?.getD 0

end SHA512 --#

/-!
## 5.3 Setting the Initial Hash Value ($H^{(0)}$)

Before hash computation begins for each of the secure hash algorithms, the initial
hash value, $H^{(0)}$, must be set. The size and number of words in $H^{(0)}$ depends
on the message digest size.

### 5.3.1 SHA-1

For SHA-1, the initial hash value, $H^{(0)}$, shall consist of the following five
32-bit words, in hex:
-/

namespace SHA1 --#

/-- FIPS-180-4 §5.3.1: SHA-1 initial hash value `H⁽⁰⁾`. -/ --#
def H0 : HashValue := #v[
  0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0
]

end SHA1 --#

/-!
### 5.3.2 SHA-224

For SHA-224, the initial hash value, $H^{(0)}$, shall consist of the following eight
32-bit words, in hex:
-/

namespace SHA256 --#

/-- FIPS-180-4 §5.3.2: SHA-224 initial hash value `H⁽⁰⁾`. -/ --#
def H0_224 : HashValue := #v[
  0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
  0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4
]

end SHA256 --#

/-!
### 5.3.3 SHA-256

For SHA-256, the initial hash value, $H^{(0)}$, shall consist of the following eight
32-bit words, in hex:
-/

namespace SHA256 --#

/-- FIPS-180-4 §5.3.3: SHA-256 initial hash value `H⁽⁰⁾`. -/ --#
def H0_256 : HashValue := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

end SHA256 --#

/-!
These words were obtained by taking the first thirty-two bits of the fractional parts
of the square roots of the first eight prime numbers.

### 5.3.4 SHA-384

For SHA-384, the initial hash value, $H^{(0)}$, shall consist of the following eight
64-bit words, in hex:
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.3.4: SHA-384 initial hash value `H⁽⁰⁾`. -/ --#
def H0_384 : HashValue := #v[
  0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
  0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4
]

end SHA512 --#

/-!
These words were obtained by taking the first sixty-four bits of the fractional parts
of the square roots of the ninth through sixteenth prime numbers.

### 5.3.5 SHA-512

For SHA-512, the initial hash value, $H^{(0)}$, shall consist of the following eight
64-bit words, in hex:
-/

namespace SHA512 --#

/-- FIPS-180-4 §5.3.5: SHA-512 initial hash value `H⁽⁰⁾`. -/ --#
def H0_512 : HashValue := #v[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
]

end SHA512 --#

end SHS --#
