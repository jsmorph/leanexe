--#--
import Library.Hashing.Sha2.Spec.Setup
set_option autoImplicit true
--#--

namespace SHS --#

/-!
# 3. NOTATION AND CONVENTIONS

## 3.1 Bit Strings and Integers

The following terminology related to bit strings and integers will be used.

1. A *hex digit* is an element of the set {0, 1, ..., 9, a, ..., f}. A hex digit is the
   representation of a 4-bit string. For example, the hex digit "7" represents the
   4-bit string "0111", and the hex digit "a" represents the 4-bit string "1010".

2. A *word* is a *w*-bit string that may be represented as a sequence of hex digits.
   To convert a word to hex digits, each 4-bit string is converted to its hex digit
   equivalent, as described in (1) above. For example, the 32-bit string

   ```
   1010 0001 0000 0011 1111 1110 0010 0011
   ```

   can be expressed as "`a103fe23`", and the 64-bit string

   ```
   1010 0001 0000 0011 1111 1110 0010 0011
   0011 0010 1110 1111 0011 0000 0001 1010
   ```

   can be expressed as "`a103fe2332ef301a`".

   *Throughout this specification, the "big-endian" convention is used when expressing
   both 32- and 64-bit words, so that within each word, the most significant bit is
   stored in the left-most bit position.*

3. An *integer* may be represented as a word or pair of words. A word representation of
   the message length, $\ell$, in bits, is required for the padding techniques of
   Sec. 5.1.

   An integer between 0 and $2^{32}-1$ inclusive may be represented as a 32-bit word.
   The least significant four bits of the integer are represented by the right-most hex
   digit of the word representation. For example, the integer
   $291 = 2^8 + 2^5 + 2^1 + 2^0 = 256+32+2+1$ is represented by the hex word
   "`00000123`".

   The same holds true for an integer between 0 and $2^{64}-1$ inclusive, which may be
   represented as a 64-bit word.

   If $Z$ is an integer, $0 \leq Z < 2^{64}$, then $Z = 2^{32}X + Y$, where
   $0 \leq X < 2^{32}$ and $0 \leq Y < 2^{32}$. Since $X$ and $Y$ can be represented as
   32-bit words $x$ and $y$, respectively, the integer $Z$ can be represented as the
   pair of words $(x, y)$. This property is used for SHA-1, SHA-224 and SHA-256.

   If $Z$ is an integer, $0 \leq Z < 2^{128}$, then $Z = 2^{64}X + Y$, where
   $0 \leq X < 2^{64}$ and $0 \leq Y < 2^{64}$. Since $X$ and $Y$ can be represented as
   64-bit words $x$ and $y$, respectively, the integer $Z$ can be represented as the
   pair of words $(x, y)$. This property is used for SHA-384, SHA-512, SHA-512/224 and
   SHA-512/256.

4. For the secure hash algorithms, the size of the *message block* - $m$ bits - depends
   on the algorithm.

   a) For **SHA-1**, **SHA-224** and **SHA-256**, each message block has **512 bits**,
      which are represented as a sequence of sixteen **32-bit words**.

   b) For **SHA-384**, **SHA-512**, **SHA-512/224** and **SHA-512/256** each message
      block has **1024 bits**, which are represented as a sequence of sixteen
      **64-bit words**.
-/

/-!
## 3.2 Operations on Words

The following operations are applied to *w*-bit words in all five secure hash
algorithms. SHA-1, SHA-224 and SHA-256 operate on 32-bit words ($w=32$), and SHA-384,
SHA-512, SHA-512/224 and SHA-512/256 operate on 64-bit words ($w=64$).

1. Bitwise *logical* word operations: $\wedge$, $\vee$, $\oplus$, and $\neg$
   (see Sec. 2.2.2).

2. Addition modulo $2^w$.

   The operation $x + y$ is defined as follows. The words $x$ and $y$ represent
   integers $X$ and $Y$, where $0 \leq X < 2^w$ and $0 \leq Y < 2^w$. For positive
   integers $U$ and $V$, let $U \bmod V$ be the remainder upon dividing $U$ by $V$.
   Compute

   $$Z = (X + Y) \bmod 2^w.$$

   Then $0 \leq Z < 2^w$. Convert the integer $Z$ to a word, $z$, and define $z = x + y$.

3. The *right shift* operation `SHR n x`, where $x$ is a *w*-bit word and $n$ is an
   integer with $0 \leq n < w$, is defined by
-/

/-- FIPS-180-4 §2.2.2 (3): right shift `SHR n x` of the `w`-bit word `x` by `n` positions. -/ --#
def SHR (n : Nat) (x : Word w) : Word w := x >> n

/-!
   This operation is used in the SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
   SHA-512/256 algorithms.

4. The *rotate right* (circular right shift) operation `ROTR n x`, where $x$ is a
   *w*-bit word and $n$ is an integer with $0 \leq n < w$, is defined by
-/

/-- FIPS-180-4 §2.2.2 (4): rotate-right `ROTR n x` of the `w`-bit word `x` by `n` positions. -/ --#
def ROTR (n : Nat) (x : Word w) : Word w := (x >> n) ∨ (x << (w - n))

/-!
   Thus, `ROTR n x` is equivalent to a circular shift (rotation) of $x$ by $n$
   positions to the right.

   This operation is used by the SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
   SHA-512/256 algorithms.

5. The *rotate left* (circular left shift) operation, `ROTL n x`, where $x$ is a
   *w*-bit word and $n$ is an integer with $0 \leq n < w$, is defined by
-/

/-- FIPS-180-4 §2.2.2 (5): rotate-left `ROTL n x` of the `w`-bit word `x` by `n` positions. -/ --#
def ROTL (n : Nat) (x : Word w) : Word w := (x << n) ∨ (x >> (w - n))

/-!
   Thus, `ROTL n x` is equivalent to a circular shift (rotation) of $x$ by $n$
   positions to the left.

   This operation is used only in the SHA-1 algorithm.

6. Note the following equivalence relationships, where $w$ is fixed in each
   relationship:
-/

theorem ROTL_eq_ROTR {w n m : Nat} (hn : n < w) (hm : m < w) (heq : n + m = w)
    (x : BitVec w) : ROTL n x = ROTR m x
--#--
  := by
  unfold ROTL ROTR
  have h1 : w - n = m := by grind
  have h2 : w - m = n := by grind
  rw [h1, h2, BitVec.or_comm]
--#--

/-! -/

theorem ROTR_eq_ROTL {w n m : Nat} (hn : n < w) (hm : m < w) (heq : n + m = w)
    (x : BitVec w) : ROTR n x = ROTL m x
--#--
  := by
  unfold ROTR ROTL
  have h1 : w - n = m := by grind
  have h2 : w - m = n := by grind
  rw [h1, h2, BitVec.or_comm]
--#--

end SHS --#
