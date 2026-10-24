import Mathlib.Computability.RegularExpressions

/-! Regular expressions over bytes, their languages, and the postfix form in which a pattern
reaches the matcher.  A regular expression matches no string, the empty string, one byte of a
set, a concatenation, an alternation, or a repetition, and its language is built with the operations
of Mathlib's `Language`: `0`, `1`, `+` for union, `*` for concatenation, and `∗` for the Kleene
star.  `lang_eq_matches'` shows that the language is the one Mathlib's `RegularExpression` gives
when each set of bytes is the sum of its bytes.

A pattern is a sequence of words in postfix order.  The opcode 0 pushes `empty`, 1 pushes `eps`,
and 2 pushes the set of bytes given by the next four words, numbered 0 to 3: byte `b` is in the
set when bit `b % 64` of word `b / 64` is set, where bit `i` has the value `2 ^ i`.  The opcode 3
replaces the top two expressions `a` and `b`, with `b` on top, by `cat a b`, 4 replaces them by
`alt a b`, and 5 replaces the top expression `a` by `star a`.  A pattern decodes when every
opcode is one of these, every operator finds its operands, every opcode 2 is followed by four
words, and one expression remains.  `answer` is the result that the matcher must return. -/

namespace Library.Regex.Spec

open scoped Computability

/-- A regular expression over bytes.  `cls p` matches one byte `b` with `p b = true`. -/
inductive Re where
  | empty
  | eps
  | cls (p : UInt8 → Bool)
  | cat (a b : Re)
  | alt (a b : Re)
  | star (a : Re)

/-- The language of a regular expression. -/
def Re.lang : Re → Language UInt8
  | .empty => 0
  | .eps => 1
  | .cls p => {w | ∃ b, p b = true ∧ w = [b]}
  | .cat a b => a.lang * b.lang
  | .alt a b => a.lang + b.lang
  | .star a => a.lang∗

/-- The number of sets of bytes in a regular expression: the positions of its automaton. -/
def Re.positions : Re → Nat
  | .empty | .eps => 0
  | .cls _ => 1
  | .cat a b | .alt a b => a.positions + b.positions
  | .star a => a.positions

/-- The bytes `0` to `255`. -/
def allBytes : List UInt8 := (List.range 256).map Nat.toUInt8

/-- Mathlib's regular expression with the language of a regular expression, with a set of bytes as
the sum of its bytes. -/
def Re.toMathlib : Re → RegularExpression UInt8
  | .empty => 0
  | .eps => 1
  | .cls p => (allBytes.filter p).foldr (fun b acc => RegularExpression.char b + acc) 0
  | .cat a b => a.toMathlib * b.toMathlib
  | .alt a b => a.toMathlib + b.toMathlib
  | .star a => RegularExpression.star a.toMathlib

theorem mem_allBytes (b : UInt8) : b ∈ allBytes :=
  List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr b.toNat_lt, UInt8.ofNat_toNat⟩

theorem matches'_sum (l : List UInt8) :
    (l.foldr (fun b acc => RegularExpression.char b + acc) 0).matches' =
      {w | ∃ b ∈ l, w = [b]} := by
  induction l with
  | nil =>
    ext w
    show w ∈ (∅ : Set (List UInt8)) ↔ w ∈ {w : List UInt8 | ∃ b ∈ ([] : List UInt8), w = [b]}
    simp
  | cons a l ih =>
    rw [List.foldr_cons, RegularExpression.matches'_add, RegularExpression.matches'_char, ih]
    ext w
    show w ∈ ({[a]} : Set (List UInt8)) ∨ w ∈ {w : List UInt8 | ∃ b ∈ l, w = [b]} ↔
      w ∈ {w : List UInt8 | ∃ b ∈ a :: l, w = [b]}
    simp

/-- The language of `r` is the language of Mathlib's regular expression for `r`. -/
theorem Re.lang_eq_matches' : ∀ r : Re, r.lang = r.toMathlib.matches'
  | .empty => rfl
  | .eps => rfl
  | .cls p => by
    rw [Re.toMathlib, matches'_sum]
    ext w
    simp only [Re.lang, List.mem_filter]
    exact ⟨fun ⟨b, hb, hw⟩ => ⟨b, ⟨mem_allBytes b, hb⟩, hw⟩, fun ⟨b, ⟨_, hb⟩, hw⟩ => ⟨b, hb, hw⟩⟩
  | .cat a b => by
    rw [Re.lang, Re.toMathlib, RegularExpression.matches'_mul, a.lang_eq_matches',
      b.lang_eq_matches']
  | .alt a b => by
    rw [Re.lang, Re.toMathlib, RegularExpression.matches'_add, a.lang_eq_matches',
      b.lang_eq_matches']
  | .star a => by
    rw [Re.lang, Re.toMathlib, RegularExpression.matches'_star, a.lang_eq_matches']

/-- The set of bytes whose bits the four words `w0` to `w3` hold. -/
def byteSet (w0 w1 w2 w3 : UInt64) (b : UInt8) : Bool :=
  let w := match b.toNat / 64 with
    | 0 => w0
    | 1 => w1
    | 2 => w2
    | _ => w3
  (w >>> (b.toNat % 64).toUInt64) &&& 1 == 1

/-- Runs the postfix words `ws` from the stack `stack`, whose head is the top. -/
def run : List UInt64 → List Re → Option (List Re)
  | [], stack => some stack
  | op :: ws, stack =>
    if op == 0 then run ws (.empty :: stack)
    else if op == 1 then run ws (.eps :: stack)
    else if op == 2 then
      match ws with
      | w0 :: w1 :: w2 :: w3 :: rest => run rest (.cls (byteSet w0 w1 w2 w3) :: stack)
      | _ => none
    else if op == 3 then
      match stack with
      | b :: a :: rest => run ws (.cat a b :: rest)
      | _ => none
    else if op == 4 then
      match stack with
      | b :: a :: rest => run ws (.alt a b :: rest)
      | _ => none
    else if op == 5 then
      match stack with
      | a :: rest => run ws (.star a :: rest)
      | _ => none
    else none

/-- The regular expression of the postfix words `ws`, when they decode. -/
def decode (ws : List UInt64) : Option Re :=
  match run ws [] with
  | some [r] => some r
  | _ => none

#print axioms Re.lang_eq_matches'

/-- Membership in the language of a regular expression, decided by Mathlib's derivative matcher
`rmatch` on its Mathlib regular expression. -/
instance Re.decidableMem (r : Re) : DecidablePred (· ∈ r.lang) := fun w =>
  decidable_of_iff (w ∈ r.toMathlib.matches') (by rw [r.lang_eq_matches'])

/-- The matcher's result for the pattern words `ws` and the input `input`: 2 when the pattern does
not decode, otherwise 3 when it has more than 63 positions, and otherwise 1 when the input is in
its language and 0 when it is not.  A pattern that does not decode gives 2 whatever its number of
sets. -/
def answer (ws : List UInt64) (input : List UInt8) : UInt64 :=
  match decode ws with
  | none => 2
  | some r => if 63 < r.positions then 3 else if input ∈ r.lang then 1 else 0

end Library.Regex.Spec
