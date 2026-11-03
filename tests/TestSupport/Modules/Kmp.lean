import Library.Strings.Kmp.Spec
import Library.Random.SplitMix64.Program
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the occurrences of a pattern. -/

namespace Library.Strings.Kmp

/-- Bytes packed eight to a word in little-endian order. -/
def pack (bs : List Nat) : List UInt64 :=
  (List.range ((bs.length + 7) / 8)).map fun w =>
    (List.range 8).foldl (fun acc k =>
      acc ||| (UInt64.ofNat (bs.getD (8 * w + k) 0 % 256) <<< UInt64.ofNat (8 * k))) 0

/-- The bytes of a string of ASCII characters. -/
def ascii (s : String) : List Nat := s.toList.map Char.toNat

/-- The Fibonacci word of index `k` over the bytes 97 and 98, of the `k`-th Fibonacci number of
bytes from 1, 1, 2. -/
def fib : Nat → List Nat
  | 0 => [98]
  | 1 => [97]
  | k + 2 => fib (k + 1) ++ fib k

/-- The inputs `(pattern words, m, text words, n)` of the cases.  Short texts cover the empty
pattern with texts of 0, 1, 3, and 17 bytes, the empty text, a pattern longer than the text, a
pattern as long as a text it differs from, overlapping occurrences such as `aa` in `aaaa`,
occurrences at the start and at the end, bytes 0, 127, 128, and 255, bytes that differ only in bit
7, and patterns and texts that cross a word.  The fall-back chains reach 9 steps on one byte for
`a⁹b` in `a⁹c`, and stop where the result depends on it for `aaa` in `aabaa` and `aa` in `aba`.
Some cases give text lengths beyond the bytes of the array, whose bytes read as zero, an empty text
array with a length of 4, a pattern length beyond the bytes of its array, a text array with nonzero
bytes past its length, and a pattern array with nonzero bytes and a whole word past its length.
The long texts are Fibonacci words of 233 and 2,584 bytes with Fibonacci patterns, 4,000 bytes
drawn from 2 values by the SplitMix64 output of the position and from 4 values by that of the
position plus 10,000, with patterns cut from them, and 8,000 bytes of `a` with the patterns `a`,
`aa`, and 100 bytes of `a`. -/
def kmpInputs : List (List UInt64 × UInt64 × List UInt64 × UInt64) :=
  let mk := fun (p t : List Nat) =>
    (pack p, UInt64.ofNat p.length, pack t, UInt64.ofNat t.length)
  let draw := fun (k : Nat) => (Library.Random.SplitMix64.splitMix (UInt64.ofNat k)).2.toNat
  let two := (List.range 4000).map fun k => 97 + draw k % 2
  let four := (List.range 4000).map fun k => 97 + draw (k + 10000) % 4
  let as := List.replicate 8000 97
  let a9 := List.replicate 9 97
  [mk [] [], mk [] (ascii "abc"), mk [] (ascii "x"), mk [] (ascii "abcdefghijklmnopq"),
    mk (ascii "a") [], mk (ascii "abcd") (ascii "abc"), mk (ascii "abcd") (ascii "abce"),
    mk (ascii "aa") (ascii "aaaa"), mk (ascii "abra") (ascii "abracadabra"),
    mk (ascii "abc") (ascii "abcxxabc"), mk (ascii "xyz") (ascii "abcabc"),
    mk (ascii "abab") (ascii "abababab"), mk (ascii "aabaaab") (ascii "aabaabaaabaaab"),
    mk (ascii "abcabcabd") (ascii "abcabcabcabdabcabcabd"), mk (ascii "ab") (ascii "ab"),
    mk [0] [0, 1, 0, 0], mk [255, 128] [128, 255, 128, 127, 255, 128],
    mk [127, 128] [128, 127, 128, 127], mk [0] [128, 0, 128], mk [255] [127, 255],
    mk (ascii "abcdefghij") (ascii "xxabcdefghijabcdefghij"),
    mk (ascii "efghijklm") (ascii "abcdefghijklmnopabcdefghijklm"),
    mk (a9 ++ [98]) (a9 ++ [99] ++ a9 ++ [98]), mk (ascii "aaa") (ascii "aabaa"),
    mk (ascii "aa") (ascii "aba"),
    (pack [0, 0], 2, pack (ascii "abc"), 12), (pack (ascii "ab"), 2, pack (ascii "abab"), 20),
    (pack [], 1, pack [], 4), (pack (ascii "b"), 10, pack (ascii "b"), 10),
    (pack (ascii "ab"), 2, pack (ascii "abababab"), 3),
    (pack (ascii "abcabcab"), 3, pack (ascii "xabcabc"), 7),
    (pack (ascii "aaaaaaaaaaaaaaaa"), 9, pack (ascii "aaaaaaaaaaaa"), 12),
    (pack (ascii "abcdefghijklmnop"), 5, pack (ascii "xxabcdexx"), 9),
    mk (fib 5) (fib 12), mk (fib 8) (fib 12), mk (fib 11) (fib 17), mk (fib 13) (fib 17),
    mk (two.take 12) two, mk ((two.drop 1000).take 30) two, mk ((four.drop 2000).take 6) four,
    mk ((four.drop 100).take 200) four, mk [97] as, mk [97, 97] as, mk (as.take 100) as]

end Library.Strings.Kmp
