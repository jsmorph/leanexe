import LeanExe.Dialect.Bytes

namespace Demos.RandomChoice

open LeanExe

/-- The buffer of the bytes `bs`. -/
def byteBuffer (bs : List UInt8) : Bytes := ⟨⟨bs.toArray⟩⟩

/-- A buffer of `count` bytes, each `b`. -/
def fillBuffer (count : Nat) (b : UInt8) : Bytes := ⟨⟨(List.replicate count b).toArray⟩⟩

/-- The eight little-endian bytes of `w`, the least significant first. -/
def wordBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun i => ((w >>> (8 * UInt64.ofNat i)) &&& 255).toUInt8

/-- The buffer of the words `ws`, each in its little-endian bytes, followed by the bytes `extra`. -/
def wordBuffer (ws : List UInt64) (extra : List UInt8 := []) : Bytes :=
  byteBuffer (ws.flatMap wordBytes ++ extra)

/-- 512 words that spread over the whole range of words. -/
def spreadWords : List UInt64 :=
  (List.range 512).map fun j => UInt64.ofNat (j + 1) * 11400714819323198485

def putPicksSamples : List (Bytes × UInt64 × Bytes × UInt64) :=
  -- N = 6, whose threshold 2^64 mod 6 is 4: the words 0 and 1 are rejected, and 5, 6, and
  -- 2^64 - 1 give 6, 1, and 4.  The limit takes all values, two of them, or none.
  [(fillBuffer 32 170, 6, wordBuffer [0, 1, 5, 6, 18446744073709551615], 10),
    (fillBuffer 32 170, 6, wordBuffer [0, 1, 5, 6, 18446744073709551615], 2),
    (fillBuffer 32 170, 6, wordBuffer [0, 1, 5, 6, 18446744073709551615], 0),
    (fillBuffer 32 170, 6, wordBuffer [3, 4], 1),
    -- N = 0 accepts no word, and N = 1 accepts every word with the value 1.
    (fillBuffer 16 170, 0, wordBuffer [0, 7, 18446744073709551615], 10),
    (fillBuffer 16 170, 1, wordBuffer [0, 7, 18446744073709551615], 10),
    -- N = 2^64 - 1, whose threshold is 1, gives a value of 20 digits for 2^64 - 2.
    (fillBuffer 48 170, 18446744073709551615,
      wordBuffer [0, 1, 18446744073709551614, 18446744073709551615], 10),
    -- N = 3 · 2^62, whose threshold is 2^62.
    (fillBuffer 64 170, 13835058055282163712,
      wordBuffer [4611686018427387903, 4611686018427387904, 18446744073709551615, 0], 10),
    -- Bytes after the last whole word, a draw shorter than a word, and an empty draw.
    (fillBuffer 16 170, 6, wordBuffer [5, 6] [5, 6, 7, 8, 9], 10),
    (fillBuffer 16 170, 6, byteBuffer [5, 0, 0, 0, 0, 0, 0], 10),
    (fillBuffer 16 170, 6, byteBuffer [], 10),
    -- Lines longer than the buffer, an empty buffer, and lines that end at its last byte.
    (fillBuffer 3 170, 6, wordBuffer [5, 6, 18446744073709551615], 10),
    (byteBuffer [], 6, wordBuffer [5, 6, 18446744073709551615], 10),
    (fillBuffer 6 170, 6, wordBuffer [5, 6, 18446744073709551615], 10),
    -- The largest limit.
    (fillBuffer 16 170, 6, wordBuffer [5, 6, 18446744073709551615], 18446744073709551615),
    -- A buffer of varied bytes, which keeps those after the lines.
    (byteBuffer ((List.range 40).map fun i => UInt8.ofNat (7 * i + 1)), 6,
      wordBuffer [5, 6, 18446744073709551615], 10),
    -- Lines longer than the buffer, which ends after a newline, and lines that the limit cuts and
    -- that are longer than the buffer.
    (fillBuffer 4 170, 6, wordBuffer [5, 6, 18446744073709551615], 10),
    (fillBuffer 3 170, 6, wordBuffer [5, 6, 18446744073709551615], 2),
    -- N of 2, 2^32, and 2^63, whose threshold is 0: every word is accepted.
    (fillBuffer 32 170, 2, wordBuffer [0, 1, 18446744073709551615], 10),
    (fillBuffer 48 170, 4294967296, wordBuffer [0, 4294967295, 18446744073709551615], 10),
    (fillBuffer 64 170, 9223372036854775808, wordBuffer [0, 9223372036854775807,
      9223372036854775808, 18446744073709551615], 10),
    -- A draw of 512 words into a buffer of 10,752 bytes, the command's sizes, with N of 6, of
    -- 2^63 + 1, which rejects 2^63 - 1 words, and of 2^64 - 1, and with a limit of 100.
    (fillBuffer 10752 0, 6, wordBuffer spreadWords, 1000000),
    (fillBuffer 10752 0, 9223372036854775809, wordBuffer spreadWords, 1000000),
    (fillBuffer 10752 0, 18446744073709551615, wordBuffer spreadWords, 1000000),
    (fillBuffer 10752 0, 6, wordBuffer spreadWords, 100),
    -- 512 values of 20 digits, whose lines fill 10,752 bytes, over a buffer of varied bytes.
    (byteBuffer ((List.range 10752).map fun i => UInt8.ofNat (i % 251)), 18446744073709551615,
      wordBuffer ((List.range 512).map fun j => 18446744073709551614 - UInt64.ofNat j), 1000000),
    -- A draw of 600 words, more than a call of `random_get` returns.
    (fillBuffer 4096 0, 7,
      wordBuffer ((List.range 600).map fun j => UInt64.ofNat (j + 1) * 11400714819323198485),
      1000000)]

end Demos.RandomChoice
