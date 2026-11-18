import LeanExe.Dialect.Bytes

namespace Demos.RandomHistogram

open LeanExe

/-- The argument buffer of the arguments `args`: the UTF-8 bytes of each argument followed by a zero
byte. -/
def argBuffer (args : List String) : Bytes :=
  ⟨⟨(args.flatMap fun a => a.toUTF8.data.toList ++ [0]).toArray⟩⟩

/-- The buffer of the bytes `bs`. -/
def rawBuffer (bs : List UInt8) : Bytes := ⟨⟨bs.toArray⟩⟩

def parseSamples : List Bytes :=
  -- No argument at all, and the program name alone.
  [rawBuffer [], argBuffer ["prog"],
    -- The values of the command's runs.
    argBuffer ["prog", "1"], argBuffer ["prog", "9"], argBuffer ["prog", "10"],
    argBuffer ["prog", "512"], argBuffer ["prog", "513"], argBuffer ["prog", "1000"],
    argBuffer ["prog", "1000000"],
    -- Zero, written once and with leading zeros, and leading zeros before a positive value.
    argBuffer ["prog", "0"], argBuffer ["prog", "000"], argBuffer ["prog", "007"],
    argBuffer ["prog", "000000000000000000000000000001"],
    -- An empty argument, letters, signs, spaces, and a digit followed by a letter.
    argBuffer ["prog", ""], argBuffer ["prog", "abc"], argBuffer ["prog", "-5"],
    argBuffer ["prog", "+5"], argBuffer ["prog", " 5"], argBuffer ["prog", "5 "],
    argBuffer ["prog", "12a"],
    -- The bytes on either side of the digits, '/' (47) and ':' (58), and a byte above 127.
    argBuffer ["prog", "4/"], argBuffer ["prog", "4:"], rawBuffer [112, 0, 52, 200, 0],
    -- 2^64 - 1, the largest value, then 2^64, a 20-digit value above it, and 21 digits.
    argBuffer ["prog", "18446744073709551615"], argBuffer ["prog", "18446744073709551616"],
    argBuffer ["prog", "18446744073709551619"], argBuffer ["prog", "99999999999999999999"],
    argBuffer ["prog", "184467440737095516150"],
    -- 2^64 - 1 after leading zeros, and 2^64 - 2.
    argBuffer ["prog", "0018446744073709551615"], argBuffer ["prog", "18446744073709551614"],
    -- Arguments after the first, which do not matter, and a first argument that is invalid
    -- before a valid one.
    argBuffer ["prog", "5", "7"], argBuffer ["prog", "5", "x"], argBuffer ["prog", "x", "5"],
    argBuffer ["prog", "", "5"],
    -- An empty program name, a program name of digits, and a name with letters and digits.
    argBuffer ["", "42"], argBuffer ["17", "3"], argBuffer ["a1b2", "64"],
    -- An argument without its terminating zero byte, a buffer with no zero byte, and two
    -- zero bytes alone.
    rawBuffer [112, 0, 53], rawBuffer [53, 53], rawBuffer [0, 0],
    -- A trailing newline, a tab, the bytes 127 and 255, and the digits five outside ASCII:
    -- fullwidth (EF BC 95) and Arabic-Indic (D9 A5).
    argBuffer ["prog", "5\n"], argBuffer ["prog", "5\t"], rawBuffer [112, 0, 53, 127, 0],
    rawBuffer [112, 0, 53, 255, 0], argBuffer ["prog", "５"], argBuffer ["prog", "٥"],
    -- 2^64 after a leading zero, and a 20-digit value below 2^64.
    argBuffer ["prog", "018446744073709551616"], argBuffer ["prog", "10000000000000000000"],
    -- A terminated first argument followed by a last argument without its zero byte.
    rawBuffer [112, 114, 111, 103, 0, 53, 0, 55]]

def histogramSamples : List (Array UInt64) :=
  [#[], #[0], #[9], #[10], #[19], #[18446744073709551615], #[18446744073709551614],
    -- 2^63 and 2^63 - 1, whose residues 8 and 7 an unsigned reading gives.
    #[9223372036854775808, 9223372036854775807],
    -- Each residue once, and 0 to 19.
    #[10, 21, 32, 43, 54, 65, 76, 87, 98, 109],
    ((List.range 20).map fun i => UInt64.ofNat i).toArray,
    -- One residue many times.
    ((List.range 50).map fun i => UInt64.ofNat (10 * i + 3)).toArray,
    -- Words around 2^32 and 2^64 - 10.
    #[4294967295, 4294967296, 4294967297, 18446744073709551606, 18446744073709551605],
    -- 1,000 and 4,096 words, `(i · 0x9E3779B97F4A7C15 + 12345) mod 2^64`.
    ((List.range 1000).map fun i => UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64)).toArray,
    ((List.range 4096).map fun i => UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64)).toArray]

def renderSamples : List (Array UInt64) :=
  [#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
    -- The counts of 1,000,000 words, near 100,000 each.
    #[99781, 100212, 99950, 100034, 99877, 100101, 99923, 100066, 100005, 100051],
    -- The edges of the digit counts.
    #[9, 10, 99, 100, 999, 1000, 99999, 100000, 999999999, 1000000000],
    #[1000000000000000000, 9999999999999999999, 10000000000000000000, 18446744073709551615,
      18446744073709551614, 4294967295, 4294967296, 1, 0, 12345678901234567890],
    -- Counts of 7, 8, and 11 to 18 digits.
    #[1234567, 12345678, 12345678901, 123456789012, 1234567890123, 12345678901234,
      123456789012345, 1234567890123456, 12345678901234567, 123456789012345678],
    -- Fewer than ten elements, and more than ten.
    #[], #[5], #[1, 2, 3, 4, 5, 6, 7, 8, 9],
    #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], #[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]]

end Demos.RandomHistogram
