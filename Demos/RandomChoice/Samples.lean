import LeanExe.Dialect.Bytes

namespace Demos.RandomChoice

open LeanExe

/-- The argument buffer of the arguments `args`: the UTF-8 bytes of each argument followed by a zero
byte. -/
def argBuffer (args : List String) : Bytes :=
  ⟨⟨(args.flatMap fun a => a.toUTF8.data.toList ++ [0]).toArray⟩⟩

/-- The buffer of the bytes `bs`. -/
def rawBuffer (bs : List UInt8) : Bytes := ⟨⟨bs.toArray⟩⟩

/-- The buffer of `choose N K` for the texts `n` and `k`. -/
def chooseBuffer (n k : String) : Bytes := argBuffer ["choose", n, k]

def parseSamples : List (Bytes × UInt64) :=
  -- No argument at all, the program name alone, and N without K.
  [(rawBuffer [], 1), (argBuffer ["choose"], 1), (argBuffer ["choose"], 2),
    (argBuffer ["choose", "6"], 1), (argBuffer ["choose", "6"], 2),
    -- N and K of the command's runs.
    (chooseBuffer "6" "10", 1), (chooseBuffer "6" "10", 2),
    (chooseBuffer "1" "1000000", 1), (chooseBuffer "1" "1000000", 2),
    (chooseBuffer "9223372036854775809" "1000", 1), (chooseBuffer "9223372036854775809" "1000", 2),
    -- The program name as argument 0, a name of digits, and an argument past the last.
    (chooseBuffer "6" "10", 0), (argBuffer ["17", "6", "10"], 0), (chooseBuffer "6" "10", 3),
    (argBuffer ["choose", "6", "10", "12"], 3), (chooseBuffer "6" "10", 18446744073709551615),
    (chooseBuffer "6" "10", 4294967296),
    -- Zero, written once and with leading zeros, and leading zeros before a positive value.
    (chooseBuffer "0" "5", 1), (chooseBuffer "5" "000", 2), (chooseBuffer "007" "5", 1),
    (chooseBuffer "5" "000000000000000000000000000001", 2),
    -- An empty argument, letters, signs, spaces, and a digit followed by a letter.
    (chooseBuffer "" "5", 1), (chooseBuffer "5" "", 2), (chooseBuffer "abc" "5", 1),
    (chooseBuffer "-5" "5", 1), (chooseBuffer "+5" "5", 1), (chooseBuffer " 5" "5", 1),
    (chooseBuffer "5 " "5", 1), (chooseBuffer "5" "12a", 2),
    -- The bytes on either side of the digits, '/' (47) and ':' (58), and a byte above 127.
    (chooseBuffer "4/" "5", 1), (chooseBuffer "5" "4:", 2), (rawBuffer [99, 0, 53, 0, 52, 200, 0], 2),
    -- 2^64 - 1, the largest value, then 2^64, a 20-digit value above it, and 21 digits.
    (chooseBuffer "18446744073709551615" "18446744073709551615", 1),
    (chooseBuffer "18446744073709551615" "18446744073709551615", 2),
    (chooseBuffer "18446744073709551616" "5", 1), (chooseBuffer "5" "18446744073709551619", 2),
    (chooseBuffer "99999999999999999999" "5", 1), (chooseBuffer "5" "184467440737095516150", 2),
    (chooseBuffer "30000000000000000000" "5", 1),
    -- 2^64 - 1 after leading zeros, 2^64 after a leading zero, 2^64 - 2, and values between 10^6
    -- and 10^19.
    (chooseBuffer "0018446744073709551615" "5", 1), (chooseBuffer "5" "018446744073709551616", 2),
    (chooseBuffer "18446744073709551614" "5", 1), (chooseBuffer "4294967295" "4294967296", 1),
    (chooseBuffer "4294967295" "4294967296", 2), (chooseBuffer "9223372036854775808" "5", 1),
    (chooseBuffer "10000000000000000000" "5", 1),
    -- An invalid N before a valid K, and a valid N before an invalid K.
    (chooseBuffer "x" "5", 2), (chooseBuffer "5" "x", 1),
    -- An argument without its terminating zero byte, a buffer with no zero byte, and zero bytes
    -- alone.
    (rawBuffer [99, 0, 53, 0, 55], 1), (rawBuffer [99, 0, 53, 0, 55], 2), (rawBuffer [53, 53], 0),
    (rawBuffer [0, 0], 1), (rawBuffer [0, 0, 0], 1), (rawBuffer [0, 0, 0], 2),
    -- A trailing newline, a tab, the bytes 127 and 255, and the digits five outside ASCII:
    -- fullwidth (EF BC 95) and Arabic-Indic (D9 A5).
    (chooseBuffer "5\n" "5", 1), (chooseBuffer "5" "5\t", 2), (rawBuffer [99, 0, 53, 127, 0, 53, 0], 1),
    (rawBuffer [99, 0, 53, 0, 53, 255, 0], 2), (chooseBuffer "５" "5", 1), (chooseBuffer "5" "٥", 2),
    -- An empty program name as argument 0, argument 0 of the empty buffer, and an overflowing
    -- numeral followed by a letter.
    (rawBuffer [0, 0], 0), (rawBuffer [], 0), (chooseBuffer "18446744073709551616x" "5", 1)]

def pickSamples : List (UInt64 × UInt64) :=
  -- N = 0 accepts no word.
  [(0, 0), (0, 5), (0, 18446744073709551615),
    -- N = 1: 2^64 mod 1 = 0, so every word gives 1.
    (1, 0), (1, 1), (1, 18446744073709551615),
    -- N = 2 and N = 2^63 divide 2^64, so every word is accepted.
    (2, 0), (2, 1), (2, 18446744073709551615), (9223372036854775808, 0),
    (9223372036854775808, 9223372036854775807), (9223372036854775808, 9223372036854775808),
    (9223372036854775808, 18446744073709551615),
    -- N = 3: 2^64 mod 3 = 1, so 0 is rejected and 1 gives 2.
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 18446744073709551615),
    -- N = 6: 2^64 mod 6 = 4.
    (6, 0), (6, 3), (6, 4), (6, 5), (6, 9), (6, 18446744073709551615),
    -- N = 10: 2^64 mod 10 = 6.
    (10, 5), (10, 6), (10, 7), (10, 16), (10, 18446744073709551615),
    -- N = 2^63 + 1: 2^64 mod N = 2^63 - 1, so about half the words are rejected.
    (9223372036854775809, 0), (9223372036854775809, 9223372036854775806),
    (9223372036854775809, 9223372036854775807), (9223372036854775809, 9223372036854775808),
    (9223372036854775809, 18446744073709551615),
    -- N = 2^64 - 1: 2^64 mod N = 1, and 2^64 - 1 itself gives 1.
    (18446744073709551615, 0), (18446744073709551615, 1), (18446744073709551615, 2),
    (18446744073709551615, 18446744073709551614), (18446744073709551615, 18446744073709551615),
    -- N = 2^64 - 2: 2^64 mod N = 2.
    (18446744073709551614, 1), (18446744073709551614, 2), (18446744073709551614, 18446744073709551613),
    (18446744073709551614, 18446744073709551615),
    -- N = 4 and N = 2^32, powers of two that divide 2^64.
    (4, 0), (4, 7), (4294967296, 4294967295), (4294967296, 18446744073709551615),
    -- N = 2^63 - 1, with 2^64 mod N = 2, and N = 3 · 2^62, with 2^64 mod N = 2^62.
    (9223372036854775807, 1), (9223372036854775807, 2), (9223372036854775807, 18446744073709551615),
    (13835058055282163712, 4611686018427387903), (13835058055282163712, 4611686018427387904),
    (13835058055282163712, 18446744073709551615),
    -- N = 2^32 + 1, with 2^64 mod N = 1, and N = 1,000,000,007, with 2^64 mod N = 582,344,008.
    (4294967297, 0), (4294967297, 1), (4294967297, 4294967296),
    (4294967297, 18446744073709551615), (1000000007, 582344007), (1000000007, 582344008),
    (1000000007, 12345678901234567890)]

def renderSamples : List (Array UInt64) :=
  [#[], #[1], #[0], #[1, 2, 3, 4, 5, 6],
    -- The edges of the digit counts.
    #[9, 10, 99, 100, 999, 1000, 99999, 100000, 999999999, 1000000000],
    #[1000000000000000000, 9999999999999999999, 10000000000000000000, 18446744073709551615,
      18446744073709551614, 4294967295, 4294967296, 12345678901234567890],
    -- Values of 7, 8, and 11 to 18 digits.
    #[1234567, 12345678, 12345678901, 123456789012, 1234567890123, 12345678901234,
      123456789012345, 1234567890123456, 12345678901234567, 123456789012345678],
    -- One value many times, and 512 values.
    #[6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
    ((List.range 512).map fun i => UInt64.ofNat (i * 37 % 1000 + 1)).toArray]

end Demos.RandomChoice
