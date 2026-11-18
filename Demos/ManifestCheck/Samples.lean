import LeanExe.Dialect.Bytes
import Library.Hashing.Words.Program

/-! Sample inputs of the manifest checker's pure core.  `H0` and `H1` are the SHA-256 digests of
the empty message and of `abc` in hex, and `D0` and `D1` the same digests as four words, eight
bytes to a word, least significant first. -/

namespace Demos.ManifestCheck

open LeanExe Library.Hashing.Words

/-- The bytes of the UTF-8 text `s`. -/
def text (s : String) : Bytes := ⟨s.toUTF8⟩

/-- The bytes of `s` followed by the bytes `tail`. -/
def textThen (s : String) (tail : List UInt8) : Bytes := ⟨⟨(s.toUTF8.data.toList ++ tail).toArray⟩⟩

/-- The first `n` characters of `s`. -/
def first (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

/-- The characters of `s` after the first `n`. -/
def after (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

def H0 : String := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
def H1 : String := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
def H1upper : String := "BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD"
def H1mixed : String := "Ba7816bF8f01CfEa414140De5DaE2223B00361a396177A9cB410fF61F20015aD"

def D0 : Words4 := ⟨0x141cfc9842c4b0e3, 0x24b96f99c8f4fb9a, 0x4c939b64e441ae27, 0x55b852781b9995a4⟩
def D1 : Words4 := ⟨0xeacf018fbf1678ba, 0x2322ae5dde404141, 0x9c7a1796a36103b0, 0xad1500f261ff10b4⟩

def parseSamples : List Bytes := [
  text "",
  text "\n",
  text "\n\n\n",
  text (H0 ++ "  empty\n"),
  text (H0 ++ "  empty"),
  text (H0 ++ " *empty\n"),
  text (H0 ++ "  a\n" ++ H1 ++ "  abc\n"),
  text ("\n" ++ H0 ++ "  a\n\n\n" ++ H1 ++ " *b"),
  text (H0 ++ "  a\r\n"),
  text (H1upper ++ "  up\n"),
  text (H1mixed ++ "  mixed\n"),
  text (H0 ++ "  "),
  text (H0 ++ "  \n"),
  text (H0 ++ " *\n"),
  text (H0 ++ "  x"),
  text ((first H0 63) ++ "  name\n"),
  text (H0 ++ "e  name\n"),
  text ((first H0 10) ++ "g" ++ (after H0 11) ++ "  name\n"),
  text (H0 ++ " \tname\n"),
  text (H0 ++ " name\n"),
  text (H0 ++ "\t name\n"),
  text (H0 ++ "**name\n"),
  text (H0 ++ "  *name\n"),
  text ("\\" ++ H0 ++ "  a\\\\b\n"),
  text ("# comment\n" ++ H0 ++ "  a\n"),
  text ("SHA256 (a) = " ++ H0 ++ "\n"),
  text (" " ++ H0 ++ "  a\n"),
  text (H0 ++ "  a\ngarbage\n"),
  text (H0 ++ "  a\n\r\n" ++ H1 ++ "  b\n"),
  text (H0 ++ "  name with spaces\n"),
  text (H0 ++ "   lead"),
  text (H0 ++ "  name  \n"),
  text (H0 ++ "  ../escape\n" ++ H1 ++ "  /etc/passwd\n" ++ H0 ++ "  dir/./f\n"),
  textThen (H0 ++ "  a") [0, 98, 10],
  text (H0 ++ "  é\n"),
  textThen (H0 ++ "  ") [255, 254, 10],
  text (H0 ++ "  1\n" ++ H1 ++ "  2\n" ++ H0 ++ " *3\n" ++ H1 ++ "  4\n" ++ H0 ++ "  5\n"),
  text (H0 ++ "  a\n" ++ H0 ++ "  a\n"),
  textThen (first H0 32) [10],
  text ((first H0 5) ++ "/" ++ (after H0 6) ++ "  a\n"),
  text ((first H0 5) ++ ":" ++ (after H0 6) ++ "  a\n"),
  text ((first H0 5) ++ "@" ++ (after H0 6) ++ "  a\n"),
  text ((first H0 5) ++ "`" ++ (after H0 6) ++ "  a\n"),
  text ((first H0 5) ++ "G" ++ (after H0 6) ++ "  a\n"),
  text (H0 ++ "  a\\b\n"),
  text (H0 ++ " **a\n"),
  text (H0 ++ " * a\n"),
  text (H0 ++ "  a\n" ++ "bad line\n" ++ H1 ++ "  b\n"),
  text (H0 ++ "  a\n" ++ H1 ++ "  b\n\n\n"),
  text ("\t" ++ H0 ++ "  a\n") ]

def hexMatchesSamples : List (Bytes × UInt64 × Words4) := [
  (text H0, 0, D0),
  (text H0.toUpper, 0, D0),
  (text H1, 0, D1),
  (text H1upper, 0, D1),
  (text H1mixed, 0, D1),
  (text H0, 0, D1),
  (text H1, 0, D0),
  (text ((first H0 63) ++ "4"), 0, D0),
  (text ("f" ++ (after H0 1)), 0, D0),
  (text ("3e" ++ (after H0 2)), 0, D0),
  (text ("xx" ++ H0), 2, D0),
  (text ("xx" ++ H0), 0, D0),
  (text (H0 ++ "xx"), 0, D0),
  (text (first H0 63), 0, D0),
  (text H0, 1, D0),
  (text "", 0, D0),
  (text H0, 64, D0),
  (text H0, 0xFFFFFFFFFFFFFFFF, D0),
  (text H0, 0xFFFFFFFFFFFFFFFE, D0),
  (text H0, 0xFFFFFFFFFFFFFFC0, D0),
  (text (String.ofList (List.replicate 64 '0')), 0, ⟨0, 0, 0, 0⟩),
  (text (String.ofList (List.replicate 64 'f')), 0,
    ⟨0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF⟩),
  (text (String.ofList (List.replicate 64 'F')), 0,
    ⟨0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF⟩),
  (text (String.ofList (List.replicate 64 '0')), 0, ⟨1, 0, 0, 0⟩),
  (text (String.ofList (List.replicate 64 '0')), 0, ⟨0, 0, 0, 0x100000000000000⟩),
  (text ((first H0 30) ++ "g" ++ (after H0 31)), 0, D0),
  (text ((first H0 30) ++ "G" ++ (after H0 31)), 0, D0),
  (text (H0 ++ "  empty\n" ++ H1 ++ "  abc\n"), 72, D1),
  (text (H0 ++ "  empty\n" ++ H1 ++ "  abc\n"), 72, D0),
  (text H0, 0, ⟨0x141cfc9842c4b0e3, 0x24b96f99c8f4fb9b, 0x4c939b64e441ae27, 0x55b852781b9995a4⟩),
  (text H0, 0, ⟨0x141cfc9842c4b0e3, 0x24b96f99c8f4fb9a, 0x4c939b64e441ae37, 0x55b852781b9995a4⟩),
  (text ((first H0 20) ++ "0" ++ (after H0 21)), 0, D0),
  (text ((first H0 40) ++ "/" ++ (after H0 41)), 0, D0),
  (text ((first H0 40) ++ ":" ++ (after H0 41)), 0, D0),
  (text ((first H0 40) ++ "@" ++ (after H0 41)), 0, D0),
  (text ((first H0 40) ++ "`" ++ (after H0 41)), 0, D0) ]

def renderSamples : List (Bytes × Bool) := [
  (text "a", true),
  (text "a", false),
  (text "", true),
  (text "", false),
  (text "name with spaces", true),
  (text "a\r", false),
  (text "é", true),
  (text "dir/sub/file.txt", false),
  (text "../x", false),
  (textThen "" [0, 255, 10], true),
  (text (String.ofList (List.replicate 300 'n')), true),
  (text (String.ofList (List.replicate 300 'n')), false),
  (text "a\\b", true) ]

end Demos.ManifestCheck
