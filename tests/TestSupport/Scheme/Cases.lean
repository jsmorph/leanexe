module

public import Demos.Scheme.Corpus
public import Demos.Scheme.Machine.Run
public import Demos.Scheme.Machine.Names
public import TestSupport.Scheme.Oracle

@[expose] public section

/-! The cases of the module `scheme`, the export `run` of the executable interpreter.  Each program
of the corpus `Demos.Scheme.Corpus.all` and of `syntaxCases` runs in native Lean in mode 0, which
reads and writes the data, and mode 1, which expands and writes the code, and each result must
equal the reference semantics's, from `TestSupport.Scheme.Oracle`.  The cases print one line for
each program and mode, whose expected result is the native result, for the module in the
Wasmtime host. -/

namespace TestSupport.Scheme.Cases

open Demos.Scheme Demos.Scheme.Semantics TestSupport.Scheme.Oracle

/-- Programs that test the reader and the expander beyond the corpus: the forms of each read
error, the derived forms' syntax errors and their order, temporaries, nested definitions, and
quasiquotation. -/
def syntaxCases : List String :=
  ["'(a . b) #(1 \"x\" #\\A) `(1 ,x ,@y)", "#t #F #x-1f #b101 #e7 #i7 1/2 +5 -0 ... + -",
    "(1 . 2 . 3)", "(. 1)", "#(1 . 2)", "\"a\\qb\"", "\"abc", "#\\", "#", "#q", "abc\x01",
    "(a ')", "(a . )", "'", "x;comment\n(y)", "(((((1)))))", "\"\xc3\xa9\"", "#\\(",
    "#\\SPACE #\\Newline", "abcdefghijklmnopqrstuvwxyz0123456789abcdefghij",
    "(begin (define a 1) (begin (define b 2)) (define c 3))", "(begin (define a 1) 2)",
    "(begin)", "(define (f) 1)", "(define 5 6)", "(let loop ((i 0)) i)", "(letrec () 1)",
    "(letrec ((a 1) (b a)) b)", "(lambda (a b . c) c)", "(lambda args args)",
    "(lambda (x . if) x)", "(let ((x 1) (x 2)) x)", "(letrec ((x 1) (x 2)) x)",
    "(cond (1 => 2))", "(cond)", "(cond (else))", "(cond (else 1) (2))", "(case 1)",
    "(case 1 (else 1) ((2) 3))", "(case 1 (5 1))", "`(1 . ,x)", "`(1 unquote x)", "`,@x",
    "`#(a ,b ,@c)", "``,,x", "`(unquote x y)", "(quote)", "(if 1)", "(set! if 1)", "(f . 5)",
    "((lambda (x) x) . 5)", "(lambda (x))", "(lambda (x) . 5)", "(begin . 5)",
    "(let ((x 1) . 5) x)", "(let ((x)) x)", "(or 1 . 2)", "(and 1 2 3)", "(delay 1)",
    "(unquote 1)", "(case 1 ((1 2) 3) ((2) 4))",
    "(case 1 ((a b) 3) ((\"s\") 4) ((\"s\") 5) (((1)) 6) (((1)) 7))",
    "(let ((cons 1)) `(a ,cons))", "(lambda (x) (lambda (y) (set! x y) x))",
    "(letrec ((f (lambda () g)) (g 1)) (f))", "(define x 1) (begin (define y 2)) x y"]

def cap : UInt64 := 65536
def outCap : UInt64 := 65536
def fuel : UInt64 := 10000000

/-- The bytes `bs` in hexadecimal, two digits a byte. -/
def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let digits := Nat.toDigits 16 b.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits))

/-- The native result of the export on the program `src` in mode `mode`. -/
def native (mode : UInt64) (src : List UInt8) : List UInt8 :=
  (Machine.runWith Machine.names mode cap outCap fuel ⟨⟨src.toArray⟩⟩).data.toList

/-- The reference outcome of a mode. -/
def reference (mode : UInt64) (src : List UInt8) : List UInt8 :=
  if mode == 0 then readOutcome src else expandOutcome src

/-- Prints the cases, and returns the number of programs whose native result differs from the
reference's. -/
def cases : IO UInt32 := do
  let mut failures : UInt32 := 0
  let programs := Corpus.all.map Corpus.Case.src ++ syntaxCases
  for src in programs do
    let b := bytes src
    for mode in [(0 : UInt64), 1] do
      let got := native mode b
      if got != reference mode b then
        failures := failures + 1
        IO.eprintln s!"scheme: mode {mode} differs from the reference on {repr src}"
      IO.println s!"scheme|run|bytes|i64:{mode} i64:{cap} i64:{outCap} i64:{fuel} bytes:{hex b}|{hex got}|1"
  return failures

end TestSupport.Scheme.Cases
