module

public import Demos.Scheme.Acceptance

@[expose] public section

/-! The corpus of programs that tests the reference semantics and the executable interpreter, each
with the outcome that the report and [the profile](profile.md) give it: a status byte and a text.
The expected outcomes are written by hand, not computed.  The corpus holds the acceptance cases of
the design's section 7 that milestones 1 and 2 cover, with cases for each form and procedure that
the profile implements. -/

namespace Demos.Scheme.Corpus

open Demos.Scheme.Semantics (bytes)

/-- A program, its expected status, and its expected text. -/
structure Case where
  name : String
  src : String
  status : UInt8
  text : String

/-- The expected bytes of a case's outcome. -/
def Case.expected (c : Case) : List UInt8 := c.status :: bytes c.text

def all : List Case := [
  ⟨"or-42", "(let ((_ 42)) (or #f _))", 0, "42"⟩,
  ⟨"or-temporaries", "(let ((x 1) (thunk 2)) (or #f x thunk))", 0, "1"⟩,
  ⟨"and-temporaries", "(let ((x 5) (thunk 6)) (and x thunk))", 0, "6"⟩,
  ⟨"quasiquote-capture", "(let ((cons 0) (list 1) (append 2)) `(a ,cons ,@'(b c) ,list))", 0,
    "(a 0 b c 1)"⟩,
  ⟨"case-capture", "(let ((memv 0)) (case 2 ((1 2) 'yes) (else 'no)))", 0, "yes"⟩,
  ⟨"repeated-escape", "(let ((again #f) (visits 0))
  (let ((x (+ 1 (call/cc (lambda (k) (set! again k) 10)))))
    (set! visits (+ visits 1))
    (if (< visits 3)
        (+ 1000 (again x))
        (list x visits))))", 0, "(13 3)"⟩,
  ⟨"letrec-reentry", "(let ((retry #f) (first? #t))
  (letrec ((x 10)
           (y (call/cc (lambda (k) (set! retry k) 0))))
    (if first?
        (begin (set! first? #f) (set! x 99) (retry 1))
        (list x y))))", 0, "(10 1)"⟩,
  ⟨"operand-order",
    "(let ((n 0)) (list (begin (set! n (+ n 1)) n) (begin (set! n (* n 10)) n)))", 0, "(1 10)"⟩,
  ⟨"operator-first", "(let ((log '()))
  ((begin (set! log (cons 'op log)) (lambda (a b) (reverse log)))
   (begin (set! log (cons 'a log)) 1)
   (begin (set! log (cons 'b log)) 2)))", 0, "(op a b)"⟩,
  ⟨"letrec-staging", "(let ((retry #f) (first? #t))
  (letrec ((y (call/cc (lambda (k) (set! retry k) 0)))
           (x 10))
    (if first?
        (begin (set! first? #f) (set! x 99) (retry 1))
        (list x y))))", 0, "(10 1)"⟩,
  ⟨"or-once", "(let ((n 0)) (or (begin (set! n (+ n 1)) #f) (begin (set! n (+ n 1)) n)))", 0,
    "2"⟩,
  ⟨"and-once", "(let ((n 0)) (and (begin (set! n (+ n 1)) n) n))", 0, "1"⟩,
  ⟨"fresh-reentry", "(let ((k #f) (cells '()))
  (let ((x (call/cc (lambda (c) (set! k c) 0))))
    (set! cells (cons (lambda () x) cells))
    (if (< x 2) (k (+ x 1)) (map (lambda (f) (f)) cells))))", 0, "(2 1 0)"⟩,
  ⟨"shared-cell", "(let ((n 0))
  (let ((inc (lambda () (set! n (+ n 1)) n)) (get (lambda () n)))
    (inc) (inc) (get)))", 0, "2"⟩,
  ⟨"apply-rest-fresh", "(let ((xs (list 1 2))) (apply (lambda r (set-car! r 9)) xs) (car xs))", 0,
    "1"⟩,
  ⟨"callcc-through-apply", "(+ 1 (apply call/cc (list (lambda (k) (k 41)))))", 0, "42"⟩,
  ⟨"map-reentry", "(let ((k #f) (n 0))
  (let ((r (map (lambda (x) (call/cc (lambda (c) (if (= x 2) (set! k c) #f) x))) '(1 2 3))))
    (set! n (+ n 1))
    (if (< n 3) (k (* 10 n)) r)))", 0, "(1 20 3)"⟩,
  ⟨"callcc-names", "(eq? call/cc call-with-current-continuation)", 0, "#t"⟩,
  ⟨"toplevel-reentry", "(define k #f)
(define n 0)
(+ 1 (call/cc (lambda (c) (set! k c) 1)))
(set! n (+ n 1))
(if (< n 3) (k 0) n)", 0, "3"⟩,
  ⟨"alias-mutation", "(let ((p (list 1 2))) (let ((q p)) (set-car! q 5) (car p)))", 0, "5"⟩,
  ⟨"cycle-list", "(let ((p (list 1 2))) (set-cdr! (cdr p) p) (list? p))", 0, "#f"⟩,
  ⟨"range-max", "1152921504606846975", 0, "1152921504606846975"⟩,
  ⟨"range-min", "-1152921504606846976", 0, "-1152921504606846976"⟩,
  ⟨"range-literal", "1152921504606846976", 4, "number out of range"⟩,
  ⟨"sum-cancel", "(+ 1152921504606846975 1 -1)", 0, "1152921504606846975"⟩,
  ⟨"sum-overflow", "(+ 1152921504606846975 1)", 4, "number out of range"⟩,
  ⟨"product-zero", "(* 1152921504606846975 2 0)", 0, "0"⟩,
  ⟨"product-overflow", "(* 1152921504606846975 2)", 4, "number out of range"⟩,
  ⟨"divide-exact", "(/ 12 4)", 0, "3"⟩,
  ⟨"divide-rational", "(/ 1 2)", 4, "non-integer result"⟩,
  ⟨"divide-zero", "(/ 5 0)", 3, "division by zero"⟩,
  ⟨"divide-one", "(/ -1)", 0, "-1"⟩,
  ⟨"division-signs",
    "(list (quotient 17 -5) (remainder 17 -5) (modulo 17 -5) (quotient -17 5) (remainder -17 5) (modulo -17 5))",
    0, "(-3 2 -3 -3 -2 3)"⟩,
  ⟨"quotient-overflow", "(quotient -1152921504606846976 -1)", 4, "number out of range"⟩,
  ⟨"radixes", "(list #x1F #b101 #o17 #d10 #e5 #X1f)", 0, "(31 5 15 10 5 31)"⟩,
  ⟨"inexact-literal", "#i5", 4, "number outside the profile"⟩,
  ⟨"decimal-literal", "1.5", 4, "number outside the profile"⟩,
  ⟨"dotted-data", "'(1 (2 . 3) . 4)", 0, "(1 (2 . 3) . 4)"⟩,
  ⟨"nested-quasiquote", "`(a `(b ,(+ 1 2) ,(foo ,(+ 1 3) d) e) f)", 0,
    "(a (quasiquote (b (unquote (+ 1 2)) (unquote (foo 4 d)) e)) f)"⟩,
  ⟨"quasiquote-list", "`(list ,(+ 1 2) 4)", 0, "(list 3 4)"⟩,
  ⟨"quasiquote-quote", "(let ((name 'a)) `(list ,name ',name))", 0, "(list a (quote a))"⟩,
  ⟨"quasiquote-dotted", "`((foo ,(- 10 3)) ,@(cdr '(c)) . ,(car '(cons)))", 0, "((foo 7) . cons)"⟩,
  ⟨"quasiquote-vector", "`#(10 5 ,(- 4 2) ,@(map abs '(-4 3)) 8)", 0, "#(10 5 2 4 3 8)"⟩,
  ⟨"quasiquote-double", "(let ((name1 'x) (name2 'y)) `(a `(b ,,name1 ,',name2 d) e))", 0,
    "(a (quasiquote (b (unquote x) (unquote (quote y)) d)) e)"⟩,
  ⟨"quoted-vector", "'#(1 2)", 0, "#(1 2)"⟩,
  ⟨"vector-expression", "#(1 2)", 2, "vector as expression"⟩,
  ⟨"incomplete", "(+ 1 2", 1, "incomplete datum at 6"⟩,
  ⟨"empty-program", "", 0, "#<unspecified>"⟩,
  ⟨"redefinition", "(define x 1) (define g (lambda () x)) (define x 2) (g)", 0, "2"⟩,
  ⟨"forward-global", "(define h (lambda () (later))) (define later (lambda () 7)) (h)", 0, "7"⟩,
  ⟨"one-armed-if", "(if #t 1)", 2, "unsupported form: if"⟩,
  ⟨"keyword-variable", "(let ((if 1)) if)", 2, "keyword as variable: if"⟩,
  ⟨"immutable-literal", "(set-car! '(1 2) 3)", 3, "immutable object"⟩,
  ⟨"arity", "((lambda (x) x))", 3, "wrong number of arguments"⟩,
  ⟨"letrec-undefined", "(letrec ((x y) (y 1)) x)", 3, "undefined variable"⟩,
  ⟨"map-order", "(let ((acc '())) (map (lambda (x) (set! acc (cons x acc)) x) '(1 2 3)) acc)", 0,
    "(3 2 1)"⟩,
  ⟨"for-each", "(let ((s 0)) (for-each (lambda (x y) (set! s (+ s (* x y)))) '(1 2) '(3 4)) s)",
    0, "11"⟩,
  ⟨"tail-loop", "(letrec ((loop (lambda (n) (if (= n 0) 'done (loop (- n 1)))))) (loop 100))", 0,
    "done"⟩,
  ⟨"gcd-lcm", "(list (gcd 32 -36) (gcd) (lcm 32 -36) (lcm))", 0, "(4 0 288 1)"⟩,
  ⟨"rounding", "(list (floor 7) (ceiling -7) (truncate 3) (round -2))", 0, "(7 -7 3 -2)"⟩,
  ⟨"numeric-types", "(list (complex? 1) (real? 'a) (rational? 2) (inexact? 1) (exact? 'a))", 3,
    "wrong type of argument"⟩,
  ⟨"numeric-types-numbers", "(list (complex? 1) (real? 'a) (rational? 2) (inexact? 1))", 0,
    "(#t #f #t #f)"⟩,
  ⟨"comparisons", "(list (< 1 2 3) (< 1 3 2) (= 1 1 1) (>= 3 3 1))", 0, "(#t #f #t #t)"⟩,
  ⟨"max-min", "(list (max 1 5 3) (min 4 -2))", 0, "(5 -2)"⟩,
  ⟨"append", "(append '(1) '(2 3) '() '(4 . 5))", 0, "(1 2 3 4 . 5)"⟩,
  ⟨"member-assoc", "(list (memv 2 '(1 2 3)) (assq 'b '((a 1) (b 2))) (memq 'z '(a)))", 0,
    "((2 3) (b 2) #f)"⟩,
  ⟨"cxr", "(list (caddr '(1 2 3)) (cdadr '(1 (2 3))) (caar '((4))))", 0, "(3 (3) 4)"⟩,
  ⟨"list-ref", "(list-ref '(a b c) 2)", 0, "c"⟩,
  ⟨"list-ref-range", "(list-ref '(a b c) 3)", 3, "index out of range"⟩,
  ⟨"length-reverse", "(list (length '(1 2 3)) (reverse '(1 2 3)))", 0, "(3 (3 2 1))"⟩,
  ⟨"string-char", "(list \"a\\\"b\" #\\a #\\space #\\A)", 0, "(\"a\\\"b\" #\\a #\\space #\\A)"⟩,
  ⟨"procedure-write", "car", 0, "#<procedure>"⟩,
  ⟨"cond-test-clause", "(cond (#f 1) ((+ 1 1)) (else 3))", 0, "2"⟩,
  ⟨"case-else", "(case 'x ((a) 1) (else 2))", 0, "2"⟩,
  ⟨"case-none", "(case 'x ((a) 1))", 0, "#<unspecified>"⟩,
  ⟨"empty-vectors", "(list (eqv? '#() '#()) (let ((v '#())) (eqv? v v)))", 0, "(#f #t)"⟩,
  ⟨"predicates",
    "(list (number? 1) (integer? 'a) (exact? 3) (inexact? 3) (procedure? car) (procedure? 'car) (vector? '#(1)) (boolean? #f) (null? '()) (pair? '()))",
    0, "(#t #f #t #f #t #f #t #t #t #f)"⟩,
  ⟨"not", "(list (not #f) (not '()) (not 0))", 0, "(#t #f #f)"⟩,
  ⟨"list-to-vector", "(list->vector '(1 2))", 0, "#(1 2)"⟩,
  ⟨"subtraction", "(list (abs -7) (- 5) (- 5 7))", 0, "(7 -5 -2)"⟩,
  ⟨"subtraction-three", "(- 1 2 3)", 3, "wrong number of arguments"⟩,
  ⟨"abs-overflow", "(abs -1152921504606846976)", 4, "number out of range"⟩,
  ⟨"parity", "(list (even? -2) (odd? -3) (zero? 0) (positive? -1) (negative? -1))", 0,
    "(#t #t #t #f #t)"⟩,
  ⟨"unbound", "(foo)", 3, "unbound variable: foo"⟩,
  ⟨"set-unbound", "(set! zz 1)", 3, "unbound variable: zz"⟩,
  ⟨"unexpected-close", ")", 1, "unexpected ) at 0"⟩,
  ⟨"bad-dot", "(1 . 2 3)", 1, "misplaced dot at 7"⟩,
  ⟨"bad-char", "#\\foo", 1, "unknown character name at 0"⟩,
  ⟨"not-procedure", "(1 2)", 3, "not a procedure"⟩,
  ⟨"empty-combination", "()", 2, "empty combination"⟩,
  ⟨"duplicate", "(lambda (x x) x)", 2, "duplicate variable: x"⟩,
  ⟨"begin-definitions", "(begin (define a 1) (define b 2)) (+ a b)", 0, "3"⟩,
  ⟨"begin-expression", "(begin 1 2 3)", 0, "3"⟩,
  ⟨"escape-arity", "(call/cc (lambda (k) (k 1 2)))", 3, "wrong number of arguments"⟩,
  ⟨"map-lists", "(map + '(1 2) '(10 20))", 0, "(11 22)"⟩,
  ⟨"map-unequal", "(map + '(1 2) '(10))", 3, "wrong type of argument"⟩,
  ⟨"or-and-empty", "(list (or #f #f) (and) (or))", 0, "(#f #t #f)"⟩,
  ⟨"case-folding", "(list 'FooBar (quote ABC))", 0, "(foobar abc)"⟩,
  ⟨"define-shorthand", "(define (f x) x)", 2, "unsupported form: define"⟩,
  ⟨"let-star", "(let* ((x 1)) x)", 2, "unsupported form: let*"⟩,
  ⟨"internal-define", "(lambda () (define x 1) x)", 2, "definition in expression context"⟩,
  ⟨"duplicate-case", "(case 1 ((1 2) 'a) ((2) 'b))", 2, "duplicate case datum"⟩,
  ⟨"else-misplaced", "(else 1)", 2, "misplaced keyword: else"⟩,
  ⟨"letrec-mutual", "(letrec ((ev? (lambda (n) (if (= n 0) #t (od? (- n 1))))) (od? (lambda (n) (if (= n 0) #f (ev? (- n 1)))))) (list (ev? 10) (od? 7)))",
    0, "(#t #t)"⟩
]

end Demos.Scheme.Corpus
