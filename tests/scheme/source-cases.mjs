// Source-level cases for the deliberately small Scheme compiler.
export const sourceCases = [
  {name: 'addition', source: '(+ 100 23)', expected: '123'},
  {name: 'word-wrap', source: '(+ 18446744073709551615 1)', expected: '0'},
  {name: 'argument-order', source: '((lambda (a b) (- a b)) 10 3)', expected: '7'},
  {name: 'pending-operand', source: '(+ 100 ((lambda () 23)))', expected: '123'},
  {name: 'first-class-arithmetic', source: '(let ((add +)) (add 100 23))', expected: '123'},
  {name: 'truth', source: '(if 0 7 999)', expected: '7'},
  {name: 'false', source: '(if #f 999 7)', expected: '7'},
  {name: 'branch-join', source: '(+ (if #f 99 10) (if #t 3 99))', expected: '13'},
  {name: 'unit', source: '(if #f 1)', expected: '0', kind: 3},
  {name: 'empty-begin', source: '(begin)', expected: '0', kind: 3},
  {name: 'empty-program', source: '', expected: '0', kind: 3},
  {name: 'shadowing', source: `
    (define x 42)
    (define f (let ((x 3)) (lambda () x)))
    (+ (f) x)`, expected: '45'},
  {name: 'parallel-let', source: `
    (let ((x 10)) (let ((x 3) (y x)) (- y x)))`, expected: '7'},
  {name: 'builtin-shadowing', source: `
    (let ((+ (lambda (a b) (- a b)))) (+ 10 3))`, expected: '7'},
  {name: 'callcc-shadowing', source: `
    (let ((call/cc (lambda (x) (+ x 1)))) (call/cc 6))`, expected: '7'},
  {name: 'nested-captures', source: `
    (let ((x 7)) (((lambda () (lambda () x)))))`, expected: '7'},
  {name: 'shared-mutation', source: `
    (let ((x 1))
      (let ((get (lambda () x)) (put (lambda (v) (set! x v))))
        (put 9) (get)))`, expected: '9'},
  {name: 'lexical-mutation', source: `
    (define x 100)
    (+ (let ((x 1)) (set! x 7) x) x)`, expected: '107'},
  {name: 'definition-only', source: '(define x 7)', expected: '0', kind: 3},
  {name: 'runtime-type-error', source: '(+ #t 1)', expected: '0', error: 5},
  {name: 'runtime-arity-error', source: '(define (f x) x) (f)', expected: '0', error: 8},
  {name: 'tail-10000', source: `
    (define (countdown n) (if (= n 0) 7 (countdown (- n 1))))
    (countdown 10000)`, expected: '7', capacity: 32, tail: true, skipSteps: true},
  {name: 'tail-100', source: `
    (define (countdown n) (if (= n 0) 7 (countdown (- n 1))))
    (countdown 100)`, expected: '7', capacity: 32, tail: true},
  {name: 'mutual-recursion', source: `
    (define (even n) (if (= n 0) #t (odd (- n 1))))
    (define (odd n) (if (= n 0) #f (even (- n 1))))
    (if (even 100) 7 999)`, expected: '7'},
  {name: 'first-class-callcc', source: `
    (let ((capture call/cc)) (capture (lambda (k) (k 7))))`, expected: '7'},
  {name: 'nested-escape', source: `
    (+ 100 (call/cc (lambda (k) ((lambda () (k 7) 999)) 999)))`, expected: '107'},
  {name: 'multi-shot', source: `
    (define counter 0)
    (define saved #f)
    (define result 0)
    (set! result (+ 100 (call/cc (lambda (k) (set! saved k) 10))))
    (if (< counter 2)
        (begin (set! counter (+ counter 1)) (saved counter))
        result)`, expected: '102', counter: '2'},
];

export const rejectedSources = [
  '-1', '18446744073709551616', '1.5', '1/2', '"hello"', "'x", '()', 'missing',
  '(lambda x x)', '(lambda (x x) x)', '(lambda (if) 1)', '(lambda (x))',
  '(let ((x 1) (x 2)) x)', '(let ((x)) x)', '(let loop ((x 1)) x)',
  '(if #t)', '(+ 1)', '(set! missing 1)', '(lambda () (define x 1) x)',
  '(define x 1) (define x 2) x', '(define 1 2)', '(1 . 2)',
];
