# Clause inventory of R4RS's essential features

This inventory lists every form and procedure that the [Revised⁴ Report](https://standards.scheme.org/official/r4rs.pdf) marks essential, at the arities that the report marks essential, with the clause that defines it and its status in this interpreter.  §1.3.1 makes a feature essential only when its entry says so, so a non-essential arity of an essential procedure, such as `(- z1 z2 z3)` or `(apply proc arg1 … args)`, appears under its own row as outside the profile.  [The profile](profile.md) states the implementation choices that the report leaves open, each with its clause, and [the journal](devnotes.md) records the stages of the work.

A status of *this request* assigns the feature to milestones 1 and 2: the reference semantics of `Demos/Scheme/Semantics/` and the executable machine compiled by the verified compiler.  The Reference column names the definitions of the namespace `Demos.Scheme.Semantics` that implement the feature, the Machine column those of the executable machine, and the Cases column the programs of the corpus `Demos.Scheme.Corpus.all` that test it.  The theorem `corpus_outcomes` of `Demos/Scheme/Semantics/CorpusCheck.lean` states that the reference semantics gives every program of the corpus its expected outcome, which the corpus states by hand.  A status of *milestone 4* assigns the feature to the complete language of the design's fourth milestone.  The report's syntax keywords `=>`, `delay`, `do`, `let*`, and `else` in a position other than a final clause belong to non-essential forms, and the reserved-keyword rule of §2.1 still applies to them.

## Syntax

| Form | Clause | Status | Reference | Machine | Cases |
|---|---|---|---|---|---|
| Variable reference | §4.1.1 | This request | `expand`, `step` on `.var` | | `shared-cell`, `unbound`, `letrec-undefined` |
| `(quote datum)`, `'datum` | §4.1.2 | This request | `expand`, `allocExpr` | | `dotted-data`, `quoted-vector`, `immutable-literal` |
| Self-evaluating constants: booleans, numbers, characters, strings | §4.1.2 | This request | `expand` | | `string-char`, `range-max` |
| Procedure call `(operator operand …)` | §4.1.3 | This request | `step`, `Frame.fn`, `Frame.arg` | | `operand-order`, `operator-first`, `not-procedure`, `arity` |
| `(lambda formals body)`, with formals `(var …)`, `var`, and `(var … . var)` | §4.1.4 | This request | `expand`, `lambdaFormals`, `bindArgs` | | `apply-rest-fresh`, `fresh-reentry`, `duplicate`, `arity` |
| `(if test consequent alternate)` | §4.1.5 | This request | `expand`, `Frame.branch` | | `repeated-escape`, `one-armed-if` |
| `(set! var expression)` | §4.1.6 | This request | `expand`, `Frame.assign` | | `shared-cell`, `set-unbound` |
| `(cond clause …)`, with `(test expression …)`, `(test)`, and a final `(else expression …)` | §4.2.1, §7.3 | This request | `expandCond` | | `cond-test-clause`, `else-misplaced` |
| `(case key clause …)`, with a final `else` clause | §4.2.1, §7.3 | This request | `expandCase` | | `case-capture`, `case-else`, `case-none`, `duplicate-case` |
| `(and test …)` | §4.2.1, §7.3 | This request | `expandAnd`, `andCore` | | `and-temporaries`, `and-once`, `or-and-empty` |
| `(or test …)` | §4.2.1, §7.3 | This request | `expandOr`, `orCore` | | `or-42`, `or-temporaries`, `or-once`, `or-and-empty` |
| `(let bindings body)` | §4.2.2, §7.3 | This request | `letCore` | | `or-42`, `keyword-variable` |
| `(letrec bindings body)` | §4.2.2, §7.3 | This request | `letrecCore` | | `letrec-reentry`, `letrec-staging`, `letrec-mutual`, `letrec-undefined` |
| `(begin expression …)` | §4.2.3, §7.3 | This request | `beginCore` | | `begin-expression` |
| `(quasiquote template)`, `` `template ``, with `unquote`, `unquote-splicing`, nesting, and vector templates | §4.2.6, §7.1.4 | This request | `qq` | | `quasiquote-capture`, `nested-quasiquote`, `quasiquote-vector`, `quasiquote-double` |
| Top-level `(define var expression)` | §5.2, §5.2.1 | This request | `expandTop`, `Frame.define` | | `redefinition`, `forward-global`, `define-shorthand` |
| Top-level `(begin definition …)` | §5.2, §7.1.5 | This request | `expandTops`, `allDefinitions` | | `begin-definitions`, `internal-define` |
| A program: a sequence of commands and definitions | §5.1, §7.1.5 | This request | `start`, `prepare`, `Frame.top` | | `toplevel-reentry`, `empty-program` |

The forms below are not essential, and the profile omits them.

| Form | Clause |
|---|---|
| `(if test consequent)` | §4.1.5 |
| `(test => recipient)` clauses of `cond` | §4.2.1 |
| `let*` | §4.2.2 |
| `do` and named `let` | §4.2.4 |
| `delay` | §4.2.5 |
| `(define (var formals) body)` and `(define (var . formal) body)` | §5.2 |
| Internal definitions | §5.2.2 |

## External representations

| Feature | Clause | Status | Reference | Machine | Cases |
|---|---|---|---|---|---|
| Identifiers, with case folding | §2.1, §7.1.1 | This request | `readAtom` | | `case-folding` |
| Comments and whitespace | §2.2, §7.1.1 | This request | `skipAtmosphere` | | `repeated-escape` |
| Booleans `#t`, `#f` | §6.1, §7.1.1 | This request | `readHash` | | `predicates` |
| Integers in radixes 2, 8, 10, and 16, with exactness prefixes | §6.5.4, §7.1.1 | This request | `readNumeral` | | `radixes`, `inexact-literal`, `decimal-literal`, `range-literal` |
| Characters `#\x`, `#\space`, `#\newline` | §6.6, §7.1.1 | This request | `readChar` | | `string-char`, `bad-char` |
| Strings with `\"` and `\\` | §6.7, §7.1.1 | This request | `readString` | | `string-char` |
| Lists, dotted lists, and vectors | §6.3, §6.8, §7.1.2 | This request | `readList`, `readVector` | | `dotted-data`, `bad-dot`, `incomplete`, `unexpected-close` |
| Abbreviations `'`, `` ` ``, `,`, `,@` | §6.3, §7.1.2 | This request | `abbreviated` | | `quasiquote-quote` |

## Procedures

| Procedures | Arities | Clause | Status | Reference | Machine | Cases |
|---|---|---|---|---|---|---|
| `not`, `boolean?` | 1 | §6.1 | This request | `applySimple` | | `not`, `predicates` |
| `eqv?`, `eq?` | 2 | §6.2 | This request | `eqv` | | `callcc-names`, `empty-vectors` |
| `equal?` | 2 | §6.2 | Milestone 4 | | | |
| `pair?`, `car`, `cdr`, `null?`, `list?`, `length`, `reverse` | 1 | §6.3 | This request | `applySimple` | | `cycle-list`, `length-reverse`, `predicates` |
| `cons`, `set-car!`, `set-cdr!`, `list-ref`, `memq`, `memv`, `assq`, `assv` | 2 | §6.3 | This request | `applySimple`, `memFind`, `assFind` | | `alias-mutation`, `list-ref`, `list-ref-range`, `member-assoc` |
| `caar` through `cddddr`, the 28 compositions of two to four `car`s and `cdr`s | 1 | §6.3 | This request | `cxrNames`, `cxrWalk` | | `cxr` |
| `list`, `append` | 0 or more | §6.3 | This request | `State.list`, `applySimple` | | `append` |
| `member`, `assoc` | 2 | §6.3 | Milestone 4 | | | |
| `symbol?`, `symbol->string`, `string->symbol` | 1 | §6.4 | Milestone 4 | | | |
| `number?`, `complex?`, `real?`, `rational?`, `integer?`, `exact?`, `inexact?` | 1 | §6.5.5 | This request | `applyNumeric`, `Numeric.eval` | | `predicates`, `numeric-types`, `numeric-types-numbers` |
| `=`, `<`, `>`, `<=`, `>=` | 2 or more | §6.5.5 | This request | `Numeric.chain` | | `comparisons` |
| `zero?`, `positive?`, `negative?`, `odd?`, `even?`, `abs` | 1 | §6.5.5 | This request | `Numeric.eval` | | `parity`, `subtraction`, `abs-overflow` |
| `max`, `min` | 1 or more | §6.5.5 | This request | `Numeric.eval` | | `max-min` |
| `+`, `*` | 0 or more | §6.5.5 | This request | `Numeric.eval`, `numResult` | | `sum-cancel`, `sum-overflow`, `product-zero`, `product-overflow` |
| `-`, `/` | 1 or 2 | §6.5.5 | This request | `Numeric.eval`, `Numeric.divide` | | `subtraction`, `subtraction-three`, `divide-exact`, `divide-rational`, `divide-zero`, `divide-one` |
| `quotient`, `remainder`, `modulo` | 2 | §6.5.5 | This request | `Numeric.eval` | | `division-signs`, `quotient-overflow` |
| `gcd`, `lcm` | 0 or more | §6.5.5 | This request | `Numeric.eval` | | `gcd-lcm` |
| `floor`, `ceiling`, `truncate`, `round` | 1 | §6.5.5 | This request | `Numeric.eval` | | `rounding` |
| `number->string`, `string->number` | 1 or 2 | §6.5.6 | Milestone 4 | | | |
| `char?`, `char-alphabetic?`, `char-numeric?`, `char-whitespace?`, `char-upper-case?`, `char-lower-case?`, `char->integer`, `integer->char`, `char-upcase`, `char-downcase` | 1 | §6.6 | Milestone 4 | | | |
| `char=?`, `char<?`, `char>?`, `char<=?`, `char>=?`, `char-ci=?`, `char-ci<?`, `char-ci>?`, `char-ci<=?`, `char-ci>=?` | 2 | §6.6 | Milestone 4 | | | |
| `string?`, `string-length`, `string->list`, `list->string` | 1 | §6.7 | Milestone 4 | | | |
| `make-string` | 1 or 2 | §6.7 | Milestone 4 | | | |
| `string` | 0 or more | §6.7 | Milestone 4 | | | |
| `string-ref` | 2 | §6.7 | Milestone 4 | | | |
| `string-set!`, `substring` | 3 | §6.7 | Milestone 4 | | | |
| `string=?`, `string<?`, `string>?`, `string<=?`, `string>=?`, `string-ci=?`, `string-ci<?`, `string-ci>?`, `string-ci<=?`, `string-ci>=?` | 2 | §6.7 | Milestone 4 | | | |
| `string-append` | 0 or more | §6.7 | Milestone 4 | | | |
| `vector?`, `list->vector` | 1 | §6.8 | This request | `applySimple` | | `predicates`, `list-to-vector`, `quasiquote-vector` |
| `make-vector`, `vector-length`, `vector->list` | 1 | §6.8 | Milestone 4 | | | |
| `vector` | 0 or more | §6.8 | Milestone 4 | | | |
| `vector-ref` | 2 | §6.8 | Milestone 4 | | | |
| `vector-set!` | 3 | §6.8 | Milestone 4 | | | |
| `procedure?` | 1 | §6.9 | This request | `applySimple` | | `predicates` |
| `apply` | 2 | §6.9 | This request | `applyPrim` | | `apply-rest-fresh`, `callcc-through-apply` |
| `map`, `for-each` | 2 or more | §6.9 | This request | `mapNext`, `forEachNext` | | `map-reentry`, `map-order`, `map-lists`, `map-unequal`, `for-each` |
| `call-with-current-continuation`, with the alias `call/cc` | 1 | §6.9 | This request | `applyPrim`, `Proc.escape` | | `repeated-escape`, `letrec-reentry`, `toplevel-reentry`, `escape-arity` |
| `call-with-input-file`, `call-with-output-file` | 2 | §6.10.1 | Milestone 4 | | | |
| `input-port?`, `output-port?`, `open-input-file`, `open-output-file`, `close-input-port`, `close-output-port`, `eof-object?` | 1 | §6.10.1, §6.10.2 | Milestone 4 | | | |
| `current-input-port`, `current-output-port` | 0 | §6.10.1 | Milestone 4 | | | |
| `read`, `read-char`, `peek-char`, `newline` | 0 or 1 | §6.10.2, §6.10.3 | Milestone 4 | | | |
| `write`, `display`, `write-char` | 1 or 2 | §6.10.3 | Milestone 4 | | | |
| `load` | 1 | §6.10.4 | Milestone 4 | | | |

The alias `call/cc` is no R4RS name.  The design asks for it, and it is an ordinary top-level binding to the same procedure value as `call-with-current-continuation`.  The non-essential arities and procedures that the profile omits include `(- z1 z2 z3 …)`, `(/ z1 z2 z3 …)`, `(apply proc arg1 … args)`, `(make-vector k fill)`, `list-tail`, `string-copy`, `string-fill!`, `vector-fill!`, `force`, `char-ready?`, `with-input-from-file`, `with-output-to-file`, `transcript-on`, `transcript-off`, and the inexact and complex procedures of §6.5.5.
