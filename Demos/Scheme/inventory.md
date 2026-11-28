# Clause inventory of R4RS's essential features

This inventory lists every form and procedure that the [Revised⁴ Report](https://standards.scheme.org/official/r4rs.pdf) marks essential, at the arities that the report marks essential, with the clause that defines it and its status in this interpreter.  §1.3.1 makes a feature essential only when its entry says so, so a non-essential arity of an essential procedure, such as `(- z1 z2 z3)` or `(apply proc arg1 … args)`, appears under its own row as outside the profile.  [The profile](profile.md) states the implementation choices that the report leaves open, each with its clause, and [the journal](devnotes.md) records the stages of the work.

A status of *this request* assigns the feature to milestones 1 and 2: the reference semantics of `Demos/Scheme/Semantics/` and the executable machine compiled by the verified compiler.  When a stage implements and tests a feature, the row names the reference definition, the machine definition, and the cases that test it.  A status of *milestone 4* assigns the feature to the complete language of the design's fourth milestone.  The report's syntax keywords `=>`, `delay`, `do`, `let*`, and `else` in a position other than a final clause belong to non-essential forms, and the reserved-keyword rule of §2.1 still applies to them.

## Syntax

| Form | Clause | Status | Reference | Machine | Cases |
|---|---|---|---|---|---|
| Variable reference | §4.1.1 | This request | | | |
| `(quote datum)`, `'datum` | §4.1.2 | This request | | | |
| Self-evaluating constants: booleans, numbers, characters, strings | §4.1.2 | This request | | | |
| Procedure call `(operator operand …)` | §4.1.3 | This request | | | |
| `(lambda formals body)`, with formals `(var …)`, `var`, and `(var … . var)` | §4.1.4 | This request | | | |
| `(if test consequent alternate)` | §4.1.5 | This request | | | |
| `(set! var expression)` | §4.1.6 | This request | | | |
| `(cond clause …)`, with `(test expression …)`, `(test)`, and a final `(else expression …)` | §4.2.1, §7.3 | This request | | | |
| `(case key clause …)`, with a final `else` clause | §4.2.1, §7.3 | This request | | | |
| `(and test …)` | §4.2.1, §7.3 | This request | | | |
| `(or test …)` | §4.2.1, §7.3 | This request | | | |
| `(let bindings body)` | §4.2.2, §7.3 | This request | | | |
| `(letrec bindings body)` | §4.2.2, §7.3 | This request | | | |
| `(begin expression …)` | §4.2.3, §7.3 | This request | | | |
| `(quasiquote template)`, `` `template ``, with `unquote`, `unquote-splicing`, nesting, and vector templates | §4.2.6, §7.1.4 | This request | | | |
| Top-level `(define var expression)` | §5.2, §5.2.1 | This request | | | |
| Top-level `(begin definition …)` | §5.2, §7.1.5 | This request | | | |
| A program: a sequence of commands and definitions | §5.1, §7.1.5 | This request | | | |

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
| Identifiers, with case folding | §2.1, §7.1.1 | This request | | | |
| Comments and whitespace | §2.2, §7.1.1 | This request | | | |
| Booleans `#t`, `#f` | §6.1, §7.1.1 | This request | | | |
| Integers in radixes 2, 8, 10, and 16, with exactness prefixes | §6.5.4, §7.1.1 | This request | | | |
| Characters `#\x`, `#\space`, `#\newline` | §6.6, §7.1.1 | This request | | | |
| Strings with `\"` and `\\` | §6.7, §7.1.1 | This request | | | |
| Lists, dotted lists, and vectors | §6.3, §6.8, §7.1.2 | This request | | | |
| Abbreviations `'`, `` ` ``, `,`, `,@` | §6.3, §7.1.2 | This request | | | |

## Procedures

| Procedures | Arities | Clause | Status | Reference | Machine | Cases |
|---|---|---|---|---|---|---|
| `not`, `boolean?` | 1 | §6.1 | This request | | | |
| `eqv?`, `eq?` | 2 | §6.2 | This request | | | |
| `equal?` | 2 | §6.2 | Milestone 4 | | | |
| `pair?`, `car`, `cdr`, `null?`, `list?`, `length`, `reverse` | 1 | §6.3 | This request | | | |
| `cons`, `set-car!`, `set-cdr!`, `list-ref`, `memq`, `memv`, `assq`, `assv` | 2 | §6.3 | This request | | | |
| `caar` through `cddddr`, the 28 compositions of two to four `car`s and `cdr`s | 1 | §6.3 | This request | | | |
| `list`, `append` | 0 or more | §6.3 | This request | | | |
| `member`, `assoc` | 2 | §6.3 | Milestone 4 | | | |
| `symbol?`, `symbol->string`, `string->symbol` | 1 | §6.4 | Milestone 4 | | | |
| `number?`, `complex?`, `real?`, `rational?`, `integer?`, `exact?`, `inexact?` | 1 | §6.5.5 | This request | | | |
| `=`, `<`, `>`, `<=`, `>=` | 2 or more | §6.5.5 | This request | | | |
| `zero?`, `positive?`, `negative?`, `odd?`, `even?`, `abs` | 1 | §6.5.5 | This request | | | |
| `max`, `min` | 1 or more | §6.5.5 | This request | | | |
| `+`, `*` | 0 or more | §6.5.5 | This request | | | |
| `-`, `/` | 1 or 2 | §6.5.5 | This request | | | |
| `quotient`, `remainder`, `modulo` | 2 | §6.5.5 | This request | | | |
| `gcd`, `lcm` | 0 or more | §6.5.5 | This request | | | |
| `floor`, `ceiling`, `truncate`, `round` | 1 | §6.5.5 | This request | | | |
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
| `vector?`, `list->vector` | 1 | §6.8 | This request | | | |
| `make-vector`, `vector-length`, `vector->list` | 1 | §6.8 | Milestone 4 | | | |
| `vector` | 0 or more | §6.8 | Milestone 4 | | | |
| `vector-ref` | 2 | §6.8 | Milestone 4 | | | |
| `vector-set!` | 3 | §6.8 | Milestone 4 | | | |
| `procedure?` | 1 | §6.9 | This request | | | |
| `apply` | 2 | §6.9 | This request | | | |
| `map`, `for-each` | 2 or more | §6.9 | This request | | | |
| `call-with-current-continuation`, with the alias `call/cc` | 1 | §6.9 | This request | | | |
| `call-with-input-file`, `call-with-output-file` | 2 | §6.10.1 | Milestone 4 | | | |
| `input-port?`, `output-port?`, `open-input-file`, `open-output-file`, `close-input-port`, `close-output-port`, `eof-object?` | 1 | §6.10.1, §6.10.2 | Milestone 4 | | | |
| `current-input-port`, `current-output-port` | 0 | §6.10.1 | Milestone 4 | | | |
| `read`, `read-char`, `peek-char`, `newline` | 0 or 1 | §6.10.2, §6.10.3 | Milestone 4 | | | |
| `write`, `display`, `write-char` | 1 or 2 | §6.10.3 | Milestone 4 | | | |
| `load` | 1 | §6.10.4 | Milestone 4 | | | |

The alias `call/cc` is no R4RS name.  The design asks for it, and it is an ordinary top-level binding to the same procedure value as `call-with-current-continuation`.  The non-essential arities and procedures that the profile omits include `(- z1 z2 z3 …)`, `(/ z1 z2 z3 …)`, `(apply proc arg1 … args)`, `(make-vector k fill)`, `list-tail`, `string-copy`, `string-fill!`, `vector-fill!`, `force`, `char-ready?`, `with-input-from-file`, `with-output-to-file`, `transcript-on`, `transcript-off`, and the inexact and complex procedures of §6.5.5.
