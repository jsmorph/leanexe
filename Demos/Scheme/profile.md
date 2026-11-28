# The profile's choices

R4RS leaves some behavior to the implementation, permits restrictions, and calls some situations errors without requiring their detection.  This document states the choices of this interpreter, each beside the clause that permits it.  The reference semantics of `Demos/Scheme/Semantics/` defines each choice, and the executable machine implements the same choice, so a test can compare their outcomes byte for byte.  [The clause inventory](inventory.md) lists the essential features and their status.

## Numbers

The profile implements exact integers and no other numbers.  §6.5.3 permits an implementation to support a coherent subset of the numerical tower and a limited range of each type, and it requires exact integers throughout the range of indexes and lengths.  The supported range is the signed 61-bit range from −2^60 to 2^60 − 1, which contains every length and index that the heap can hold.  The reference semantics computes every numeric procedure over Lean's `Int`, and a separate predicate, `Numeric.Profile.representable`, decides whether an exact result lies in the range.  A result or a numeral outside the range ends the run with an implementation restriction, which §1.3.2 and §6.5.3 permit.  A later profile with integers of any size replaces the predicate and the machine's numeric layer, and it changes no rule of the semantics.

| Situation | Outcome | Clause |
|---|---|---|
| An exact result in the range | The result, even when an intermediate machine word would overflow, as in `(+ 1152921504606846975 1 -1)` | §6.5.3 |
| An exact integer result outside the range | Implementation restriction | §6.5.3, §1.3.2 |
| `(/ n1 n2)` whose quotient is an integer | The quotient, so `(/ 12 4)` is 3 | §6.5.5 |
| `(/ n1 n2)` whose quotient is no integer, such as `(/ 1 2)` | Implementation restriction | §6.5.3 |
| Division by zero in `/`, `quotient`, `remainder`, or `modulo` | Error | §6.5.5, §1.3.2 |
| A numeral with a fraction, a decimal point, an exponent, the prefix `#i`, or a complex part | Implementation restriction | §6.5.3, §6.5.4 |
| A numeral with the prefix `#e` | The exact integer it denotes, when it denotes one | §6.5.4 |
| `quotient`, `remainder`, `modulo` | Truncated quotient, remainder with the sign of the dividend, and modulo with the sign of the divisor | §6.5.5 |
| `exact?` and `inexact?` | `#t` and `#f` for every number | §6.5.5 |
| `number?`, `complex?`, `real?`, `rational?`, `integer?` | `#t` exactly for numbers | §6.5.5 |
| `floor`, `ceiling`, `truncate`, `round` | The argument | §6.5.5 |

## Syntax and data

| Choice | Clause |
|---|---|
| Identifiers are folded to lower case when read.  Characters and strings keep their case. | §2, §6.4 |
| The syntactic keywords of §2.1 are reserved, and a binding or a reference of one as a variable is a syntax error. | §2.1, §7.1.1 |
| Characters are ASCII.  The character names are `space` and `newline`, in any case. | §6.6, §7.1.1 |
| Whitespace is space, line feed, tab, carriage return, and form feed.  A byte above 127 outside a comment, or a control byte other than whitespace outside a comment, a string, and a character, is a read error. | §2.2, §6.6 |
| A token that begins with a digit, with `+`, `-`, or `.` and is no peculiar identifier, or with `#` and one of the letters `b o d x e i`, is a numeral.  A numeral of prefixes, an optional sign, and digits of its radix denotes an exact integer, unless a prefix is `#i`.  Any other numeral whose bytes are digits of its radix, `#`, `.`, `/`, `+`, `-`, `@`, or one of the letters `e s f d l i` reports the implementation restriction for numbers outside the profile, and a numeral with another byte is a read error. | §6.5.3, §6.5.4, §7.1.1 |
| `#f` is the only false value.  The empty list is true and distinct from `#f`. | §3.2, §6.1 |
| The operator of a call is evaluated first, and then the operands from left to right, in every call. | §4.1.3 |
| `letrec` follows the rewrite rule of §7.3: every location of the group is bound to the undefined marker, every initializer is evaluated into a fresh temporary, and then each value is assigned before the body. | §4.2.2, §7.3 |
| Every derived form follows its rewrite rule of §7.3, with temporaries that no source identifier can name and with `memv` as the standard procedure, which no binding can capture. | §7.3 |
| `(letrec () body)` is `(let () body)`, since the rule's second `let` would have no body. | §7.3 |
| Quasiquote builds a fresh pair for every pair of a list template and a fresh vector for every vector template, and its introduced calls of `cons`, `list`, `append`, and `list->vector` name the standard procedures, which no binding can capture. | §4.2.6, §7.1.4 |
| The symbols `quasiquote`, `unquote`, and `unquote-splicing` in a template position other than those of §7.1.4 are a syntax error. | §4.2.6 |
| Quoted constants and the program's text are immutable, and storing into them is an error. | §3.5, §4.1.2 |
| A quoted constant denotes one object for every evaluation of its quotation. | §4.1.2 |
| A program is read whole before any form runs, so a read error ends the run before any evaluation.  Each top-level form is expanded when the run reaches it, so a syntax error ends the run at that form. | §5.1 |
| A top-level `begin` whose forms are all definitions is the sequence of those definitions.  Any other `begin` is an expression. | §5.2, §7.1.5 |
| A top-level definition of a bound variable assigns it, and one of an unbound variable binds a fresh location. | §5.2.1 |
| The value of a program is the value of its last form, and a definition's value is the unspecified value. | §5.1 |

## Procedures and control

| Choice | Clause |
|---|---|
| `call-with-current-continuation` and `call/cc` are bound to one procedure value, and both bindings can be passed, applied, assigned, or shadowed. | §6.9 |
| An escape procedure has unlimited extent and accepts one argument. | §6.9, §7.2 |
| A call of a procedure with a rest parameter stores fresh pairs for the surplus arguments, also when `apply` supplies them from a list. | §4.1.4, §6.9 |
| `map` calls its procedure on the elements from left to right, and `for-each` does as §6.9 requires. | §6.9 |
| `map` and `for-each` signal an error when a list ends before another or is not a proper list, after the calls of the earlier elements. | §6.9, §1.3.2 |
| An empty vector or string is a distinct object, so `eqv?` of two of them is `#f`. | §6.2 |
| `length`, `reverse`, `append`, `list-ref`, `memq`, `memv`, `assq`, `assv`, `list->vector`, and `apply` signal an error for an argument that must be a list and is no proper list, a circular list included, and `assq` and `assv` for an element of the list that is no pair.  `map`, `for-each`, `apply`, and `call-with-current-continuation` signal an error for a first argument that is no procedure before any call. | §6.3, §6.9, §1.3.2 |
| `eq?` and `eqv?` agree on every value of this profile. | §6.2 |

## Errors and outcomes

Every error situation that the interpreter can detect is signalled, including those that the report calls only "an error", which §1.3.2 permits.  The report's required signals are a subset of these.  A run ends with one of the outcomes below, and the executable's result is a status byte followed by text.  The text of a value is its external representation as `write` produces it, with `#<procedure>` for a procedure and `#<unspecified>` for the unspecified value, which have no standard representation (§3.3).

| Status | Outcome | Text |
|---|---|---|
| 0 | Value | The value's external representation |
| 1 | Read error | The kind and the byte offset at which the reader detected it |
| 2 | Syntax error | The kind of the malformed form |
| 3 | Error | The kind, with an irritant for an unbound variable |
| 4 | Implementation restriction | The kind |
| 5 | Out of space | None |
| 6 | Fuel exhausted | None |
| 7 | Output limit | None |

The reference semantics has no bound on its store and no fuel in its rules, so its outcomes are those of statuses 0 to 4, and a run that reaches none of them diverges.  The executable adds statuses 5 to 7 for its arena, its step budget, and its output buffer.
