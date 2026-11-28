module

public import Demos.Scheme.Report
public import Demos.Scheme.Semantics.Results

@[expose] public section

/-! The three acceptance programs computed through the transcription of §7.2, as a cross-check of
the reference semantics: under the reader and the expander of the reference semantics, the
equations of §7.2 give each program the answer that the rules of `Demos/Scheme/Semantics/` give
it.  The check is a computation for these programs, not a proof of adequacy. -/

namespace Demos.Scheme.ReportCheck

open Demos.Scheme Demos.Scheme.Acceptance Demos.Scheme.Semantics Numeric

/-- §7.2's equations give `(let ((_ 42)) (or #f _))` the answer 42. -/
theorem report_or_case : Report.answerOf 1000 orCase = some (.int 42) := by decide +kernel

/-- §7.2's equations give the repeated-escape program the answer `(13 3)`. -/
theorem report_repeated_escape :
    Report.answerOf 1000 repeatedEscape = some (Datum.list [.int 13, .int 3]) := by
  decide +kernel

/-- §7.2's equations give the `letrec` re-entry program the answer `(10 1)`. -/
theorem report_letrec_reentry :
    Report.answerOf 1000 letrecReentry = some (Datum.list [.int 10, .int 1]) := by
  decide +kernel

/-- The transcription and the reference semantics agree on the three programs. -/
theorem cross_check :
    ∀ p ∈ [orCase, repeatedEscape, letrecReentry],
      Report.answerOf 1000 p = resultDatum (Semantics.run fixnum 1000 (Semantics.start fixnum p)) := by
  decide +kernel

/-- Programs that reach the parts of the transcription that the three programs leave
unreached: a variable-arity lambda and a rest list (`tievalsrest`, `dropfirst`, `takefirst`),
`apply` and `valueslist`, `car`, `cdr`, and `setcar`, `eqv`, an escape through `apply`, and the
whole-program translation of definitions. -/
def morePrograms : List (List UInt8) :=
  ["((lambda (a . r) (cons a r)) 1 2 3)", "((lambda r r) 1 2)",
    "(apply (lambda (x y) (cons y x)) (list 1 2))",
    "(let ((p (cons 1 2))) (set-car! p 5) (cons (car p) (cdr p)))",
    "(list (eqv? 'a 'a) (eqv? car car) (eqv? (cons 1 2) (cons 1 2)))",
    "(call/cc (lambda (k) (apply k (list 7))))", "`(1 ,(+ 1 1))",
    "(define x 1) (set! x (+ x 1)) x", "((lambda (x) (if (< x 0) 'neg 'pos)) -1)"].map
    Semantics.bytes

/-- The transcription gives each of `morePrograms` an answer, and it is the reference
semantics's result. -/
theorem cross_check_more :
    ∀ p ∈ morePrograms, (Report.answerOf 2000 p).isSome ∧
      Report.answerOf 2000 p = resultDatum (Semantics.run fixnum 2000 (Semantics.start fixnum p)) := by
  decide +kernel

#print axioms report_or_case
#print axioms report_repeated_escape
#print axioms report_letrec_reentry
#print axioms cross_check
#print axioms cross_check_more

end Demos.Scheme.ReportCheck
