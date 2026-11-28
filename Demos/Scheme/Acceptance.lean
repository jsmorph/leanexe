module

public import Demos.Scheme.Semantics.Datum

@[expose] public section

/-! The bytes of the acceptance programs of the design's section 7 that milestones 1 and 2
cover, as the reference semantics and the executable interpreter read them. -/

namespace Demos.Scheme.Acceptance

open Demos.Scheme.Semantics (bytes)

/-- `or` evaluates its second operand in the surrounding environment, so the result is 42. -/
def orCase : List UInt8 := bytes "(let ((_ 42)) (or #f _))"

/-- Each invocation of the escape procedure drops a pending addition of 1000, reinstates an
addition of 1, and sees the current `visits`, so the result is `(13 3)`. -/
def repeatedEscape : List UInt8 := bytes "(let ((again #f) (visits 0))
  (let ((x (+ 1 (call/cc (lambda (k) (set! again k) 10)))))
    (set! visits (+ visits 1))
    (if (< visits 3)
        (+ 1000 (again x))
        (list x visits))))"

/-- Re-entry into a `letrec` initializer reassigns both staged values, 10 and 1, to the group's
locations before the body, so the result is `(10 1)`. -/
def letrecReentry : List UInt8 := bytes "(let ((retry #f) (first? #t))
  (letrec ((x 10)
           (y (call/cc (lambda (k) (set! retry k) 0))))
    (if first?
        (begin (set! first? #f) (set! x 99) (retry 1))
        (list x y))))"

end Demos.Scheme.Acceptance
