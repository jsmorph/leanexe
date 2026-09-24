import Project.Correct.Scalar64.Encode

namespace Project.Correct.Scalar64

private def identityFixture : Function :=
  { arity := 1, localCount := 0, scratch := 1, body := .skip, result := .get 0 }
private def selfCallFixture : Function :=
  { identityFixture with body := .call 0 0 [.get 0] }

example : checkModule [identityFixture] 0 = true := by decide
example : checkModule [] 0 = false := by decide
example : checkModule [identityFixture] 1 = false := by decide
example : checkModule [selfCallFixture] 0 = false := by decide
example : (encode [selfCallFixture] "cycle" 0).isOk = false := by decide
example : checkModule [
    { identityFixture with body := .call 0 1 [.get 0] }, identityFixture] 0 = false := by decide
example : checkModule [identityFixture,
    { identityFixture with body := .call 0 0 [] }] 1 = false := by decide
example : checkModule [identityFixture,
    { identityFixture with body := .call 1 0 [.get 0] }] 1 = false := by decide
example : checkModule [{ identityFixture with result := .get 1 }] 0 = false := by decide
example : checkModule [{ identityFixture with
    result := .bin .divU (.get 0) (.const 0) }] 0 = false := by decide
example : checkModule [{ identityFixture with
    localCount := 2, result := .bin .divU (.get 0) (.const 0) }] 0 = true := by decide

end Project.Correct.Scalar64
