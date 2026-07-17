import Project.ClobMatchFuel.Program
import Project.BranchPost

/-!
# Matcher branch continuations

The generated matcher specializes the shared structured-branch postconditions
to its module.  Existing matcher proofs retain their artifact-qualified names.
Limit and later artifacts use the module-parameterized definitions directly.
-/

namespace Project.ClobMatchFuel.BranchPost

open Wasm Project.ClobMatchFuel

theorem withValues_eq_self (s : Locals) (values : List Value)
    (hValues : s.values = values) : { s with values := values } = s :=
  Project.BranchPost.withValues_eq_self s values hValues

abbrev oneResultIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  Project.BranchPost.oneResultIffPost «module» env rest Q

abbrev doubleResultIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  Project.BranchPost.doubleResultIffPost «module» env rest Q

theorem trueOneResultIff (env : HostEnv Unit) (st : Store Unit)
    (guard : Locals) (body els rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : guard.values = [.i32 1])
    (hBody : wp «module» body (oneResultIffPost env rest Q) st
      { guard with values := [] } env) :
    wp «module» (.iff 0 1 body els :: rest) Q st guard env :=
  Project.BranchPost.trueOneResultIff «module» env st guard body els rest Q
    hValues hBody

theorem oneResultIffPost_of_wp (env : HostEnv Unit) (st : Store Unit)
    (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : s.values.take 1 = s.values)
    (hDone : wp «module» rest Q st s env) :
    wp «module» [] (oneResultIffPost env rest Q) st s env :=
  Project.BranchPost.oneResultIffPost_of_wp «module» env st s rest Q hValues
    hDone

theorem doubleResultIffPost_of_wp (env : HostEnv Unit) (st : Store Unit)
    (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : (s.values.take 1).take 1 = s.values)
    (hDone : wp «module» rest Q st s env) :
    wp «module» [] (doubleResultIffPost env rest Q) st s env :=
  Project.BranchPost.doubleResultIffPost_of_wp «module» env st s rest Q hValues
    hDone

end Project.ClobMatchFuel.BranchPost
