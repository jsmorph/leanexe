import Interpreter.Wasm.Wp.Tactic

/-!
# Structured branch continuations

Generated one-result branches retain one operand-stack value before their
surrounding program resumes.  These definitions state that continuation for
an arbitrary module.  Nested branches compose the same operation without
expanding the enclosing artifact proof.
-/

namespace Project.BranchPost

open Wasm

theorem withValues_eq_self (s : Locals) (values : List Value)
    (hValues : s.values = values) : { s with values := values } = s := by
  cases s
  simp_all

def oneResultIffPost (m : Wasm.Module) (env : HostEnv Unit)
    (rest : Wasm.Program) (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp m rest Q st' { s' with values := s'.values.take 1 } env
    | .Break 0 st' s' =>
        wp m rest Q st' { s' with values := s'.values.take 1 } env
    | .Break (k + 1) st' s' => Q (.Break k st' s')
    | other => Q other

def doubleResultIffPost (m : Wasm.Module) (env : HostEnv Unit)
    (rest : Wasm.Program) (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp m rest Q st'
          { s' with values := (s'.values.take 1).take 1 } env
    | .Break 0 st' s' =>
        wp m rest Q st'
          { s' with values := (s'.values.take 1).take 1 } env
    | .Break (k + 1) st' s' => oneResultIffPost m env rest Q (.Break k st' s')
    | other => oneResultIffPost m env rest Q other

theorem trueOneResultIff (m : Wasm.Module) (env : HostEnv Unit)
    (st : Store Unit) (guard : Locals) (body els rest : Wasm.Program)
    (Q : Assertion Unit) (hValues : guard.values = [.i32 1])
    (hBody : wp m body (oneResultIffPost m env rest Q) st
      { guard with values := [] } env) :
    wp m (.iff 0 1 body els :: rest) Q st guard env := by
  apply wp_iff_cons hValues
  rw [if_pos (by decide)]
  refine wp.imp hBody ?_
  intro c hc
  unfold oneResultIffPost at hc
  cases c <;> try simpa only [List.drop, List.append_nil] using hc
  case Break k _ _ =>
    cases k <;> simpa only [List.drop, List.append_nil] using hc

theorem oneResultIffPost_of_wp (m : Wasm.Module) (env : HostEnv Unit)
    (st : Store Unit) (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : s.values.take 1 = s.values) (hDone : wp m rest Q st s env) :
    wp m [] (oneResultIffPost m env rest Q) st s env := by
  have hBase : { s with values := s.values.take 1 } = s := by
    cases s
    simp_all
  simpa [oneResultIffPost, wp_simp, hBase] using hDone

theorem doubleResultIffPost_of_wp (m : Wasm.Module) (env : HostEnv Unit)
    (st : Store Unit) (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : (s.values.take 1).take 1 = s.values)
    (hDone : wp m rest Q st s env) :
    wp m [] (doubleResultIffPost m env rest Q) st s env := by
  have hBase : { s with values := (s.values.take 1).take 1 } = s := by
    cases s
    simp_all
  simpa [doubleResultIffPost, oneResultIffPost, wp_simp, hBase] using hDone

end Project.BranchPost
