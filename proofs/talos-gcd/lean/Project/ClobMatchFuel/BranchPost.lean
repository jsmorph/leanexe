import Project.ClobMatchFuel.Program
import Interpreter.Wasm.Wp.Tactic

/-!
# Nested branch continuations

The generated matcher performs the erased-book update inside two one-result
`if` instructions.  Their successful path preserves the returned book pointer
before continuing with the trade update.  This module states that continuation
once so the physical update proofs do not expand both control frames.
-/

namespace Project.ClobMatchFuel.BranchPost

open Wasm Project.ClobMatchFuel

theorem withValues_eq_self (s : Locals) (values : List Value)
    (hValues : s.values = values) : { s with values := values } = s := by
  cases s
  simp_all

def oneResultIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp «module» rest Q st' { s' with values := s'.values.take 1 } env
    | .Break 0 st' s' =>
        wp «module» rest Q st' { s' with values := s'.values.take 1 } env
    | .Break (k + 1) st' s' => Q (.Break k st' s')
    | other => Q other

def doubleResultIffPost (env : HostEnv Unit) (rest : Wasm.Program)
    (Q : Assertion Unit) : Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
        wp «module» rest Q st'
          { s' with values := (s'.values.take 1).take 1 } env
    | .Break 0 st' s' =>
        wp «module» rest Q st'
          { s' with values := (s'.values.take 1).take 1 } env
    | .Break (k + 1) st' s' =>
        oneResultIffPost env rest Q (.Break k st' s')
    | other => oneResultIffPost env rest Q other

theorem trueOneResultIff (env : HostEnv Unit) (st : Store Unit)
    (guard : Locals) (body els rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : guard.values = [.i32 1])
    (hBody : wp «module» body (oneResultIffPost env rest Q) st
      { guard with values := [] } env) :
    wp «module» (.iff 0 1 body els :: rest) Q st
      guard env := by
  apply wp_iff_cons hValues
  rw [if_pos (by decide)]
  refine wp.imp hBody ?_
  intro c hc
  unfold oneResultIffPost at hc
  cases c <;> try simpa only [List.drop, List.append_nil] using hc
  case Break k _ _ =>
    cases k <;> simpa only [List.drop, List.append_nil] using hc

theorem oneResultIffPost_of_wp (env : HostEnv Unit) (st : Store Unit)
    (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : s.values.take 1 = s.values)
    (hDone : wp «module» rest Q st s env) :
    wp «module» [] (oneResultIffPost env rest Q) st s env := by
  have hBase : { s with values := s.values.take 1 } = s := by
    cases s
    simp_all
  simpa [oneResultIffPost, wp_simp, hBase] using hDone

theorem doubleResultIffPost_of_wp (env : HostEnv Unit) (st : Store Unit)
    (s : Locals) (rest : Wasm.Program) (Q : Assertion Unit)
    (hValues : (s.values.take 1).take 1 = s.values)
    (hDone : wp «module» rest Q st s env) :
    wp «module» [] (doubleResultIffPost env rest Q) st s env := by
  have hBase : { s with values := (s.values.take 1).take 1 } = s := by
    cases s
    simp_all
  simpa [doubleResultIffPost, oneResultIffPost, wp_simp, hBase] using hDone

end Project.ClobMatchFuel.BranchPost
