import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Wp.Loop

/-!
# Loop-body scaffold

The loop rule's body obligation carries a match continuation over the
outcome.  Writing that continuation into a lemma statement is not
workable, and goals that hold it stuck are hostile to context extension
and multi-component splits.  The working pattern states a body lemma
generic over the postcondition, with one premise per outcome the body
produces, and instantiates it at the rule's continuation.  This theorem
performs that instantiation once and for all: a per-loop body lemma
proves `wp m body POST st s env` for every postcondition satisfying the
trap, repeat, fallthrough, and break premises, and this theorem turns it
into the loop rule's `hStep` argument.
-/

namespace Project.Common

open Wasm

/-- Turn a postcondition-generic body lemma into the loop rule's body
obligation.  `hQT` supplies the trap case of the outer postcondition;
the other premises of the body lemma receive the continuation's own
case computations, which reduce definitionally. -/
theorem wp_loop_body_intro {α : Type} {m : Module} {env : HostEnv α}
    {ps rs : Nat} {body rest : Program} {Q : Assertion α}
    (Inv : AssertionF α) (μ : Store α → Locals → Nat)
    (hQT : ∀ (st' : Store α) (msg : String), Q (.Trap st' msg) = False)
    (hB : ∀ (st : Store α) (s : Locals), Inv st s →
      ∀ (POST : Assertion α),
      (∀ (st' : Store α) (msg : String), POST (.Trap st' msg) = False) →
      (∀ (st' : Store α) (s' : Locals),
        Inv st' { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
        μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } <
          μ st s →
        POST (.Break 0 st' s')) →
      (∀ (st' : Store α) (s' : Locals),
        wp m rest Q st'
          { s' with values := s'.values.take rs ++ s.values.drop ps } env →
        POST (.Fallthrough st' s')) →
      (∀ (k : Nat) (st' : Store α) (s' : Locals),
        Q (.Break k st' s') → POST (.Break (k + 1) st' s')) →
      wp m body POST st s env) :
    ∀ (st : Store α) (s : Locals), Inv st s →
      wp m body
        (fun c => match c with
          | .Fallthrough st' s' =>
            wp m rest Q st'
              { s' with values := s'.values.take rs ++ s.values.drop ps } env
          | .Break 0 st' s' =>
            Inv st'
              { s' with values := s'.values.take ps ++ s.values.drop ps } ∧
            μ st' { s' with values := s'.values.take ps ++ s.values.drop ps } <
              μ st s
          | .Break (k+1) st' s' => Q (.Break k st' s')
          | other => Q other)
        st s env := by
  intro st s hInv
  refine hB st s hInv _ ?_ ?_ ?_ ?_
  · intro st' msg
    exact hQT st' msg
  · intro st' s' h
    exact h
  · intro st' s' h
    exact h
  · intro k st' s' h
    exact h

/-- Peel byte-level frame facts through a chain of word and byte
writes: a byte below every write survives, and a byte outside a byte
write's cell survives.  The separation conditions discharge by `omega`
after normalizing the `UInt32.ofNat (_ % 2 ^ 32)` address forms, as in
`read_frames`. -/
macro "bytes_frames" : tactic =>
  `(tactic|
    repeat first
      | rw [write64_bytes_lo _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      | rw [write64_bytes_ne _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      | rw [write8_bytes_ne _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)])

/-- `read_frames` extended over byte writes: peel disjoint word writes
and byte writes from a word read, stopping at the syntactic hit. -/
macro "read_frames8" : tactic =>
  `(tactic|
    repeat first
      | rw [Wasm.Mem.read64_write64_same]
      | rw [read64_write64_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      | rw [read64_write8_ne _ _ _ _
          (by simp only [toUInt32_ofNat_mod_toNat]; omega)])

end Project.Common
