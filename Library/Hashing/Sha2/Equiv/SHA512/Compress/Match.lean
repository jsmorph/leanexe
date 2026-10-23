import Library.Hashing.Sha2.Equiv.SHA512.Lift
import Library.Hashing.Sha2.Equiv.SHA512.Functions
import Library.Hashing.Sha2.Equiv.SHA512.Constants
import Library.Hashing.Sha2.Equiv.SHA512.Foldl.Fused
import Library.Hashing.Sha2.Equiv.SHA512.Compress.Impl
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 compression equivalence — spec ↔ impl bridge

With `Impl.compress` reified as `messageSchedule + 80-round sequential
mix` (`Compress/Impl.lean`), the bridge factors into two per-step
inductions transported through `fin_foldl_transport`:

* **Schedule bridge** — `toSpecSchedule (Impl.messageSchedule block)
  = SHS.SHA512.schedule (toSpecBlock block)`.
* **Rounds bridge** — `toSpecState ∘ Fin.foldl implRoundStep
  = Fin.foldl specRoundStep ∘ toSpecState`.

The composite `toSpecState_implCompressFoldl` (consumed by
`Pipeline.lean`) routes through `specCompressSeq` to match
`specCompressFused`. -/

open SHS.Equiv.SHA512.Bridge
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Functions
open SHS.Equiv.SHA512.Constants
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Compress.Impl
open SHS.Equiv.Loop
open SHS.Equiv.VecBridge

open SHS.SHA512

namespace SHS.Equiv.SHA512.Compress.Match

open scoped SHS.SHA512

/-! ## Indexing bridges -/

/-- Lift `Impl.Schedule` to spec `Schedule` by mapping each word through `toBitVec`. -/
def toSpecSchedule (w : Impl.Schedule) : Schedule := w.map UInt64.toBitVec

/-- In-bounds indexing commutes with `toSpecSchedule`. -/
theorem toSpecSchedule_getElem (w : Impl.Schedule) (k : Nat) (hk : k < 80) :
    (toSpecSchedule w)[k]'hk = (w[k]'hk).toBitVec :=
  Vector.getElem_map ..

/-- In-bounds indexing commutes with `toSpecState`. -/
theorem toSpecState_getElem (s : Impl.State) (k : Nat) (hk : k < 8) :
    (toSpecState s)[k]'hk = (s[k]'hk).toBitVec :=
  Vector.getElem_map ..

/-- Panicking indexing commutes with `toSpecSchedule`.  Both branches
(in-bounds vs out-of-bounds) reduce via the corresponding `VecBridge`
lemma. -/
theorem toSpecSchedule_getElem! (w : Impl.Schedule) (t : Nat) :
    (toSpecSchedule w)[t]! = (w[t]!).toBitVec := by
  by_cases ht : t < 80
  · simp only [getElem_bang_eq_getElem _ _ ht, toSpecSchedule_getElem]
  · rw [getElem_bang_oob _ _ ht, getElem_bang_oob _ _ ht]; rfl

/-- `map` commutes with `set!`. -/
theorem toSpecSchedule_set! (w : Impl.Schedule) (t : Nat) (x : UInt64) :
    toSpecSchedule (w.set! t x) = (toSpecSchedule w).set! t x.toBitVec := by
  unfold toSpecSchedule
  by_cases ht : t < 80
  · rw [set_bang_eq_set _ _ ht, set_bang_eq_set _ _ ht, Vector.map_set]
  · rw [set_bang_oob _ _ _ ht, set_bang_oob _ _ _ ht]

/-- Bridge `K64` indexing through `[]!`. -/
theorem K64_toBitVec_bang (t : Nat) :
    (Impl.K64[t]!).toBitVec = SHS.SHA512.K[t]! := by
  by_cases ht : t < 80
  · rw [getElem_bang_eq_getElem _ _ ht]; exact K64_toBitVec_nat t ht
  · rw [getElem_bang_oob _ _ ht, getElem_bang_oob _ _ ht]; rfl

/-! ## Schedule bridge -/

/-- Per-step schedule bridge.  Both branches share the
`toSpecSchedule (·.set! t ·)` rewrite; they differ only in the value written
(`block[t]` vs `σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`). -/
theorem implScheduleStep_toSpec (block : Impl.Block) (t : Nat) (w : Impl.Schedule) :
    toSpecSchedule (implScheduleStep block t w) =
      specScheduleStep (toSpecBlock block) t (toSpecSchedule w) := by
  unfold implScheduleStep specScheduleStep
  split <;> rw [toSpecSchedule_set!] <;> congr 1
  · rename_i ht; simp [toSpecBlock, getElem_bang_eq_getElem _ _ ht]
  · simp only [toBitVec_add, ← smallSigma1_toBitVec, ← smallSigma0_toBitVec,
               toSpecSchedule_getElem!]
    ac_rfl

/-- Schedule bridge: lifting `Impl.messageSchedule` matches the spec's `schedule`. -/
theorem messageSchedule_toSpec (block : Impl.Block) :
    toSpecSchedule (Impl.messageSchedule block) =
      SHS.SHA512.schedule (toSpecBlock block) := by
  have h0 : toSpecSchedule (Vector.replicate 80 (0 : UInt64))
      = Vector.replicate 80 (default : BitVec 64) := by
    rw [toSpecSchedule, Vector.map_replicate]; rfl
  rw [messageSchedule_eq_foldl, schedule_eq_foldl, ← h0, implScheduleFoldl]
  exact fin_foldl_transport 80 _ _ toSpecSchedule _
    (fun w t => implScheduleStep_toSpec block t.val w)

/-! ## Round bridge -/

/-- Per-step round bridge.  Six of the eight cases are variable shifts and
close by `simp only`; the `a`- and `e`-cases mix `Σ + Ch/Maj` with `+` and need
AC reassociation. -/
theorem implRoundStep_toSpec
    (w : Impl.Schedule) (t : Nat) (s : Impl.State) :
    toSpecState (implRoundStep w t s) =
      specRoundStep (toSpecSchedule w) t (toSpecState s) := by
  unfold implRoundStep specRoundStep
  apply Vector.ext
  intro k hk
  rw [toSpecState_getElem]
  -- Six variable-shift cases (b..d, f..h) close directly with `simp only`;
  -- the `a` and `e` cases need `ac_rfl` after to reassociate the
  -- `Σ + Ch + K + W + …` round-body sum.  `try` lets the same tactic body
  -- close all eight cases without duplicating the `simp only` set.
  interval_cases k <;>
    (simp only [Vector.getElem_mk, List.getElem_toArray,
                List.getElem_cons_zero, List.getElem_cons_succ,
                toBitVec_add, ← bigSigma0_toBitVec, ← bigSigma1_toBitVec,
                ← Ch_toBitVec, ← Maj_toBitVec,
                K64_toBitVec_bang, toSpecSchedule_getElem!,
                toSpecState_getElem]
     try ac_rfl)

/-- Foldl-form round bridge: lifting commutes with the 80-round fold. -/
theorem implRoundsFoldl_toSpec
    (block : Impl.Block) (state : Impl.State) :
    toSpecState (Fin.foldl 80 (fun s (t : Fin 80) =>
        implRoundStep (Impl.messageSchedule block) t.val s) state) =
      Fin.foldl 80 (fun s (t : Fin 80) =>
        specRoundStep (SHS.SHA512.schedule (toSpecBlock block)) t.val s)
        (toSpecState state) :=
  fin_foldl_transport 80 _ _ toSpecState state (fun s t => by
    rw [implRoundStep_toSpec]; congr 1; exact messageSchedule_toSpec block)

/-! ## Composite -/

/-- The impl's foldl-form compression matches the spec's `specCompressFused`
(consumed by `Pipeline.foldl_compress_lift_gen`).  Routes through
`specCompressSeq`, whose `addH (fold ... (initVars H))` shape matches the
impl's `#v[state[i] + final[i]]` post-mix add. -/
theorem toSpecState_implCompressFoldl
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  rw [← spec_compress_eq_fused, spec_compress_eq_seq]
  -- `initVars` is the identity after lifting (`ofFn (H[i]!)`-shape).
  have hinit : initVars (toSpecState state) = toSpecState state := by
    ext i _; simp [initVars]
  unfold implCompressFoldl specCompressSeq addH
  rw [hinit]
  apply Vector.ext; intro k _
  -- Each of the 8 cases reduces to `(state[i] + final[i]).toBitVec = final[i]' + state[i]'`
  -- modulo `+`-commutativity; `← implRoundsFoldl_toSpec` rewrites the spec fold to the
  -- lifted impl fold so the per-element bridges (`toSpecState_getElem`) line up.
  interval_cases k <;>
    simp [← implRoundsFoldl_toSpec, toSpecState_getElem, BitVec.add_comm]

end SHS.Equiv.SHA512.Compress.Match
