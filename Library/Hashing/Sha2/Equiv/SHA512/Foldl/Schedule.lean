import Library.Hashing.Sha2.Equiv.Common.Loop
import Library.Hashing.Sha2.Impl.SHA512
import Library.Hashing.Sha2.Spec.HashAlgorithms

-- Bounds discharge inside `for h : t in [a:b] do` ranges.  Range
-- membership (`Std.Legacy.Range`) carries `.upper` / `.lower`; extract
-- them and let `grind` close the resulting arithmetic goals (e.g.
-- `t < 80`, `t - 16 < 80`).
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)))

/-! # Pure-foldl form of the SHA-512 message schedule

Parallel to `equiv/SHA256/Foldl/Schedule.lean` at 80 rounds (16-word
copy phase + 64-word extension phase, vs SHA-256's 16+48).

The spec writes `SHS.SHA512.schedule` as `Id.run do { mut … for … }`
across two `for` loops.  This module restates it as a single
`Fin.foldl 80` over a pure step function (`specScheduleStep`), which
is the shape everything downstream wants.

Nothing in this file references the round body or the working
variables; that lives in `Foldl/Sequential.lean` and `Foldl/Fused.lean`. -/

open SHS.Equiv.Loop

open SHS.SHA512

namespace SHS.Equiv.SHA512.Foldl.Schedule

open scoped SHS.SHA512

/-- One step of the SHA-512 message schedule, as a pure function.

For `t < 16`, copy block word `t`; otherwise, mix four prior words via
`smallSigma0`/`smallSigma1`.  This is exactly the body of the two
`for` loops in `SHS.SHA512.schedule`.

Indexed by `Nat` rather than `Fin 80`: out-of-range `t` panics through
`Vector.set!`, but every call site has `t < 80`.  The `Nat` index keeps
the `Fused.lean` proof free of `Fin.castSucc`-handling. -/
def specScheduleStep (M : Block) (t : Nat) (W : Schedule) : Schedule :=
  if t < 16 then
    W.set! t M[t]!
  else
    W.set! t
      (SHS.SHA512.smallSigma1 W[t - 2]! + W[t - 7]! +
        SHS.SHA512.smallSigma0 W[t - 15]! + W[t - 16]!)

/-- The spec's `schedule` is `Fin.foldl 80 specScheduleStep` over a
zero-initialized 80-word vector.

This rephrases spec's two-`for`-loop schedule as a single
`Fin.foldl 80`, which is the shape we need to match the implementation
and to drive the fused-form argument below. -/
theorem schedule_eq_foldl (M : Block) :
    SHS.SHA512.schedule M =
      Fin.foldl 80 (fun W (t : Fin 80) => specScheduleStep M t.val W)
        (Vector.replicate 80 default) := by
  -- 1. Rewrite spec from `forIn'` form to `forIn` form (proof erasure),
  --    using `set!`/`getElem!` (in-bounds, so equal to `set`/`getElem`).
  have hspec :
      SHS.SHA512.schedule M =
        Id.run (forIn [16:80]
          (Id.run (forIn [0:16] (Vector.replicate 80 default)
            (fun t W => pure (ForInStep.yield (W.set! t M[t]!)))))
          (fun t (W : Schedule) => pure (ForInStep.yield
            (W.set! t (SHS.SHA512.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA512.smallSigma0 W[t - 15]! + W[t - 16]!))))) := by
    unfold SHS.SHA512.schedule
    show Id.run _ = _
    -- Inner spec body (the 16-word block-copy phase), with explicit bound proofs.
    let innerBody : (t : Nat) → t ∈ [0:16] → Schedule → Id (ForInStep Schedule) :=
      fun t h W =>
        have h16 : t < 16 := h.upper
        have h80 : t < 80 := by grind
        pure (ForInStep.yield (W.set t (M[t]'h16) h80))
    -- Bridge inner forIn' → forIn (the `set` is in-bounds so equals `set!`).
    have hinner : ∀ (W₀ : Schedule),
        Id.run (forIn' [0:16] W₀ innerBody) =
        Id.run (forIn [0:16] W₀
          (fun t W => pure (ForInStep.yield (W.set! t M[t]!)))) := by
      intro W₀
      rw [← forIn'_id_eq_forIn 0 16 W₀ (fun t W => W.set! t M[t]!)]
      simp only [Id.run]
      congr 1
      funext t htmem W
      have ht16 : t < 16 := htmem.upper
      have ht80 : t < 80 := by grind
      have h1 : M[t]! = M[t]'ht16 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem M t ht16
      have h2 : W.set! t M[t]! = W.set t (M[t]'ht16) ht80 := by
        rw [h1]; exact SHS.Equiv.VecBridge.set_bang_eq_set W t ht80 _
      simp only [innerBody]
      rw [h2]
    -- Outer spec body (the 64-word extension phase), with explicit bound proofs.
    let outerBody : (t : Nat) → t ∈ [16:80] → Schedule → Id (ForInStep Schedule) :=
      fun t h W =>
        have h1 : t < 80 := h.upper
        have h2 : t - 2 < 80 := by have := h.upper; grind
        have h7 : t - 7 < 80 := by have := h.upper; grind
        have h15 : t - 15 < 80 := by have := h.upper; have := h.lower; grind
        have h16 : t - 16 < 80 := by have := h.upper; have := h.lower; grind
        pure (ForInStep.yield
          (W.set t
            (SHS.SHA512.smallSigma1 (W[t - 2]'h2) + (W[t - 7]'h7) +
              SHS.SHA512.smallSigma0 (W[t - 15]'h15) + (W[t - 16]'h16)) h1))
    have houter : ∀ (W₀ : Schedule),
        Id.run (forIn' [16:80] W₀ outerBody) =
        Id.run (forIn [16:80] W₀
          (fun t W => pure (ForInStep.yield
            (W.set! t (SHS.SHA512.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA512.smallSigma0 W[t - 15]! + W[t - 16]!))))) := by
      intro W₀
      rw [← forIn'_id_eq_forIn 16 80 W₀
            (fun t W => W.set! t (SHS.SHA512.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA512.smallSigma0 W[t - 15]! + W[t - 16]!))]
      simp only [Id.run]
      congr 1
      funext t htmem W
      have htlb : 16 ≤ t := htmem.lower
      have ht80 : t < 80 := htmem.upper
      have hm2 : t - 2 < 80 := by grind
      have hm7 : t - 7 < 80 := by grind
      have hm15 : t - 15 < 80 := by grind
      have hm16 : t - 16 < 80 := by grind
      have e2 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-2) hm2
      have e7 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-7) hm7
      have e15 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-15) hm15
      have e16 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-16) hm16
      have hset := SHS.Equiv.VecBridge.set_bang_eq_set W t ht80
        (SHS.SHA512.smallSigma1 W[t - 2] + W[t - 7] +
              SHS.SHA512.smallSigma0 W[t - 15] + W[t - 16])
      rw [e2, e7, e15, e16, hset]
    -- The spec, fully unfolded, equals:
    --   Id.run (forIn' [16:80] (Id.run (forIn' [0:16] _ innerBody)) outerBody).
    -- The Id.run / pure / bind sequence reduces to nested forIn'/run.
    show Id.run (do
            let r ← forIn' [0:16] (Vector.replicate 80 default) innerBody
            forIn' [16:80] r outerBody) = _
    show (forIn' [16:80]
            (Id.run (forIn' [0:16] (Vector.replicate 80 default) innerBody))
            outerBody : Id _).run = _
    rw [hinner (Vector.replicate 80 default)]
    exact houter _
  -- 2. Now apply the existing Loop bridges.
  rw [hspec]
  rw [forIn_id_eq_Fin_foldl 16
        (Vector.replicate 80 default)
        (fun n W => W.set! n M[n]!)]
  rw [forIn_id_eq_Fin_foldl_offset 16 80
        (Fin.foldl 16 (fun s t => (fun n W => W.set! n M[n]!) t.val s)
          (Vector.replicate 80 default))
        (fun n W => W.set! n
          (SHS.SHA512.smallSigma1 W[n - 2]! + W[n - 7]! +
            SHS.SHA512.smallSigma0 W[n - 15]! + W[n - 16]!))]
  -- 3. Re-fuse the two halves into a single Fin.foldl 80 over specScheduleStep.
  rw [show (80 - 16) = 64 from rfl]
  symm
  rw [show (fun W (t : Fin 80) => specScheduleStep M t.val W) =
        (fun W (t : Fin 80) => if t.val < 16
          then (fun n (W : Schedule) => W.set! n M[n]!) t.val W
          else (fun n (W : Schedule) => W.set! n
            (SHS.SHA512.smallSigma1 W[n - 2]! + W[n - 7]! +
              SHS.SHA512.smallSigma0 W[n - 15]! + W[n - 16]!)) t.val W) from by
        funext W t
        unfold specScheduleStep
        split <;> rfl]
  rw [fin_foldl_split 16 80 (by decide)
        (fun n (W : Schedule) => W.set! n M[n]!)
        (fun n (W : Schedule) => W.set! n
          (SHS.SHA512.smallSigma1 W[n - 2]! + W[n - 7]! +
            SHS.SHA512.smallSigma0 W[n - 15]! + W[n - 16]!))]

end SHS.Equiv.SHA512.Foldl.Schedule
