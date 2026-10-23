import Library.Hashing.Sha2.Equiv.Common.Loop
import Library.Hashing.Sha2.Impl.SHA256
import Library.Hashing.Sha2.Spec.HashAlgorithms

-- Bounds discharge inside `for h : t in [a:b] do` ranges.  Range
-- membership (`Std.Legacy.Range`) carries `.upper` / `.lower`; extract
-- them and let `grind` close the resulting arithmetic goals (e.g.
-- `t < 64`, `t - 16 < 64`).
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)))

/-! # Pure-foldl form of the spec message schedule

The spec writes `SHS.SHA256.schedule` as `Id.run do { mut … for … }`
across two `for` loops.  This module restates it as a single
`Fin.foldl 64` over a pure step function (`specScheduleStep`), which
is the shape everything downstream wants.

Nothing in this file references the round body or the working
variables; that lives in `Foldl/Sequential.lean` and `Foldl/Fused.lean`. -/

open SHS.Equiv.Loop

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Schedule

open scoped SHS.SHA256

/-- One step of the spec's message schedule, as a pure function.

For `t < 16`, copy block word `t`; otherwise, mix four prior words via
`smallSigma0`/`smallSigma1`.  This is exactly the body of the two
`for` loops in `SHS.SHA256.schedule`.

Indexed by `Nat` rather than `Fin 64`: out-of-range `t` panics through
`Vector.set!`, but every call site has `t < 64`.  The `Nat` index keeps
the `Fused.lean` proof free of `Fin.castSucc`-handling. -/
def specScheduleStep (M : Block) (t : Nat) (W : Schedule) : Schedule :=
  if t < 16 then
    W.set! t M[t]!
  else
    W.set! t
      (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
        SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!)

/-- The spec's `schedule` is `Fin.foldl 64 specScheduleStep` over a
zero-initialized 64-word vector.

This rephrases spec's two-`for`-loop schedule as a single
`Fin.foldl 64`, which is the shape we need to match the implementation
and to drive the fused-form argument below. -/
theorem schedule_eq_foldl (M : Block) :
    SHS.SHA256.schedule M =
      Fin.foldl 64 (fun W (t : Fin 64) => specScheduleStep M t.val W)
        (Vector.replicate 64 default) := by
  -- 1. Rewrite spec from `forIn'` form to `forIn` form (proof erasure),
  --    using `set!`/`getElem!` (in-bounds, so equal to `set`/`getElem`).
  have hspec :
      SHS.SHA256.schedule M =
        Id.run (forIn [16:64]
          (Id.run (forIn [0:16] (Vector.replicate 64 default)
            (fun t W => pure (ForInStep.yield (W.set! t M[t]!)))))
          (fun t (W : Schedule) => pure (ForInStep.yield
            (W.set! t (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!))))) := by
    unfold SHS.SHA256.schedule
    show Id.run _ = _
    -- Inner spec body, with explicit bound proofs.
    let innerBody : (t : Nat) → t ∈ [0:16] → Schedule → Id (ForInStep Schedule) :=
      fun t h W =>
        have h16 : t < 16 := h.upper
        have h64 : t < 64 := by grind
        pure (ForInStep.yield (W.set t (M[t]'h16) h64))
    -- Outer spec body declared above the houter `have`; we redefine here too
    -- to keep both visible in the rewriting `show`.
    -- Bridge inner forIn' → forIn.
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
      have ht64 : t < 64 := by grind
      have h1 : M[t]! = M[t]'ht16 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem M t ht16
      have h2 : W.set! t M[t]! = W.set t (M[t]'ht16) ht64 := by
        rw [h1]; exact SHS.Equiv.VecBridge.set_bang_eq_set W t ht64 _
      simp only [innerBody]
      rw [h2]
    -- Helper for the spec body of the [16:64] loop, with explicit bound proofs.
    let outerBody : (t : Nat) → t ∈ [16:64] → Schedule → Id (ForInStep Schedule) :=
      fun t h W =>
        have h1 : t < 64 := h.upper
        have h2 : t - 2 < 64 := by have := h.upper; grind
        have h7 : t - 7 < 64 := by have := h.upper; grind
        have h15 : t - 15 < 64 := by have := h.upper; have := h.lower; grind
        have h16 : t - 16 < 64 := by have := h.upper; have := h.lower; grind
        pure (ForInStep.yield
          (W.set t
            (SHS.SHA256.smallSigma1 (W[t - 2]'h2) + (W[t - 7]'h7) +
              SHS.SHA256.smallSigma0 (W[t - 15]'h15) + (W[t - 16]'h16)) h1))
    have houter : ∀ (W₀ : Schedule),
        Id.run (forIn' [16:64] W₀ outerBody) =
        Id.run (forIn [16:64] W₀
          (fun t W => pure (ForInStep.yield
            (W.set! t (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!))))) := by
      intro W₀
      rw [← forIn'_id_eq_forIn 16 64 W₀
            (fun t W => W.set! t (SHS.SHA256.smallSigma1 W[t - 2]! + W[t - 7]! +
              SHS.SHA256.smallSigma0 W[t - 15]! + W[t - 16]!))]
      simp only [Id.run]
      congr 1
      funext t htmem W
      have htlb : 16 ≤ t := htmem.lower
      have ht64 : t < 64 := htmem.upper
      have hm2 : t - 2 < 64 := by grind
      have hm7 : t - 7 < 64 := by grind
      have hm15 : t - 15 < 64 := by grind
      have hm16 : t - 16 < 64 := by grind
      have e2 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-2) hm2
      have e7 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-7) hm7
      have e15 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-15) hm15
      have e16 := SHS.Equiv.VecBridge.getElem_bang_eq_getElem W (t-16) hm16
      have hset := SHS.Equiv.VecBridge.set_bang_eq_set W t ht64
        (SHS.SHA256.smallSigma1 W[t - 2] + W[t - 7] +
              SHS.SHA256.smallSigma0 W[t - 15] + W[t - 16])
      rw [e2, e7, e15, e16, hset]
    -- The spec, fully unfolded, equals:
    --   Id.run (forIn' [16:64] (Id.run (forIn' [0:16] _ innerBody)) outerBody).
    -- The Id.run / pure / bind sequence reduces to nested forIn'/run.
    show Id.run (do
            let r ← forIn' [0:16] (Vector.replicate 64 default) innerBody
            forIn' [16:64] r outerBody) = _
    show (forIn' [16:64]
            (Id.run (forIn' [0:16] (Vector.replicate 64 default) innerBody))
            outerBody : Id _).run = _
    rw [hinner (Vector.replicate 64 default)]
    exact houter _
  -- 2. Now apply the existing Loop bridges.
  rw [hspec]
  rw [forIn_id_eq_Fin_foldl 16
        (Vector.replicate 64 default)
        (fun n W => W.set! n M[n]!)]
  rw [forIn_id_eq_Fin_foldl_offset 16 64
        (Fin.foldl 16 (fun s t => (fun n W => W.set! n M[n]!) t.val s)
          (Vector.replicate 64 default))
        (fun n W => W.set! n
          (SHS.SHA256.smallSigma1 W[n - 2]! + W[n - 7]! +
            SHS.SHA256.smallSigma0 W[n - 15]! + W[n - 16]!))]
  -- 3. Re-fuse the two halves into a single Fin.foldl 64 over specScheduleStep.
  rw [show (64 - 16) = 48 from rfl]
  symm
  rw [show (fun W (t : Fin 64) => specScheduleStep M t.val W) =
        (fun W (t : Fin 64) => if t.val < 16
          then (fun n (W : Schedule) => W.set! n M[n]!) t.val W
          else (fun n (W : Schedule) => W.set! n
            (SHS.SHA256.smallSigma1 W[n - 2]! + W[n - 7]! +
              SHS.SHA256.smallSigma0 W[n - 15]! + W[n - 16]!)) t.val W) from by
        funext W t
        unfold specScheduleStep
        split <;> rfl]
  rw [fin_foldl_split 16 64 (by decide)
        (fun n (W : Schedule) => W.set! n M[n]!)
        (fun n (W : Schedule) => W.set! n
          (SHS.SHA256.smallSigma1 W[n - 2]! + W[n - 7]! +
            SHS.SHA256.smallSigma0 W[n - 15]! + W[n - 16]!))]

end SHS.Equiv.SHA256.Foldl.Schedule
