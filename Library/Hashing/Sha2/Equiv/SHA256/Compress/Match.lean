import Library.Hashing.Sha2.Equiv.SHA256.Compress.Impl
import Mathlib.Tactic.IntervalCases

/-! # Compression equivalence — `MatchAfter` invariant + cross-side meet

The intellectual core of the compress equivalence: the named impl
factored form (`implCompressFoldl`, from `Compress/Impl`) tracks the
named spec fused form (`specCompressFused`, from `Foldl/Fused`)
round-by-round, after lifting impl values through `toSpecState` /
`toSpecBlock`.

This module defines the `MatchAfter` invariant linking the two folds'
intermediate states, proves its base case (`MatchAfter_zero`) and
inductive preservation (`MatchAfter_step`), lifts the preservation to
the full 64-round fold (`MatchAfter_iter`), and finally peels the
invariant at `n = 64` to give the public `toSpecState_implCompressFoldl`
consumed by `Main.lean`'s top-level `compress_correct` rewrite chain. -/

open SHS.Equiv.SHA256.Bridge
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Functions
open SHS.Equiv.SHA256.Constants
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential
open SHS.Equiv.SHA256.Foldl.Fused
open SHS.Equiv.SHA256.Compress.Impl

open SHS.SHA256

namespace SHS.Equiv.SHA256.Compress.Match

open scoped SHS.SHA256

/-- The round-by-round invariant linking the impl fold's paired state
to the spec fold's paired state.  After `n` rounds:

* `W` has the spec schedule's full size (64);
* the working vars match element-wise (`impl_state[k] ≈ vars[k]`);
* the ring buffer's last (up to) 16 written entries match the spec
  schedule entries `W[k]` for `n - 16 ≤ k < n`;
* untouched ring-buffer slots (`n ≤ k < 16`) still hold the original
  block input.

## Why the ring-buffer condition is asymmetric (`n - 16 ≤ k < n`)

The impl's schedule is a 16-word sliding ring buffer: at round `n` it
holds exactly the last 16 schedule words `W[n-16], …, W[n-1]` (older
ones were overwritten via `% 16` indexing, future ones are not yet
computed).  The spec's schedule is a fixed-length 64-word array
holding all of `W[0], …, W[63]` simultaneously.  The two only agree on
the impl's *live window* — the 16 indices `n - 16 ≤ k < n` — and that
is exactly what the round body reads (`W[t-2], W[t-7], W[t-15],
W[t-16]` at round `t = n`).  Outside the window we cannot — and need
not — compare. -/
structure MatchAfter
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) : Prop where
  /-- The spec schedule has its full 64-word size. -/
  wsize : W.size = 64
  /-- Working variables match element-wise. -/
  vars : ∀ k : Fin 8, impl_state[k].toBitVec = vars[k]
  /-- Ring-buffer window: entries `n - 16 ≤ k < n` of the spec schedule
  are present at positions `k % 16` in the impl block. -/
  ring : ∀ k : Nat, k < n → n ≤ k + 16 →
    (impl_block[k % 16]'(mod16_lt _)).toBitVec
      = W[k]!
  /-- Untouched slots: entries `n ≤ k < 16` of the original block still match. -/
  untouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k]

/-- Initial-state invariant: at round 0, the impl/spec states match trivially.
Base case for `MatchAfter_iter`. -/
theorem MatchAfter_zero
    (state : Impl.State) (block : Impl.Block) :
    MatchAfter block block state (Vector.replicate 64 default)
      (initVars (toSpecState state)) 0 where
  wsize := by simp
  vars k := by rw [initVars_toSpecState_getElem]
  ring k hk _ := by omega
  untouched k _ := rfl

/-- Preservation: one round of `implFusedStep` paired with `specFusedStep`
preserves the `MatchAfter` invariant.  Inductive step for
`MatchAfter_iter`; the round-by-round bridge between the two folds.

The proof discharges the four conjuncts independently; `vars_match`
enumerates the eight working-variable indices via `interval_cases`
because a `∀ k : Fin 8` packaging would block `Vector.getElem_mk`
matching. -/
theorem MatchAfter_step
    (block₀ : Impl.Block)
    (impl_block : Impl.Block) (impl_state : Impl.State)
    (W : Schedule) (vars : SpecVars) (n : Nat) (hn : n < 64)
    (h : MatchAfter block₀ impl_block impl_state W vars n) :
    let i : Fin 64 := ⟨n, hn⟩
    let next_impl := implFusedStep i (impl_block, impl_state)
    let next_spec := specFusedStep (toSpecBlock block₀) i (W, vars)
    MatchAfter block₀ next_impl.1 next_impl.2 next_spec.1 next_spec.2 (n + 1) := by
  have hWsize := h.wsize
  have hstate := h.vars
  have hring := h.ring
  have huntouched := h.untouched
  simp only [implFusedStep, specFusedStep]
  refine ⟨?sched_size, ?vars_match, ?ring_match, ?untouched⟩
  case sched_size =>
    unfold specScheduleStep; split <;> simp [hWsize]
  case vars_match =>
    have hw := implScheduleStep_value_match block₀ impl_block W n hn huntouched hring
    -- The 8 working-var hypotheses (and `hK`) are bound at literal `Nat`
    -- indices because `interval_cases k_val` produces goals indexed by
    -- numeric literals, not `Fin` constructors.
    have h0 : impl_state[(0 : Nat)].toBitVec = vars[(0 : Nat)] := hstate 0
    have h1 : impl_state[(1 : Nat)].toBitVec = vars[(1 : Nat)] := hstate 1
    have h2 : impl_state[(2 : Nat)].toBitVec = vars[(2 : Nat)] := hstate 2
    have h3 : impl_state[(3 : Nat)].toBitVec = vars[(3 : Nat)] := hstate 3
    have h4 : impl_state[(4 : Nat)].toBitVec = vars[(4 : Nat)] := hstate 4
    have h5 : impl_state[(5 : Nat)].toBitVec = vars[(5 : Nat)] := hstate 5
    have h6 : impl_state[(6 : Nat)].toBitVec = vars[(6 : Nat)] := hstate 6
    have h7 : impl_state[(7 : Nat)].toBitVec = vars[(7 : Nat)] := hstate 7
    have hK := K32_toBitVec_nat n hn
    intro k
    have ⟨k_val, _k_lt⟩ := k
    -- For each of the 8 working-variable indices, the round-body equation has
    -- the same shape: unfold both sides, push `toBitVec` to the leaves via the
    -- `_toBitVec` simp set (which includes `hw` for the freshly written
    -- schedule entry).  Seven cases are then variable shifts and close by
    -- `assumption` against `h0..h7`; the `a`-case requires the
    -- `Σ₀ + Maj + …` reassociation and finishes with `ac_rfl`.
    interval_cases k_val <;>
      (unfold implRoundBody specRoundStep
       simp only [Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
         List.getElem_cons_zero, List.getElem_cons_succ,
         toBitVec_add, ← bigSigma1_toBitVec, ← bigSigma0_toBitVec,
         ← Ch_toBitVec, ← Maj_toBitVec, hw, hK]
       -- Seven cases (b..h) close by `assumption` against `h0..h7`; the
       -- single remaining `a`-case needs the `simp only [h0..h7]; ac_rfl`
       -- to reassociate `Σ₀ + Maj + …`.  `try` lets one tactic per line
       -- handle either pattern without per-case bullets.
       try assumption
       try (simp only [h0, h1, h2, h3, h4, h5, h6, h7]; ac_rfl))
  case ring_match =>
    intro k hk1 hk2
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk1) with hk_lt | hk_eq
    · -- k < n: schedule and ring buffer at index k unchanged from previous round.
      have hkn : k ≠ n := Nat.ne_of_lt hk_lt
      have hold := hring k hk_lt (by omega)
      have hkW : k < W.size := by simp only [hWsize]; omega
      have hk64 : k < 64 := hkW
      have hn64 : n < 64 := hn
      have hspec_k : (specScheduleStep (toSpecBlock block₀) n W)[k]! = W[k]! := by
        unfold specScheduleStep
        rw [getElem!_pos _ k hkW]
        split
        · rw [getElem!_pos _ k hk64]
          rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn64,
              Vector.getElem_set_ne hn64 hk64 hkn.symm]
        · rw [getElem!_pos _ k hk64]
          rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn64,
              Vector.getElem_set_ne hn64 hk64 hkn.symm]
      rw [hspec_k]
      by_cases hn16 : n < 16
      · unfold implScheduleStep
        rw [dif_pos hn16]
        exact hold
      · push Not at hn16
        unfold implScheduleStep
        rw [dif_neg (show ¬ (⟨n, hn⟩ : Fin 64).val < 16 by simpa using hn16)]
        -- `k % 16 ≠ n % 16` because `k ∈ [n-15, n-1]` avoids n's mod class.
        have hk_mod : k % 16 ≠ n % 16 := by omega
        rw [Vector.getElem_set_ne (by omega) (by omega) (Ne.symm hk_mod)]
        exact hold
    · -- k = n: the freshly written schedule entry.
      cases hk_eq
      have hself := implScheduleStep_fst_at_self ⟨n, hn⟩ impl_block
      have hval := implScheduleStep_value_match block₀ impl_block W n hn
                     huntouched hring
      rw [hself]
      exact hval
  case untouched =>
    -- Vacuous when `n ≥ 16`: `k.isLt` (k < 16) ∧ `n ≤ k.val` give the contradiction.
    intro k hk
    have hn16 : n < 16 := by have := k.isLt; omega
    unfold implScheduleStep
    rw [dif_pos hn16]
    exact huntouched k (by omega)

/-- Iteration: applying both folds for `n` rounds preserves `MatchAfter`.
Lifts the per-step preservation to the full 64-round fold. -/
theorem MatchAfter_iter
    (state : Impl.State) (block : Impl.Block)
    (n : Nat) (hn : n ≤ 64) :
    let impl_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        implFusedStep ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ acc) (block, state)
    let spec_acc :=
      Fin.foldl n (fun acc (i : Fin n) =>
        specFusedStep (toSpecBlock block) i.val acc)
        (Vector.replicate 64 default, initVars (toSpecState state))
    MatchAfter block impl_acc.1 impl_acc.2 spec_acc.1 spec_acc.2 n := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero]
    exact MatchAfter_zero state block
  | succ k ih =>
    have hk : k ≤ 64 := by omega
    have hk_lt : k < 64 := by omega
    have ih' := ih hk
    simp only [Fin.foldl_succ_last] at *
    exact MatchAfter_step block _ _ _ _ k hk_lt ih'

/-- Final cross-side meet: lifting the impl factored fold through
`toSpecState` yields the spec fused fold (on the lifted block).
Headline lemma of the compress equivalence; consumed by `Main.lean`'s
top-level `compress_correct` rewrite chain. -/
theorem toSpecState_implCompressFoldl
    (state : Impl.State) (block : Impl.Block) :
    toSpecState (implCompressFoldl state block) =
      specCompressFused (toSpecState state) (toSpecBlock block) := by
  have hvars := (MatchAfter_iter state block 64 (le_refl 64)).vars
  -- Reindex `hvars` from `⟨i.val, lt_of_lt_of_le ..⟩` (produced by
  -- `MatchAfter_iter`) to a `Nat`-index form so `interval_cases` can
  -- `rw` against it below.
  have hvars' : ∀ (k : Nat) (hk : k < 8),
      ((Fin.foldl 64 (fun acc (i : Fin 64) => implFusedStep i acc)
        (block, state)).2[k]'hk).toBitVec =
      ((Fin.foldl 64
          (fun acc (t : Fin 64) => specFusedStep (toSpecBlock block) t.val acc)
        (Vector.replicate 64 default, initVars (state.map UInt32.toBitVec))).2[k]'hk) := by
    intro k hk
    exact hvars ⟨k, hk⟩
  -- `Nat`-indexed access at literal `k` against the `Vector.map` form
  -- that `unfold toSpecState` exposes inside the goal.
  have getElem!_lit : ∀ (k : Nat) (h : k < 8),
      (state.map UInt32.toBitVec)[k]! = (state[k]'h).toBitVec := by
    intro k h
    have := getElem!_toSpecState state ⟨k, h⟩
    simpa [toSpecState] using this
  -- Both sides agree at every index `k < 8`; reduce by Vector.ext.
  apply Vector.ext
  intro k hk
  unfold implCompressFoldl specCompressFused addH toSpecState
  rw [Vector.getElem_map, Vector.getElem_zipWith, toBitVec_add]
  rw [hvars' k hk]
  -- Eight working-variable indices; each side reduces to the same
  -- `state[k] + ⟨fold result⟩[k]` after `simp`, modulo `+`-associativity.
  generalize (Fin.foldl 64
      (fun acc (t : Fin 64) => specFusedStep (toSpecBlock block) t.val acc)
      (Vector.replicate 64 default, initVars (state.map UInt32.toBitVec))).2 = B
  interval_cases k <;> (simp; ac_rfl)

end SHS.Equiv.SHA256.Compress.Match
