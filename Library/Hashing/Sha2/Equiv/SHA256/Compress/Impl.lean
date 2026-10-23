import Library.Hashing.Sha2.Equiv.SHA256.Lift
import Library.Hashing.Sha2.Equiv.SHA256.Functions
import Library.Hashing.Sha2.Equiv.SHA256.Constants
import Library.Hashing.Sha2.Equiv.SHA256.Foldl.Fused
import Mathlib.Tactic.IntervalCases

/-! # Compression equivalence — implementation-side factoring

The implementation's `compress` is imperative; this file recasts it as
a pure `Fin.foldl 64` (`implCompressFoldl`), proves the agreement with
`Impl.compress` via a `RoundState ↔ (Block, State)` fold-homomorphism
(`impl_compress_eq_foldl`), and proves the per-step bridge lemmas that
connect the impl fold's transitions to the spec's `specScheduleStep` /
`specRoundStep` primitives.

These per-step bridges are stated as standalone lemmas (independent
of the 64-round induction) so that `MatchAfter_step` in
`Compress/Match.lean` can call them directly without case-splitting
inline. -/

open SHS.Equiv.SHA256.Bridge
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Functions
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential

open SHS.SHA256

namespace SHS.Equiv.SHA256.Compress.Impl

open scoped SHS.SHA256

/-- The ring-buffer index bound used at every schedule-step site:
`k % 16 < 16`.  Extracted to deduplicate the inline
`Nat.mod_lt _ (by decide)` proofs at the lemma sites and inside
`MatchAfter`'s `ring` field. -/
theorem mod16_lt (k : Nat) : k % 16 < 16 := Nat.mod_lt _ (by decide)

/-! ## Implementation-side factoring -/

/-- One schedule step on the impl side: read `W[i]` (for `i < 16`,
straight from the block) or compute `W[i]` from the ring buffer and
store it back. Returns the updated ring buffer and the freshly-known
`W[i]`. -/
def implScheduleStep (i : Fin 64) (block : Impl.Block) : Impl.Block × UInt32 :=
  if hi : i.val < 16 then
    (block, block[i.val]'hi)
  else
    let w15 := block[(i.val - 15) % 16]'(by omega)
    let s0  := (Impl.UInt32.rotr w15 7) ^^^ (Impl.UInt32.rotr w15 18) ^^^ (w15 >>> 3)
    let w2  := block[(i.val - 2) % 16]'(by omega)
    let s1  := (Impl.UInt32.rotr w2 17) ^^^ (Impl.UInt32.rotr w2 19) ^^^ (w2 >>> 10)
    let w16 := block[(i.val - 16) % 16]'(by omega)
    let w7  := block[(i.val - 7) % 16]'(by omega)
    let new := w16 + s0 + w7 + s1
    (block.set ((i.val) % 16) new (by omega), new)

/-- One round body on the impl side: mix the schedule word `w` into the
eight working variables. -/
def implRoundBody (i : Fin 64) (w : UInt32) (s : Impl.State) : Impl.State :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let s1 := (Impl.UInt32.rotr e 6) ^^^ (Impl.UInt32.rotr e 11) ^^^ (Impl.UInt32.rotr e 25)
  let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
  let t1 := s1 + ch + Impl.K32[i] + w + h
  let s0 := (Impl.UInt32.rotr a 2) ^^^ (Impl.UInt32.rotr a 13) ^^^ (Impl.UInt32.rotr a 22)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let t2 := s0 + mj
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- One full round step: schedule, then mix. -/
def implFusedStep (i : Fin 64) (acc : Impl.Block × Impl.State) :
    Impl.Block × Impl.State :=
  let (block', w) := implScheduleStep i acc.1
  (block', implRoundBody i w acc.2)

/-- The named factored form of the implementation's `compress`:
`Fin.foldl 64 implFusedStep` plus the final hash add.

This definition plays a dual role:
1. **Pivot for the spec ↔ impl equivalence proof** — the `MatchAfter`
   induction in `Compress/Match.lean` is stated against the per-step
   primitives `implScheduleStep` / `implRoundBody` that compose into
   `implFusedStep`, and `Main.lean` rewrites `Impl.compress` to this
   form so the induction applies.
2. **Aeneas-bridge target** — the shape (8-tuple working state +
   16-word ring-buffer schedule, pure functional `Fin.foldl 64`, no
   `Id.run`/`let mut`/imperative state) is precisely what an Aeneas
   Rust→Lean extraction of SHA-256 lands in after `noncomputable`
   lifting.  A future consumer wanting to refine an extraction against
   our spec needs only to prove `aeneas_compress = implCompressFoldl`
   (mostly type-level rewrites between `Std.U32` and `UInt32`); the
   spec ↔ `implCompressFoldl` half is what this project verifies. -/
def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let (_, s') := Fin.foldl 64 (fun acc i => implFusedStep i acc) (block, state)
  Vector.zipWith (· + ·) state s'

/-- Used in `impl_compress_eq_foldl` to convert `implCompressFoldl`'s
`Vector.zipWith` epilogue into the same 8-element literal shape as
`impl_compress_eq_foldl_form`'s reduction of `Impl.compress`. -/
private theorem zipWith_add_eq_mk (state s' : Impl.State) :
    Vector.zipWith (· + ·) state s' =
      #v[ state[0] + s'[0], state[1] + s'[1], state[2] + s'[2], state[3] + s'[3],
          state[4] + s'[4], state[5] + s'[5], state[6] + s'[6], state[7] + s'[7] ] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp

/-! ### Bridge to `Impl.compress`'s `RoundState`-shaped fold

`Impl.compress` runs `Fin.foldl 64 Impl.roundStep` over a `RoundState`
struct; `implCompressFoldl` runs `Fin.foldl 64 implFusedStep` over a
`(Block, Vector UInt32 8)` pair.  Both share the same outer
`Fin.foldl 64` shape, so the bridge is a per-iteration `RoundState ↔
(Block, State)` correspondence carried through fold-homomorphism. -/

/-- The state correspondence: a `RoundState` on the impl side maps to
`(rs.schedule, #v[rs.a, …, rs.h])` on the equiv side. -/
private def roundStateToPair (rs : Impl.RoundState) : Impl.Block × Impl.State :=
  (rs.schedule, #v[rs.a, rs.b, rs.c, rs.d, rs.e, rs.f, rs.g, rs.h])

/-- Generic `Fin.foldl` homomorphism: if a per-step morphism `f`
intertwines two step functions, it intertwines their folds. -/
private theorem fin_foldl_hom {α β : Type _} : ∀ {n : Nat}
    (f : α → β) (g : α → Fin n → α) (h : β → Fin n → β),
    (∀ a i, f (g a i) = h (f a) i) → ∀ (init : α),
    f (Fin.foldl n g init) = Fin.foldl n h (f init)
  | 0, _, _, _, _, _ => by simp [Fin.foldl_zero]
  | m + 1, f, g, h, step_eq, init => by
    rw [Fin.foldl_succ, Fin.foldl_succ]
    -- Apply IH at `m` with the new init `g init 0` (which corresponds
    -- to `h (f init) 0` via `step_eq init 0`).
    rw [fin_foldl_hom f (fun x (j : Fin m) => g x j.succ)
                       (fun x (j : Fin m) => h x j.succ)
          (fun a j => step_eq a j.succ) (g init 0)]
    rw [step_eq init 0]

/-- One impl round equals one equiv `implFusedStep` after the
correspondence.  Both bodies have the same structural shape; the
proof is unfold + `Vector.ext` per indexed slot. -/
private theorem roundStep_corresponds (rs : Impl.RoundState) (i : Fin 64) :
    roundStateToPair (Impl.roundStep rs i) = implFusedStep i (roundStateToPair rs) := by
  unfold roundStateToPair Impl.roundStep implFusedStep implScheduleStep implRoundBody
  apply Prod.ext
  · -- Block component: identical conditional schedule update.
    rfl
  · -- State component: literal 8-vector vs. literal 8-vector.
    apply Vector.ext
    intro k hk
    interval_cases k <;> rfl

/-- The impl's `Impl.compress` reduces (modulo the `unroll64`/`Fin.foldl`
codegen-vs-proof equivalence) to a `Fin.foldl 64 Impl.roundStep` over
`RoundState` followed by the `#v[state[i] + final.field]` hash add. -/
private theorem impl_compress_eq_foldl_form (state : Impl.State) (block : Impl.Block) :
    Impl.compress state block =
      let final := Fin.foldl 64 Impl.roundStep (Impl.RoundState.ofState state block)
      #v[ state[0] + final.a, state[1] + final.b, state[2] + final.c, state[3] + final.d,
          state[4] + final.e, state[5] + final.f, state[6] + final.g, state[7] + final.h ] := by
  unfold Impl.compress
  simp only [SHS.Impl.Unroll.unroll64_eq_foldl]

/-- Public bridge: the impl's `RoundState`-shaped fold equals the
equiv's `(Block, State)`-shaped fold, plus matching final hash adds. -/
theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := by
  rw [impl_compress_eq_foldl_form]
  unfold implCompressFoldl
  -- Apply the fold homomorphism with `f = roundStateToPair`.
  have h_fold := fin_foldl_hom (n := 64) roundStateToPair
    Impl.roundStep (fun acc i => implFusedStep i acc)
    roundStep_corresponds (Impl.RoundState.ofState state block)
  -- The starting RoundState corresponds to `(block, state)`.
  have h_init : roundStateToPair (Impl.RoundState.ofState state block) = (block, state) := by
    unfold roundStateToPair Impl.RoundState.ofState
    apply Prod.ext
    · rfl
    · apply Vector.ext
      intro k hk
      interval_cases k <;> rfl
  rw [h_init] at h_fold
  -- Destruct the equiv-side fold result and the impl-side `let`-bindings.
  set final_rs := Fin.foldl 64 Impl.roundStep
    (Impl.RoundState.ofState state block)
  set final_pair := Fin.foldl 64 (fun acc i => implFusedStep i acc) (block, state)
  show Vector.zipWith (fun x1 x2 => x1 + x2) state final_pair.2 =
    #v[ state[0] + final_rs.a, state[1] + final_rs.b, state[2] + final_rs.c, state[3] + final_rs.d,
        state[4] + final_rs.e, state[5] + final_rs.f, state[6] + final_rs.g, state[7] + final_rs.h ]
  -- `final_pair.2 = #v[final_rs.fields]` by the fold equation.
  have h_pair_eq : final_pair.2 =
      #v[final_rs.a, final_rs.b, final_rs.c, final_rs.d,
         final_rs.e, final_rs.f, final_rs.g, final_rs.h] := by
    have h := h_fold
    unfold roundStateToPair at h
    exact congrArg Prod.snd h.symm
  rw [h_pair_eq, zipWith_add_eq_mk]
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-! ## Per-step bridges

Single-round equivalences between impl primitives and their spec
counterparts.  These are reusable independently of the 64-round
induction. -/

/-- The initial working variables built from a lifted impl state agree
with the impl state pointwise.  Base case of the `MatchAfter` invariant
in `Compress/Match.lean`. -/
theorem initVars_toSpecState_getElem (state : Impl.State) (k : Fin 8) :
    (initVars (toSpecState state))[k] = state[k].toBitVec := by
  simp [initVars, toSpecState, getElem!_pos]

-- Note: a per-index round-body equivalence lemma was attempted here but
-- cannot be packaged as a `∀ k : Fin 8` because `fin_cases` /
-- `match k with ⟨0,_⟩ ... ⟨7,_⟩` substitutes `⟨k, _⟩` into the goal,
-- preventing `Vector.getElem_mk` from matching the indexing pattern.
-- The 8-way enumeration therefore lives inline inside `MatchAfter_step`
-- in `Compress/Match.lean`.

/-- Schedule-step value equivalence (extension case `i ≥ 16`).
Used by `implScheduleStep_value_match` to align the impl's freshly
computed `W[i]` with the spec's `smallSigma1 + … + smallSigma0 + …`
formula, given the four ring-buffer entries already match. -/
theorem implScheduleStep_value_ge_16
    (i : Fin 64) (impl_block : Impl.Block) (W : Schedule) (hi : 16 ≤ i.val)
    (h2 : (impl_block[(i.val - 2) % 16]'(by omega)).toBitVec = W[i.val - 2]!)
    (h7 : (impl_block[(i.val - 7) % 16]'(by omega)).toBitVec = W[i.val - 7]!)
    (h15 : (impl_block[(i.val - 15) % 16]'(by omega)).toBitVec = W[i.val - 15]!)
    (h16 : (impl_block[(i.val - 16) % 16]'(by omega)).toBitVec = W[i.val - 16]!) :
    (implScheduleStep i impl_block).2.toBitVec =
      SHS.SHA256.smallSigma1 W[i.val - 2]! + W[i.val - 7]! +
        SHS.SHA256.smallSigma0 W[i.val - 15]! + W[i.val - 16]! := by
  unfold implScheduleStep
  rw [dif_neg (by omega : ¬ i.val < 16)]
  simp only [toBitVec_add,
    ← smallSigma1_toBitVec, ← smallSigma0_toBitVec,
    h2, h7, h15, h16]
  ac_rfl

/-- The freshly-known schedule word (`(implScheduleStep i b).2`) is exactly
the entry stored at `i.val % 16` in the updated ring buffer
(`(implScheduleStep i b).1`).

Used in `MatchAfter_step`'s `ring_match` sub-case to bridge "the new
schedule entry at index `n`" with "what the impl wrote to the ring
buffer at slot `n % 16`". -/
theorem implScheduleStep_fst_at_self
    (i : Fin 64) (impl_block : Impl.Block) :
    ((implScheduleStep i impl_block).1[i.val % 16]'(mod16_lt _)) =
      (implScheduleStep i impl_block).2 := by
  unfold implScheduleStep
  by_cases hi : i.val < 16
  · simp only [dif_pos hi]; simp [Nat.mod_eq_of_lt hi]
  · simp only [dif_neg hi]; simp

/-- Schedule-step value match (both branches `i.val < 16` and `i.val ≥ 16`):
the impl's freshly-known schedule word matches the spec's just-written
`W[i.val]!`, given the previous-round invariant on the ring buffer.

The schedule half of the per-round equivalence; consumed by the
`vars_match` and `ring_match` sub-cases of `MatchAfter_step`. -/
theorem implScheduleStep_value_match
    (block₀ impl_block : Impl.Block) (W : Schedule) (n : Nat) (hn : n < 64)
    (huntouched : ∀ k : Fin 16, n ≤ k.val → impl_block[k] = block₀[k])
    (hring : ∀ k < n, n ≤ k + 16 →
      (impl_block[k % 16]'(by
        have := Nat.mod_lt k (show 0 < 16 by decide); omega)).toBitVec = W[k]!) :
    ((implScheduleStep ⟨n, hn⟩ impl_block).2).toBitVec =
      (specScheduleStep (toSpecBlock block₀) n W)[n]! := by
  by_cases hn16 : n < 16
  · -- Initial case: spec writes `M[n]!`; impl block unchanged.
    unfold implScheduleStep specScheduleStep
    simp only [dif_pos hn16, if_pos hn16]
    rw [show impl_block[n] = block₀[n] from huntouched ⟨n, hn16⟩ (le_refl n)]
    rw [show (toSpecBlock block₀)[n]! = block₀[n].toBitVec from
        getElem!_toSpecBlock block₀ ⟨n, hn16⟩]
    rw [getElem!_pos _ n hn]
    rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn, Vector.getElem_set_self]
  · -- Extension case: both sides compute the `smallSigma1/smallSigma0` formula.
    push Not at hn16
    have h2 := hring (n - 2) (by omega) (by omega)
    have h7 := hring (n - 7) (by omega) (by omega)
    have h15 := hring (n - 15) (by omega) (by omega)
    have h16 := hring (n - 16) (by omega) (by omega)
    rw [implScheduleStep_value_ge_16 ⟨n, hn⟩ impl_block W hn16 h2 h7 h15 h16]
    unfold specScheduleStep
    simp only [if_neg (Nat.not_lt.mpr hn16)]
    rw [getElem!_pos _ n hn]
    rw [SHS.Equiv.VecBridge.set_bang_eq_set _ _ hn, Vector.getElem_set_self]

end SHS.Equiv.SHA256.Compress.Impl
