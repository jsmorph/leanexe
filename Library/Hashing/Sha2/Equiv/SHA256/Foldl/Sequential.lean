import Library.Hashing.Sha2.Equiv.Common.Loop
import Library.Hashing.Sha2.Spec.HashAlgorithms

-- Bounds discharge inside `for h : t in [a:b] do` ranges; see the
-- matching note in `equiv/SHA256/Foldl/Schedule.lean`.
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic|
        first
        | grind
        | (first
              | (have := ‹_ ∈ _›.upper; have := ‹_ ∈ _›.lower; grind)
              | (have := ‹_ ∈ _›.upper; grind)))

/-! # Pure-foldl form of the spec compression — sequential

Restates `SHS.SHA256.compress` as `addH H (Fin.foldl 64 specRoundStep
(initVars H))` after precomputing the schedule.

The desugaring of `Id.run do { mut a..h; for t in [0:64] do … }`
introduces a right-associated 8-`MProd` working tuple; this file owns
that bridge (`SpecVarsTuple`, `tupleToVec`) so consumers reason against
`SpecVars` and never touch `MProd`. -/

open SHS.Equiv.Loop

open SHS.SHA256

namespace SHS.Equiv.SHA256.Foldl.Sequential

open scoped SHS.SHA256

/-- Eight working variables `(a, b, c, d, e, f, g, h)`, in the spec's
`BitVec 32` representation. -/
abbrev SpecVars := Vector (BitVec 32) 8

/-- Build the initial working variables from the input hash value. -/
def initVars (H : HashValue) : SpecVars :=
  Vector.ofFn (fun i : Fin 8 => H[i.val]!)

/-- One round of the spec's compression loop, as a pure function:
shifts `(a..h)` by one, with `a` and `e` updated by the standard
`T1`/`T2` mixing.  This matches the body of the `for t in [0:64]`
loop in `SHS.SHA256.compress`.

Indexed by `Nat` rather than `Fin 64`: see `specScheduleStep` for the
rationale. -/
def specRoundStep (W : Schedule) (t : Nat) (s : SpecVars) : SpecVars :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let T1 := h + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g + SHS.SHA256.K[t]! + W[t]!
  let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

/-- Add the post-loop working variables back into the input hash value. -/
def addH (H : HashValue) (s : SpecVars) : HashValue :=
  #v[s[0] + H[0]!, s[1] + H[1]!, s[2] + H[2]!, s[3] + H[3]!,
    s[4] + H[4]!, s[5] + H[5]!, s[6] + H[6]!, s[7] + H[7]!]

/-! ## Spec-tuple bridge

When Lean desugars `Id.run do { mut a..h; for t in [0:64] do … }`, the
eight `mut` variables become a *nested right-associated `MProd`* —
NOT a custom structure.  The body destructures via `.fst` / `.snd.fst`
/ `.snd.snd.fst` / … and rebuilds via the same anonymous constructor.
The abbreviations and lemmas below mirror that exact shape so the
proof can pattern-match the desugaring directly. -/

/-- The 8-tuple of `BitVec 32` carrying the spec compress's working
variables `(a, b, c, d, e, f, g, h)`, matching the *exact* nested
`Prod` shape produced by `Id.run do { mut a..h; for ... }` desugaring. -/
abbrev SpecVarsTuple :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
    BitVec 32

/-- Convert the desugared tuple state into a `SpecVars` vector. -/
def tupleToVec (t : SpecVarsTuple) : SpecVars :=
  #v[t.fst, t.snd.fst, t.snd.snd.fst, t.snd.snd.snd.fst,
     t.snd.snd.snd.snd.fst, t.snd.snd.snd.snd.snd.fst,
     t.snd.snd.snd.snd.snd.snd.fst, t.snd.snd.snd.snd.snd.snd.snd]

/-- The desugared tuple round step matches the body of spec's
`Id.run do` form: destructure `r` via `.fst`/`.snd.fst`/…, compute
`T1`/`T2`, rotate, and rebuild via anonymous constructor. -/
def tupleRoundStep (W : Schedule) (t : Nat) (r : SpecVarsTuple) : SpecVarsTuple :=
  let a := r.fst
  let x := r.snd
  let b := x.fst
  let x := x.snd
  let c := x.fst
  let x := x.snd
  let d := x.fst
  let x := x.snd
  let e := x.fst
  let x := x.snd
  let f := x.fst
  let x := x.snd
  let g := x.fst
  let h := x.snd
  let T1 := h + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g + SHS.SHA256.K[t]! + W[t]!
  let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
  ⟨T1 + T2, a, b, c, d + T1, e, f, g⟩

/-- The tuple round step matches `specRoundStep` once both states are
viewed through `tupleToVec`. -/
@[simp] theorem tupleToVec_tupleRoundStep (W : Schedule) (t : Fin 64) (r : SpecVarsTuple) :
    tupleToVec (tupleRoundStep W t.val r) = specRoundStep W t.val (tupleToVec r) := by
  rfl

/-- The initial tuple state matches `initVars H` through `tupleToVec`. -/
@[simp] theorem tupleToVec_init (H : HashValue) :
    tupleToVec (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple) =
      initVars H := by
  unfold initVars tupleToVec; rfl

/-- `addH H` applied to a `tupleToVec`-converted tuple equals the
explicit 8-element vector adding each tuple projection to `H[i]!`. -/
@[simp] theorem addH_tupleToVec (H : HashValue) (r : SpecVarsTuple) :
    addH H (tupleToVec r) =
      (#v[r.fst + H[0]!, r.snd.fst + H[1]!, r.snd.snd.fst + H[2]!,
          r.snd.snd.snd.fst + H[3]!, r.snd.snd.snd.snd.fst + H[4]!,
          r.snd.snd.snd.snd.snd.fst + H[5]!, r.snd.snd.snd.snd.snd.snd.fst + H[6]!,
          r.snd.snd.snd.snd.snd.snd.snd + H[7]!] : HashValue) := by
  rfl

/-- Spec `compress` in **sequential** pure-foldl form: precompute the
full schedule, then fold the round body over the 64 rounds. -/
def specCompressSeq (H : HashValue) (M : Block) : HashValue :=
  addH H (Fin.foldl 64
    (fun s (t : Fin 64) => specRoundStep (SHS.SHA256.schedule M) t.val s) (initVars H))

/-- The spec's `compress` equals its sequential pure-foldl form
(`specCompressSeq`).  Downstream consumers reason against
`specCompressSeq` instead of the `Id.run do` form.

After unfolding both sides, LHS is the literal `Id.run do { mut a..h;
for t in [0:64] do … }` desugared into a let-chain wrapping `(forIn
[0:64] ⟨a..h⟩ stepBody).run` followed by an extract-and-add pattern.
The `tupleRoundStep` definition above mirrors the desugaring's `stepBody`
exactly, so `forIn_id_eq_Fin_foldl` lifts the inner `forIn` to a
`Fin.foldl` over `tupleRoundStep`; `tupleToVec_*` simp-lemmas then
bridge to `addH H (Fin.foldl 64 specRoundStep (initVars H))`. -/
theorem spec_compress_eq_seq (H : HashValue) (M : Block) :
    SHS.SHA256.compress H M = specCompressSeq H M := by
  unfold specCompressSeq SHS.SHA256.compress
  -- Spec body: explicit tuple form with bound proofs.
  let bodyTup : (t : Nat) → t ∈ [0:64] → SpecVarsTuple → Id (ForInStep SpecVarsTuple) :=
    fun t h r =>
      have h64 : t < 64 := h.upper
      pure (ForInStep.yield (tupleRoundStep (SHS.SHA256.schedule M) t r))
  -- Show that the spec's full do-block reduces to:
  --   addH H (tupleToVec (Id.run (forIn' [0:64] ⟨H[0]!,...⟩ bodyTup)))
  -- since `H[i]` (with proof) equals `H[i]!` for `i < 8`, and likewise for `K[t]`/`W[t]`.
  have hH (i : Nat) (hi : i < 8) : H[i]'hi = H[i]! :=
    (SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi).symm
  have hbody : (fun (t : Nat) (h : t ∈ [0:64]) (r : SpecVarsTuple) =>
        let a := r.fst; let x := r.snd; let b := x.fst; let x := x.snd
        let c := x.fst; let x := x.snd; let d := x.fst; let x := x.snd
        let e := x.fst; let x := x.snd; let f := x.fst; let x := x.snd
        let g := x.fst; let h_ := x.snd
        let T1 := h_ + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g +
          (SHS.SHA256.K[t]'h.upper) + ((SHS.SHA256.schedule M)[t]'h.upper)
        let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
        pure (ForInStep.yield (⟨T1 + T2, a, b, c, d + T1, e, f, g⟩ : SpecVarsTuple))) =
      bodyTup := by
    funext t h r
    simp only [bodyTup, tupleRoundStep]
    have h64 : t < 64 := h.upper
    rw [SHS.Equiv.VecBridge.getElem_bang_eq_getElem SHS.SHA256.K t h64,
        SHS.Equiv.VecBridge.getElem_bang_eq_getElem (SHS.SHA256.schedule M) t h64]
  -- Reduce the spec do-block (matching its desugared form exactly).
  show Id.run (do
        let r ← forIn' [0:64]
          (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
             H[4]'(by decide), H[5]'(by decide),
             H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple)
          (fun t (h : t ∈ [0:64]) r =>
            let a := r.fst; let x := r.snd; let b := x.fst; let x := x.snd
            let c := x.fst; let x := x.snd; let d := x.fst; let x := x.snd
            let e := x.fst; let x := x.snd; let f := x.fst; let x := x.snd
            let g := x.fst; let h_ := x.snd
            let T1 := h_ + SHS.SHA256.bigSigma1 e + SHS.SHA256.Ch e f g +
              (SHS.SHA256.K[t]'h.upper) + ((SHS.SHA256.schedule M)[t]'h.upper)
            let T2 := SHS.SHA256.bigSigma0 a + SHS.SHA256.Maj a b c
            pure (ForInStep.yield (⟨T1 + T2, a, b, c, d + T1, e, f, g⟩ : SpecVarsTuple)))
        match r with
        | ⟨a, b, c, d, e, f, g, h⟩ =>
          pure (#v[a + H[0], b + H[1], c + H[2], d + H[3],
                  e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) = _
  rw [hbody]
  -- Now bridge forIn' → forIn.
  show (Id.run (forIn' [0:64]
          (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
             H[4]'(by decide), H[5]'(by decide),
             H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple)
          bodyTup)
        |> fun r => match r with
          | ⟨a, b, c, d, e, f, g, h⟩ =>
            (#v[a + H[0], b + H[1], c + H[2], d + H[3],
                e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) = _
  -- Replace `H[i]` (with proof) by `H[i]!` everywhere using hH.
  have hinit_eq :
      (⟨H[0]'(by decide), H[1]'(by decide), H[2]'(by decide), H[3]'(by decide),
         H[4]'(by decide), H[5]'(by decide), H[6]'(by decide), H[7]'(by decide)⟩ : SpecVarsTuple) =
      ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ := by
    rw [hH 0, hH 1, hH 2, hH 3, hH 4, hH 5, hH 6, hH 7]
  rw [hinit_eq]
  rw [show Id.run (forIn' [0:64]
          (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
          bodyTup) =
      Id.run (forIn [0:64]
        (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
        (fun t r => pure (ForInStep.yield
          (tupleRoundStep (SHS.SHA256.schedule M) t r)))) from by
    rw [← forIn'_id_eq_forIn 0 64 _
          (fun t r => tupleRoundStep (SHS.SHA256.schedule M) t r)]]
  -- Convert to Fin.foldl, transport via tupleToVec.
  rw [forIn_id_eq_Fin_foldl 64
        (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple)
        (tupleRoundStep (SHS.SHA256.schedule M))]
  -- Now the goal is:
  --   (match Fin.foldl ... ⟨H[0]!,...⟩ with | ⟨a,...,h⟩ => #v[a + H[0],...]) = addH H (...)
  -- Pull out the matched tuple, then unfold `addH` on the RHS via `tupleToVec`.
  have hfinal :
      (fun r : SpecVarsTuple =>
        match r with
        | ⟨a, b, c, d, e, f, g, h⟩ =>
          (#v[a + H[0], b + H[1], c + H[2], d + H[3],
              e + H[4], f + H[5], g + H[6], h + H[7]] : HashValue)) =
      (fun r : SpecVarsTuple => addH H (tupleToVec r)) := by
    funext r
    obtain ⟨a, b, c, d, e, f, g, h⟩ := r
    simp only [addH, tupleToVec]
    rw [← hH 0, ← hH 1, ← hH 2, ← hH 3, ← hH 4, ← hH 5, ← hH 6, ← hH 7]
    rfl
  -- Apply hfinal pointwise, with the fold abstracted so that no definitional check unfolds it.
  generalize hF : Fin.foldl 64 (fun s (t : Fin 64) =>
      tupleRoundStep (SHS.SHA256.schedule M) t.val s)
    (⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ : SpecVarsTuple) = F
  refine (congrFun hfinal F).trans ?_
  subst hF
  rw [fin_foldl_transport 64
        (fun r t => tupleRoundStep (SHS.SHA256.schedule M) t.val r)
        (fun s (t : Fin 64) => specRoundStep (SHS.SHA256.schedule M) t.val s)
        tupleToVec
        ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
        (fun a i => tupleToVec_tupleRoundStep _ i a)]
  rw [tupleToVec_init]

end SHS.Equiv.SHA256.Foldl.Sequential
