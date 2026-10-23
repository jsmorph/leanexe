import Library.Hashing.Sha2.Equiv.Common.Loop
import Library.Hashing.Sha2.Impl.SHA512
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 compression equivalence — implementation-side factoring

The impl's `Impl.compress` is built from `Impl.messageSchedule` (80-word
expansion) followed by an 80-round mix.  Both pieces parallel the spec's
`SHS.SHA512.schedule` / `SHS.SHA512.compress` structure exactly; this file
reifies each as a pure `Fin.foldl`:

* `implScheduleFoldl` / `messageSchedule_eq_foldl` — the schedule.
* `implCompressFoldl` / `impl_compress_eq_foldl`   — the full compression.

The spec ↔ impl bridge over these reifications lives in
`Compress/Match.lean` (per-step induction via `fin_foldl_transport`). -/

-- Bounds discharge inside `for h : t in [a:b] do` ranges.  Range membership
-- (`Std.Legacy.Range`) carries `.upper` / `.lower`; extract them and let
-- `grind` close the resulting arithmetic goals (e.g. `t < 80`, `t - 16 < 80`).
local macro_rules
  | `(tactic| get_elem_tactic) =>
    `(tactic| first
        | grind
        | (have := ‹_ ∈ _›.upper; (try have := ‹_ ∈ _›.lower); grind))

open SHS.Equiv.Loop
open SHS.Equiv.VecBridge
open SHS.SHA512

namespace SHS.Equiv.SHA512.Compress.Impl

/-! ## Foldl form of `Impl.messageSchedule`

Same two-loop shape as the spec (`[0:16]` copy + `[16:80]` extension),
reified as a single `Fin.foldl 80`; mirrors `Foldl/Schedule.lean`. -/

/-- One step of the impl schedule, as a pure function on `Impl.Schedule`. -/
def implScheduleStep (block : Impl.Block) (t : Nat) (w : Impl.Schedule) : Impl.Schedule :=
  if t < 16 then
    w.set! t block[t]!
  else
    let w15 := w[t - 15]!
    let s0  := (Impl.UInt64.rotr w15 1) ^^^ (Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
    let w2  := w[t - 2]!
    let s1  := (Impl.UInt64.rotr w2 19) ^^^ (Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
    w.set! t (w[t - 16]! + s0 + w[t - 7]! + s1)

/-- Pure-foldl form of the impl schedule. -/
def implScheduleFoldl (block : Impl.Block) : Impl.Schedule :=
  Fin.foldl 80 (fun w (t : Fin 80) => implScheduleStep block t.val w)
    (Vector.replicate 80 0)

/-- `Impl.messageSchedule` is `Fin.foldl 80 implScheduleStep`.

Mirrors `Foldl/Schedule.lean`'s `schedule_eq_foldl`: convert each loop
`forIn' → forIn → Fin.foldl`, then splice via `fin_foldl_split`.  The
phases are `let`-bound as `copyStep`/`extStep` so the splice matches
`implScheduleStep`'s `if`-branches by `rfl`. -/
theorem messageSchedule_eq_foldl (block : Impl.Block) :
    Impl.messageSchedule block = implScheduleFoldl block := by
  -- Plain-Nat-indexed step functions for the two phases, in `set!`/`[]!` form.
  let copyStep : Nat → Impl.Schedule → Impl.Schedule :=
    fun n w => w.set! n block[n]!
  let extStep  : Nat → Impl.Schedule → Impl.Schedule := fun n w =>
    let w15 := w[n - 15]!
    let s0  := (Impl.UInt64.rotr w15 1) ^^^ (Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
    let w2  := w[n - 2]!
    let s1  := (Impl.UInt64.rotr w2 19) ^^^ (Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
    w.set! n (w[n - 16]! + s0 + w[n - 7]! + s1)
  -- Name the desugared `forIn'` bodies so the unfolded `Impl.messageSchedule`
  -- shape matches the `forIn'_id_eq_forIn_of_eq` rewrite targets below.
  let copyBody : (t : Nat) → t ∈ [0:16] → Impl.Schedule → Id (ForInStep Impl.Schedule) :=
    fun t h w => pure (ForInStep.yield (w.set t block[t]))
  let extBody : (t : Nat) → t ∈ [16:80] → Impl.Schedule → Id (ForInStep Impl.Schedule) :=
    fun t h w =>
      pure (ForInStep.yield (let w15 := w[t - 15]
        let s0 := (Impl.UInt64.rotr w15 1) ^^^ (Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
        let w2 := w[t - 2]
        let s1 := (Impl.UInt64.rotr w2 19) ^^^ (Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
        w.set t (w[t - 16] + s0 + w[t - 7] + s1)))
  -- Rewrite chain: (1) erase `'` per loop (body factors through copyStep/extStep
  -- on in-bounds indices), (2) `forIn` → `Fin.foldl`, (3) splice via
  -- `fin_foldl_split` — the `implScheduleStep` lambda is split-form by rfl
  -- because its `if t < 16` branches are `copyStep`/`extStep`.
  show (forIn' [16:80] (Id.run (forIn' [0:16] (Vector.replicate 80 0) copyBody))
          extBody : Id _).run = _
  rw [forIn'_id_eq_forIn_of_eq 0 16 _ _ copyStep (fun t hm w => by
        have h80 : t < 80 := by have := hm.upper; grind
        simp [copyStep, set_bang_eq_set _ _ h80,
          getElem_bang_eq_getElem block t hm.upper]),
      forIn'_id_eq_forIn_of_eq 16 80 _ _ extStep (fun t hm w => by
        have h80 : t < 80 := hm.upper
        simp [extStep,
          getElem_bang_eq_getElem w (t-2)  (by grind),
          getElem_bang_eq_getElem w (t-7)  (by grind),
          getElem_bang_eq_getElem w (t-15) (by grind),
          getElem_bang_eq_getElem w (t-16) (by grind),
          set_bang_eq_set _ _ h80]),
      forIn_id_eq_Fin_foldl 16 (Vector.replicate 80 0) copyStep,
      forIn_id_eq_Fin_foldl_offset 16 80 _ extStep,
      show (80 - 16) = 64 from rfl]
  unfold implScheduleFoldl
  exact (fin_foldl_split 16 80 (by decide) copyStep extStep _).symm

/-! ## Foldl form of `Impl.compress`'s round mix

The 80-round mix's `Id.run do` desugars to a `forIn'` over an 8-deep
`MProd` tuple (8 mutable working variables `a..h`).  We bridge that to
a `Fin.foldl` over `Impl.State` (`Vector UInt64 8`), mirroring
`Foldl/Sequential.lean`. -/

/-- The impl's round mix, as a pure function on `Impl.State`. -/
def implRoundStep (w : Impl.Schedule) (t : Nat) (s : Impl.State) : Impl.State :=
  let a := s[0]; let b := s[1]; let c := s[2]; let d := s[3]
  let e := s[4]; let f := s[5]; let g := s[6]; let h := s[7]
  let s1 := (Impl.UInt64.rotr e 14) ^^^ (Impl.UInt64.rotr e 18) ^^^ (Impl.UInt64.rotr e 41)
  let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
  let t1 := s1 + ch + Impl.K64[t]! + w[t]! + h
  let s0 := (Impl.UInt64.rotr a 28) ^^^ (Impl.UInt64.rotr a 34) ^^^ (Impl.UInt64.rotr a 39)
  let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
  let t2 := s0 + mj
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- Eight nested `Prod` cells matching the desugar of
`Id.run do { let mut a..h; for ... }`. -/
abbrev ImplVarsTuple :=
  UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- Project an `ImplVarsTuple` (8 nested `MProd`s) back to an `Impl.State` vector. -/
def implTupleToVec : ImplVarsTuple → Impl.State
  | ⟨a, b, c, d, e, f, g, h⟩ => #v[a, b, c, d, e, f, g, h]

/-- Same body as `implRoundStep`, on the `MProd`-tuple state matching the
do-block desugar (the `match`-on-`⟨a,…,h⟩` is rfl-equal to the 8-deep
`r.fst / r.snd. … .fst` projection chain). -/
def implTupleRoundStep (w : Impl.Schedule) (t : Nat) : ImplVarsTuple → ImplVarsTuple
  | ⟨a, b, c, d, e, f, g, h⟩ =>
    let s1 := (Impl.UInt64.rotr e 14) ^^^ (Impl.UInt64.rotr e 18) ^^^ (Impl.UInt64.rotr e 41)
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := s1 + ch + Impl.K64[t]! + w[t]! + h
    let s0 := (Impl.UInt64.rotr a 28) ^^^ (Impl.UInt64.rotr a 34) ^^^ (Impl.UInt64.rotr a 39)
    let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + mj
    ⟨t1 + t2, a, b, c, d + t1, e, f, g⟩

/-- `implTupleRoundStep` matches `implRoundStep` once both states are
viewed through `implTupleToVec`. -/
theorem implTupleToVec_implTupleRoundStep
    (w : Impl.Schedule) (t : Fin 80) (r : ImplVarsTuple) :
    implTupleToVec (implTupleRoundStep w t.val r) =
      implRoundStep w t.val (implTupleToVec r) := by rfl

/-- The initial 8-tuple `⟨state[0], …, state[7]⟩` projects back to
`state` through `implTupleToVec`.  Closes by enumerating the 8 indices. -/
theorem implTupleToVec_init (state : Impl.State) :
    implTupleToVec
      (⟨state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]⟩
        : ImplVarsTuple) = state :=
  Vector.ext fun i _ => by interval_cases i <;> rfl

/-! ## Foldl form of `Impl.compress` -/

/-- Pure-foldl form of `Impl.compress`: `Impl.messageSchedule`, an 80-round
fold of `implRoundStep`, then the per-slot `state[i] + final[i]` add.  The
schedule is bridged via `messageSchedule_eq_foldl` above. -/
def implCompressFoldl (state : Impl.State) (block : Impl.Block) : Impl.State :=
  let w := Impl.messageSchedule block
  let final := Fin.foldl 80 (fun s (t : Fin 80) => implRoundStep w t.val s) state
  #v[state[0] + final[0], state[1] + final[1], state[2] + final[2], state[3] + final[3],
     state[4] + final[4], state[5] + final[5], state[6] + final[6], state[7] + final[7]]

/-- `Impl.compress` agrees with its `Fin.foldl` reification.

Mirrors `Foldl/Sequential.lean`'s `spec_compress_eq_seq`: desugar the
`Id.run do { mut a..h; for ... }` into a `forIn'` over `ImplVarsTuple`,
erase the `'`, convert to `Fin.foldl`, then transport to a fold over
`Impl.State` via `fin_foldl_transport`. -/
theorem impl_compress_eq_foldl (state : Impl.State) (block : Impl.Block) :
    implCompressFoldl state block = Impl.compress state block := by
  symm
  unfold implCompressFoldl Impl.compress
  -- Initial 8-tuple (matches `let mut a := state[0]; …`), tuple-shaped round step
  -- specialised to this block's schedule, and the post-loop hash-add (rfl-equal
  -- to the `match`-on-`⟨a,…,h⟩` produced by the desugar).
  let initTup : ImplVarsTuple :=
    ⟨state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]⟩
  let tupStep : Nat → ImplVarsTuple → ImplVarsTuple :=
    implTupleRoundStep (Impl.messageSchedule block)
  let postAdd : Impl.State → Impl.State := fun v =>
    #v[state[0] + v[0], state[1] + v[1], state[2] + v[2], state[3] + v[3],
       state[4] + v[4], state[5] + v[5], state[6] + v[6], state[7] + v[7]]
  -- The desugared `forIn'` body (8-deep `MProd` projection + round formula);
  -- named so the `show` reshape below `rfl`-matches.
  let roundBody : (t : Nat) → t ∈ [0:80] → ImplVarsTuple → Id (ForInStep ImplVarsTuple) :=
    fun t hmem r =>
      let a := r.fst; let x := r.snd; let b := x.fst; let x := x.snd
      let c := x.fst; let x := x.snd; let d := x.fst; let x := x.snd
      let e := x.fst; let x := x.snd; let f := x.fst; let x := x.snd
      let g := x.fst; let h := x.snd
      let s1 := (Impl.UInt64.rotr e 14) ^^^ (Impl.UInt64.rotr e 18) ^^^ (Impl.UInt64.rotr e 41)
      let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
      let t1 := s1 + ch + Impl.K64[t] + (Impl.messageSchedule block)[t] + h
      let s0 := (Impl.UInt64.rotr a 28) ^^^ (Impl.UInt64.rotr a 34) ^^^ (Impl.UInt64.rotr a 39)
      let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := s0 + mj
      pure (ForInStep.yield (⟨t1 + t2, a, b, c, d + t1, e, f, g⟩ : ImplVarsTuple))
  -- Reshape to `postAdd ∘ implTupleToVec ∘ Id.run (forIn' …)` (the `match`-on-tuple
  -- post-loop is rfl-equal to `postAdd ∘ implTupleToVec`).  Then: erase `'`,
  -- fold-ify, transport through `implTupleToVec`, reduce `implTupleToVec initTup`.
  show (Id.run (forIn' [0:80] initTup roundBody) |> implTupleToVec |> postAdd) = _
  rw [forIn'_id_eq_forIn_of_eq 0 80 initTup _ tupStep (fun t hmem r => by
        have h80 : t < 80 := hmem.upper
        simp only [tupStep, implTupleRoundStep,
          getElem_bang_eq_getElem Impl.K64 t h80,
          getElem_bang_eq_getElem (Impl.messageSchedule block) t h80]),
      forIn_id_eq_Fin_foldl 80 initTup tupStep,
      fin_foldl_transport 80
        (fun r (t : Fin 80) => tupStep t.val r)
        (fun s (t : Fin 80) => implRoundStep (Impl.messageSchedule block) t.val s)
        implTupleToVec initTup
        (fun a i => implTupleToVec_implTupleRoundStep _ i a),
      implTupleToVec_init]

end SHS.Equiv.SHA512.Compress.Impl
