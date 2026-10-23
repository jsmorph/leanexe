import Batteries.Data.List.Lemmas

/-!
# Generic loop infrastructure for the spec ↔ implementation equivalence

The SHA-256 / SHA-512 specs are written in `do`-notation:
```
Id.run do
  for t in [0:n] do
    …
```
which makes induction over the loop body awkward.  This module provides
the generic plumbing that lets the equivalence proofs treat such loops
as `Fin.foldl` instead, and that lets us fuse / split / transport folds
as needed.

## Contents (`SHS.Equiv.Loop`)

* `forIn_id_eq_Fin_foldl` — convert `for t in [0:n]` ↦ `Fin.foldl n`.
* `forIn_id_eq_Fin_foldl_offset` — same, for ranges `[a:b]` (with shift).
* `forIn'_id_eq_forIn` — erase the membership-proof `'` from a `forIn'`
  whose body is a plain function of the index.
* `forIn'_id_eq_forIn_of_eq` — same, when the body uses the membership
  proof internally but agrees pointwise with an external function.
* `fin_foldl_split` — split a `[0:m]` fold whose body branches on `i < n`
  into two consecutive folds (`[0:n]` then `[n:m]`).
* `fin_foldl_transport` — push a state-bijection `φ` through a fold,
  provided each step commutes with `φ`.

## Contents (`SHS.Equiv.VecBridge`)

* `set_bang_eq_set` / `getElem_bang_eq_getElem` — in-bounds:
  `Vector.set!` / `xs[i]!` reduce to `Vector.set` / `xs[i]'h`.
* `set_bang_oob` / `getElem_bang_oob` — out-of-bounds:
  `Vector.set!` is a no-op and `xs[i]!` returns the inhabited default.

These lemmas are domain-agnostic; they live here (rather than under
`equiv/SHA256/` or `equiv/SHA512/`) so each hash family can reuse them.
-/

namespace SHS.Equiv.Loop

/-! ## `forIn` ↔ `Fin.foldl` -/

/-- Pure-yield `forIn` over `[0:n]` in the identity monad equals `Fin.foldl n`.

This is the entry point used by every spec-side proof: it converts the
`do`-notation form the spec is written in into a `Fin.foldl`, on which we
can do induction, splitting, transport, etc. -/
theorem forIn_id_eq_Fin_foldl {β : Type _} (n : Nat) (init : β) (f : Nat → β → β) :
    Id.run (forIn [0:n] init (fun t s => pure (ForInStep.yield (f t s)))) =
      Fin.foldl n (fun s t => f t.val s) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp only [Std.Legacy.Range.size, Id.run]
  show List.foldl (fun b a => f a b) init (List.range' 0 ((n + 1 - 1) / 1) 1) =
       Fin.foldl n (fun s t => f t.val s) init
  have hsize : (n + 1 - 1) / 1 = n := by simp
  rw [hsize]
  rw [show List.range' 0 n 1 = List.range n from List.range_eq_range'.symm]
  rw [Fin.foldl_eq_finRange_foldl, ← List.map_coe_finRange_eq_range, List.foldl_map]

/-- Offset variant of `forIn_id_eq_Fin_foldl`: a `for t in [a:b]` becomes
a `Fin.foldl (b - a)` whose body sees `t.val + a` (the original index).

Used for e.g. the SHA-256 message schedule's second half (`[16:64]`) before
it gets fused with the first half via `fin_foldl_split`. -/
theorem forIn_id_eq_Fin_foldl_offset {β : Type _} (a b : Nat) (init : β) (f : Nat → β → β) :
    Id.run (forIn [a:b] init (fun t s => pure (ForInStep.yield (f t s)))) =
      Fin.foldl (b - a) (fun s t => f (t.val + a) s) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp only [Std.Legacy.Range.size, Id.run]
  have hsize : (b - a + 1 - 1) / 1 = b - a := by simp
  rw [hsize]
  rw [show List.range' a (b - a) 1 = (List.range (b - a)).map (a + ·) from
        List.range'_eq_map_range]
  rw [List.foldl_map, Fin.foldl_eq_finRange_foldl,
      ← List.map_coe_finRange_eq_range, List.foldl_map]
  simp only [Nat.add_comm]
  rfl

/-! ## `forIn'` ↔ `forIn` proof erasure

The spec uses `for h : t in [a:b]` (which desugars to `forIn'`) so that
`get_elem_tactic` can use the membership proof `h : t ∈ [a:b]` to
discharge `Vector` index bounds.  When the body's behaviour does not
depend on which particular membership proof is fed to it (i.e. it can
be expressed as a function of the index alone, with bounds proved
externally), we can erase the `'` and fall back to ordinary `forIn`.

This is the bridge that lets the spec's two-loop `Id.run do` form be
rewritten with the existing `forIn_id_eq_Fin_foldl`. -/

/-- Pure-yield `forIn'` over `[a:b]` in the identity monad equals the
plain `forIn` form, when the body factors through the index alone. -/
theorem forIn'_id_eq_forIn {β : Type _} (a b : Nat) (init : β)
    (f : Nat → β → β) :
    Id.run (forIn' [a:b] init (fun t _ s => pure (ForInStep.yield (f t s)))) =
      Id.run (forIn [a:b] init (fun t s => pure (ForInStep.yield (f t s)))) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Id.run, List.forIn'_pure_yield_eq_foldl, List.forIn_pure_yield_eq_foldl]
  congr 1
  exact List.foldl_attach (l := List.range' a [a:b].size) (f := fun b a => f a b) (b := init)

/-- Variant of `forIn'_id_eq_forIn` for bodies whose effect uses the membership
proof internally (e.g. bounds-checked `Vector.set t _ h` or `xs[t]'h`).  If the
body `F t hm s` happens to agree pointwise with a membership-free `f t s`, the
`forIn'` equals the corresponding plain `forIn`.

Used by `messageSchedule_eq_foldl` to bridge the desugared loops (whose body
uses `block[t]` / `w.set t _ _` with proofs from `t ∈ [a:b]`) to their
`[]!`/`set!` counterparts in one step. -/
theorem forIn'_id_eq_forIn_of_eq {β : Type _} (a b : Nat) (init : β)
    (F : (t : Nat) → t ∈ [a:b] → β → β) (f : Nat → β → β)
    (h : ∀ t hm s, F t hm s = f t s) :
    Id.run (forIn' [a:b] init (fun t hm s => pure (ForInStep.yield (F t hm s)))) =
      Id.run (forIn [a:b] init (fun t s => pure (ForInStep.yield (f t s)))) := by
  rw [← forIn'_id_eq_forIn a b init f]
  simp only [Id.run]; congr 1
  funext t hm s; rw [h]

/-! ## Splitting and transporting folds -/

/-- Split a single `Fin.foldl m` whose body switches on `i < n` into two
sequential folds: an `[0:n]` fold using `f`, then an `[n:m]` fold using `g`.

This is the key step that lets us fuse the spec's two SHA-256 inner
loops (`[0:16]` schedule prefix, `[16:64]` schedule extension) — written
as one fused `[0:64]` fold — back into the implementation's two-stage
shape (or vice versa). -/
theorem fin_foldl_split {β : Type _} (n m : Nat) (hnm : n ≤ m)
    (f g : Nat → β → β) (init : β) :
    Fin.foldl m (fun s i => if i.val < n then f i.val s else g i.val s) init =
      Fin.foldl (m - n) (fun s' i => g (i.val + n) s')
        (Fin.foldl n (fun s i => f i.val s) init) := by
  have hm : m = n + (m - n) := (Nat.add_sub_cancel' hnm).symm
  conv => lhs; rw [hm]
  rw [Fin.foldl_add]
  -- Inner fold: every index has `.val < n` (via `castLE`), so the `if` selects `f`.
  have hinner :
      Fin.foldl n
          (fun x (i : Fin n) =>
            if (i.castLE (Nat.le_add_right n (m - n))).val < n then
              f (i.castLE (Nat.le_add_right n (m - n))).val x
            else
              g (i.castLE (Nat.le_add_right n (m - n))).val x) init =
        Fin.foldl n (fun s i => f i.val s) init := by
    congr 1
    funext x i
    simp [Fin.castLE, i.isLt]
  rw [hinner]
  -- Outer fold: `(natAdd n i).val = n + i.val ≥ n`, so the `if` selects `g`.
  congr 1
  funext x i
  have hge : ¬ i.val + n < n := Nat.not_lt.mpr (Nat.le_add_left n i.val)
  simp only [Fin.natAdd, Nat.add_comm n i.val, if_neg hge]

/-- Transport a `Fin.foldl` along a state-bijection `φ`: if `φ` commutes
with each step (`φ (f a i) = g (φ a) i`), then it commutes with the
whole fold.

This is how we cross the impl/spec divide: the inner loop on the impl
side folds `Impl.State`, the inner loop on the spec side folds
`HashValue`, and `φ = toSpecState` carries one to the other.  The
per-step commutation hypothesis `h` is discharged by the round-body
bridges in `Functions.lean`. -/
theorem fin_foldl_transport {α β : Type _} (n : Nat)
    (f : α → Fin n → α) (g : β → Fin n → β) (φ : α → β) (init : α)
    (h : ∀ (a : α) (i : Fin n), φ (f a i) = g (φ a) i) :
    φ (Fin.foldl n f init) = Fin.foldl n g (φ init) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ k ih =>
    simp only [Fin.foldl_succ_last]
    rw [show (fun a (i : Fin k) => f a i.castSucc) = (fun a i => f a i.castSucc) from rfl,
        show (fun b (i : Fin k) => g b i.castSucc) = (fun b i => g b i.castSucc) from rfl]
    rw [h, ih (fun a i => f a i.castSucc) (fun b i => g b i.castSucc)
              (fun a i => h a i.castSucc)]

end SHS.Equiv.Loop

/-! ## Vector `set!`/`set` and `getElem!`/`getElem` bridges

The spec uses bounds-checked `Vector.set` / `_[i]` (in-bounds via the
`forIn'` membership proof); the equiv layer's `Nat`-indexed step
functions use the panicking `Vector.set!` / `_[i]!`.  Bridge lemmas
in both directions: in-bounds the two agree, out-of-bounds `set!` is
a no-op and `_[i]!` returns the inhabited default. -/

namespace SHS.Equiv.VecBridge

/-! ### In-bounds bridges -/

/-- In-bounds `Vector.set!` reduces to the bounds-checked `Vector.set`. -/
theorem set_bang_eq_set {α : Type _} {n : Nat} (xs : Vector α n) (i : Nat)
    (h : i < n) (x : α) : xs.set! i x = xs.set i x := by
  apply Vector.toArray_inj.mp
  simp [Vector.toArray_set!, Vector.toArray_set, Array.set!_eq_setIfInBounds,
        Array.setIfInBounds, h]

/-- In-bounds `xs[i]!` reduces to the bounds-checked `xs[i]`. -/
theorem getElem_bang_eq_getElem {α : Type _} [Inhabited α] {n : Nat}
    (xs : Vector α n) (i : Nat) (h : i < n) : xs[i]! = xs[i] := by
  simp [getElem!_pos, h]

/-! ### Out-of-bounds bridges -/

/-- Out-of-bounds `Vector.set!` is a no-op. -/
theorem set_bang_oob {α : Type _} {n : Nat} (xs : Vector α n) (i : Nat) (x : α)
    (h : ¬ i < n) : xs.set! i x = xs :=
  Vector.toArray_inj.mp <| by
    simp [Vector.toArray_set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds, h]

/-- Out-of-bounds `xs[i]!` returns the inhabited default. -/
theorem getElem_bang_oob {α : Type _} [Inhabited α] {n : Nat} (xs : Vector α n) (i : Nat)
    (h : ¬ i < n) : xs[i]! = default := by simp [getElem!_neg, h]

end SHS.Equiv.VecBridge
