/-!
# Loop unrolling helpers

`Fin.foldl n f init` compiles (after `@[specialize]`) to a tail-recursive
loop, but the per-round counter still runs through `lean_nat_*` ops on
the `Fin n` index — modulo, subtraction, less-than-check — every
iteration.  Crypto inner loops in this project (SHA-256's 64-round
compression, SHA-512's 80-round compression, …) read the schedule from
`block[(i - k) % 16]`, so per-iteration counter arithmetic is on the
hot path.

A manual unroll with literal `Fin` indices lets the codegen
constant-fold `(i - k) % 16` to a literal slot, eliminating the
counter arithmetic entirely.  The resulting C is straight-line code
with explicit literal indices.

Each unroll function pairs an explicit unrolled body (for codegen)
with an equivalence theorem `… = Fin.foldl n …` (for proofs); the
equivalence is proven once via the generic `unrollN` recursion and
applies uniformly to any step function.
-/

namespace SHS.Impl.Unroll

/-! ## Generic recursive unroll

`unrollN n g init` is structurally equal to `Fin.foldl n g init`,
but written so that for a *concrete* literal `n` and a step function
`g` the term reduces by definitional `rfl` to a chain of `n` explicit
applications of `g` at literal `Fin n` indices (modulo `castSucc`s).

This is the bridge between the hand-unrolled `unroll64` / `unroll80`
forms below (which are 64- / 80-deep `let` chains for codegen) and
`Fin.foldl n` (which is what the equivalence proofs are stated
against). -/

@[inline] def unrollN {α : Type _} : (n : Nat) → (α → Fin n → α) → α → α
  | 0,     _, x => x
  | n + 1, g, x =>
    g (unrollN n (fun a (j : Fin n) => g a j.castSucc) x) (Fin.last n)

theorem unrollN_eq_foldl {α : Type _} :
    ∀ (n : Nat) (g : α → Fin n → α) (init : α),
      unrollN n g init = Fin.foldl n g init
  | 0,     _, _ => by simp [unrollN, Fin.foldl_zero]
  | n + 1, g, init => by
    show g _ _ = _
    rw [Fin.foldl_succ_last, unrollN_eq_foldl n]

/-! ## 64-step unrolling (SHA-256 compression) -/

/-- 64 explicit applications of `f` at literal `Fin 64` indices,
right-associated through `|>`.  Equivalent to `Fin.foldl 64 f init`
by `unroll64_eq_foldl`; compiles to straight-line code with literal
indices, letting the C codegen constant-fold any per-iteration
counter arithmetic the body might do. -/
@[inline] def unroll64 {α : Type _} (f : α → Fin 64 → α) (init : α) : α :=
  init
  |> (f · ⟨ 0, by decide⟩) |> (f · ⟨ 1, by decide⟩)
  |> (f · ⟨ 2, by decide⟩) |> (f · ⟨ 3, by decide⟩)
  |> (f · ⟨ 4, by decide⟩) |> (f · ⟨ 5, by decide⟩)
  |> (f · ⟨ 6, by decide⟩) |> (f · ⟨ 7, by decide⟩)
  |> (f · ⟨ 8, by decide⟩) |> (f · ⟨ 9, by decide⟩)
  |> (f · ⟨10, by decide⟩) |> (f · ⟨11, by decide⟩)
  |> (f · ⟨12, by decide⟩) |> (f · ⟨13, by decide⟩)
  |> (f · ⟨14, by decide⟩) |> (f · ⟨15, by decide⟩)
  |> (f · ⟨16, by decide⟩) |> (f · ⟨17, by decide⟩)
  |> (f · ⟨18, by decide⟩) |> (f · ⟨19, by decide⟩)
  |> (f · ⟨20, by decide⟩) |> (f · ⟨21, by decide⟩)
  |> (f · ⟨22, by decide⟩) |> (f · ⟨23, by decide⟩)
  |> (f · ⟨24, by decide⟩) |> (f · ⟨25, by decide⟩)
  |> (f · ⟨26, by decide⟩) |> (f · ⟨27, by decide⟩)
  |> (f · ⟨28, by decide⟩) |> (f · ⟨29, by decide⟩)
  |> (f · ⟨30, by decide⟩) |> (f · ⟨31, by decide⟩)
  |> (f · ⟨32, by decide⟩) |> (f · ⟨33, by decide⟩)
  |> (f · ⟨34, by decide⟩) |> (f · ⟨35, by decide⟩)
  |> (f · ⟨36, by decide⟩) |> (f · ⟨37, by decide⟩)
  |> (f · ⟨38, by decide⟩) |> (f · ⟨39, by decide⟩)
  |> (f · ⟨40, by decide⟩) |> (f · ⟨41, by decide⟩)
  |> (f · ⟨42, by decide⟩) |> (f · ⟨43, by decide⟩)
  |> (f · ⟨44, by decide⟩) |> (f · ⟨45, by decide⟩)
  |> (f · ⟨46, by decide⟩) |> (f · ⟨47, by decide⟩)
  |> (f · ⟨48, by decide⟩) |> (f · ⟨49, by decide⟩)
  |> (f · ⟨50, by decide⟩) |> (f · ⟨51, by decide⟩)
  |> (f · ⟨52, by decide⟩) |> (f · ⟨53, by decide⟩)
  |> (f · ⟨54, by decide⟩) |> (f · ⟨55, by decide⟩)
  |> (f · ⟨56, by decide⟩) |> (f · ⟨57, by decide⟩)
  |> (f · ⟨58, by decide⟩) |> (f · ⟨59, by decide⟩)
  |> (f · ⟨60, by decide⟩) |> (f · ⟨61, by decide⟩)
  |> (f · ⟨62, by decide⟩) |> (f · ⟨63, by decide⟩)

/-- The 64-step unroll equals `Fin.foldl 64`.  Reduces to `unrollN 64`
followed by the generic `unrollN_eq_foldl` bridge; the `unroll64`-side
unfolding is `rfl` because both reduce to the same nested term. -/
theorem unroll64_eq_foldl {α : Type _} (f : α → Fin 64 → α) (init : α) :
    unroll64 f init = Fin.foldl 64 f init := by
  rw [← unrollN_eq_foldl 64 f init]
  rfl

/-! ## 80-step unrolling (SHA-512 compression) -/

/-- 80 explicit applications of `f` at literal `Fin 80` indices.  Same
shape as `unroll64`; SHA-512's compression loop runs 80 rounds rather
than 64. -/
@[inline] def unroll80 {α : Type _} (f : α → Fin 80 → α) (init : α) : α :=
  init
  |> (f · ⟨ 0, by decide⟩) |> (f · ⟨ 1, by decide⟩)
  |> (f · ⟨ 2, by decide⟩) |> (f · ⟨ 3, by decide⟩)
  |> (f · ⟨ 4, by decide⟩) |> (f · ⟨ 5, by decide⟩)
  |> (f · ⟨ 6, by decide⟩) |> (f · ⟨ 7, by decide⟩)
  |> (f · ⟨ 8, by decide⟩) |> (f · ⟨ 9, by decide⟩)
  |> (f · ⟨10, by decide⟩) |> (f · ⟨11, by decide⟩)
  |> (f · ⟨12, by decide⟩) |> (f · ⟨13, by decide⟩)
  |> (f · ⟨14, by decide⟩) |> (f · ⟨15, by decide⟩)
  |> (f · ⟨16, by decide⟩) |> (f · ⟨17, by decide⟩)
  |> (f · ⟨18, by decide⟩) |> (f · ⟨19, by decide⟩)
  |> (f · ⟨20, by decide⟩) |> (f · ⟨21, by decide⟩)
  |> (f · ⟨22, by decide⟩) |> (f · ⟨23, by decide⟩)
  |> (f · ⟨24, by decide⟩) |> (f · ⟨25, by decide⟩)
  |> (f · ⟨26, by decide⟩) |> (f · ⟨27, by decide⟩)
  |> (f · ⟨28, by decide⟩) |> (f · ⟨29, by decide⟩)
  |> (f · ⟨30, by decide⟩) |> (f · ⟨31, by decide⟩)
  |> (f · ⟨32, by decide⟩) |> (f · ⟨33, by decide⟩)
  |> (f · ⟨34, by decide⟩) |> (f · ⟨35, by decide⟩)
  |> (f · ⟨36, by decide⟩) |> (f · ⟨37, by decide⟩)
  |> (f · ⟨38, by decide⟩) |> (f · ⟨39, by decide⟩)
  |> (f · ⟨40, by decide⟩) |> (f · ⟨41, by decide⟩)
  |> (f · ⟨42, by decide⟩) |> (f · ⟨43, by decide⟩)
  |> (f · ⟨44, by decide⟩) |> (f · ⟨45, by decide⟩)
  |> (f · ⟨46, by decide⟩) |> (f · ⟨47, by decide⟩)
  |> (f · ⟨48, by decide⟩) |> (f · ⟨49, by decide⟩)
  |> (f · ⟨50, by decide⟩) |> (f · ⟨51, by decide⟩)
  |> (f · ⟨52, by decide⟩) |> (f · ⟨53, by decide⟩)
  |> (f · ⟨54, by decide⟩) |> (f · ⟨55, by decide⟩)
  |> (f · ⟨56, by decide⟩) |> (f · ⟨57, by decide⟩)
  |> (f · ⟨58, by decide⟩) |> (f · ⟨59, by decide⟩)
  |> (f · ⟨60, by decide⟩) |> (f · ⟨61, by decide⟩)
  |> (f · ⟨62, by decide⟩) |> (f · ⟨63, by decide⟩)
  |> (f · ⟨64, by decide⟩) |> (f · ⟨65, by decide⟩)
  |> (f · ⟨66, by decide⟩) |> (f · ⟨67, by decide⟩)
  |> (f · ⟨68, by decide⟩) |> (f · ⟨69, by decide⟩)
  |> (f · ⟨70, by decide⟩) |> (f · ⟨71, by decide⟩)
  |> (f · ⟨72, by decide⟩) |> (f · ⟨73, by decide⟩)
  |> (f · ⟨74, by decide⟩) |> (f · ⟨75, by decide⟩)
  |> (f · ⟨76, by decide⟩) |> (f · ⟨77, by decide⟩)
  |> (f · ⟨78, by decide⟩) |> (f · ⟨79, by decide⟩)

/-- The 80-step unroll equals `Fin.foldl 80`.  Same proof as
`unroll64_eq_foldl`: route through the generic `unrollN_eq_foldl`. -/
theorem unroll80_eq_foldl {α : Type _} (f : α → Fin 80 → α) (init : α) :
    unroll80 f init = Fin.foldl 80 f init := by
  rw [← unrollN_eq_foldl 80 f init]
  rfl

end SHS.Impl.Unroll
