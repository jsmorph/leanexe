module

@[expose] public section

/-!
# Instance priorities for every leanexe module

Every module of leanexe imports this module, directly or through another leanexe module.

Lean v4.36.0 declares `UInt8.instDecidableForall` to `UInt64.instDecidableForall` in
`Init/Data/UInt/Decidable.lean`.  Each decides `∀ x, P x` over its word type through `BitVec`,
which enumerates every word.  Instance search tries them before `List.decidableBAll` for a bounded
quantifier `∀ w ∈ ws, P w` over words, so `decide` on such a statement enumerates all `2 ^ 64`
words of `UInt64` and does not finish.  The higher priority makes instance search choose
`List.decidableBAll`, which decides the statement over the list.  Lean's fix, lean4#16691, merged
after v4.37.0-rc1.
-/

attribute [instance high] List.decidableBAll
