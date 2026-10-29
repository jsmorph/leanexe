import Mathlib.Tactic

/-- The rules with which `simp` runs straight-line code under `wpA`, together with Talos's
`wp_simp`: the rule for each atomic access-free instruction, the continuation `thenA` that these
rules use, and the rules for `load64`, `store64`, and the empty program. -/
register_simp_attr wpA_simp
