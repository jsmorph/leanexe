import Lean

/-!
# Simp set for generated folded-frame lemmas

`tools/gen-frame-lemmas.py` tags its output with `@[frame_step]`, and
`wp_run_folded` includes the set, so folded-frame stepping picks up
every generated access and update lemma without naming them and without
entering the global simp set.
-/

register_simp_attr frame_step
