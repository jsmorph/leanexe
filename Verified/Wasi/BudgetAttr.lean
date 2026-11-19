import Lean

/-! The simp attribute `charge_eqs`.  A budget proof of a WASI command gives it, as a local
attribute, the equations of the charges of the command's pure functions, which the tactics of
`Verified/Wasi/BudgetTactics.lean` then rewrite. -/

register_simp_attr charge_eqs
