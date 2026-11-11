import Library.Numerics.Arithmetic.Gcd.Master

/-! The registry of the library's master theorems: one `Verified.Master` statement for each
function of the library sections of the algorithm index.  `master_registry` checks that each name
is such a statement, and `tools/source-layout` checks that every `*_master` theorem of the library
is listed here and that the index names it. -/

master_registry [
  Library.Numerics.Arithmetic.Gcd.gcd_master]
