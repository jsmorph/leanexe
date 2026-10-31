import Demos.Energy.Site

/-! The worked example of the plan, evaluated by the kernel under the test site's profile table.
Every input has snapshot time 0 and the mode word 0.  Except where a theorem's docstring states
otherwise, it has stored energy in `[14,400,000, 15,120,000]` J, the limits `[0, 0]` W in force,
load in `[3,000, 4,000]` W, and PV in `[0, 3,000]` W, and a proposal of one power is the held
setpoint `[s, s]`.  A signed power `p` is the word `p + 2 ^ 32`. -/

namespace Demos.Energy.Examples

/-- A discharge of 1,000 W passes the export and floor tests and expires at `t_m + 870`. -/
theorem example_accept :
    authorize #[1, 0, 14400000, 15120000, 0, 4294967296, 4294967296, 3000, 4000, 0, 3000,
      4294966296, 4294966296] = ⟨.accepted, 4294966296, 4294966296, 870⟩ := by
  decide +kernel

/-- A discharge of 3,000 W fails the export test. -/
theorem example_export :
    (authorize #[1, 0, 14400000, 15120000, 0, 4294967296, 4294967296, 3000, 4000, 0, 3000,
      4294964296, 4294964296]).status = .exportCap := by
  decide +kernel

/-- A discharge of 1,000 W from stored energy of at least 11,520,000 J fails the floor test. -/
theorem example_floor :
    (authorize #[1, 0, 11520000, 15120000, 0, 4294967296, 4294967296, 3000, 4000, 0, 3000,
      4294966296, 4294966296]).status = .floor := by
  decide +kernel

/-- A charge of 3,000 W with load in `[500, 1,000]` W and PV in `[3,000, 5,000]` W passes the
import and ceiling tests, with export relative to idle fallback. -/
theorem example_relative :
    (authorize #[1, 0, 14400000, 15120000, 0, 4294967296, 4294967296, 500, 1000, 3000, 5000,
      4294970296, 4294970296]).status = .accepted := by
  decide +kernel

/-- A renewal of a 1,000 W discharge in force, from stored energy of at least 11,288,000 J, fails
the floor test. -/
theorem example_renewal :
    (authorize #[1, 0, 11288000, 12008000, 0, 4294966296, 4294966296, 3000, 4000, 0, 3000,
      4294966296, 4294966296]).status = .floor := by
  decide +kernel

/-- The limits `[-1,000, 500]` W pass the export and floor tests on the lower side and the import
and ceiling tests on the upper side. -/
theorem example_limits :
    authorize #[1, 0, 14400000, 15120000, 0, 4294967296, 4294967296, 3000, 4000, 0, 3000,
      4294966296, 4294967796] = ⟨.accepted, 4294966296, 4294967796, 870⟩ := by
  decide +kernel

/-- The limits `[-1,000, 1,000]` W fail the import test: with the load at 4,000 W and no PV, a
charge of 1,050 W imports 5,050 W against a cap of 5,000 W. -/
theorem example_limits_import :
    (authorize #[1, 0, 14400000, 15120000, 0, 4294967296, 4294967296, 3000, 4000, 0, 3000,
      4294966296, 4294968296]).status = .importCap := by
  decide +kernel

end Demos.Energy.Examples
