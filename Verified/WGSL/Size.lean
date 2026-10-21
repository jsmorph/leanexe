import Verified.WGSL.Scalar

namespace Verified.WGSL

def Context.size (ctx : Context Γ) (base : Nat) (bound : ctx.Bounded base)
    (x : Var Γ (.array e)) :
    Option (Code ctx base (S := S) (t := .word) (fun _ env => (env.get x).size.toUInt64)) := by
  cases hr : ctx.get x with
  | words index size | bools index size | floats32 index size =>
      cases hs : size with
      | none => exact none
      | some value =>
          exact some (.atom (.word value)
            (by simpa only [hr, hs, Rep.locals, sizeLocals] using bound _ x)
            (by
              intro funs env locals arrays agree
              have h := agree _ x
              simp only [hr, hs, Rep.Holds] at h
              exact h.2 value rfl))

end Verified.WGSL
