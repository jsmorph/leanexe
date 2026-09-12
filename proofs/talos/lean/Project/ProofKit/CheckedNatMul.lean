import Project.ProofKit.CheckedNatMulArithmetic
import Project.TalosCompat

namespace Project.ProofKit.CheckedNatMul
open Wasm

def program (leftLocal rightLocal : Nat) : Wasm.Program :=
  [.localGet rightLocal, .constI64 0, .eqI64,
    .iff 0 1 [.constI64 0]
      [.constI64 (-1), .localGet rightLocal, .divUI64, .localGet leftLocal, .ltUI64,
        .iff 0 1 [.unreachable]
          [.localGet leftLocal, .localGet rightLocal, .mulI64] [] [.i64]] [] [.i64]]

theorem zero_spec (leftLocal rightLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (tail : List Value)
    (hValues : frame.values = tail)
    (hRight : frame.get rightLocal = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store { frame with values := .i64 0 :: tail } env) :
    wp module_ (program leftLocal rightLocal ++ rest) Q store frame env := by
  unfold program
  simp only [List.cons_append, List.nil_append, wp_simp, hRight, hValues]
  refine wp_iff_cons rfl ?_
  simpa [wp_simp, hValues] using hNext

theorem program_spec (leftLocal rightLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (tail : List Value)
    (hValues : frame.values = tail)
    (hLeft : frame.get leftLocal = some (.i64 left))
    (hRight : frame.get rightLocal = some (.i64 right))
    (hFit : left.toNat * right.toNat < UInt64.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i64 (left * right) :: tail } env) :
    wp module_ (program leftLocal rightLocal ++ rest) Q store frame env := by
  by_cases hZero : right = 0
  · subst right
    exact zero_spec leftLocal rightLocal module_ env store frame tail hValues hRight
      Q rest (by simpa using hNext)
  have hGuard := guard_of_fits left right hFit hZero
  have hLeftRead := hLeft
  have hRightRead := hRight
  simp only [Locals.get] at hLeftRead hRightRead
  unfold program
  simp only [List.cons_append, List.nil_append, wp_simp, hRight, hValues]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hZero, hRightRead, hLeftRead]
  refine wp_iff_cons rfl ?_
  simpa [wp_simp, hGuard, hValues, hLeftRead, hRightRead] using hNext

#print axioms zero_spec
#print axioms program_spec

end Project.ProofKit.CheckedNatMul
