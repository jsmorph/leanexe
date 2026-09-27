import Project.ProofKit.Control
import Project.TalosCompat

namespace Project.ProofKit.CheckedDivMod
open Wasm

def program (remainder : Bool) (leftLocal rightLocal : Nat) : Wasm.Program :=
  [.localGet rightLocal, .constI64 0, .eqI64,
    .iff 0 1 (if remainder then [.localGet leftLocal] else [.constI64 0])
      [.localGet leftLocal, .localGet rightLocal,
        if remainder then .remUI64 else .divUI64] [] [.i64]]

def result (remainder : Bool) (left right : UInt64) : UInt64 :=
  if remainder then left % right else left / right

theorem program_spec (remainder : Bool) (leftLocal rightLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (tail : List Value)
    (hValues : frame.values = tail)
    (hLeft : frame.get leftLocal = some (.i64 left))
    (hRight : frame.get rightLocal = some (.i64 right))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i64 (result remainder left right) :: tail } env) :
    wp module_ (program remainder leftLocal rightLocal ++ rest) Q store frame env := by
  have hLeftRead := hLeft
  have hRightRead := hRight
  simp only [Locals.get] at hLeftRead hRightRead
  unfold program
  simp only [List.cons_append, List.nil_append, wp_simp, hRight, hValues]
  refine wp_iff_cons rfl ?_
  by_cases hZero : right = 0
  · subst right
    cases remainder <;>
      simpa [wp_simp, result, hValues, hLeftRead] using hNext
  · cases remainder <;>
      simpa [wp_simp, result, hZero, hValues, hLeftRead, hRightRead] using hNext

#print axioms program_spec

end Project.ProofKit.CheckedDivMod
