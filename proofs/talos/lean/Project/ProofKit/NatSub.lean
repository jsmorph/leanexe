import Project.ProofKit.Control
import Project.ProofKit.Frame

namespace Project.ProofKit.NatSub
open Wasm

def program (leftLocal rightLocal : Nat) : Wasm.Program :=
  [.localGet leftLocal, .localGet rightLocal, .ltUI64,
    .iff 0 1 [.constI64 0]
      [.localGet leftLocal, .localGet rightLocal, .subI64] [] [.i64]]

theorem program_spec (leftLocal rightLocal : Nat) (module_ : Wasm.Module)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (left right : UInt64) (tail : List Value)
    (hValues : frame.values = tail)
    (hLeft : frame.get leftLocal = some (.i64 left))
    (hRight : frame.get rightLocal = some (.i64 right))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      { frame with values := .i64 (UInt64.ofNat (left.toNat - right.toNat)) :: tail } env) :
    wp module_ (program leftLocal rightLocal ++ rest) Q store frame env := by
  have hLeftRead := hLeft
  have hRightRead := hRight
  simp only [Locals.get] at hLeftRead hRightRead
  unfold program
  simp only [List.cons_append, List.nil_append, wp_simp,
    Frame.withValues_get, hLeft, hRight, hValues]
  refine wp_iff_cons rfl ?_
  by_cases hLt : left < right
  · have hSub : left.toNat - right.toNat = 0 := by
      have := UInt64.lt_iff_toNat_lt.mp hLt
      omega
    simpa [wp_simp, hLt, hSub, hValues] using hNext
  · have hLe : right.toNat ≤ left.toNat := by
      have := UInt64.lt_iff_toNat_lt.not.mp hLt
      omega
    have hSub : UInt64.ofNat (left.toNat - right.toNat) = left - right := by
      rw [UInt64.ofNat_sub hLe]
      simp
    simpa [wp_simp, hLt, hSub, hValues, hLeftRead, hRightRead] using hNext

#print axioms program_spec

end Project.ProofKit.NatSub
