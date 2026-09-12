import Project.EulerRiemann.Program
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.Annotation
import Project.ProofKit.Frame

namespace Project.EulerRiemann.Execution
open Wasm

theorem initial_mul_region : Project.ProofKit.Annotation.region func87 [] 5 9 =
    some (Project.ProofKit.CheckedNatMul.program 43 44) := rfl

def initialQuadrupleFrame (frame : Locals) (n : Nat) (tail : List Value) : Locals :=
  { frame with
    locals := ((frame.locals.set 41 (.i64 4)).set 42 (.i64 (UInt64.ofNat n))).set 39
      (.i64 (UInt64.ofNat (4 * n)))
    values := .i64 5 :: tail }

theorem initial_quadruple_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (tail : List Value) (hn : n ≤ 800)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 45)
    (hValues : frame.values = tail) (hN : frame.get 0 = some (.i64 (UInt64.ofNat n)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (initialQuadrupleFrame frame n tail) env) :
    wp Project.EulerRiemann.«module» (func87.take 10 ++ rest) Q store frame env := by
  have hShape : func87.take 10 =
      [.constI64 5, .constI64 4, .localSet 43, .localGet 0, .localSet 44] ++
        Project.ProofKit.CheckedNatMul.program 43 44 ++ [.localSet 41] := rfl
  let staged : Locals := { frame with
    locals := (frame.locals.set 41 (.i64 4)).set 42 (.i64 (UInt64.ofNat n))
    values := .i64 5 :: tail }
  have hn64 : n < UInt64.size := by change n < 18446744073709551616; omega
  have hFit : (4 : UInt64).toNat * (UInt64.ofNat n).toNat < UInt64.size := by
    rw [UInt64.toNat_ofNat_of_lt' hn64]
    change 4 * n < 18446744073709551616
    omega
  have hMul : wp Project.EulerRiemann.«module»
      (Project.ProofKit.CheckedNatMul.program 43 44 ++ [.localSet 41] ++ rest) Q store staged env := by
    rw [List.append_assoc]
    apply Project.ProofKit.CheckedNatMul.program_spec 43 44 _ env store staged 4
      (UInt64.ofNat n) (.i64 5 :: tail) rfl
    · simp [staged, Locals.get, hParams, hLocals]
    · simp [staged, Locals.get, hParams, hLocals]
    · exact hFit
    · simpa [wp_simp, staged, initialQuadrupleFrame, hParams, hLocals,
        UInt64.ofNat_mul] using hNext
  rw [hShape, List.append_assoc]
  have hNRead := Project.ProofKit.Frame.parameter_getElem_of_get frame 0
    (.i64 (UInt64.ofNat n)) (by omega) hN
  simpa [wp_simp, staged, List.cons_append, List.nil_append,
    hParams, hLocals, hValues, hNRead] using hMul

#print axioms initial_mul_region
#print axioms initial_quadruple_spec

end Project.EulerRiemann.Execution
