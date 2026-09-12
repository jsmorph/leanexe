import Project.EulerRiemann.InitialMapLoad
import Project.EulerRiemann.ExecutionInitialCell

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def initialMapCallProgram : Wasm.Program :=
  [.localGet 1, .localSet 18, .localGet 11, .localSet 54,
    .localGet 10, .localSet 55, .localGet 54, .localGet 55, .addI64,
    .localTee 56, .localGet 54, .ltUI64,
    .iff 0 1 [.unreachable] [.localGet 56] [] [.i64],
    .localSet 19, .localGet 18, .localGet 19, .call 87,
    .localSet 26, .localSet 25, .localSet 24, .localSet 23,
    .localSet 22, .localSet 21, .localSet 20,
    .localGet 20, .localSet 27, .localGet 21, .localSet 28,
    .localGet 22, .localSet 29, .localGet 23, .localSet 30,
    .localGet 24, .localSet 31, .localGet 25, .localSet 32,
    .localGet 26, .localSet 33]

theorem initial_map_call_shape : (initialMapLoop.drop 88).take 38 = initialMapCallProgram := by
  rfl

def initialCallSetupFrame (frame : Locals) (n index offset : Nat) : Locals :=
  let slots0 := frame.locals.set 13 (.i64 (UInt64.ofNat n))
  let slots1 := slots0.set 49 (.i64 (UInt64.ofNat index))
  let slots2 := slots1.set 50 (.i64 (UInt64.ofNat offset))
  let slots3 := slots2.set 51 (.i64 (UInt64.ofNat (index + offset)))
  let slots4 := slots3.set 14 (.i64 (UInt64.ofNat (index + offset)))
  { frame with locals := slots4, values := [] }

def initialCallResultFrame (frame : Locals) (cell : Traversal.Cell) : Locals :=
  let slots5 := frame.locals.set 21 (.i64 ((Memory.cellWords cell).getD 6 0))
  let slots6 := slots5.set 20 (.i64 ((Memory.cellWords cell).getD 5 0))
  let slots7 := slots6.set 19 (.i64 ((Memory.cellWords cell).getD 4 0))
  let slots8 := slots7.set 18 (.i64 ((Memory.cellWords cell).getD 3 0))
  let slots9 := slots8.set 17 (.i64 ((Memory.cellWords cell).getD 2 0))
  let slots10 := slots9.set 16 (.i64 ((Memory.cellWords cell).getD 1 0))
  let slots11 := slots10.set 15 (.i64 ((Memory.cellWords cell).getD 0 0))
  let slots12 := slots11.set 22 (.i64 ((Memory.cellWords cell).getD 0 0))
  let slots13 := slots12.set 23 (.i64 ((Memory.cellWords cell).getD 1 0))
  let slots14 := slots13.set 24 (.i64 ((Memory.cellWords cell).getD 2 0))
  let slots15 := slots14.set 25 (.i64 ((Memory.cellWords cell).getD 3 0))
  let slots16 := slots15.set 26 (.i64 ((Memory.cellWords cell).getD 4 0))
  let slots17 := slots16.set 27 (.i64 ((Memory.cellWords cell).getD 5 0))
  let slots18 := slots17.set 28 (.i64 ((Memory.cellWords cell).getD 6 0))
  { frame with locals := slots18, values := [] }

def initialCalledFrame (frame : Locals) (n index offset : Nat) : Locals :=
  initialCallResultFrame (initialCallSetupFrame frame n index offset)
    (Traversal.initialCell n (index + offset))

theorem initial_map_call_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n index offset : Nat) (hn : n ≤ 800) (hSum : index + offset < 1048576)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hN : frame.get 1 = some (.i64 (UInt64.ofNat n)))
    (hOffset : frame.get 10 = some (.i64 (UInt64.ofNat offset)))
    (hIndex : frame.get 11 = some (.i64 (UInt64.ofNat index)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (initialCalledFrame frame n index offset) env) :
    wp module ((initialMapLoop.drop 88).take 38 ++ rest) Q store frame env := by
  have hNRead : frame.params[1]? = some (.i64 (UInt64.ofNat n)) := by
    simpa [Locals.get, hParams] using hN
  have hOffsetRead := Frame.internal_getElem?_of_get frame 5 5 (.i64 (UInt64.ofNat offset))
    hParams (by omega) hOffset
  have hIndexRead := Frame.internal_getElem?_of_get frame 5 6 (.i64 (UInt64.ofNat index))
    hParams (by omega) hIndex
  have hSum64 : index + offset < UInt64.size := by change index + offset < 18446744073709551616; omega
  have hIndex64 : index < UInt64.size := by omega
  have hAdd : UInt64.ofNat index + UInt64.ofNat offset = UInt64.ofNat (index + offset) :=
    (UInt64.ofNat_add index offset).symm
  have hGuard : ¬UInt64.ofNat (index + offset) < UInt64.ofNat index := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSum64, UInt64.toNat_ofNat_of_lt' hIndex64]
    omega
  rw [initial_map_call_shape]
  unfold initialMapCallProgram
  simp only [List.cons_append, List.nil_append]
  wp_run [List.set, List.length_set, List.getElem?_set, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
  refine wp_iff_cons rfl ?_
  conv => arg 2; simp
  wp_run [List.set, List.length_set, List.getElem?_set, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
  refine wp_call_tw (initialCell_exact env store n (index + offset) hn hSum) ?_
  rintro current values ⟨hStore, hResult⟩
  subst current
  subst values
  wp_run [cellValues, List.set, List.length_set, List.getElem?_set, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
  simpa [initialCalledFrame, initialCallSetupFrame, initialCallResultFrame,
    cellValues, Memory.cellWords, Array.getD] using hNext

#print axioms initial_map_call_shape
#print axioms initial_map_call_spec

end Project.EulerRiemann.Execution
