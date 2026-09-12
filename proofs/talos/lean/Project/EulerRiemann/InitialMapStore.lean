import Project.EulerRiemann.InitialMapLoad

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

theorem initial_map_store_shape : (initialMapLoop.drop 126).take 84 =
    ArrayField.storeProgram 50 51 27 7 0 ++
    ArrayField.storeProgram 50 51 28 7 1 ++
    ArrayField.storeProgram 50 51 29 7 2 ++
    ArrayField.storeProgram 50 51 30 7 3 ++
    ArrayField.storeProgram 50 51 31 7 4 ++
    ArrayField.storeProgram 50 51 32 7 5 ++
    ArrayField.storeProgram 50 51 33 7 6 := by
  rfl

theorem initial_map_store_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (target : UInt64) (size index : Nat) (cell : Traversal.Cell)
    (hValues : frame.values = [])
    (hTarget : frame.get 50 = some (.i64 target))
    (hIndex : frame.get 51 = some (.i64 (UInt64.ofNat index)))
    (hData : ∀ field : Nat, field < 7 →
      frame.get (27 + field) = some (.i64 ((Memory.cellWords cell).getD field 0)))
    (hFit32 : target.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hFitMemory : target.toNat + 8 * (7 * size + 1) ≤ store.mem.pages * 65536)
    (hi : index < size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (Memory.writeCell store target index cell) frame env) :
    wp module ((initialMapLoop.drop 126).take 84 ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  have hBound : ∀ field : Nat, field < 7 →
      (UInt64Array.wordAddress target (7 * index + field + 1)).toNat + 8 ≤
        store.mem.pages * 65536 := by
    intro field hf
    rw [UInt64Array.wordAddress_toNat hFit32 (by omega)]
    omega
  let written0 := Memory.writeField store target index 0
    ((Memory.cellWords cell).getD 0 0)
  let written1 := Memory.writeField written0 target index 1
    ((Memory.cellWords cell).getD 1 0)
  let written2 := Memory.writeField written1 target index 2
    ((Memory.cellWords cell).getD 2 0)
  let written3 := Memory.writeField written2 target index 3
    ((Memory.cellWords cell).getD 3 0)
  let written4 := Memory.writeField written3 target index 4
    ((Memory.cellWords cell).getD 4 0)
  let written5 := Memory.writeField written4 target index 5
    ((Memory.cellWords cell).getD 5 0)
  let written6 := Memory.writeField written5 target index 6
    ((Memory.cellWords cell).getD 6 0)
  rw [initial_map_store_shape]
  simp only [List.append_assoc]
  refine ArrayField.store_spec 50 51 27 7 0 module env store frame target _ index []
    hValues hTarget hIndex (hData 0 (by decide)) ?_ Q _ ?_
  · simpa only [Memory.writeField_pages] using hBound 0 (by decide)
  rw [hEmpty]
  change wp module _ Q written0 frame env
  refine ArrayField.store_spec 50 51 28 7 1 module env written0 frame target _ index []
    hValues hTarget hIndex (hData 1 (by decide)) ?_ Q _ ?_
  · simpa only [written0, Memory.writeField_pages] using hBound 1 (by decide)
  rw [hEmpty]
  change wp module _ Q written1 frame env
  refine ArrayField.store_spec 50 51 29 7 2 module env written1 frame target _ index []
    hValues hTarget hIndex (hData 2 (by decide)) ?_ Q _ ?_
  · simpa only [written0, written1, Memory.writeField_pages] using hBound 2 (by decide)
  rw [hEmpty]
  change wp module _ Q written2 frame env
  refine ArrayField.store_spec 50 51 30 7 3 module env written2 frame target _ index []
    hValues hTarget hIndex (hData 3 (by decide)) ?_ Q _ ?_
  · simpa only [written0, written1, written2, Memory.writeField_pages] using hBound 3 (by decide)
  rw [hEmpty]
  change wp module _ Q written3 frame env
  refine ArrayField.store_spec 50 51 31 7 4 module env written3 frame target _ index []
    hValues hTarget hIndex (hData 4 (by decide)) ?_ Q _ ?_
  · simpa only [written0, written1, written2, written3, Memory.writeField_pages] using hBound 4 (by decide)
  rw [hEmpty]
  change wp module _ Q written4 frame env
  refine ArrayField.store_spec 50 51 32 7 5 module env written4 frame target _ index []
    hValues hTarget hIndex (hData 5 (by decide)) ?_ Q _ ?_
  · simpa only [written0, written1, written2, written3, written4, Memory.writeField_pages] using hBound 5 (by decide)
  rw [hEmpty]
  change wp module _ Q written5 frame env
  refine ArrayField.store_spec 50 51 33 7 6 module env written5 frame target _ index []
    hValues hTarget hIndex (hData 6 (by decide)) ?_ Q _ ?_
  · simpa only [written0, written1, written2, written3, written4, written5, Memory.writeField_pages] using hBound 6 (by decide)
  rw [hEmpty]
  change wp module _ Q written6 frame env
  simpa [written0, written1, written2, written3, written4, written5, written6,
    Memory.writeCell, Memory.cellWords, Array.getD] using hNext

#print axioms initial_map_store_shape
#print axioms initial_map_store_spec

end Project.EulerRiemann.Execution
