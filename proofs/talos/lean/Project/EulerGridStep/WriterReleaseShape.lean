import Project.EulerGridStep.WriterReleaseOne

namespace Project.EulerGridStep.Execution
open Wasm

def writerReleaseSetup : Wasm.Program :=
  [.localSet 61, .localSet 60, .localGet 60, .localSet 65, .localGet 61, .localSet 66]

theorem writer_release_setup_prefix : writerReleaseTail.take 6 = writerReleaseSetup := rfl

theorem writer_release_setup_shape : writerReleaseTail =
    writerReleaseSetup ++ writerReleaseTail.drop 6 := by
  calc
    _ = writerReleaseTail.take 6 ++ writerReleaseTail.drop 6 := (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_setup_prefix]

theorem writer_release_stage0_prefix : (writerReleaseTail.drop 6).take 18 =
    writerReleaseOne 51 (writerProtected 5) := rfl

theorem writer_release_stage0_shape : writerReleaseTail.drop 6 =
    writerReleaseOne 51 (writerProtected 5) ++ writerReleaseTail.drop 24 := by
  calc
    _ = (writerReleaseTail.drop 6).take 18 ++ (writerReleaseTail.drop 6).drop 18 :=
      (List.take_append_drop 18 _).symm
    _ = _ := by rw [writer_release_stage0_prefix, List.drop_drop]

theorem writer_release_stage1_prefix : (writerReleaseTail.drop 24).take 15 =
    writerReleaseOne 42 (writerProtected 4) := rfl

theorem writer_release_stage1_shape : writerReleaseTail.drop 24 =
    writerReleaseOne 42 (writerProtected 4) ++ writerReleaseTail.drop 39 := by
  calc
    _ = (writerReleaseTail.drop 24).take 15 ++ (writerReleaseTail.drop 24).drop 15 :=
      (List.take_append_drop 15 _).symm
    _ = _ := by rw [writer_release_stage1_prefix, List.drop_drop]

theorem writer_release_stage2_prefix : (writerReleaseTail.drop 39).take 12 =
    writerReleaseOne 33 (writerProtected 3) := rfl

theorem writer_release_stage2_shape : writerReleaseTail.drop 39 =
    writerReleaseOne 33 (writerProtected 3) ++ writerReleaseTail.drop 51 := by
  calc
    _ = (writerReleaseTail.drop 39).take 12 ++ (writerReleaseTail.drop 39).drop 12 :=
      (List.take_append_drop 12 _).symm
    _ = _ := by rw [writer_release_stage2_prefix, List.drop_drop]

theorem writer_release_stage3_prefix : (writerReleaseTail.drop 51).take 9 =
    writerReleaseOne 24 (writerProtected 2) := rfl

theorem writer_release_stage3_shape : writerReleaseTail.drop 51 =
    writerReleaseOne 24 (writerProtected 2) ++ writerReleaseTail.drop 60 := by
  calc
    _ = (writerReleaseTail.drop 51).take 9 ++ (writerReleaseTail.drop 51).drop 9 :=
      (List.take_append_drop 9 _).symm
    _ = _ := by rw [writer_release_stage3_prefix, List.drop_drop]

theorem writer_release_stage4_prefix : (writerReleaseTail.drop 60).take 6 =
    writerReleaseOne 15 (writerProtected 1) := rfl

theorem writer_release_stage4_shape : writerReleaseTail.drop 60 =
    writerReleaseOne 15 (writerProtected 1) ++ writerReleaseTail.drop 66 := by
  calc
    _ = (writerReleaseTail.drop 60).take 6 ++ (writerReleaseTail.drop 60).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage4_prefix, List.drop_drop]

theorem writer_release_end : writerReleaseTail.drop 66 = [] := rfl

#print axioms writer_release_setup_shape
#print axioms writer_release_stage0_shape
#print axioms writer_release_stage1_shape
#print axioms writer_release_stage2_shape
#print axioms writer_release_stage3_shape
#print axioms writer_release_stage4_shape
#print axioms writer_release_end
end Project.EulerGridStep.Execution
