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

theorem writer_release_stage0_prefix : (writerReleaseTail.drop 6).take 6 =
    writerReleaseOne 51 := rfl

theorem writer_release_stage0_shape : writerReleaseTail.drop 6 =
    writerReleaseOne 51 ++ writerReleaseTail.drop 12 := by
  calc
    _ = (writerReleaseTail.drop 6).take 6 ++ (writerReleaseTail.drop 6).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage0_prefix, List.drop_drop]

theorem writer_release_stage1_prefix : (writerReleaseTail.drop 12).take 6 =
    writerReleaseOne 42 := rfl

theorem writer_release_stage1_shape : writerReleaseTail.drop 12 =
    writerReleaseOne 42 ++ writerReleaseTail.drop 18 := by
  calc
    _ = (writerReleaseTail.drop 12).take 6 ++ (writerReleaseTail.drop 12).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage1_prefix, List.drop_drop]

theorem writer_release_stage2_prefix : (writerReleaseTail.drop 18).take 6 =
    writerReleaseOne 33 := rfl

theorem writer_release_stage2_shape : writerReleaseTail.drop 18 =
    writerReleaseOne 33 ++ writerReleaseTail.drop 24 := by
  calc
    _ = (writerReleaseTail.drop 18).take 6 ++ (writerReleaseTail.drop 18).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage2_prefix, List.drop_drop]

theorem writer_release_stage3_prefix : (writerReleaseTail.drop 24).take 6 =
    writerReleaseOne 24 := rfl

theorem writer_release_stage3_shape : writerReleaseTail.drop 24 =
    writerReleaseOne 24 ++ writerReleaseTail.drop 30 := by
  calc
    _ = (writerReleaseTail.drop 24).take 6 ++ (writerReleaseTail.drop 24).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage3_prefix, List.drop_drop]

theorem writer_release_stage4_prefix : (writerReleaseTail.drop 30).take 6 =
    writerReleaseOne 15 := rfl

theorem writer_release_stage4_shape : writerReleaseTail.drop 30 =
    writerReleaseOne 15 ++ writerReleaseTail.drop 36 := by
  calc
    _ = (writerReleaseTail.drop 30).take 6 ++ (writerReleaseTail.drop 30).drop 6 :=
      (List.take_append_drop 6 _).symm
    _ = _ := by rw [writer_release_stage4_prefix, List.drop_drop]

theorem writer_release_end : writerReleaseTail.drop 36 = [] := rfl

#print axioms writer_release_setup_shape
#print axioms writer_release_stage0_shape
#print axioms writer_release_stage1_shape
#print axioms writer_release_stage2_shape
#print axioms writer_release_stage3_shape
#print axioms writer_release_stage4_shape
#print axioms writer_release_end
end Project.EulerGridStep.Execution
