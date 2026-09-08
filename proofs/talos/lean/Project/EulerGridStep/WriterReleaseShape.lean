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

theorem writer_release_stage0_prefix : (writerReleaseTail.drop 6).take 5 =
    writerReleaseOne 51 := rfl

theorem writer_release_stage0_shape : writerReleaseTail.drop 6 =
    writerReleaseOne 51 ++ writerReleaseTail.drop 11 := by
  calc
    _ = (writerReleaseTail.drop 6).take 5 ++ (writerReleaseTail.drop 6).drop 5 :=
      (List.take_append_drop 5 _).symm
    _ = _ := by rw [writer_release_stage0_prefix, List.drop_drop]

theorem writer_release_stage1_prefix : (writerReleaseTail.drop 11).take 5 =
    writerReleaseOne 42 := rfl

theorem writer_release_stage1_shape : writerReleaseTail.drop 11 =
    writerReleaseOne 42 ++ writerReleaseTail.drop 16 := by
  calc
    _ = (writerReleaseTail.drop 11).take 5 ++ (writerReleaseTail.drop 11).drop 5 :=
      (List.take_append_drop 5 _).symm
    _ = _ := by rw [writer_release_stage1_prefix, List.drop_drop]

theorem writer_release_stage2_prefix : (writerReleaseTail.drop 16).take 5 =
    writerReleaseOne 33 := rfl

theorem writer_release_stage2_shape : writerReleaseTail.drop 16 =
    writerReleaseOne 33 ++ writerReleaseTail.drop 21 := by
  calc
    _ = (writerReleaseTail.drop 16).take 5 ++ (writerReleaseTail.drop 16).drop 5 :=
      (List.take_append_drop 5 _).symm
    _ = _ := by rw [writer_release_stage2_prefix, List.drop_drop]

theorem writer_release_stage3_prefix : (writerReleaseTail.drop 21).take 5 =
    writerReleaseOne 24 := rfl

theorem writer_release_stage3_shape : writerReleaseTail.drop 21 =
    writerReleaseOne 24 ++ writerReleaseTail.drop 26 := by
  calc
    _ = (writerReleaseTail.drop 21).take 5 ++ (writerReleaseTail.drop 21).drop 5 :=
      (List.take_append_drop 5 _).symm
    _ = _ := by rw [writer_release_stage3_prefix, List.drop_drop]

theorem writer_release_stage4_prefix : (writerReleaseTail.drop 26).take 5 =
    writerReleaseOne 15 := rfl

theorem writer_release_stage4_shape : writerReleaseTail.drop 26 =
    writerReleaseOne 15 ++ writerReleaseTail.drop 31 := by
  calc
    _ = (writerReleaseTail.drop 26).take 5 ++ (writerReleaseTail.drop 26).drop 5 :=
      (List.take_append_drop 5 _).symm
    _ = _ := by rw [writer_release_stage4_prefix, List.drop_drop]

theorem writer_release_end : writerReleaseTail.drop 31 = [] := rfl

#print axioms writer_release_setup_shape
#print axioms writer_release_stage0_shape
#print axioms writer_release_stage1_shape
#print axioms writer_release_stage2_shape
#print axioms writer_release_stage3_shape
#print axioms writer_release_stage4_shape
#print axioms writer_release_end
end Project.EulerGridStep.Execution
