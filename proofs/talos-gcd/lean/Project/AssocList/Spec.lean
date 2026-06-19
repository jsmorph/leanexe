import Project.AssocList.Program
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `lookupDemo`
-/

namespace Project.AssocList.Spec

open Wasm

private def lookupDemoExpected (key : UInt64) : UInt64 :=
  if key == 7 then
    70
  else
    if key == 2 then
      20
    else if key == 9 then
      90
    else
      0

private def node4224Expected (key : UInt64) : UInt64 :=
  if key == 2 then
    22
  else
    0

private def node4304Expected (key : UInt64) : UInt64 :=
  if key == 9 then
    90
  else
    node4224Expected key

private def node4384Expected (key : UInt64) : UInt64 :=
  if key == 2 then
    20
  else
    node4304Expected key

private def read64At (st : Store Unit) (addr : Nat) : UInt64 :=
  st.mem.read64 (UInt32.ofNat addr)

private def SampleListStore (st : Store Unit) : Prop :=
  read64At st 4464 = 1 ∧
  read64At st 4472 = 7 ∧
  read64At st 4480 = 70 ∧
  read64At st 4488 = 4384 ∧
  read64At st 4384 = 1 ∧
  read64At st 4392 = 2 ∧
  read64At st 4400 = 20 ∧
  read64At st 4408 = 4304 ∧
  read64At st 4304 = 1 ∧
  read64At st 4312 = 9 ∧
  read64At st 4320 = 90 ∧
  read64At st 4328 = 4224 ∧
  read64At st 4224 = 1 ∧
  read64At st 4232 = 2 ∧
  read64At st 4240 = 22 ∧
  read64At st 4248 = 4144 ∧
  read64At st 4144 = 0

private def sampleListStoreOk (st : Store Unit) : Bool :=
  read64At st 4464 == (1 : UInt64) &&
  read64At st 4472 == (7 : UInt64) &&
  read64At st 4480 == (70 : UInt64) &&
  read64At st 4488 == (4384 : UInt64) &&
  read64At st 4384 == (1 : UInt64) &&
  read64At st 4392 == (2 : UInt64) &&
  read64At st 4400 == (20 : UInt64) &&
  read64At st 4408 == (4304 : UInt64) &&
  read64At st 4304 == (1 : UInt64) &&
  read64At st 4312 == (9 : UInt64) &&
  read64At st 4320 == (90 : UInt64) &&
  read64At st 4328 == (4224 : UInt64) &&
  read64At st 4224 == (1 : UInt64) &&
  read64At st 4232 == (2 : UInt64) &&
  read64At st 4240 == (22 : UInt64) &&
  read64At st 4248 == (4144 : UInt64) &&
  read64At st 4144 == (0 : UInt64)

private theorem sampleListStoreOk_true {st : Store Unit}
    (h : sampleListStoreOk st = true) : SampleListStore st := by
  simp [sampleListStoreOk] at h
  rcases h with ⟨h, h4144⟩
  rcases h with ⟨h, h4248⟩
  rcases h with ⟨h, h4240⟩
  rcases h with ⟨h, h4232⟩
  rcases h with ⟨h, h4224⟩
  rcases h with ⟨h, h4328⟩
  rcases h with ⟨h, h4320⟩
  rcases h with ⟨h, h4312⟩
  rcases h with ⟨h, h4304⟩
  rcases h with ⟨h, h4408⟩
  rcases h with ⟨h, h4400⟩
  rcases h with ⟨h, h4392⟩
  rcases h with ⟨h, h4384⟩
  rcases h with ⟨h, h4488⟩
  rcases h with ⟨h, h4480⟩
  rcases h with ⟨h4464, h4472⟩
  exact ⟨h4464, h4472, h4480, h4488, h4384, h4392, h4400, h4408,
    h4304, h4312, h4320, h4328, h4224, h4232, h4240, h4248, h4144⟩

private theorem func0_nil_terminates
    (st : Store Unit) (hBound : 5000 ≤ st.mem.pages * 65536)
    (h4144 : read64At st 4144 = 0) (key : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st)
      (env := ({} : HostEnv Unit)) [.i64 key, .i64 4144]
      (fun st' vs => st' = st ∧ vs = [.i64 0]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 4144, .i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func0
    wp_run
    simp
    constructor
    · omega
    · have hread : st.mem.read64 (4144 : UInt32) = 0 := by
        simpa [read64At] using h4144
      simp [hread]
      apply wp_iff_cons rfl
      wp_run
      simp [func0Def]

private theorem func0_node4224_terminates
    (st : Store Unit) (hBound : 5000 ≤ st.mem.pages * 65536)
    (h4224 : read64At st 4224 = 1) (h4232 : read64At st 4232 = 2)
    (h4240 : read64At st 4240 = 22) (h4248 : read64At st 4248 = 4144)
    (h4144 : read64At st 4144 = 0) (key : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st)
      (env := ({} : HostEnv Unit)) [.i64 key, .i64 4224]
      (fun st' vs => st' = st ∧ vs = [.i64 (node4224Expected key)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 4224, .i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func0
    wp_run
    simp
    constructor
    · omega
    · have hread4224 : st.mem.read64 (4224 : UInt32) = 1 := by
        simpa [read64At] using h4224
      simp [hread4224]
      apply wp_iff_cons rfl
      wp_run
      simp
      constructor
      · omega
      · have hread4232 : st.mem.read64 (4232 : UInt32) = 2 := by
          simpa [read64At] using h4232
        simp [hread4232]
        by_cases hkey : (2 : UInt64) = key
        · subst key
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4240 : st.mem.read64 (4240 : UInt32) = 22 := by
              simpa [read64At] using h4240
            simp [func0Def, node4224Expected, hread4240]
        · simp [hkey]
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4248 : st.mem.read64 (4248 : UInt32) = 4144 := by
              simpa [read64At] using h4248
            simp [hread4248]
            apply wp_call_tw (func0_nil_terminates st hBound h4144 key)
            rintro st' vs ⟨rfl, rfl⟩
            wp_run
            have hkey' : key ≠ 2 := fun hk => hkey hk.symm
            simp [func0Def, node4224Expected, hkey']

private theorem func0_node4304_terminates
    (st : Store Unit) (hBound : 5000 ≤ st.mem.pages * 65536)
    (h4304 : read64At st 4304 = 1) (h4312 : read64At st 4312 = 9)
    (h4320 : read64At st 4320 = 90) (h4328 : read64At st 4328 = 4224)
    (h4224 : read64At st 4224 = 1) (h4232 : read64At st 4232 = 2)
    (h4240 : read64At st 4240 = 22) (h4248 : read64At st 4248 = 4144)
    (h4144 : read64At st 4144 = 0) (key : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st)
      (env := ({} : HostEnv Unit)) [.i64 key, .i64 4304]
      (fun st' vs => st' = st ∧ vs = [.i64 (node4304Expected key)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 4304, .i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func0
    wp_run
    simp
    constructor
    · omega
    · have hread4304 : st.mem.read64 (4304 : UInt32) = 1 := by
        simpa [read64At] using h4304
      simp [hread4304]
      apply wp_iff_cons rfl
      wp_run
      simp
      constructor
      · omega
      · have hread4312 : st.mem.read64 (4312 : UInt32) = 9 := by
          simpa [read64At] using h4312
        simp [hread4312]
        by_cases hkey : (9 : UInt64) = key
        · subst key
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4320 : st.mem.read64 (4320 : UInt32) = 90 := by
              simpa [read64At] using h4320
            simp [func0Def, node4304Expected, hread4320]
        · simp [hkey]
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4328 : st.mem.read64 (4328 : UInt32) = 4224 := by
              simpa [read64At] using h4328
            simp [hread4328]
            apply wp_call_tw
              (func0_node4224_terminates st hBound h4224 h4232 h4240 h4248 h4144 key)
            rintro st' vs ⟨rfl, rfl⟩
            wp_run
            have hkey' : key ≠ 9 := fun hk => hkey hk.symm
            simp [func0Def, node4304Expected, hkey']

private theorem func0_node4384_terminates
    (st : Store Unit) (hBound : 5000 ≤ st.mem.pages * 65536)
    (h4384 : read64At st 4384 = 1) (h4392 : read64At st 4392 = 2)
    (h4400 : read64At st 4400 = 20) (h4408 : read64At st 4408 = 4304)
    (h4304 : read64At st 4304 = 1) (h4312 : read64At st 4312 = 9)
    (h4320 : read64At st 4320 = 90) (h4328 : read64At st 4328 = 4224)
    (h4224 : read64At st 4224 = 1) (h4232 : read64At st 4232 = 2)
    (h4240 : read64At st 4240 = 22) (h4248 : read64At st 4248 = 4144)
    (h4144 : read64At st 4144 = 0) (key : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st)
      (env := ({} : HostEnv Unit)) [.i64 key, .i64 4384]
      (fun st' vs => st' = st ∧ vs = [.i64 (node4384Expected key)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 4384, .i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func0
    wp_run
    simp
    constructor
    · omega
    · have hread4384 : st.mem.read64 (4384 : UInt32) = 1 := by
        simpa [read64At] using h4384
      simp [hread4384]
      apply wp_iff_cons rfl
      wp_run
      simp
      constructor
      · omega
      · have hread4392 : st.mem.read64 (4392 : UInt32) = 2 := by
          simpa [read64At] using h4392
        simp [hread4392]
        by_cases hkey : (2 : UInt64) = key
        · subst key
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4400 : st.mem.read64 (4400 : UInt32) = 20 := by
              simpa [read64At] using h4400
            simp [func0Def, node4384Expected, hread4400]
        · simp [hkey]
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4408 : st.mem.read64 (4408 : UInt32) = 4304 := by
              simpa [read64At] using h4408
            simp [hread4408]
            apply wp_call_tw
              (func0_node4304_terminates st hBound h4304 h4312 h4320 h4328
                h4224 h4232 h4240 h4248 h4144 key)
            rintro st' vs ⟨rfl, rfl⟩
            wp_run
            have hkey' : key ≠ 2 := fun hk => hkey hk.symm
            simp [func0Def, node4384Expected, hkey']

private theorem func0_sample_terminates
    (st : Store Unit) (hBound : 5000 ≤ st.mem.pages * 65536)
    (hSample : SampleListStore st) (key : UInt64) :
    TerminatesWith (m := «module») (id := 0) (initial := st)
      (env := ({} : HostEnv Unit)) [.i64 key, .i64 4464]
      (fun st' vs => st' = st ∧ vs = [.i64 (lookupDemoExpected key)]) := by
  rcases hSample with
    ⟨h4464, h4472, h4480, h4488, h4384, h4392, h4400, h4408,
     h4304, h4312, h4320, h4328, h4224, h4232, h4240, h4248, h4144⟩
  apply TerminatesWith.of_wp_entry_for (f := func0Def)
  · simp [«module»]
  · change wp «module» func0 _ st
      { params := [.i64 4464, .i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func0
    wp_run
    simp
    constructor
    · omega
    · have hread4464 : st.mem.read64 (4464 : UInt32) = 1 := by
        simpa [read64At] using h4464
      simp [hread4464]
      apply wp_iff_cons rfl
      wp_run
      simp
      constructor
      · omega
      · have hread4472 : st.mem.read64 (4472 : UInt32) = 7 := by
          simpa [read64At] using h4472
        simp [hread4472]
        by_cases hkey : (7 : UInt64) = key
        · subst key
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4480 : st.mem.read64 (4480 : UInt32) = 70 := by
              simpa [read64At] using h4480
            simp [func0Def, lookupDemoExpected, hread4480]
        · simp [hkey]
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          apply wp_iff_cons rfl
          wp_run
          simp
          constructor
          · omega
          · have hread4488 : st.mem.read64 (4488 : UInt32) = 4384 := by
              simpa [read64At] using h4488
            simp [hread4488]
            apply wp_call_tw
              (func0_node4384_terminates st hBound h4384 h4392 h4400 h4408
                h4304 h4312 h4320 h4328 h4224 h4232 h4240 h4248 h4144 key)
            rintro st' vs ⟨rfl, rfl⟩
            wp_run
            have hkey' : key ≠ 7 := fun hk => hkey hk.symm
            simp [func0Def, lookupDemoExpected, node4384Expected, node4304Expected,
              node4224Expected, hkey']
            by_cases h2 : key = 2
            · simp [h2]
            · by_cases h9 : key = 9
              · simp [h9]
              · simp [h2, h9]

private def sampleRunOk : Bool :=
  match run 5000 «module» 1 («module».initialStore (α := Unit)) []
      ({} : HostEnv Unit) with
  | .Success vs st =>
      decide (vs = [.i64 4464]) &&
      sampleListStoreOk st &&
      decide (5000 ≤ st.mem.pages * 65536)
  | _ => false

private theorem func1_constructs_sample :
    TerminatesWith (m := «module») (id := 1)
      (initial := «module».initialStore (α := Unit))
      (env := ({} : HostEnv Unit)) []
      (fun st vs => vs = [.i64 4464] ∧ SampleListStore st ∧
        5000 ≤ st.mem.pages * 65536) := by
  have hok : sampleRunOk = true := by
    native_decide
  unfold TerminatesWith
  refine ⟨5000, fun fuel hfuel => ?_⟩
  cases hrun : run 5000 «module» 1 («module».initialStore (α := Unit)) []
      ({} : HostEnv Unit) with
  | Success vs st =>
      have hpost : vs = [.i64 4464] ∧ SampleListStore st ∧
          5000 ≤ st.mem.pages * 65536 := by
        have hbits : (vs = [.i64 4464] ∧ sampleListStoreOk st = true) ∧
            5000 ≤ st.mem.pages * 65536 := by
          simpa [sampleRunOk, hrun, Bool.and_eq_true] using hok
        exact ⟨hbits.1.1, sampleListStoreOk_true hbits.1.2, hbits.2⟩
      refine ⟨vs, st, ?_, hpost⟩
      have h_ne :
          run 5000 «module» 1 («module».initialStore (α := Unit)) []
              ({} : HostEnv Unit) ≠ .OutOfFuel := by
        rw [hrun]
        intro h
        cases h
      rw [run_fuel_mono hfuel h_ne]
      exact hrun
  | OutOfFuel =>
      simp [sampleRunOk, hrun] at hok
  | Trap st msg =>
      simp [sampleRunOk, hrun] at hok
  | Invalid msg =>
      simp [sampleRunOk, hrun] at hok
  | Thrown tag args st =>
      simp [sampleRunOk, hrun] at hok

@[spec_of "lean" "LeanExe.Examples.TalosAssocList.lookupDemo"]
def LookupDemoSpec : Prop :=
  ∀ key : UInt64,
    TerminatesWith (m := «module») (id := 2)
      (initial := «module».initialStore (α := Unit))
      (env := ({} : HostEnv Unit)) [.i64 key]
      (fun _ vs => vs = [.i64 (lookupDemoExpected key)])

@[proves Project.AssocList.Spec.LookupDemoSpec]
theorem lookupDemo_correct : LookupDemoSpec := by
  intro key
  apply TerminatesWith.of_wp_entry_for (f := func2Def)
  · simp [«module»]
  · change wp «module» func2 _ («module».initialStore (α := Unit))
      { params := [.i64 key],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] }
    unfold func2
    wp_run
    apply wp_call_tw func1_constructs_sample
    rintro st1 vs1 ⟨rfl, hSample, hBound⟩
    wp_run
    apply wp_call_tw (func0_sample_terminates st1 hBound hSample key)
    rintro st2 vs2 ⟨rfl, rfl⟩
    wp_run
    simp [func2Def]

end Project.AssocList.Spec
