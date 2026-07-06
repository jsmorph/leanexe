import Project.AssocList.Program
import Project.Common
import LeanExe.Examples.TalosAssocList
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `lookupDemo`

The generated module builds the source-level sample association list in linear
memory and searches it.  The lookup function is specified against an abstract
list-segment predicate, so the search theorem is one induction over the list
rather than one lemma per concrete cell address.
-/

namespace Project.AssocList.Spec

open Wasm
open Project.Common

/-- A linked association-list segment: each cell holds a tag word `1`, the key,
the value, and the tail pointer in consecutive 8-byte slots, and the terminator
holds a tag word `0`.  Every read carries its bound in the current memory. -/
inductive ListSegAt (st : Store Unit) : UInt64 → List (UInt64 × UInt64) → Prop
  | nil {addr : UInt64} :
      st.mem.read64 addr.toUInt32 = 0 →
      addr.toUInt32.toNat + 8 ≤ st.mem.pages * 65536 →
      ListSegAt st addr []
  | cons {addr k v next : UInt64} {rest : List (UInt64 × UInt64)} :
      st.mem.read64 addr.toUInt32 = 1 →
      st.mem.read64 (addr + 8).toUInt32 = k →
      st.mem.read64 (addr + 16).toUInt32 = v →
      st.mem.read64 (addr + 24).toUInt32 = next →
      addr.toUInt32.toNat + 8 ≤ st.mem.pages * 65536 →
      (addr + 8).toUInt32.toNat + 8 ≤ st.mem.pages * 65536 →
      (addr + 16).toUInt32.toNat + 8 ≤ st.mem.pages * 65536 →
      (addr + 24).toUInt32.toNat + 8 ≤ st.mem.pages * 65536 →
      ListSegAt st next rest →
      ListSegAt st addr ((k, v) :: rest)

/-- The generated lookup returns the first value whose key matches, or `0` when
the segment is exhausted, for every association-list segment in memory. -/
private theorem func0_seg (st : Store Unit) :
    ∀ (kvs : List (UInt64 × UInt64)) (addr key : UInt64),
      ListSegAt st addr kvs →
      TerminatesWith (m := «module») (id := 0) (initial := st)
        (env := ({} : HostEnv Unit)) [.i64 key, .i64 addr]
        (fun st' vs => st' = st ∧
          vs = [.i64 (LeanExe.Examples.TalosAssocList.lookup kvs key)]) := by
  intro kvs
  induction kvs with
  | nil =>
      intro addr key hSeg
      cases hSeg with
      | nil h0 hb =>
          rw [toUInt32_eq_ofNat] at h0 hb
          rw [toUInt32_ofNat_mod_toNat] at hb
          apply TerminatesWith.of_wp_entry_for (f := func0Def)
          · simp [«module»]
          · change wp «module» func0 _ st
              { params := [.i64 addr, .i64 key],
                locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
                values := [] }
            unfold func0
            wp_run
            simp
            constructor
            · omega
            · simp [h0]
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              simp [func0Def, LeanExe.Examples.TalosAssocList.lookup]
  | cons kv rest ih =>
      intro addr key hSeg
      cases hSeg with
      | @cons _ k v next rest' h1 hk hv hn b1 b2 b3 b4 hRest =>
          have e8 : (addr + 8).toUInt32 =
              UInt32.ofNat ((addr.toNat + 8) % 4294967296) := by
            rw [toUInt32_eq_ofNat, UInt64.toNat_add]
            have h8 : (8 : UInt64).toNat = 8 := rfl
            rw [h8]
            congr 1
            omega
          have e16 : (addr + 16).toUInt32 =
              UInt32.ofNat ((addr.toNat + 16) % 4294967296) := by
            rw [toUInt32_eq_ofNat, UInt64.toNat_add]
            have h16 : (16 : UInt64).toNat = 16 := rfl
            rw [h16]
            congr 1
            omega
          have e24 : (addr + 24).toUInt32 =
              UInt32.ofNat ((addr.toNat + 24) % 4294967296) := by
            rw [toUInt32_eq_ofNat, UInt64.toNat_add]
            have h24 : (24 : UInt64).toNat = 24 := rfl
            rw [h24]
            congr 1
            omega
          rw [toUInt32_eq_ofNat] at h1 b1
          rw [e8] at hk b2
          rw [e16] at hv b3
          rw [e24] at hn b4
          rw [toUInt32_ofNat_mod_toNat] at b1 b2 b3 b4
          apply TerminatesWith.of_wp_entry_for (f := func0Def)
          · simp [«module»]
          · change wp «module» func0 _ st
              { params := [.i64 addr, .i64 key],
                locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
                values := [] }
            unfold func0
            wp_run
            simp
            constructor
            · omega
            · simp [h1]
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              wp_run
              simp
              constructor
              · omega
              · simp [hk]
                by_cases hkey : k = key
                · subst hkey
                  simp
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  wp_run
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  wp_run
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  wp_run
                  simp
                  constructor
                  · omega
                  · simp [hv, func0Def, LeanExe.Examples.TalosAssocList.lookup]
                · have hkey' : ¬ (k = key) := hkey
                  simp [hkey']
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  wp_run
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  wp_run
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  wp_run
                  simp
                  constructor
                  · omega
                  · simp [hn]
                    apply wp_call_tw (ih next key hRest)
                    rintro st' vs ⟨rfl, rfl⟩
                    wp_run
                    have hbeq : (k == key) = false := by
                      simp [hkey']
                    simp [func0Def, LeanExe.Examples.TalosAssocList.lookup, hbeq]

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

private theorem boundAt {st : Store Unit} (hBound : 5000 ≤ st.mem.pages * 65536)
    {a : UInt32} (ha : a.toNat + 8 ≤ 5000) :
    a.toNat + 8 ≤ st.mem.pages * 65536 := by
  omega

/-- The concrete constructed sample list is a list segment at its root. -/
private theorem sample_seg (st : Store Unit)
    (hBound : 5000 ≤ st.mem.pages * 65536) (hSample : SampleListStore st) :
    ListSegAt st 4464 LeanExe.Examples.TalosAssocList.sample := by
  rcases hSample with
    ⟨h4464, h4472, h4480, h4488, h4384, h4392, h4400, h4408,
     h4304, h4312, h4320, h4328, h4224, h4232, h4240, h4248, h4144⟩
  refine ListSegAt.cons
    (by simpa [read64At] using h4464) (by simpa [read64At] using h4472)
    (by simpa [read64At] using h4480) (by simpa [read64At] using h4488)
    (boundAt hBound (by decide)) (boundAt hBound (by decide))
    (boundAt hBound (by decide)) (boundAt hBound (by decide)) ?_
  refine ListSegAt.cons
    (by simpa [read64At] using h4384) (by simpa [read64At] using h4392)
    (by simpa [read64At] using h4400) (by simpa [read64At] using h4408)
    (boundAt hBound (by decide)) (boundAt hBound (by decide))
    (boundAt hBound (by decide)) (boundAt hBound (by decide)) ?_
  refine ListSegAt.cons
    (by simpa [read64At] using h4304) (by simpa [read64At] using h4312)
    (by simpa [read64At] using h4320) (by simpa [read64At] using h4328)
    (boundAt hBound (by decide)) (boundAt hBound (by decide))
    (boundAt hBound (by decide)) (boundAt hBound (by decide)) ?_
  refine ListSegAt.cons
    (by simpa [read64At] using h4224) (by simpa [read64At] using h4232)
    (by simpa [read64At] using h4240) (by simpa [read64At] using h4248)
    (boundAt hBound (by decide)) (boundAt hBound (by decide))
    (boundAt hBound (by decide)) (boundAt hBound (by decide)) ?_
  exact ListSegAt.nil (by simpa [read64At] using h4144)
    (boundAt hBound (by decide))

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

def wasmRunsTo (key output : UInt64) : Prop :=
  TerminatesWith (m := «module») (id := 2)
    (initial := «module».initialStore (α := Unit))
    (env := ({} : HostEnv Unit)) [.i64 key]
    (fun _ vs => vs = [.i64 output])

@[spec_of "lean" "LeanExe.Examples.TalosAssocList.lookupDemo"]
def LookupDemoSpec : Prop :=
  LeanExe.Examples.TalosAssocList.LookupSpec wasmRunsTo

@[proves Project.AssocList.Spec.LookupDemoSpec]
theorem lookupDemo_correct : LookupDemoSpec := by
  unfold LookupDemoSpec LeanExe.Examples.TalosAssocList.LookupSpec wasmRunsTo
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
    have hlook := func0_seg st1 LeanExe.Examples.TalosAssocList.sample 4464 key
      (sample_seg st1 hBound hSample)
    have heq : LeanExe.Examples.TalosAssocList.lookup
        LeanExe.Examples.TalosAssocList.sample key =
        LeanExe.Examples.TalosAssocList.lookupDemoExpected key :=
      LeanExe.Examples.TalosAssocList.lookupDemo_eq_expected key
    rw [heq] at hlook
    apply wp_call_tw hlook
    rintro st2 vs2 ⟨rfl, rfl⟩
    wp_run
    simp [func2Def]

end Project.AssocList.Spec
