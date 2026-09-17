import Project.F64Clip.Execution
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.BlockLoop

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit UInt64Array Memory

def mapSuffix : Wasm.Program :=
  [.localGet 17, .localGet 18, .constI64 1, .mulI64, .constI64 1, .addI64,
   .constI64 8, .mulI64, .addI64, .wrapI64,
   .localGet 1, .localSet 9, .localGet 8, .localSet 10, .localGet 9, .localGet 10,
   .call 5, .localSet 11, .localGet 11, .store64 0,
   .localGet 18, .constI64 1, .addI64, .localSet 18, .br 0]

def mapBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 15 18 16 8 ++ mapSuffix

def mapFrame (count bound ptr root : UInt64) (size index : Nat)
    (last argument result : UInt64) (tail : List Value) : Locals :=
  { params := [.i64 count, .i64 bound, .i64 ptr]
    locals := [.i64 count, .i64 bound, .i64 0, .i64 ptr, .i64 1,
      .i64 last, .i64 argument, .i64 last, .i64 result, .i64 0, .i64 0, .i64 0,
      .i64 ptr, .i64 (UInt64.ofNat size), .i64 root, .i64 (UInt64.ofNat index), .i64 0, .i64 0] ++ tail
    values := [] }

macro "wp_clip_map" : tactic => `(tactic|
  simp +arith [wp_simp, Locals.get, Locals.set?, Locals.set, Locals.validIndex,
    mapFrame, FixedArrayTraversalInput.dynamicResultFrame])

def mapInv (initial : Store Unit) (count bound ptr root : UInt64) (w : Array UInt64)
    (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ index last argument result, index ≤ w.size ∧
    frame = mapFrame count bound ptr root w.size index last argument result tail ∧
    PrefixAt st root (w.map (clip bound)) index ∧
    WritesRange initial st root.toNat (root.toNat+8*(w.size+1))

def mapDone (initial : Store Unit) (count bound ptr root : UInt64) (w : Array UInt64)
    (tail : List Value) : AssertionF Unit := fun st frame =>
  ∃ last argument result,
    frame = mapFrame count bound ptr root w.size w.size last argument result tail ∧
    UInt64Array.At st root (w.map (clip bound)) ∧
    WritesRange initial st root.toNat (root.toNat+8*(w.size+1))

def mapMeasure (w : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 18 with
  | some (.i64 index) => w.size-index.toNat
  | _ => 0

theorem map_address (root : UInt64) (index : Nat) :
    UInt32.ofNat ((root+(UInt64.ofNat index*1+1)*8).toNat % 2^32) = wordAddress root (index+1) := by
  have hOffset : (UInt64.ofNat index*1+1)*8 = UInt64.ofNat (8*(index+1)) := by
    rw [UInt64.mul_one]
    change (UInt64.ofNat index+UInt64.ofNat 1)*UInt64.ofNat 8 = _
    rw [← UInt64.ofNat_add, ← UInt64.ofNat_mul, Nat.mul_comm (index+1) 8]
  rw [hOffset]
  exact (Memory.toUInt32_eq_ofNat _).symm

theorem map_step (env : HostEnv Unit) (initial : Store Unit) (count bound ptr root : UInt64)
    (w : Array UInt64) (tail : List Value) (hInput : UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ root.toNat)
    (st : Store Unit) (frame : Locals) (hInv : mapInv initial count bound ptr root w tail st frame) :
    wp Project.F64Clip.module mapBody
      (BlockLoop.stepPost (mapInv initial count bound ptr root w tail)
        (mapDone initial count bound ptr root w tail) (mapMeasure w) (mapMeasure w st frame)) st frame env := by
  rcases hInv with ⟨index, last, argument, result, hIndex, rfl, hPrefix, hWrites⟩
  have hCurrent := hInput.writesRange hWrites (Or.inl hBefore)
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat w.size).toNat = w.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = w.size
  · subst index
    unfold mapBody
    refine FixedArrayTraversalInput.continuingProgram_exit_spec 15 18 16 8
      Project.F64Clip.module env st _ (UInt64.ofNat w.size) rfl
      (by simp +arith [mapFrame, Locals.get]) (by simp +arith [mapFrame, Locals.get]) _ _ ?_
    exact ⟨last, argument, result, rfl,
      PrefixAt.complete (by simpa using hPrefix), hWrites⟩
  · have hi : index < w.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat w.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold mapBody
    refine FixedArrayTraversalInput.continuingProgram_spec 15 18 16 8 Project.F64Clip.module env
      st _ ptr (UInt64.ofNat index) (UInt64.ofNat w.size) w index
      rfl (by simp +arith [mapFrame, Locals.get]) (by simp +arith [mapFrame, Locals.get])
      (by simp +arith [mapFrame, Locals.get]) rfl hlt
      (by simp [mapFrame, Locals.validIndex]; omega) hCurrent hi _ _ ?_
    unfold mapSuffix
    wp_clip_map
    have hAddress := map_address root index
    simp +arith at hAddress
    rw [hAddress]
    refine wp_call_exact_append (clip_exact env st bound w[index]) rfl rfl rfl
      [.i32 (wordAddress root (index+1))] rfl ?_
    have hBound := hPrefix.elementBound index (by simpa using hi)
    have hNext := hPrefix.write_next (by simpa using hi)
    have hFrame := writeElement_frame st root w.size index (clip bound w[index])
      (by simpa using hPrefix.1) hi
    wp_clip_map
    rw [ite_eq_right (show ¬65536*st.mem.pages ≤ (wordAddress root (index+1)).toNat+7 by omega)]
    constructor
    · refine ⟨index+1, w[index], bound, clip bound w[index], by omega, ?_, ?_, hWrites.trans hFrame⟩
      · simp [mapFrame, UInt64.ofNat_add]
      · simpa [writeElement, hi] using hNext
    · have hNextMod : (index+1)%18446744073709551616 = index+1 :=
        Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hInput.size_lt)
      simp +arith [mapMeasure, Locals.get, hNextMod, hIndexNat]
      omega

theorem map_program_spec (env : HostEnv Unit) (initial : Store Unit)
    (count bound ptr root : UInt64) (w : Array UInt64) (tail : List Value)
    (hInput : UInt64Array.At initial ptr w)
    (hBefore : ptr.toNat+8*(w.size+1) ≤ root.toNat)
    (hPrefix : PrefixAt initial root (w.map (clip bound)) 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ st last argument result,
      UInt64Array.At st root (w.map (clip bound)) →
      WritesRange initial st root.toNat (root.toNat+8*(w.size+1)) →
      wp Project.F64Clip.module rest Q st
        (mapFrame count bound ptr root w.size w.size last argument result tail) env) :
    wp Project.F64Clip.module ([.block 0 0 [.loop 0 0 mapBody]] ++ rest) Q initial
      (mapFrame count bound ptr root w.size 0 0 0 0 tail) env := by
  refine BlockLoop.program_spec Project.F64Clip.module env initial _ mapBody
    (mapInv initial count bound ptr root w tail) (mapDone initial count bound ptr root w tail)
    (mapMeasure w) ?_ ?_ ?_ (map_step env initial count bound ptr root w tail hInput hBefore) _ _ ?_
  · rintro st frame ⟨index, last, argument, result, _, rfl, _⟩
    rfl
  · rintro st frame ⟨last, argument, result, rfl, _⟩
    rfl
  · exact ⟨0, 0, 0, 0, Nat.zero_le _, rfl, hPrefix, WritesRange.refl ..⟩
  · rintro st frame ⟨last, argument, result, rfl, hOut, hWrites⟩
    exact hNext st last argument result hOut hWrites

#print axioms map_step
#print axioms map_program_spec
end Project.F64Clip.Spec
