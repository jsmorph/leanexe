import Project.ClobDepth.MissingFields

/-!
# Missing-price allocation preparation

The missing branch prepares a stride-two array with one additional level.
The theorem records the source capacity and the allocator scratch locals used
by the following empty free-list search and bump allocation.
-/

namespace Project.ClobDepth.MissingPrepare

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

def prepareFrame (owner ptr price qty : UInt64) (levels : List LevelL)
    (f4 f5 : UInt64) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 price, .i64 qty]
    locals := [.i64 f4, .i64 f5, .i64 0, .i64 ptr, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat levels.length),
      .i64 (UInt64.ofNat levels.length * 2),
      .i64 (UInt64.ofNat (levels.length + 1)), .i64 0, .i64 0,
      .i64 price, .i64 qty, .i64 0, .i64 0,
      .i64 (fixedArrayBytesU (levels.length + 1) 2), .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0]
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem missingPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner ptr price qty : UInt64) (levels : List LevelL) (f4 f5 : UInt64)
    (hLength : levels.length < 4294967296)
    (hGlobal1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (prepareFrame owner ptr price qty levels f4 f5) env) :
    wp «module» (Entry.missingAllocPrepareProg ++ rest) Q st
      (MissingFields.fieldFrame owner ptr price qty levels f4 f5) env := by
  have hBytes : fixedArrayBytes (levels.length + 1) 2 + 7 < UInt64.size := by
    rw [size_eq]
    unfold fixedArrayBytes
    omega
  have hRound := fixedArrayBytesU_round (levels.length + 1) 2
    (by rw [size_eq]; omega) (by decide) hBytes
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hLengthOne : UInt64.ofNat levels.length + 1 =
      UInt64.ofNat (levels.length + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hLengthU, size_eq]; omega), hLengthU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  have hCapacity :
      (8 + (UInt64.ofNat levels.length + 1) * 2 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU (levels.length + 1) 2 := by
    rw [hLengthOne]
    change (fixedArrayBytesU (levels.length + 1) 2 + 7) / 8 * 8 =
      fixedArrayBytesU (levels.length + 1) 2
    exact hRound
  have hNeedNat : (fixedArrayBytesU (levels.length + 1) 2).toNat =
      fixedArrayBytes (levels.length + 1) 2 :=
    fixedArrayBytesU_toNat (levels.length + 1) 2
      (by rw [size_eq]; omega) (by decide) (by omega)
  have hNeedNotLt : ¬fixedArrayBytesU (levels.length + 1) 2 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hNeedNat]
    change ¬fixedArrayBytes (levels.length + 1) 2 < 8
    unfold fixedArrayBytes
    omega
  simp only [Entry.missingAllocPrepareProg, List.cons_append,
    List.nil_append]
  simp [MissingFields.fieldFrame]
  rw [hCapacity]
  refine wp_iff_cons rfl ?_
  rw [if_neg hNeedNotLt]
  rw [if_neg (by simp)]
  wp_run
  simpa [hGlobal1, prepareFrame] using hNext

end Project.ClobDepth.MissingPrepare
