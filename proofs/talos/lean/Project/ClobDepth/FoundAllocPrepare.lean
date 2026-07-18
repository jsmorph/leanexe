import Project.ClobDepth.FoundPrepare

/-!
# Found-price allocation preparation

The found branch allocates a stride-two array with the same level count.
The theorem records the source capacity and the allocator scratch locals used
by the following empty free-list search and bump allocation.
-/

namespace Project.ClobDepth.FoundAllocPrepare

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

def allocFrame (owner source price qty : UInt64) (levels : List LevelL)
    (i : Nat) : Locals :=
  { params := [.i64 owner, .i64 source, .i64 price, .i64 qty]
    locals := [.i64 levels[i]!.lprice, .i64 levels[i]!.lqty,
      .i64 (UInt64.ofNat i + 1), .i64 0, .i64 0, .i64 source,
      .i64 (UInt64.ofNat i), .i64 0, .i64 0, .i64 0, .i64 source,
      .i64 (UInt64.ofNat i), .i64 (UInt64.ofNat levels.length),
      .i64 (UInt64.ofNat levels.length * 2), .i64 0, .i64 0, .i64 price,
      .i64 (levels[i]!.lqty + qty), .i64 0, .i64 0,
      .i64 (fixedArrayBytesU levels.length 2), .i64 0, .i64 0, .i64 1,
      .i64 0, .i64 0]
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem foundAllocPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty : UInt64) (levels : List LevelL) (i : Nat)
    (hLength : levels.length < 4294967296)
    (hGlobal1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (allocFrame owner source price qty levels i) env) :
    wp «module» (Entry.foundAllocPrepareProg ++ rest) Q st
      { FoundPrepare.prepareFrame owner source price qty levels i with
          values := [] } env := by
  have hBytes : fixedArrayBytes levels.length 2 + 7 < UInt64.size := by
    rw [size_eq]
    unfold fixedArrayBytes
    omega
  have hRound := fixedArrayBytesU_round levels.length 2
    (by rw [size_eq]; omega) (by decide) hBytes
  have hCapacity :
      (8 + UInt64.ofNat levels.length * 2 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU levels.length 2 := by
    change (fixedArrayBytesU levels.length 2 + 7) / 8 * 8 =
      fixedArrayBytesU levels.length 2
    exact hRound
  have hNeedNat : (fixedArrayBytesU levels.length 2).toNat =
      fixedArrayBytes levels.length 2 :=
    fixedArrayBytesU_toNat levels.length 2
      (by rw [size_eq]; omega) (by decide) (by omega)
  have hNeedNotLt : ¬fixedArrayBytesU levels.length 2 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hNeedNat]
    change ¬fixedArrayBytes levels.length 2 < 8
    unfold fixedArrayBytes
    omega
  simp only [Entry.foundAllocPrepareProg, List.cons_append,
    List.nil_append]
  simp [FoundPrepare.prepareFrame]
  rw [hCapacity]
  refine wp_iff_cons rfl ?_
  rw [if_neg hNeedNotLt]
  rw [if_neg (by simp)]
  wp_run
  simpa [hGlobal1, allocFrame] using hNext

end Project.ClobDepth.FoundAllocPrepare
