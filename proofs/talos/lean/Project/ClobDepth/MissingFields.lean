import Project.ClobDepth.Scan

/-!
# Missing-price field preparation

This phase copies the new level fields, reads the represented length, and
computes the source and target word counts.  Capacity arithmetic remains in a
separate module.
-/

namespace Project.ClobDepth.MissingFields

open Wasm Project.Common Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Representation

def branchFrame (owner ptr price qty : UInt64) (levels : List LevelL)
    (f4 f5 : UInt64) : Locals :=
  { Scan.outcomeFrame owner ptr price qty (UInt64.ofNat levels.length)
      (UInt64.ofNat levels.length) 0 f4 f5 1 with values := [] }

def fieldFrame (owner ptr price qty : UInt64) (levels : List LevelL)
    (f4 f5 : UInt64) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 price, .i64 qty]
    locals := [.i64 f4, .i64 f5, .i64 0, .i64 ptr, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat levels.length),
      .i64 (UInt64.ofNat levels.length * 2),
      .i64 (UInt64.ofNat (levels.length + 1)), .i64 0, .i64 0,
      .i64 price, .i64 qty, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0]
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem missingFieldsProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner ptr price qty : UInt64) (levels : List LevelL) (f4 f5 : UInt64)
    (hLength : levels.length < 4294967296)
    (hLevels : LevelsAt st ptr levels)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (fieldFrame owner ptr price qty levels f4 f5) env) :
    wp «module» (Entry.missingFieldsProg ++ rest) Q st
      (branchFrame owner ptr price qty levels f4 f5) env := by
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hLengthOne : UInt64.ofNat levels.length + 1 =
      UInt64.ofNat (levels.length + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hLengthU, size_eq]; omega), hLengthU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  simp only [Entry.missingFieldsProg, List.cons_append, List.nil_append]
  simp [branchFrame, Scan.outcomeFrame]
  rw [if_neg (Nat.not_lt.mpr hLevels.1.2), hLevels.1.1]
  rw [hLengthOne]
  exact hNext

end Project.ClobDepth.MissingFields
