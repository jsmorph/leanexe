import Project.Beck.Program
import LeanExe.Examples.Beck
import Project.ProofKit.FixedFrame
import Project.TalosCompat

namespace Project.Beck.Execution

open Wasm Project.ProofKit LeanExe.Examples.Beck

def boolWord (b : Bool) : UInt64 := if b then 1 else 0

def parseValues (state : ParseState) (owner pointer : UInt64) : List Value :=
  [.i64 pointer, .i64 owner, .i64 state.overlap.toUInt64, .i64 state.position.toUInt64]

def inputValues (input : Input) (owner pointer : UInt64) : List Value :=
  [.i64 pointer, .i64 owner, .i64 input.overlap.toUInt64, .i64 input.categories.toUInt64,
    .i64 input.jobs.toUInt64, .i64 input.status]

def pointValues (point : Point) (owner pointer : UInt64) : List Value :=
  [.i64 pointer, .i64 owner, .i64 point.denominator]

def basisValues (basis : Basis) (rowsOwner rowsPointer columnsOwner columnsPointer : UInt64) : List Value :=
  [.i64 basis.determinant, .i64 columnsPointer, .i64 columnsOwner, .i64 rowsPointer, .i64 rowsOwner]

theorem negative_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env «module» 9 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (negative x))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func9Def) rfl ?_
  change wp «module» func9 _ initial { params := [.i64 x], locals := [.i64 0] } env
  simp only [func9]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  by_cases h : (9223372036854775808 : UInt64) ≤ x
  · simp [h]
    wp_fixed_frame [func9Def, boolWord, negative, h]
    trivial
  · simp [h]
    wp_fixed_frame [func9Def, boolWord, negative, h]
    trivial

theorem magnitude_exact (env : HostEnv Unit) (initial : Store Unit) (x : UInt64) :
    TerminatesWith env «module» 10 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (magnitude x)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func10Def) rfl ?_
  change wp «module» func10 _ initial { params := [.i64 x], locals := List.replicate 3 (.i64 0) } env
  simp only [func10]
  wp_fixed_frame
  refine wp_call_tw (negative_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  by_cases h : negative x = true
  all_goals
    repeat' ((try wp_fixed_frame [func10Def, boolWord, magnitude, h]) <;>
      (refine wp_iff_cons rfl ?_; try simp))

theorem gap_exact (env : HostEnv Unit) (initial : Store Unit) (denominator numerator direction : UInt64) :
    TerminatesWith env «module» 31 initial [.i64 direction, .i64 numerator, .i64 denominator]
      (fun final values => final = initial ∧ values = [.i64 (gap denominator numerator direction)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func31Def) rfl ?_
  change wp «module» func31 _ initial
    { params := [.i64 denominator, .i64 numerator, .i64 direction], locals := List.replicate 3 (.i64 0) } env
  simp only [func31]
  wp_fixed_frame
  refine wp_call_tw (negative_exact env initial direction) ?_
  rintro final values ⟨rfl, rfl⟩
  by_cases h : negative direction = true
  all_goals
    repeat' ((try wp_fixed_frame [func31Def, boolWord, gap, h]) <;>
      (refine wp_iff_cons rfl ?_; try simp))

theorem position_exact (env : HostEnv Unit) (initial : Store Unit) (state : ParseState)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 1 initial (parseValues state owner pointer)
      (fun final values => final = initial ∧ values = [.i64 state.position.toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 state.position.toUInt64, .i64 state.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func1, func1Def]
  simp [parseValues]

theorem parseOverlap_exact (env : HostEnv Unit) (initial : Store Unit) (state : ParseState)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 3 initial (parseValues state owner pointer)
      (fun final values => final = initial ∧ values = [.i64 state.overlap.toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_
  change wp «module» func3 _ initial
    { params := [.i64 state.position.toUInt64, .i64 state.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func3, func3Def]
  simp [parseValues]

theorem parseIncidence_exact (env : HostEnv Unit) (initial : Store Unit) (state : ParseState)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 4 initial (parseValues state owner pointer)
      (fun final values => final = initial ∧ values = [.i64 pointer, .i64 owner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_
  change wp «module» func4 _ initial
    { params := [.i64 state.position.toUInt64, .i64 state.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 2 (.i64 0) } env
  wp_fixed_frame [func4, func4Def]
  simp [parseValues]

theorem status_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 7 initial (inputValues input owner pointer)
      (fun final values => final = initial ∧ values = [.i64 input.status]) := by
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_
  change wp «module» func7 _ initial
    { params := [.i64 input.status, .i64 input.jobs.toUInt64, .i64 input.categories.toUInt64, .i64 input.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func7, func7Def]
  simp [inputValues]

theorem categories_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 14 initial (inputValues input owner pointer)
      (fun final values => final = initial ∧ values = [.i64 input.categories.toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func14Def) rfl ?_
  change wp «module» func14 _ initial
    { params := [.i64 input.status, .i64 input.jobs.toUInt64, .i64 input.categories.toUInt64, .i64 input.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func14, func14Def]
  simp [inputValues]

theorem jobs_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 15 initial (inputValues input owner pointer)
      (fun final values => final = initial ∧ values = [.i64 input.jobs.toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func15Def) rfl ?_
  change wp «module» func15 _ initial
    { params := [.i64 input.status, .i64 input.jobs.toUInt64, .i64 input.categories.toUInt64, .i64 input.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func15, func15Def]
  simp [inputValues]

theorem incidence_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 16 initial (inputValues input owner pointer)
      (fun final values => final = initial ∧ values = [.i64 pointer, .i64 owner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func16Def) rfl ?_
  change wp «module» func16 _ initial
    { params := [.i64 input.status, .i64 input.jobs.toUInt64, .i64 input.categories.toUInt64, .i64 input.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 2 (.i64 0) } env
  wp_fixed_frame [func16, func16Def]
  simp [inputValues]

theorem overlap_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 18 initial (inputValues input owner pointer)
      (fun final values => final = initial ∧ values = [.i64 input.overlap.toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func18Def) rfl ?_
  change wp «module» func18 _ initial
    { params := [.i64 input.status, .i64 input.jobs.toUInt64, .i64 input.categories.toUInt64, .i64 input.overlap.toUInt64, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func18, func18Def]
  simp [inputValues]

theorem numerators_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 8 initial (pointValues point owner pointer)
      (fun final values => final = initial ∧ values = [.i64 pointer, .i64 owner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func8Def) rfl ?_
  change wp «module» func8 _ initial
    { params := [.i64 point.denominator, .i64 owner, .i64 pointer], locals := List.replicate 2 (.i64 0) } env
  wp_fixed_frame [func8, func8Def]
  simp [pointValues]

theorem denominator_exact (env : HostEnv Unit) (initial : Store Unit) (point : Point)
    (owner pointer : UInt64) :
    TerminatesWith env «module» 11 initial (pointValues point owner pointer)
      (fun final values => final = initial ∧ values = [.i64 point.denominator]) := by
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_
  change wp «module» func11 _ initial
    { params := [.i64 point.denominator, .i64 owner, .i64 pointer], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func11, func11Def]
  simp [pointValues]

theorem basisRows_exact (env : HostEnv Unit) (initial : Store Unit) (basis : Basis)
    (rowsOwner rowsPointer columnsOwner columnsPointer : UInt64) :
    TerminatesWith env «module» 21 initial (basisValues basis rowsOwner rowsPointer columnsOwner columnsPointer)
      (fun final values => final = initial ∧ values = [.i64 rowsPointer, .i64 rowsOwner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func21Def) rfl ?_
  change wp «module» func21 _ initial
    { params := [.i64 rowsOwner, .i64 rowsPointer, .i64 columnsOwner, .i64 columnsPointer, .i64 basis.determinant], locals := List.replicate 2 (.i64 0) } env
  wp_fixed_frame [func21, func21Def]
  simp [basisValues]

theorem basisColumns_exact (env : HostEnv Unit) (initial : Store Unit) (basis : Basis)
    (rowsOwner rowsPointer columnsOwner columnsPointer : UInt64) :
    TerminatesWith env «module» 22 initial (basisValues basis rowsOwner rowsPointer columnsOwner columnsPointer)
      (fun final values => final = initial ∧ values = [.i64 columnsPointer, .i64 columnsOwner]) := by
  refine TerminatesWith.of_wp_entry_for (f := func22Def) rfl ?_
  change wp «module» func22 _ initial
    { params := [.i64 rowsOwner, .i64 rowsPointer, .i64 columnsOwner, .i64 columnsPointer, .i64 basis.determinant], locals := List.replicate 2 (.i64 0) } env
  wp_fixed_frame [func22, func22Def]
  simp [basisValues]

theorem basisDeterminant_exact (env : HostEnv Unit) (initial : Store Unit) (basis : Basis)
    (rowsOwner rowsPointer columnsOwner columnsPointer : UInt64) :
    TerminatesWith env «module» 29 initial (basisValues basis rowsOwner rowsPointer columnsOwner columnsPointer)
      (fun final values => final = initial ∧ values = [.i64 basis.determinant]) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_
  change wp «module» func29 _ initial
    { params := [.i64 rowsOwner, .i64 rowsPointer, .i64 columnsOwner, .i64 columnsPointer, .i64 basis.determinant], locals := List.replicate 1 (.i64 0) } env
  wp_fixed_frame [func29, func29Def]
  simp [basisValues]

end Project.Beck.Execution
