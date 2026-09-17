import Project.WGSL.ExecutionPackage

/-! Matrix coordinates and storage layout are kept separate. These lemmas
preserve the order of every scalar operation, including its operand order. -/
namespace Project.WGSL.MatrixView
open LeanExe.WGSL

abbrev Matrix := Nat → Nat → UInt32

def packed (cols : Nat) (weights : Matrix) : WordBuffer :=
  fun index => weights (index / cols) (index % cols)

theorem packed_at (cols : Nat) (weights : Matrix) (k col : Nat)
    (hc : col < cols) : packed cols weights (k * cols + col) = weights k col := by
  have hp : 0 < cols := Nat.zero_lt_of_lt hc
  have hd : (k * cols + col) / cols = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hc]
    simp
  simp [packed, hd, Nat.mod_eq_of_lt hc]

/-- A source-ordered column product over binary32 words. -/
def columnAccum (arithmetic : ScalarArithmetic) (x : WordBuffer)
    (weights : Matrix) (col : Nat) : Nat → UInt32
  | 0 => 0
  | k + 1 => arithmetic.add (columnAccum arithmetic x weights col k)
      (arithmetic.mul (x k) (weights k col))

/-- The same algorithm with the arithmetic choices made explicit at each step. -/
inductive ColumnRun (s : ScalarSemantics) (p : Profile) (x : WordBuffer)
    (weights : Matrix) (col : Nat) : Nat → UInt32 → Prop where
  | zero : ColumnRun s p x weights col 0 0
  | next {k acc result} : ColumnRun s p x weights col k acc →
      Accumulate s p acc (x k) (weights k col) result →
      ColumnRun s p x weights col (k + 1) result

theorem ColumnRun.exact {s arithmetic x weights col k result}
    (hs : SeparateInterpretation s arithmetic)
    (h : ColumnRun s restricted x weights col k result) :
    result = columnAccum arithmetic x weights col k := by
  induction h with
  | zero => rfl
  | next _ update ih => rw [update.restricted_exact hs, ih]; rfl

theorem packed_run_iff {s p config x weights col k result}
    (hc : col < config.cols) :
    Dot s p config x (packed config.cols weights) 0 col k result ↔
      ColumnRun s p x weights col k result := by
  constructor
  · intro h
    induction h with
    | zero => exact .zero
    | @next k acc result _ update ih =>
        apply ColumnRun.next ih
        simpa only [Nat.zero_mul, Nat.zero_add, packed_at _ _ _ _ hc] using update
  · intro h
    induction h with
    | zero => exact .zero
    | @next k acc result _ update ih =>
        apply Dot.next ih
        simpa only [Nat.zero_mul, Nat.zero_add, packed_at _ _ _ _ hc] using update

def input (config : GemmConfig) (x : WordBuffer) (weights : Matrix) : Dispatch.Input :=
  { buffers := {
      a := x
      b := packed config.cols weights
      sizeA := config.elementsA
      sizeB := config.elementsB
      sizeC := config.elementsC }
    initialC := fun _ => 0 }

theorem input_valid (config : GemmConfig) (x : WordBuffer) (weights : Matrix) :
    (input config x weights).buffers.Valid config :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem from_dispatch {source metadata} (package : Binary32.Package source metadata)
    (oneRow : package.kernel.ast.config.rows = 1) (x : WordBuffer) (weights : Matrix)
    (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel
      (input package.kernel.ast.config x weights) output)
    {col : Nat} (hc : col < package.kernel.ast.config.cols) :
    ColumnRun Binary32.semantics package.tag.profile x weights col
      package.kernel.ast.config.inner (output col) := by
  have hr : 0 < package.kernel.ast.config.rows := by omega
  have h := package.artifact.execution.corresponds _ output
    (input_valid _ x weights) run 0 col hr hc
  apply (packed_run_iff hc).1
  simpa only [Binary32.Package.artifact, input, Nat.zero_mul, Nat.zero_add] using h

/-- A column slice changes storage stride and output numbering, not the dot
product's inputs or arithmetic order. -/
def slice (weights : Matrix) (start : Nat) : Matrix :=
  fun k col => weights k (start + col)

theorem slice_run_iff {s p x weights start col k result} :
    ColumnRun s p x (slice weights start) col k result ↔
      ColumnRun s p x weights (start + col) k result := by
  constructor <;> intro h
  · induction h with
    | zero => exact .zero
    | next _ update ih => exact .next ih update
  · induction h with
    | zero => exact .zero
    | next _ update ih => exact .next ih update

def join (leftSize : Nat) (left right : WordBuffer) : WordBuffer :=
  fun col => if col < leftSize then left col else right (col - leftSize)

theorem join_runs {s p x weights leftSize rightSize inner left right}
    (hl : ∀ col, col < leftSize → ColumnRun s p x (slice weights 0) col inner (left col))
    (hr : ∀ col, col < rightSize → ColumnRun s p x (slice weights leftSize) col inner (right col))
    {col : Nat} (hc : col < leftSize + rightSize) :
    ColumnRun s p x weights col inner (join leftSize left right col) := by
  by_cases h : col < leftSize
  · simpa only [join, ite_eq_left h, Nat.zero_add] using slice_run_iff.mp (hl col h)
  · have hsub : col - leftSize < rightSize := by omega
    have hadd : leftSize + (col - leftSize) = col := by omega
    simpa only [join, ite_eq_right h, hadd] using slice_run_iff.mp (hr (col-leftSize) hsub)

end Project.WGSL.MatrixView
