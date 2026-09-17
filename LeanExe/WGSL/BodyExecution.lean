import LeanExe.WGSL.BodyParse
import LeanExe.WGSL.StatementProof
import LeanExe.WGSL.Index

/-! Whole-invocation semantics for the statement subset. The parser checks the
bindings, early-return guard, entry point and sole output store. This semantics
executes that guard and store with u32 operands and checks the buffer lengths.
Scalar operations are interpreted by the same explicit arithmetic as the Lean
source; no assertion about a particular WebGPU implementation is assumed here. -/
namespace LeanExe.WGSL.Statement
open Source

structure Write where
  address : Nat
  value : UInt32
  deriving Repr, BEq, DecidableEq

def ShapeValid (shape : Shape) : Prop :=
  0 < shape.rows ∧ 0 < shape.cols ∧
  shape.rows ≤ 524280 ∧ shape.cols ≤ 524280 ∧
  0 < shape.elementsA ∧ 0 < shape.elementsB ∧
  shape.elementsA ≤ 33554432 ∧ shape.elementsB ≤ 33554432 ∧
  shape.rows * shape.cols ≤ 33554432

instance (shape) : Decidable (ShapeValid shape) := inferInstanceAs (Decidable (_ ∧ _))

def invoke (parsed : Parsed) (ar : ScalarArithmetic) (memory : Memory) (sizeC : Nat)
    (row col : UInt32) : Except Error (Option Write) := do
  if col ≥ UInt32.ofNat parsed.cols ∨ row ≥ UInt32.ofNat parsed.rows then return none
  let word ← parsed.code.run ar memory row col [] []
  let address := (row * UInt32.ofNat parsed.cols + col).toNat
  if address < sizeC then return some ⟨address, word⟩
  else throw (.storeC address)

inductive ShaderError where
  | parse (message : String)
  | execution (error : Error)
  deriving Repr, BEq, DecidableEq

def runShader (shader : String) (ar : ScalarArithmetic) (memory : Memory) (sizeC : Nat)
    (row col : UInt32) : Except ShaderError (Option Write) := do
  let parsed ← (Source.parse shader).mapError ShaderError.parse
  (invoke parsed ar memory sizeC row col).mapError ShaderError.execution

def expected (shape : Shape) (source : Source.Kernel) (ar : ScalarArithmetic)
    (memory : Memory) (row col : UInt32) : Option Write :=
  if row.toNat < shape.rows ∧ col.toNat < shape.cols then
    some ⟨row.toNat * shape.cols + col.toNat,
      source ar memory.a memory.b row.toNat col.toNat⟩
  else none

/-- All invocations, all buffer words, and every supplied scalar interpretation.
An `.ok` result rules out local, load, store and loop-budget errors. Inactive
invocations return without touching memory. -/
def Implements (shader : String) (shape : Shape) (source : Source.Kernel) : Prop :=
  ∀ (ar : ScalarArithmetic) (memory : Memory) (sizeC : Nat) (row col : UInt32),
    shape.elementsA ≤ memory.sizeA → shape.elementsB ≤ memory.sizeB →
    shape.rows * shape.cols ≤ sizeC →
    runShader shader ar memory sizeC row col = .ok (expected shape source ar memory row col)

theorem invoke_eq (shape : Shape) (code : Code) (source : Source.Kernel)
    (hs : ShapeValid shape) (hv : code.Valid shape [] 0)
    (he : source = code.term.kernel)
    (ar : ScalarArithmetic) (memory : Memory) (sizeC : Nat) (row col : UInt32)
    (ha : shape.elementsA ≤ memory.sizeA) (hb : shape.elementsB ≤ memory.sizeB)
    (hout : shape.rows * shape.cols ≤ sizeC) :
    invoke ⟨shape.rows, shape.cols, code⟩ ar memory sizeC row col =
      .ok (expected shape source ar memory row col) := by
  have hrows : (UInt32.ofNat shape.rows).toNat = shape.rows :=
    UInt32.toNat_ofNat_of_lt' (by change shape.rows < 4294967296; have := hs.2.2.1; omega)
  have hcols : (UInt32.ofNat shape.cols).toNat = shape.cols :=
    UInt32.toNat_ofNat_of_lt' (by change shape.cols < 4294967296; have := hs.2.2.2.1; omega)
  by_cases active : row.toNat < shape.rows ∧ col.toNat < shape.cols
  · have guard : ¬ (col ≥ UInt32.ofNat shape.cols ∨ row ≥ UInt32.ofNat shape.rows) := by
      simp only [UInt32.le_iff_toNat_le, hcols, hrows]
      omega
    have hc := LeanExe.WGSL.Index.linear_lt active.1 active.2
    have hsize : shape.rows * shape.cols ≤ 33554432 := hs.2.2.2.2.2.2.2.2
    have address : (row * UInt32.ofNat shape.cols + col).toNat =
        row.toNat * shape.cols + col.toNat := by
      have h := LeanExe.WGSL.Index.word_index
        (row := row.toNat) (stride := shape.cols) (col := col.toNat)
        (by have := row.toNat_lt; change row.toNat < 4294967296 at this; omega)
        (by have := hs.2.2.2.1; omega)
        (by have := col.toNat_lt; change col.toNat < 4294967296 at this; omega)
        (by omega)
      simpa only [UInt32.ofNat_toNat] using h
    have run := code.run_eq ar memory row col [] [] active.1 active.2 ha hb
      (by intro i n h; cases i <;> simp at h) hv
    simp only [invoke, guard, ↓reduceIte, run, bind, Except.bind, address]
    rw [ite_eq_left (by omega)]
    simp [expected, active, he, Term.kernel, pure, Except.pure]
  · have guard : col ≥ UInt32.ofNat shape.cols ∨ row ≥ UInt32.ofNat shape.rows := by
      simp only [UInt32.le_iff_toNat_le, hcols, hrows]
      omega
    simp [invoke, guard, expected, active, pure, Except.pure]

theorem shader_implements (shader : String) (shape : Shape) (code : Code) (source : Source.Kernel)
    (hp : Source.parse shader = .ok ⟨shape.rows, shape.cols, code⟩)
    (hs : ShapeValid shape) (hv : code.Valid shape [] 0)
    (he : source = code.term.kernel) : Implements shader shape source := by
  intro ar memory sizeC row col ha hb hout
  simp only [runShader, hp, Except.mapError, bind, Except.bind]
  rw [invoke_eq shape code source hs hv he ar memory sizeC row col ha hb hout]

/-- Distinct active invocations have distinct output addresses. All input
bindings are read-only and the grammar permits only this final output store. -/
theorem stores_disjoint {shape : Shape} {r₁ r₂ c₁ c₂ : Nat}
    (hc₁ : c₁ < shape.cols) (hc₂ : c₂ < shape.cols)
    (different : r₁ ≠ r₂ ∨ c₁ ≠ c₂) :
    r₁ * shape.cols + c₁ ≠ r₂ * shape.cols + c₂ := by
  intro same
  obtain ⟨hr, hc⟩ := LeanExe.WGSL.Index.linear_injective hc₁ hc₂ same
  rcases different with h | h <;> contradiction

/-- The declared 8×8 workgroups cover every active cell, including edge tiles. -/
theorem dispatch_covers {shape : Shape} {row col : Nat}
    (hr : row < shape.rows) (hc : col < shape.cols) :
    row / 8 < ceilDiv shape.rows 8 ∧ col / 8 < ceilDiv shape.cols 8 ∧
    row % 8 < 8 ∧ col % 8 < 8 ∧
    row / 8 * 8 + row % 8 = row ∧ col / 8 * 8 + col % 8 = col := by
  obtain ⟨rgroup, rlocal, req⟩ := LeanExe.WGSL.Index.invocation_covered (by decide : 0 < 8) hr
  obtain ⟨cgroup, clocal, ceq⟩ := LeanExe.WGSL.Index.invocation_covered (by decide : 0 < 8) hc
  exact ⟨rgroup, cgroup, rlocal, clocal, req, ceq⟩

end LeanExe.WGSL.Statement
