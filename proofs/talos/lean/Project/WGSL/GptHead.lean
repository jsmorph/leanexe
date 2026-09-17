import Project.WGSL.HeadNumerical
import Project.WGSL.Package
import Project.TinyGpt2.Decoding
import Project.Affine.Real
import Project.Affine.Numerical

namespace Project.WGSL.GptHead
open LeanExe.WGSL Project.TinyGpt2 CodeLib.IEEE64

/-- The one-row vocabulary projection selected for WGSL generation. -/
def config : GemmConfig := { rows := 1, cols := 256, inner := 4 }
def kernel : GemmImplementation := gemmCell
def candidate : KernelCandidate := ⟨config, kernel, rfl⟩
theorem config_valid : config.Valid := by decide +kernel

def rowBuffer (x : Row) : HeadNumerical.Buffer64 := fun i => rowWords x ⟨i%4, by omega⟩
def matrixBuffer (w : Array UInt64) : HeadNumerical.Buffer64 := fun i => w[Layout.head+i]!
def bias (w : Array UInt64) (j : Fin 256) : UInt64 := w[Layout.headBias+j.val]!

def separateWord (w : Array UInt64) (x : Row) (j : Fin 256) : UInt32 :=
  kernel Binary32.arithmetic config (HeadNumerical.converted (rowBuffer x))
    (HeadNumerical.converted (matrixBuffer w)) 0 j.val

def separateResult (w : Array UInt64) (x : Row) (j : Fin 256) : UInt64 :=
  HeadNumerical.finish (separateWord w x j) (bias w j)

def Result (p : Profile) (w : Array UInt64) (x : Row) (j : Fin 256) (result : UInt64) : Prop :=
  ∃ word, Dot Binary32.semantics p config (HeadNumerical.converted (rowBuffer x))
    (HeadNumerical.converted (matrixBuffer w)) 0 j.val 4 word ∧ result = HeadNumerical.finish word (bias w j)

def dispatchInput (w : Array UInt64) (x : Row) : Dispatch.Input :=
  { buffers := {
      a := HeadNumerical.converted (rowBuffer x)
      b := HeadNumerical.converted (matrixBuffer w)
      sizeA := 4, sizeB := 1024, sizeC := 256 }
    initialC := fun _ => 0x7fc00001 }

theorem dispatch_input_valid (w : Array UInt64) (x : Row) :
    (dispatchInput w x).buffers.Valid config := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- The independently checked shader computes the declared mixed head relation. -/
theorem from_dispatch {source metadata} (package : Binary32.Package source metadata)
    (shape : package.kernel.ast.config = config) (w : Array UInt64) (x : Row) (output : WordBuffer)
    (run : (Dispatch.model Binary32.semantics).Exec package.tag.profile package.kernel (dispatchInput w x) output)
    (j : Fin 256) :
    Result package.tag.profile w x j (HeadNumerical.finish (output j.val) (bias w j)) := by
  have valid : (dispatchInput w x).buffers.Valid package.kernel.ast.config := by
    rw [shape]
    exact dispatch_input_valid w x
  have hr : 0 < package.kernel.ast.config.rows := by rw [shape]; decide
  have hc : j.val < package.kernel.ast.config.cols := by rw [shape]; exact j.isLt
  have h := package.artifact.execution.corresponds (dispatchInput w x) output valid run 0 j.val hr hc
  refine ⟨output j.val, ?_, rfl⟩
  simpa only [Binary32.Package.artifact, shape, config, dispatchInput, Nat.zero_mul, Nat.zero_add] using h

theorem separate_accum (config : GemmConfig) (a b : WordBuffer) (row col k : Nat) :
    Dot Binary32.semantics restricted config a b row col k (gemmAccum Binary32.arithmetic config a b row col k) := by
  induction k with
  | zero => exact .zero
  | succ k ih =>
      exact .next ih (.separate rfl rfl rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩)

theorem separate_result (w : Array UInt64) (x : Row) (j : Fin 256) :
    Result restricted w x j (separateResult w x j) :=
  ⟨_, separate_accum config _ _ 0 j.val 4, rfl⟩

theorem restricted_exact {w x j result} (run : Result restricted w x j result) :
    result = separateResult w x j := by
  obtain ⟨word, hrun, rfl⟩ := run
  have he := hrun.restricted_exact Binary32.separate
  rw [he]
  rfl

theorem inputs (w : Array UInt64) (x : Row) (j : Fin 256)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 7)
    (hw : ∀ i, Affine.Bounded (matrixWords w Layout.head 4 256 i j) 4) :
    HeadNumerical.Inputs config (rowBuffer x) (matrixBuffer w) 0 j.val := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk
    simpa only [Affine.Bounded, config, Nat.zero_mul, Nat.zero_add, rowBuffer, Nat.mod_eq_of_lt hk] using hx ⟨k,hk⟩
  · intro k hk
    simpa only [Affine.Bounded, matrixWords, matrixBuffer, config, Nat.add_assoc] using hw ⟨k,hk⟩

theorem real_dot (w : Array UInt64) (x : Row) (j : Fin 256) :
    HeadNumerical.realDot64 config (rowBuffer x) (matrixBuffer w) 0 j.val 4 =
      Real.matrixApply (decodeMatrix w Layout.head 4 256) (decodeRow x) j := by
  simp [HeadNumerical.realDot64, config, rowBuffer, matrixBuffer, Real.matrixApply,
    decodeMatrix, decodeRow, matrixWords, Fin.sum_univ_succ]
  ring

theorem numerical {p w x j result} (run : Result p w x j result)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 7)
    (hw : ∀ i, Affine.Bounded (matrixWords w Layout.head 4 256 i j) 4)
    (hb : Affine.Bounded (bias w j) 4) :
    Finite result ∧ |value result| ≤ 166 ∧
    |value result - (Real.matrixApply (decodeMatrix w Layout.head 4 256) (decodeRow x) j + value (bias w j))| ≤
      1/10000 := by
  obtain ⟨word, hrun, rfl⟩ := run
  have hn := HeadNumerical.finish_numerical (inputs w x j hx hw) hrun hb.1 hb.2
  simpa only [real_dot] using hn

/-- Error propagation from the full hidden-state proof to every vocabulary
output. This premise is not a claim that the hidden-state theorem is complete. -/
theorem perturbed {p w x j result} (run : Result p w x j result)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 7)
    (hw : ∀ i, Affine.Bounded (matrixWords w Layout.head 4 256 i j) 4)
    (hb : Affine.Bounded (bias w j) 4) (target : Real.Row) (error : ℝ)
    (he : 0 ≤ error) (hinput : ∀ i, |decodeRow x i - target i| ≤ error) :
    Finite result ∧ |value result -
      (Real.matrixApply (decodeMatrix w Layout.head 4 256) target j + value (bias w j))| ≤
      1/10000 + 16*error := by
  have hn := numerical run hx hw hb
  have hp := Affine.Real.dot_input_perturbation (decodeRow x) target
    (fun i => decodeMatrix w Layout.head 4 256 i j) error hinput
  have hwSum : (∑ i, |decodeMatrix w Layout.head 4 256 i j|) ≤ 16 := by
    calc
      _ ≤ ∑ _ : Fin 4, (4:ℝ) := Finset.sum_le_sum (fun i _ => (hw i).2)
      _ = 16 := by norm_num
  have hp' := mul_le_mul_of_nonneg_right hwSum he
  have ht := abs_sub_le (value result)
    (Real.matrixApply (decodeMatrix w Layout.head 4 256) (decodeRow x) j + value (bias w j))
    (Real.matrixApply (decodeMatrix w Layout.head 4 256) target j + value (bias w j))
  simp only [add_sub_add_right_eq_sub] at ht
  change |Real.matrixApply (decodeMatrix w Layout.head 4 256) (decodeRow x) j -
    Real.matrixApply (decodeMatrix w Layout.head 4 256) target j| ≤ _ at hp
  exact ⟨hn.1, by linarith [hn.2.2]⟩

#print axioms from_dispatch
#print axioms restricted_exact
#print axioms numerical
#print axioms perturbed
end Project.WGSL.GptHead
