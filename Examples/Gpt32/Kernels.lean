import Examples.Gpt32.Module
import Project.WGSL.Build
import Project.WGSL.RoundTrip
import Project.ProofKit.F32Bits
import Project.ProofKit.F32Nearest
import Project.IR.Read

/-!
The WGSL kernels of the binary32 GPT-2, translated from their compiled IR, with their element
lemmas and dispatch theorems.
-/

namespace Examples.Gpt32

open Project.IR Project.WGSL Project.ProofKit Examples.Gpt32

/-- The words of an array of binary32 values. -/
abbrev floatWords (x : Array Float32) : Array UInt64 := x.map fun v : Float32 => v.toBits.toUInt64

/-- A product of a word and `2^23`, read as binary32, has no fraction bits, so it is no NaN. -/
theorem isNaN_pow23 (w : UInt64) : Wasm.IEEE32.isNaN (w * 8388608).toUInt32 = false := by
  simp only [Wasm.IEEE32.isNaN, Wasm.IEEE32.fraction, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
    beq_iff_eq, UInt64.toNat_toUInt32, UInt64.toNat_mul, UInt64.reduceToNat]
  right
  omega

theorem ite_some {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

theorem denote_assign_f32 {arrays : Nat → Option (Array UInt64)} {L : Nat → Option Wasm.Value}
    {j : Nat} {e : Project.IR.Expr .f32} {v : UInt32} (hj : arrays j = none)
    (he : e.denote L arrays = some v) :
    (Project.IR.Stmt.assign j e).denote arrays L =
      some (fun i => if i = j then some (.f32 v) else L i) := by
  simp [Project.IR.Stmt.denote, hj, he, ScalarType.value]

theorem denote_assign_u64 {arrays : Nat → Option (Array UInt64)} {L : Nat → Option Wasm.Value}
    {j : Nat} {e : Project.IR.Expr .u64} {v : UInt64} (hj : arrays j = none)
    (he : e.denote L arrays = some v) :
    (Project.IR.Stmt.assign j e).denote arrays L =
      some (fun i => if i = j then some (.i64 v) else L i) := by
  simp [Project.IR.Stmt.denote, hj, he, ScalarType.value]

theorem denote_seq_some {arrays : Nat → Option (Array UInt64)} {L L1 : Nat → Option Wasm.Value}
    {a b : Project.IR.Stmt} (ha : a.denote arrays L = some L1) :
    (Project.IR.Stmt.seq a b).denote arrays L = b.denote arrays L1 := by
  simp [Project.IR.Stmt.denote, ha]

/-- A Taylor polynomial in Horner form over local `r`, with binary32 coefficients. -/
def hornerIR (r : Nat) : List UInt32 → UInt32 → Project.IR.Expr .f32
  | [], last => .constF32 last
  | c :: cs, last => .binF32 .add (.constF32 c) (.binF32 .mul (.getF32 r) (hornerIR r cs last))

/-- The statements of `exp32` at the element of `expArray32`'s build, locals 5 to 11. -/
def expBody : Project.IR.Stmt :=
  let x : Project.IR.Expr .f32 := .ofBits32 (.read 0 (.get 4))
  let n104 : Project.IR.Expr .f32 := .binF32 .sub (.constF32 2147483648) (.constF32 1120927744)
  .seq (.assign 5 (.iteF32 (.leF32 x (.constF32 1118961664)) x (.constF32 1118961664))) <|
  .seq (.assign 6 (.iteF32 (.leF32 n104 (.getF32 5)) (.getF32 5) n104)) <|
  .seq (.assign 7 (.unF32 .nearest (.binF32 .mul (.getF32 6) (.constF32 1069066811)))) <|
  .seq (.assign 8 (.binF32 .add (.binF32 .sub (.getF32 6) (.binF32 .mul (.getF32 7)
    (.constF32 1060208640))) (.binF32 .mul (.getF32 7) (.constF32 962494595)))) <|
  .seq (.assign 9 (hornerIR 8 [1065353216, 1065353216, 1056964608, 1042983595, 1026206379,
    1007192201, 985008993] 961547521)) <|
  .seq (.assign 10 (.bin .sub (.toBits32 (.binF32 .add (.getF32 7) (.constF32 1262485504)))
    (.const 1262485250)))
    (.assign 11 (.bin .divU (.get 10) (.const 2)))

/-- The element of `expArray32`'s build. -/
def expElement : Project.IR.Expr .u64 :=
  .toBits32 (.binF32 .mul (.binF32 .mul (.getF32 9) (.ofBits32 (.bin .mul (.get 11) (.const 8388608))))
    (.ofBits32 (.bin .mul (.bin .sub (.get 10) (.get 11)) (.const 8388608))))

theorem expArray32_body : gpt32.expArray32.ir.body =
    .seq (.arraySize 1 0) (.buildWith 2 3 4 (.get 1) expBody expElement) := rfl

theorem expElement_denote (x : Array Float32) (k : UInt64) (L : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (h4 : L 4 = some (.i64 k))
    (h0 : arrays 0 = some (floatWords x)) (hn : ∀ j, 5 ≤ j → j ≤ 11 → arrays j = none) :
    ∃ L', expBody.denote arrays L = some L' ∧
      expElement.denote L' arrays = some (exp32 x[k.toNat]!).toBits.toUInt64 := by
  have h89 : (89.0 : Float32).toBits = 1118961664 := by decide +kernel
  have h104 : (104.0 : Float32).toBits = 1120927744 := by decide +kernel
  have hlog : (1.44269502162933349609375 : Float32).toBits = 1069066811 := by decide +kernel
  have hhi : (0.693359375 : Float32).toBits = 1060208640 := by decide +kernel
  have hlo : (0.000212194441701285541057586669921875 : Float32).toBits = 962494595 := by
    decide +kernel
  have h1 : (1.0 : Float32).toBits = 1065353216 := by decide +kernel
  have h05 : (0.5 : Float32).toBits = 1056964608 := by decide +kernel
  have hc3 : (0.16666667163372039794921875 : Float32).toBits = 1042983595 := by decide +kernel
  have hc4 : (0.0416666679084300994873046875 : Float32).toBits = 1026206379 := by decide +kernel
  have hc5 : (0.008333333767950534820556640625 : Float32).toBits = 1007192201 := by
    decide +kernel
  have hc6 : (0.001388888922519981861114501953125 : Float32).toBits = 985008993 := by
    decide +kernel
  have hc7 : (0.000198412701138295233249664306640625 : Float32).toBits = 961547521 := by
    decide +kernel
  have hM : (12582912.0 : Float32).toBits = 1262485504 := by decide +kernel
  -- The binary32 values of `exp32`'s steps, as bits.
  generalize hxv : x[k.toNat]! = xv
  have hread : (Project.IR.Expr.ofBits32 (.read 0 (.get 4))).denote L arrays = some xv.toBits := by
    simp [Project.IR.Expr.denote, h0, h4, floatWords, getElem!_map_toBits32, hxv]
  have hn104 : (Project.IR.Expr.binF32 .sub (.constF32 2147483648) (.constF32 1120927744)).denote
      L arrays = some (-104.0 : Float32).toBits := by
    simp [Project.IR.Expr.denote, F32Op.apply, F32Bits.toBits_neg, h104]
  let a : Float32 := if xv ≤ 89.0 then xv else 89.0
  let c : Float32 := if -104.0 ≤ a then a else -104.0
  let kf : Float32 := LeanExe.Float32.nearest (c * 1.44269502162933349609375)
  let r : Float32 := c - kf * 0.693359375 + kf * 0.000212194441701285541057586669921875
  let pv : Float32 := 1.0 + r * (1.0 + r * (0.5 + r * (0.16666667163372039794921875 +
    r * (0.0416666679084300994873046875 + r * (0.008333333767950534820556640625 +
    r * (0.001388888922519981861114501953125 + r * 0.000198412701138295233249664306640625))))))
  let m : UInt64 := (kf + 12582912.0).toBits.toUInt64 - 1262485250
  let h : UInt64 := m / 2
  let L5 : Nat → Option Wasm.Value := fun i => if i = 5 then some (.f32 a.toBits) else L i
  let L6 : Nat → Option Wasm.Value := fun i => if i = 6 then some (.f32 c.toBits) else L5 i
  let L7 : Nat → Option Wasm.Value := fun i => if i = 7 then some (.f32 kf.toBits) else L6 i
  let L8 : Nat → Option Wasm.Value := fun i => if i = 8 then some (.f32 r.toBits) else L7 i
  let L9 : Nat → Option Wasm.Value := fun i => if i = 9 then some (.f32 pv.toBits) else L8 i
  let L10 : Nat → Option Wasm.Value := fun i => if i = 10 then some (.i64 m) else L9 i
  let L11 : Nat → Option Wasm.Value := fun i => if i = 11 then some (.i64 h) else L10 i
  have s5 : (Project.IR.Stmt.assign 5 (.iteF32 (.leF32 (.ofBits32 (.read 0 (.get 4)))
      (.constF32 1118961664)) (.ofBits32 (.read 0 (.get 4))) (.constF32 1118961664))).denote
      arrays L = some L5 := by
    refine denote_assign_f32 (hn 5 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, h0, h4, floatWords, getElem!_map_toBits32, hxv,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, ite_some]
    simp only [a, apply_ite Float32.toBits, F32Bits.le_iff, h89]
  have s6 : (Project.IR.Stmt.assign 6 (.iteF32 (.leF32 (.binF32 .sub (.constF32 2147483648)
      (.constF32 1120927744)) (.getF32 5)) (.getF32 5) (.binF32 .sub (.constF32 2147483648)
      (.constF32 1120927744)))).denote arrays L5 = some L6 := by
    refine denote_assign_f32 (hn 6 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, L5, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, F32Op.apply, ite_some]
    simp only [c, apply_ite Float32.toBits, F32Bits.le_iff, F32Bits.toBits_neg, h104]
  have s7 : (Project.IR.Stmt.assign 7 (.unF32 .nearest (.binF32 .mul (.getF32 6)
      (.constF32 1069066811)))).denote arrays L6 = some L7 := by
    refine denote_assign_f32 (hn 7 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, L6, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.map_some, F32Op.apply, F32UnOp.apply]
    simp only [kf, F32Nearest.toBits_nearest, F32Bits.toBits_mul, hlog]
  have s8 : (Project.IR.Stmt.assign 8 (.binF32 .add (.binF32 .sub (.getF32 6) (.binF32 .mul
      (.getF32 7) (.constF32 1060208640))) (.binF32 .mul (.getF32 7)
      (.constF32 962494595)))).denote arrays L7 = some L8 := by
    refine denote_assign_f32 (hn 8 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, L7, L6, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, F32Op.apply, show (6 : Nat) ≠ 7 by decide]
    simp only [r, F32Bits.toBits_add, F32Bits.toBits_sub, F32Bits.toBits_mul, hhi, hlo]
  have s9 : (Project.IR.Stmt.assign 9 (hornerIR 8 [1065353216, 1065353216, 1056964608,
      1042983595, 1026206379, 1007192201, 985008993] 961547521)).denote arrays L8 = some L9 := by
    refine denote_assign_f32 (hn 9 (by omega) (by omega)) ?_
    simp only [hornerIR, Project.IR.Expr.denote, L8, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, F32Op.apply]
    simp only [pv, F32Bits.toBits_add, F32Bits.toBits_mul, h1, h05, hc3, hc4, hc5, hc6, hc7]
  have s10 : (Project.IR.Stmt.assign 10 (.bin .sub (.toBits32 (.binF32 .add (.getF32 7)
      (.constF32 1262485504))) (.const 1262485250))).denote arrays L9 = some L10 := by
    refine denote_assign_u64 (hn 10 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, L9, L8, L7, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.map_some, F32Op.apply, U64Op.apply,
      show (7 : Nat) ≠ 9 by decide, show (7 : Nat) ≠ 8 by decide]
    simp only [m, F32Bits.toBits_add, hM]
  have s11 : (Project.IR.Stmt.assign 11 (.bin .divU (.get 10) (.const 2))).denote arrays L10 =
      some L11 := by
    refine denote_assign_u64 (hn 11 (by omega) (by omega)) ?_
    simp only [Project.IR.Expr.denote, L10, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, U64Op.apply, show (2 : UInt64) ≠ 0 by decide]
    rfl
  refine ⟨L11, ?_, ?_⟩
  · rw [expBody, denote_seq_some s5, denote_seq_some s6, denote_seq_some s7, denote_seq_some s8,
      denote_seq_some s9, denote_seq_some s10]
    exact s11
  · show expElement.denote L11 arrays =
      some (pv * Float32.ofBits (h * 8388608).toUInt32 *
        Float32.ofBits ((m - h) * 8388608).toUInt32).toBits.toUInt64
    simp only [expElement, Project.IR.Expr.denote, L11, L10, L9, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.map_some, F32Op.apply, U64Op.apply,
      show (9 : Nat) ≠ 11 by decide, show (9 : Nat) ≠ 10 by decide,
      show (10 : Nat) ≠ 11 by decide]
    rw [F32Bits.toBits_mul, F32Bits.toBits_mul, F32Bits.toBits_ofBits, F32Bits.toBits_ofBits,
      isNaN_pow23, isNaN_pow23]
    rfl

def expSpec : Spec :=
  { kinds := [.array], index := 4, count := .size 1 0,
    vars := [(5, .f32), (6, .f32), (7, .f32), (8, .f32), (9, .f32), (10, .u64), (11, .u64)],
    width := 12, body := expBody, element := expElement }

theorem expSpec_wf : expSpec.WF := expSpec.wf_of_wfb (by decide)

def expKernel : Module := (expSpec.module).getD ⟨0, 0, []⟩

theorem expSpec_module : expSpec.module = some expKernel := rfl

theorem expKernel_text : Module.parse expKernel.print = some expKernel :=
  Module.parse_print_of_wfb _ (by decide +kernel)

/-- The kernel computes `expArray32 x`: with a buffer holding `x`, an output of the result's size
whose length word the host has written, and at least `x.size` invocations, the output ends
holding the result as a Wasm array, and distinct invocations store to distinct words. -/
theorem expKernel_dispatch (x : Array Float32) (hx : x.size < 2 ^ 29) (output : Array UInt32)
    (hOut : output.size = 2 + 2 * x.size) (hL0 : output[0]? = some (UInt32.ofNat x.size))
    (hL1 : output[1]? = some 0) (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    expKernel.dispatch [(Arg.array (floatWords x)).buffer] output count =
        some (arrayWords (floatWords (expArray32 x))) ∧
      expKernel.RaceFree [(Arg.array (floatWords x)).buffer] output.size count := by
  have hfits : expSpec.Fits [.array (floatWords x)] (floatWords x).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using hx⟩
  have h := expSpec.dispatch_eq expSpec_wf expKernel expSpec_module _ _ hfits
    (fun i => (exp32 x[i.toNat]!).toBits.toUInt64)
    (fun k _ => expElement_denote x _ _ _ (by simp [Spec.locals, expSpec])
      (by simp [Spec.arrays])
      (fun j h1 h2 => by simp only [Spec.arrays]; rw [List.getElem?_eq_none (by simp; omega)]))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (expArray32 x) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (exp32 x[i.toNat]!).toBits.toUInt64) by
      simp [expArray32, floatWords, Project.IR.build_map]]
  exact h

end Examples.Gpt32
