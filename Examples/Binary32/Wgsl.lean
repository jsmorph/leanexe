import LeanExe.WGSL.Build
import LeanExe.WGSL.RoundTrip
import Examples.Binary32.Verify

/-!
The kernels of `scale32`, `axpyArray32`, `matVec32`, and `condMix32`, translated from their
compiled IR.  Each
kernel's dispatch theorem comes from `Spec.dispatch_eq` and the element lemma that the function's
Wasm proof uses, and its text theorem from `Module.parse_print_of_wfb`.
-/

namespace Examples.Binary32

open LeanExe.IR LeanExe.WGSL LeanExe.ProofKit Examples.Binary32

def scaleSpec : Spec :=
  { kinds := [.float, .array], index := 5, count := .size 2 1, vars := [], width := 6,
    body := .skip, element := scaleElement }

def axpyArraySpec : Spec :=
  { kinds := [.float, .array, .array], index := 6, count := .size 3 1, vars := [], width := 7,
    body := .skip, element := axpyArrayElement }

def matVecSpec : Spec :=
  { kinds := [.array, .array, .word, .word], index := 6, count := .param 2,
    vars := [(7, .f32), (8, .u64), (9, .u64), (10, .f32)], width := 11, body := matVecBody,
    element := matVecElement }

/-- The compiled bodies are the build shapes the specifications describe. -/
theorem scaleSpec_body : binary32.scale32.ir.body =
    .seq (.arraySize 2 1) (.buildWith 3 4 scaleSpec.index (.get 2) scaleSpec.body
      scaleSpec.element) := rfl

theorem axpyArraySpec_body : binary32.axpyArray32.ir.body =
    .seq (.arraySize 3 1) (.buildWith 4 5 axpyArraySpec.index (.get 3) axpyArraySpec.body
      axpyArraySpec.element) := rfl

theorem matVecSpec_body : binary32.matVec32.ir.body =
    .buildWith 4 5 matVecSpec.index (.get 2) matVecSpec.body matVecSpec.element := rfl

theorem scaleSpec_wf : scaleSpec.WF := scaleSpec.wf_of_wfb (by decide)

theorem axpyArraySpec_wf : axpyArraySpec.WF := axpyArraySpec.wf_of_wfb (by decide)

theorem matVecSpec_wf : matVecSpec.WF := matVecSpec.wf_of_wfb (by decide)

def scaleKernel : Module := (scaleSpec.module).getD ⟨0, 0, []⟩

def axpyArrayKernel : Module := (axpyArraySpec.module).getD ⟨0, 0, []⟩

def matVecKernel : Module := (matVecSpec.module).getD ⟨0, 0, []⟩

theorem scaleSpec_module : scaleSpec.module = some scaleKernel := rfl

theorem axpyArraySpec_module : axpyArraySpec.module = some axpyArrayKernel := rfl

theorem matVecSpec_module : matVecSpec.module = some matVecKernel := rfl

theorem scaleKernel_text : Module.parse scaleKernel.print = some scaleKernel :=
  Module.parse_print_of_wfb _ (by decide)

theorem axpyArrayKernel_text : Module.parse axpyArrayKernel.print = some axpyArrayKernel :=
  Module.parse_print_of_wfb _ (by decide)

theorem matVecKernel_text : Module.parse matVecKernel.print = some matVecKernel :=
  Module.parse_print_of_wfb _ (by decide)

/-- The words of an array of binary32 values. -/
abbrev floatWords (x : Array Float32) : Array UInt64 := x.map fun v : Float32 => v.toBits.toUInt64

/-- The kernel computes `scale32 a x`: with buffers holding `a` and `x`, an output of the result's
size whose length word the host has written, and at least `x.size` invocations, the output ends
holding the result as a Wasm array, and distinct invocations store to distinct words. -/
theorem scaleKernel_dispatch (a : Float32) (x : Array Float32) (hx : x.size < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    scaleKernel.dispatch [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer] output
        count = some (arrayWords (floatWords (scale32 a x))) ∧
      scaleKernel.RaceFree [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer]
        output.size count := by
  have hfits : scaleSpec.Fits [.float a.toBits, .array (floatWords x)] (floatWords x).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using hx⟩
  have h := scaleSpec.dispatch_eq scaleSpec_wf scaleKernel scaleSpec_module _ _ hfits
    (fun i => (a * x[i.toNat]!).toBits.toUInt64)
    (fun k hk => by
      simp only [floatWords, Array.size_map] at hk
      have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
      refine ⟨_, rfl, ?_⟩
      rw [hkn]
      exact scaleElement_denote a x k (by omega) _ _ (by simp [Spec.locals, scaleSpec, Count.sizeLocal?])
        (by simp [Spec.locals, scaleSpec]) (by simp [Spec.arrays]))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (scale32 a x) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (a * x[i.toNat]!).toBits.toUInt64) by
      simp [scale32, floatWords, build_map]]
  exact h

/-- The kernel computes `axpyArray32 a x y`, under the conditions of `scaleKernel_dispatch`. -/
theorem axpyArrayKernel_dispatch (a : Float32) (x y : Array Float32) (hx : x.size < 2 ^ 29)
    (hy : y.size < 2 ^ 29) (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    axpyArrayKernel.dispatch [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer,
        (Arg.array (floatWords y)).buffer] output count =
        some (arrayWords (floatWords (axpyArray32 a x y))) ∧
      axpyArrayKernel.RaceFree [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer,
        (Arg.array (floatWords y)).buffer] output.size count := by
  have hfits : axpyArraySpec.Fits [.float a.toBits, .array (floatWords x), .array (floatWords y)]
      (floatWords x).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using hx⟩
  have h := axpyArraySpec.dispatch_eq axpyArraySpec_wf axpyArrayKernel axpyArraySpec_module _ _
    hfits (fun i => (a * x[i.toNat]! + y[i.toNat]!).toBits.toUInt64)
    (fun k hk => by
      simp only [floatWords, Array.size_map] at hk
      have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
      refine ⟨_, rfl, ?_⟩
      rw [hkn]
      exact axpyArrayElement_denote a x y k (by omega) _ _ (by simp [Spec.locals, axpyArraySpec, Count.sizeLocal?])
        (by simp [Spec.locals, axpyArraySpec]) (by simp [Spec.arrays]) (by simp [Spec.arrays]))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (axpyArray32 a x y) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (a * x[i.toNat]! + y[i.toNat]!).toBits.toUInt64) by
      simp [axpyArray32, floatWords, build_map]]
  exact h

/-- The kernel computes `matVec32 m v rows cols`: with buffers holding `m`, `v`, `rows`, and
`cols`, an output of the result's size whose length word the host has written, and at least
`rows` invocations, the output ends holding the result as a Wasm array, and distinct invocations
store to distinct words. -/
theorem matVecKernel_dispatch (m v : Array Float32) (rows cols : UInt64) (hm : m.size < 2 ^ 29)
    (hv : v.size < 2 ^ 29) (hrows : rows.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * rows.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat rows.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : rows.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    matVecKernel.dispatch [(Arg.array (floatWords m)).buffer, (Arg.array (floatWords v)).buffer,
        (Arg.word rows).buffer, (Arg.word cols).buffer] output count =
        some (arrayWords (floatWords (matVec32 m v rows cols))) ∧
      matVecKernel.RaceFree [(Arg.array (floatWords m)).buffer, (Arg.array (floatWords v)).buffer,
        (Arg.word rows).buffer, (Arg.word cols).buffer] output.size count := by
  have hfits : matVecSpec.Fits [.array (floatWords m), .array (floatWords v), .word rows,
      .word cols] rows.toNat :=
    ⟨rfl, by simp; omega, by simp [matVecSpec], hrows⟩
  have h := matVecSpec.dispatch_eq matVecSpec_wf matVecKernel matVecSpec_module _ _ hfits
    (fun r => (row32 m v cols r).toBits.toUInt64)
    (fun k _ => matVecRow_denote m v cols (UInt64.ofNat k) _ _
      (by simp [Spec.locals, matVecSpec, Count.sizeLocal?])
      (by simp [Spec.locals, matVecSpec])
      (by simp [Spec.arrays]) (by simp [Spec.arrays])
      (fun j h1 h2 => by
        simp only [Spec.arrays]
        rw [List.getElem?_eq_none (by simp; omega)]))
    output hOut hL0 hL1 count hCover h32
  simp only [List.map_cons, List.map_nil, UInt64.ofNat_toNat] at h
  rw [show floatWords (matVec32 m v rows cols) = LeanExe.build rows
    (fun r => (row32 m v cols r).toBits.toUInt64) by
      simp [matVec32_eq, floatWords, build_map]]
  exact h

/-- The element of `condMix32`'s build. -/
def condMixElement : LeanExe.IR.Expr .u64 :=
  let xi : LeanExe.IR.Expr .f32 := .ofBits32 (.read 0 (.get 7))
  let q : LeanExe.IR.Expr .u64 := .bin .divU (.get 7) (.const 4)
  let r : LeanExe.IR.Expr .u64 := .bin .remU (.get 7) (.const 4)
  let j : LeanExe.IR.Expr .u64 := .bin .add (.bin .mul q (.const 4)) (.bin .sub (.const 3) r)
  let mx : LeanExe.IR.Expr .f32 := .iteF32 (.leF32 (.getF32 1) xi) xi (.getF32 1)
  .toBits32 (.iteF32 (.ltF32 xi (.getF32 1))
    (.iteF32 (.and (.leU r (.const 3)) (.ltU j (.get 3))) (.ofBits32 (.read 0 j)) mx)
    (.iteF32 (.leF32 (.getF32 2) xi) (.getF32 2) mx))

def condMixSpec : Spec :=
  { kinds := [.array, .float, .float, .word], index := 7, count := .size 4 0, vars := [],
    width := 8, body := .skip, element := condMixElement }

theorem condMixSpec_body : binary32.condMix32.ir.body =
    .seq (.arraySize 4 0) (.buildWith 5 6 condMixSpec.index (.get 4) condMixSpec.body
      condMixSpec.element) := rfl

theorem condMixSpec_wf : condMixSpec.WF := condMixSpec.wf_of_wfb (by decide)

def condMixKernel : Module := (condMixSpec.module).getD ⟨0, 0, []⟩

theorem condMixSpec_module : condMixSpec.module = some condMixKernel := rfl

theorem condMixKernel_text : Module.parse condMixKernel.print = some condMixKernel :=
  Module.parse_print_of_wfb _ (by decide)

/-- Element `i` of `condMix32 x lo hi n`. -/
def condMixAt (x : Array Float32) (lo hi : Float32) (n i : UInt64) : Float32 :=
  if x[i.toNat]! < lo then
    (if i % 4 ≤ 3 ∧ i / 4 * 4 + (3 - i % 4) < n then x[(i / 4 * 4 + (3 - i % 4)).toNat]!
    else max lo x[i.toNat]!)
  else if hi ≤ x[i.toNat]! then hi else max lo x[i.toNat]!

theorem condMixElement_denote (x : Array Float32) (lo hi : Float32) (n i : UInt64)
    (locals : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (h1 : locals 1 = some (.f32 lo.toBits)) (h2 : locals 2 = some (.f32 hi.toBits))
    (h3 : locals 3 = some (.i64 n)) (h7 : locals 7 = some (.i64 i))
    (h0 : arrays 0 = some (floatWords x)) :
    condMixElement.denote locals arrays = some (condMixAt x lo hi n i).toBits.toUInt64 := by
  simp only [condMixElement, condMixAt, Expr.denote, h1, h2, h3, h7, h0, floatWords,
    getElem!_map_toBits32, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_some, Option.some.injEq]
  simp only [U64Op.apply, show (4 : UInt64) ≠ 0 by decide, ↓reduceIte]
  generalize i / 4 * 4 + (3 - i % 4) = j
  generalize x[j.toNat]! = xj
  generalize x[i.toNat]! = xi
  simp only [F32Bits.lt_iff, F32Bits.le_iff, apply_ite Float32.toBits, F32Bits.toBits_max]
  cases ha : Wasm.IEEE32.lt xi.toBits lo.toBits <;>
    cases hb : Wasm.IEEE32.le lo.toBits xi.toBits <;>
    cases hc : Wasm.IEEE32.le hi.toBits xi.toBits <;>
    by_cases hd1 : i % 4 ≤ 3 <;> by_cases hd2 : j < n <;>
    simp [ha, hb, hc, hd1, hd2]

/-- The kernel computes `condMix32 x lo hi n`, under the conditions of `scaleKernel_dispatch`. -/
theorem condMixKernel_dispatch (x : Array Float32) (lo hi : Float32) (n : UInt64)
    (hx : x.size < 2 ^ 29) (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    condMixKernel.dispatch [(Arg.array (floatWords x)).buffer, (Arg.float lo.toBits).buffer,
        (Arg.float hi.toBits).buffer, (Arg.word n).buffer] output count =
        some (arrayWords (floatWords (condMix32 x lo hi n))) ∧
      condMixKernel.RaceFree [(Arg.array (floatWords x)).buffer, (Arg.float lo.toBits).buffer,
        (Arg.float hi.toBits).buffer, (Arg.word n).buffer] output.size count := by
  have hfits : condMixSpec.Fits [.array (floatWords x), .float lo.toBits, .float hi.toBits,
      .word n] (floatWords x).size :=
    ⟨rfl, by simp; omega, ⟨_, rfl, rfl⟩, by simpa using hx⟩
  have h := condMixSpec.dispatch_eq condMixSpec_wf condMixKernel condMixSpec_module _ _ hfits
    (fun i => (condMixAt x lo hi n i).toBits.toUInt64)
    (fun k _ => ⟨_, rfl, condMixElement_denote x lo hi n _ _ _
      (by simp [Spec.locals, condMixSpec, Count.sizeLocal?])
      (by simp [Spec.locals, condMixSpec, Count.sizeLocal?])
      (by simp [Spec.locals, condMixSpec, Count.sizeLocal?])
      (by simp [Spec.locals, condMixSpec])
      (by simp [Spec.arrays])⟩)
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (condMix32 x lo hi n) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (condMixAt x lo hi n i).toBits.toUInt64) by
      simp [condMix32, floatWords, build_map, condMixAt]]
  exact h

end Examples.Binary32
