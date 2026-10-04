import Project.WGSL.Build
import Project.WGSL.RoundTrip
import Project.Binary32.Verify

/-!
The kernels of `scale32`, `axpyArray32`, and `matVec32`, translated from their compiled IR.  Each
kernel's dispatch theorem comes from `Spec.dispatch_eq` and the element lemma that the function's
Wasm proof uses, and its text theorem from `Module.parse_print_of_wfb`.
-/

namespace Project.WGSL

open Project.IR Project.Binary32 LeanExe.Examples.Binary32

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

end Project.WGSL
