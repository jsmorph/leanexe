import Project.WGSL.Build
import Project.WGSL.RoundTrip
import Project.Binary32.Verify

/-!
The kernels of `scale32` and `axpyArray32`, translated from their compiled IR.  Each kernel's
dispatch theorem comes from `Spec.dispatch_eq` and the element lemma that the function's Wasm
proof uses, and its text theorem from `Module.parse_print_of_wfb`.
-/

namespace Project.WGSL

open Project.IR Project.Binary32 LeanExe.Examples.Binary32

def scaleSpec : Spec :=
  { kinds := [.float, .array], index := 5, sizeLocal := 2, sizeSource := 1, element := scaleElement }

def axpyArraySpec : Spec :=
  { kinds := [.float, .array, .array], index := 6, sizeLocal := 3, sizeSource := 1,
    element := axpyArrayElement }

/-- The compiled bodies are the build shape the specifications describe. -/
theorem scaleSpec_body : binary32.scale32.ir.body =
    .seq (.arraySize scaleSpec.sizeLocal scaleSpec.sizeSource)
      (.build 3 4 scaleSpec.index (.get scaleSpec.sizeLocal) scaleSpec.element) := rfl

theorem axpyArraySpec_body : binary32.axpyArray32.ir.body =
    .seq (.arraySize axpyArraySpec.sizeLocal axpyArraySpec.sizeSource)
      (.build 4 5 axpyArraySpec.index (.get axpyArraySpec.sizeLocal) axpyArraySpec.element) := rfl

def scaleKernel : Module := (scaleSpec.module).getD ⟨0, 0, []⟩

def axpyArrayKernel : Module := (axpyArraySpec.module).getD ⟨0, 0, []⟩

theorem scaleSpec_module : scaleSpec.module = some scaleKernel := rfl

theorem axpyArraySpec_module : axpyArraySpec.module = some axpyArrayKernel := rfl

theorem scaleKernel_text : Module.parse scaleKernel.print = some scaleKernel :=
  Module.parse_print_of_wfb _ (by decide)

theorem axpyArrayKernel_text : Module.parse axpyArrayKernel.print = some axpyArrayKernel :=
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
  have hfits : scaleSpec.Fits [.float a.toBits, .array (floatWords x)] (floatWords x) :=
    ⟨rfl, by simp; omega, rfl, by decide, by decide, by decide⟩
  have h := scaleSpec.dispatch_eq scaleKernel scaleSpec_module _ (floatWords x) hfits
    (fun i => (a * x[i.toNat]!).toBits.toUInt64)
    (fun k hk => by
      simp only [floatWords, Array.size_map] at hk
      have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
      rw [hkn]
      exact scaleElement_denote a x k (by omega) _ _ (by simp [Spec.locals, scaleSpec])
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
      (floatWords x) :=
    ⟨rfl, by simp; omega, rfl, by decide, by decide, by decide⟩
  have h := axpyArraySpec.dispatch_eq axpyArrayKernel axpyArraySpec_module _ (floatWords x) hfits
    (fun i => (a * x[i.toNat]! + y[i.toNat]!).toBits.toUInt64)
    (fun k hk => by
      simp only [floatWords, Array.size_map] at hk
      have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
      rw [hkn]
      exact axpyArrayElement_denote a x y k (by omega) _ _ (by simp [Spec.locals, axpyArraySpec])
        (by simp [Spec.locals, axpyArraySpec]) (by simp [Spec.arrays]) (by simp [Spec.arrays]))
    output (by simpa using hOut) (by simpa using hL0) hL1 count (by simpa using hCover) h32
  simp only [List.map_cons, List.map_nil] at h
  rw [show floatWords (axpyArray32 a x y) = LeanExe.build (UInt64.ofNat (floatWords x).size)
    (fun i => (a * x[i.toNat]! + y[i.toNat]!).toBits.toUInt64) by
      simp [axpyArray32, floatWords, build_map]]
  exact h

end Project.WGSL
