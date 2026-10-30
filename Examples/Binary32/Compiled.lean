import Examples.Binary32.Program
import Verified.Reflect.Command
import Verified.WGSL.Compile

/-! The verified compiler's module of seven of the example's eight functions, and the WGSL kernels
that `Verified.WGSL.compile` translates from the reflected bodies of `scale32`, `axpyArray32`, and
`matVec32`.  `condMix32` is absent: its condition `i % 4 ≤ 3 ∧ …` is a conjunction of
propositions, which the reflector rejects.  Each dispatch theorem has the premises of the LeanExe
compiler's theorem for the same kernel in `Examples/Binary32/Wgsl.lean` and comes from
`Compiled.dispatch_value` with the generated `denote_eq`. -/

namespace Examples.Binary32

open LeanExe.WGSL

verified_compile compiled := [axpy32, hypot32, ratio32, matVec32, piecewise32, scale32,
  axpyArray32]

def scale32Gpu :=
  (Verified.WGSL.compile (e := .float32) compiled.scale32.func.body).get (by decide +kernel)
def axpyArray32Gpu :=
  (Verified.WGSL.compile (e := .float32) compiled.axpyArray32.func.body).get (by decide +kernel)
def matVec32Gpu :=
  (Verified.WGSL.compile (e := .float32) compiled.matVec32.func.body).get (by decide +kernel)

def verifiedScale32Kernel : LeanExe.WGSL.Module := scale32Gpu.module
def verifiedAxpyArray32Kernel : LeanExe.WGSL.Module := axpyArray32Gpu.module
def verifiedMatVec32Kernel : LeanExe.WGSL.Module := matVec32Gpu.module

private abbrev floatWords (x : Array Float32) : Array UInt64 :=
  x.map fun v : Float32 => v.toBits.toUInt64

/-- The kernel computes `scale32 a x`: with buffers holding `a` and `x`, an output of the result's
size whose length word the host has written, and at least `x.size` invocations, the output ends
holding the result as a Wasm array, and distinct invocations store to distinct words. -/
theorem scale32_dispatch (a : Float32) (x : Array Float32) (hx : x.size < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    verifiedScale32Kernel.dispatch [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer]
        output count = some (arrayWords (floatWords (scale32 a x))) ∧
      verifiedScale32Kernel.RaceFree
        [(Arg.float a.toBits).buffer, (Arg.array (floatWords x)).buffer] output.size count := by
  have fits : scale32Gpu.spec.Fits (scale32Gpu.args (.cons a (.cons x .nil))) x.size := by
    refine ⟨rfl, ?_, ?_, hx⟩
    · change ∀ ys, Arg.array ys ∈ [Arg.float a.toBits, Arg.array (floatWords x)] →
        ys.size < 2 ^ 29
      simp [floatWords]
      exact hx
    · change ∃ ys, some (Arg.array (floatWords x)) = some (.array ys) ∧ ys.size = x.size
      exact ⟨floatWords x, rfl, by simp [floatWords]⟩
  exact scale32Gpu.dispatch_value _ (.cons a (.cons x .nil)) _ (compiled.scale32.denote_eq a x)
    x.size fits output hOut hL0 hL1 count hCover h32

/-- The kernel computes `axpyArray32 a x y`, under the conditions of `scale32_dispatch`. -/
theorem axpyArray32_dispatch (a : Float32) (x y : Array Float32) (hx : x.size < 2 ^ 29)
    (hy : y.size < 2 ^ 29) (output : Array UInt32) (hOut : output.size = 2 + 2 * x.size)
    (hL0 : output[0]? = some (UInt32.ofNat x.size)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : x.size ≤ count) (h32 : count ≤ 2 ^ 32) :
    verifiedAxpyArray32Kernel.dispatch [(Arg.float a.toBits).buffer,
        (Arg.array (floatWords x)).buffer, (Arg.array (floatWords y)).buffer] output count =
        some (arrayWords (floatWords (axpyArray32 a x y))) ∧
      verifiedAxpyArray32Kernel.RaceFree [(Arg.float a.toBits).buffer,
        (Arg.array (floatWords x)).buffer, (Arg.array (floatWords y)).buffer] output.size count := by
  have fits : axpyArray32Gpu.spec.Fits
      (axpyArray32Gpu.args (.cons a (.cons x (.cons y .nil)))) x.size := by
    refine ⟨rfl, ?_, ?_, hx⟩
    · change ∀ ys, Arg.array ys ∈ [Arg.float a.toBits, Arg.array (floatWords x),
        Arg.array (floatWords y)] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hx, hy⟩
    · change ∃ ys, some (Arg.array (floatWords x)) = some (.array ys) ∧ ys.size = x.size
      exact ⟨floatWords x, rfl, by simp [floatWords]⟩
  exact axpyArray32Gpu.dispatch_value _ (.cons a (.cons x (.cons y .nil))) _
    (compiled.axpyArray32.denote_eq a x y) x.size fits output hOut hL0 hL1 count hCover h32

/-- The kernel computes `matVec32 m v rows cols`: with buffers holding `m`, `v`, `rows`, and
`cols`, an output of the result's size whose length word the host has written, and at least
`rows` invocations, the output ends holding the result as a Wasm array, and distinct invocations
store to distinct words. -/
theorem matVec32_dispatch (m v : Array Float32) (rows cols : UInt64) (hm : m.size < 2 ^ 29)
    (hv : v.size < 2 ^ 29) (hrows : rows.toNat < 2 ^ 29)
    (output : Array UInt32) (hOut : output.size = 2 + 2 * rows.toNat)
    (hL0 : output[0]? = some (UInt32.ofNat rows.toNat)) (hL1 : output[1]? = some 0)
    (count : Nat) (hCover : rows.toNat ≤ count) (h32 : count ≤ 2 ^ 32) :
    verifiedMatVec32Kernel.dispatch [(Arg.array (floatWords m)).buffer,
        (Arg.array (floatWords v)).buffer, (Arg.word rows).buffer, (Arg.word cols).buffer] output
        count = some (arrayWords (floatWords (matVec32 m v rows cols))) ∧
      verifiedMatVec32Kernel.RaceFree [(Arg.array (floatWords m)).buffer,
        (Arg.array (floatWords v)).buffer, (Arg.word rows).buffer, (Arg.word cols).buffer]
        output.size count := by
  have fits : matVec32Gpu.spec.Fits
      (matVec32Gpu.args (.cons m (.cons v (.cons rows (.cons cols .nil))))) rows.toNat := by
    refine ⟨rfl, ?_, ?_, hrows⟩
    · change ∀ ys, Arg.array ys ∈ [Arg.array (floatWords m), Arg.array (floatWords v),
        Arg.word rows, Arg.word cols] → ys.size < 2 ^ 29
      simp [floatWords]
      exact ⟨hm, hv⟩
    · change some (Arg.word rows) = some (.word (UInt64.ofNat rows.toNat))
      simp only [UInt64.ofNat_toNat]
  exact matVec32Gpu.dispatch_value _ (.cons m (.cons v (.cons rows (.cons cols .nil)))) _
    (compiled.matVec32.denote_eq m v rows cols) rows.toNat fits output hOut hL0 hL1 count hCover
    h32

#print axioms compiled.bytes
#print axioms scale32_dispatch
#print axioms axpyArray32_dispatch
#print axioms matVec32_dispatch

end Examples.Binary32
