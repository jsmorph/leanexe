import Demos.Gpt32.VerifiedDispatch
import Verified.WgslPtx

/-!
The PTX kernels of the binary32 GPT-2 demo, which `Verified.PTX.compile` translates from the bodies
that `Demos/Gpt32/Verified.lean` compiles to WGSL, and their launch theorems.  Each theorem takes the
argument bounds of the kernel's WGSL dispatch theorem, whose `Spec.Fits` proof it shares through
`Verified.PTX.Compiled.of_wgsl`, and states the sequential run of a launch and the launch under the
PTX memory model.
-/

namespace Demos.Gpt32.VerifiedPtx

open _root_.Demos.Gpt32
open LeanExe.Source (Arg Arg.word Arg.float Arg.array)
open _root_.Verified.PTX (LaunchSeq LaunchMeets)

private abbrev floatWords (xs : Array Float32) : Array UInt64 :=
  xs.map fun x => x.toBits.toUInt64


def expPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.expArray32.func.body).get
    (by decide +kernel)

def embedPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.embed32.func.body).get
    (by decide +kernel)

def linearPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.linear32.func.body).get
    (by decide +kernel)

def logitsPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.logits32.func.body).get
    (by decide +kernel)

def mixPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.mix32.func.body).get
    (by decide +kernel)

def scoresPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.scores32.func.body).get
    (by decide +kernel)

def addPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.add32.func.body).get
    (by decide +kernel)

def appendPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.append32.func.body).get
    (by decide +kernel)

def geluPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.geluArray32.func.body).get
    (by decide +kernel)

def probsPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.probs32.func.body).get
    (by decide +kernel)

def layerNormPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.layerNorm32.func.body).get
    (by decide +kernel)

def headMaxPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.headMax32.func.body).get
    (by decide +kernel)

def headSumPtx :=
  (_root_.Verified.PTX.compile (e := .float32) Verified.compiled.headSum32.func.body).get
    (by decide +kernel)

def expKernel : LeanExe.PTX.Module := expPtx.module
def embedKernel : LeanExe.PTX.Module := embedPtx.module
def linearKernel : LeanExe.PTX.Module := linearPtx.module
def logitsKernel : LeanExe.PTX.Module := logitsPtx.module
def mixKernel : LeanExe.PTX.Module := mixPtx.module
def scoresKernel : LeanExe.PTX.Module := scoresPtx.module
def addKernel : LeanExe.PTX.Module := addPtx.module
def appendKernel : LeanExe.PTX.Module := appendPtx.module
def geluKernel : LeanExe.PTX.Module := geluPtx.module
def probsKernel : LeanExe.PTX.Module := probsPtx.module
def layerNormKernel : LeanExe.PTX.Module := layerNormPtx.module
def headMaxKernel : LeanExe.PTX.Module := headMaxPtx.module
def headSumKernel : LeanExe.PTX.Module := headSumPtx.module

/-- The launch of the `exp` kernel computes its Lean function, under the bounds of
`expKernel_dispatch`. -/
theorem expKernel_launch (x : Array Float32) (hx : x.size < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = x.size) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : x.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq expKernel [Arg.array (floatWords x)] x.size ys blocks block (floatWords (expArray32 x)) ∧
      LaunchMeets expKernel [Arg.array (floatWords x)] x.size ys blocks block (floatWords (expArray32 x)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.expArray32.func.body =
      some Verified.expGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.expArray32.func.body =
      some expPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : expPtx.spec.Fits (expPtx.args (.cons x .nil)) x.size := by
    rw [hspec, hargs]
    exact Verified.expGpu_fits x hx
  have hval : expPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := expPtx.launch_value _ (.cons x .nil) _ (Verified.compiled.expArray32.denote_eq x) x.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := expPtx.executions_eq _ (.cons x .nil) _ (Verified.compiled.expArray32.denote_eq x) x.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `embed` kernel computes its Lean function, under the bounds of
`embedKernel_dispatch`. -/
theorem embedKernel_launch (wte wpe : Array Float32) (row p d : UInt64)
    (hw : wte.size < 2 ^ 29) (hp : wpe.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = d.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : d.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq embedKernel [Arg.array (floatWords wte), Arg.array (floatWords wpe), Arg.word row, Arg.word p, Arg.word d] d.toNat ys blocks block (floatWords (embed32 wte wpe row p d)) ∧
      LaunchMeets embedKernel [Arg.array (floatWords wte), Arg.array (floatWords wpe), Arg.word row, Arg.word p, Arg.word d] d.toNat ys blocks block (floatWords (embed32 wte wpe row p d)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.embed32.func.body =
      some Verified.embedGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.embed32.func.body =
      some embedPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : embedPtx.spec.Fits (embedPtx.args (.cons wte (.cons wpe (.cons row (.cons p (.cons d .nil)))))) d.toNat := by
    rw [hspec, hargs]
    exact Verified.embedGpu_fits wte wpe row p d hw hp hd
  have hval : embedPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := embedPtx.launch_value _ (.cons wte (.cons wpe (.cons row (.cons p (.cons d .nil))))) _ (Verified.compiled.embed32.denote_eq wte wpe row p d) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := embedPtx.executions_eq _ (.cons wte (.cons wpe (.cons row (.cons p (.cons d .nil))))) _ (Verified.compiled.embed32.denote_eq wte wpe row p d) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `linear` kernel computes its Lean function, under the bounds of
`linearKernel_dispatch`. -/
theorem linearKernel_launch (x w b : Array Float32) (k m : UInt64) (hx : x.size < 2 ^ 29)
    (hw : w.size < 2 ^ 29) (hb : b.size < 2 ^ 29) (hm : m.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = m.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : m.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq linearKernel [Arg.array (floatWords x), Arg.array (floatWords w), Arg.array (floatWords b), Arg.word k, Arg.word m] m.toNat ys blocks block (floatWords (Library.Numerics.LinearAlgebra.Binary32.linear32 x w b k m)) ∧
      LaunchMeets linearKernel [Arg.array (floatWords x), Arg.array (floatWords w), Arg.array (floatWords b), Arg.word k, Arg.word m] m.toNat ys blocks block (floatWords (Library.Numerics.LinearAlgebra.Binary32.linear32 x w b k m)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.linear32.func.body =
      some Verified.linearGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.linear32.func.body =
      some linearPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : linearPtx.spec.Fits (linearPtx.args (.cons x (.cons w (.cons b (.cons k (.cons m (.nil))))))) m.toNat := by
    rw [hspec, hargs]
    exact Verified.linearGpu_fits x w b k m hx hw hb hm
  have hval : linearPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := linearPtx.launch_value _ (.cons x (.cons w (.cons b (.cons k (.cons m (.nil)))))) _ (Verified.compiled.linear32.denote_eq x w b k m) m.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := linearPtx.executions_eq _ (.cons x (.cons w (.cons b (.cons k (.cons m (.nil)))))) _ (Verified.compiled.linear32.denote_eq x w b k m) m.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `logits` kernel computes its Lean function, under the bounds of
`logitsKernel_dispatch`. -/
theorem logitsKernel_launch (h wte : Array Float32) (rows d : UInt64) (hh : h.size < 2 ^ 29)
    (hw : wte.size < 2 ^ 29) (hr : rows.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = rows.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : rows.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq logitsKernel [Arg.array (floatWords h), Arg.array (floatWords wte), Arg.word rows, Arg.word d] rows.toNat ys blocks block (floatWords (logits32 h wte rows d)) ∧
      LaunchMeets logitsKernel [Arg.array (floatWords h), Arg.array (floatWords wte), Arg.word rows, Arg.word d] rows.toNat ys blocks block (floatWords (logits32 h wte rows d)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.logits32.func.body =
      some Verified.logitsGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.logits32.func.body =
      some logitsPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : logitsPtx.spec.Fits (logitsPtx.args (.cons h (.cons wte (.cons rows (.cons d (.nil)))))) rows.toNat := by
    rw [hspec, hargs]
    exact Verified.logitsGpu_fits h wte rows d hh hw hr
  have hval : logitsPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := logitsPtx.launch_value _ (.cons h (.cons wte (.cons rows (.cons d (.nil))))) _ (Verified.compiled.logits32.denote_eq h wte rows d) rows.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := logitsPtx.executions_eq _ (.cons h (.cons wte (.cons rows (.cons d (.nil))))) _ (Verified.compiled.logits32.denote_eq h wte rows d) rows.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `mix` kernel computes its Lean function, under the bounds of
`mixKernel_dispatch`. -/
theorem mixKernel_launch (pw vc : Array Float32) (p d : UInt64) (hp : pw.size < 2 ^ 29)
    (hv : vc.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = d.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : d.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq mixKernel [Arg.array (floatWords pw), Arg.array (floatWords vc), Arg.word p, Arg.word d] d.toNat ys blocks block (floatWords (mix32 pw vc p d)) ∧
      LaunchMeets mixKernel [Arg.array (floatWords pw), Arg.array (floatWords vc), Arg.word p, Arg.word d] d.toNat ys blocks block (floatWords (mix32 pw vc p d)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.mix32.func.body =
      some Verified.mixGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.mix32.func.body =
      some mixPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : mixPtx.spec.Fits (mixPtx.args (.cons pw (.cons vc (.cons p (.cons d (.nil)))))) d.toNat := by
    rw [hspec, hargs]
    exact Verified.mixGpu_fits pw vc p d hp hv hd
  have hval : mixPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := mixPtx.launch_value _ (.cons pw (.cons vc (.cons p (.cons d (.nil))))) _ (Verified.compiled.mix32.denote_eq pw vc p d) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := mixPtx.executions_eq _ (.cons pw (.cons vc (.cons p (.cons d (.nil))))) _ (Verified.compiled.mix32.denote_eq pw vc p d) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `scores` kernel computes its Lean function, under the bounds of
`scoresKernel_dispatch`. -/
theorem scoresKernel_launch (q kc : Array Float32) (p d n : UInt64) (hq : q.size < 2 ^ 29)
    (hk : kc.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = n.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : n.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq scoresKernel [Arg.array (floatWords q), Arg.array (floatWords kc), Arg.word p, Arg.word d, Arg.word n] n.toNat ys blocks block (floatWords (scores32 q kc p d n)) ∧
      LaunchMeets scoresKernel [Arg.array (floatWords q), Arg.array (floatWords kc), Arg.word p, Arg.word d, Arg.word n] n.toNat ys blocks block (floatWords (scores32 q kc p d n)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.scores32.func.body =
      some Verified.scoresGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.scores32.func.body =
      some scoresPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : scoresPtx.spec.Fits (scoresPtx.args (.cons q (.cons kc (.cons p (.cons d (.cons n (.nil))))))) n.toNat := by
    rw [hspec, hargs]
    exact Verified.scoresGpu_fits q kc p d n hq hk hn
  have hval : scoresPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := scoresPtx.launch_value _ (.cons q (.cons kc (.cons p (.cons d (.cons n (.nil)))))) _ (Verified.compiled.scores32.denote_eq q kc p d n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := scoresPtx.executions_eq _ (.cons q (.cons kc (.cons p (.cons d (.cons n (.nil)))))) _ (Verified.compiled.scores32.denote_eq q kc p d n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `add` kernel computes its Lean function, under the bounds of
`addKernel_dispatch`. -/
theorem addKernel_launch (a b : Array Float32) (ha : a.size < 2 ^ 29) (hb : b.size < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = a.size) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : a.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq addKernel [Arg.array (floatWords a), Arg.array (floatWords b)] a.size ys blocks block (floatWords (Library.Numerics.LinearAlgebra.Binary32.add32 a b)) ∧
      LaunchMeets addKernel [Arg.array (floatWords a), Arg.array (floatWords b)] a.size ys blocks block (floatWords (Library.Numerics.LinearAlgebra.Binary32.add32 a b)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.add32.func.body =
      some Verified.addGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.add32.func.body =
      some addPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : addPtx.spec.Fits (addPtx.args (.cons a (.cons b (.nil)))) a.size := by
    rw [hspec, hargs]
    exact Verified.addGpu_fits a b ha hb
  have hval : addPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := addPtx.launch_value _ (.cons a (.cons b (.nil))) _ (Verified.compiled.add32.denote_eq a b) a.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := addPtx.executions_eq _ (.cons a (.cons b (.nil))) _ (Verified.compiled.add32.denote_eq a b) a.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `append` kernel computes its Lean function, under the bounds of
`appendKernel_dispatch`. -/
theorem appendKernel_launch (cache row : Array Float32) (base n : UInt64)
    (hc : cache.size < 2 ^ 29) (hr : row.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = n.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : n.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq appendKernel [Arg.array (floatWords cache), Arg.array (floatWords row), Arg.word base, Arg.word n] n.toNat ys blocks block (floatWords (append32 cache row base n)) ∧
      LaunchMeets appendKernel [Arg.array (floatWords cache), Arg.array (floatWords row), Arg.word base, Arg.word n] n.toNat ys blocks block (floatWords (append32 cache row base n)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.append32.func.body =
      some Verified.appendGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.append32.func.body =
      some appendPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : appendPtx.spec.Fits (appendPtx.args (.cons cache (.cons row (.cons base (.cons n (.nil)))))) n.toNat := by
    rw [hspec, hargs]
    exact Verified.appendGpu_fits cache row base n hc hr hn
  have hval : appendPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := appendPtx.launch_value _ (.cons cache (.cons row (.cons base (.cons n (.nil))))) _ (Verified.compiled.append32.denote_eq cache row base n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := appendPtx.executions_eq _ (.cons cache (.cons row (.cons base (.cons n (.nil))))) _ (Verified.compiled.append32.denote_eq cache row base n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `gelu` kernel computes its Lean function, under the bounds of
`geluKernel_dispatch`. -/
theorem geluKernel_launch (x : Array Float32) (hx : x.size < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = x.size) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : x.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq geluKernel [Arg.array (floatWords x)] x.size ys blocks block (floatWords (geluArray32 x)) ∧
      LaunchMeets geluKernel [Arg.array (floatWords x)] x.size ys blocks block (floatWords (geluArray32 x)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.geluArray32.func.body =
      some Verified.geluGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.geluArray32.func.body =
      some geluPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : geluPtx.spec.Fits (geluPtx.args (.cons x (.nil))) x.size := by
    rw [hspec, hargs]
    exact Verified.geluGpu_fits x hx
  have hval : geluPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := geluPtx.launch_value _ (.cons x (.nil)) _ (Verified.compiled.geluArray32.denote_eq x) x.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := geluPtx.executions_eq _ (.cons x (.nil)) _ (Verified.compiled.geluArray32.denote_eq x) x.size fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `probs` kernel computes its Lean function, under the bounds of
`probsKernel_dispatch`. -/
theorem probsKernel_launch (s mx sm : Array Float32) (p n : UInt64) (hs : s.size < 2 ^ 29)
    (hm : mx.size < 2 ^ 29) (hsm : sm.size < 2 ^ 29) (hn : n.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = n.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : n.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq probsKernel [Arg.array (floatWords s), Arg.array (floatWords mx), Arg.array (floatWords sm), Arg.word p, Arg.word n] n.toNat ys blocks block (floatWords (probs32 s mx sm p n)) ∧
      LaunchMeets probsKernel [Arg.array (floatWords s), Arg.array (floatWords mx), Arg.array (floatWords sm), Arg.word p, Arg.word n] n.toNat ys blocks block (floatWords (probs32 s mx sm p n)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.probs32.func.body =
      some Verified.probsGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.probs32.func.body =
      some probsPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : probsPtx.spec.Fits (probsPtx.args (.cons s (.cons mx (.cons sm (.cons p (.cons n (.nil))))))) n.toNat := by
    rw [hspec, hargs]
    exact Verified.probsGpu_fits s mx sm p n hs hm hsm hn
  have hval : probsPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := probsPtx.launch_value _ (.cons s (.cons mx (.cons sm (.cons p (.cons n (.nil)))))) _ (Verified.compiled.probs32.denote_eq s mx sm p n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := probsPtx.executions_eq _ (.cons s (.cons mx (.cons sm (.cons p (.cons n (.nil)))))) _ (Verified.compiled.probs32.denote_eq s mx sm p n) n.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `layerNorm` kernel computes its Lean function, under the bounds of
`layerNormKernel_dispatch`. -/
theorem layerNormKernel_launch (x g b : Array Float32) (d : UInt64) (nf : Float32)
    (hx : x.size < 2 ^ 29) (hg : g.size < 2 ^ 29) (hb : b.size < 2 ^ 29) (hd : d.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = d.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : d.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq layerNormKernel [Arg.array (floatWords x), Arg.array (floatWords g), Arg.array (floatWords b), Arg.word d, Arg.float nf.toBits] d.toNat ys blocks block (floatWords (layerNorm32 x g b d nf)) ∧
      LaunchMeets layerNormKernel [Arg.array (floatWords x), Arg.array (floatWords g), Arg.array (floatWords b), Arg.word d, Arg.float nf.toBits] d.toNat ys blocks block (floatWords (layerNorm32 x g b d nf)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.layerNorm32.func.body =
      some Verified.layerNormGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.layerNorm32.func.body =
      some layerNormPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : layerNormPtx.spec.Fits (layerNormPtx.args (.cons x (.cons g (.cons b (.cons d (.cons nf (.nil))))))) d.toNat := by
    rw [hspec, hargs]
    exact Verified.layerNormGpu_fits x g b d nf hx hg hb hd
  have hval : layerNormPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := layerNormPtx.launch_value _ (.cons x (.cons g (.cons b (.cons d (.cons nf (.nil)))))) _ (Verified.compiled.layerNorm32.denote_eq x g b d nf) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := layerNormPtx.executions_eq _ (.cons x (.cons g (.cons b (.cons d (.cons nf (.nil)))))) _ (Verified.compiled.layerNorm32.denote_eq x g b d nf) d.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `headMax` kernel computes its Lean function, under the bounds of
`headMaxKernel_dispatch`. -/
theorem headMaxKernel_launch (s : Array Float32) (p nh : UInt64) (hs : s.size < 2 ^ 29)
    (hnh : nh.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = nh.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : nh.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq headMaxKernel [Arg.array (floatWords s), Arg.word p, Arg.word nh] nh.toNat ys blocks block (floatWords (headMax32 s p nh)) ∧
      LaunchMeets headMaxKernel [Arg.array (floatWords s), Arg.word p, Arg.word nh] nh.toNat ys blocks block (floatWords (headMax32 s p nh)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.headMax32.func.body =
      some Verified.headMaxGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.headMax32.func.body =
      some headMaxPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : headMaxPtx.spec.Fits (headMaxPtx.args (.cons s (.cons p (.cons nh (.nil))))) nh.toNat := by
    rw [hspec, hargs]
    exact Verified.headMaxGpu_fits s p nh hs hnh
  have hval : headMaxPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := headMaxPtx.launch_value _ (.cons s (.cons p (.cons nh (.nil)))) _ (Verified.compiled.headMax32.denote_eq s p nh) nh.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := headMaxPtx.executions_eq _ (.cons s (.cons p (.cons nh (.nil)))) _ (Verified.compiled.headMax32.denote_eq s p nh) nh.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

/-- The launch of the `headSum` kernel computes its Lean function, under the bounds of
`headSumKernel_dispatch`. -/
theorem headSumKernel_launch (s mx : Array Float32) (p nh : UInt64) (hs : s.size < 2 ^ 29)
    (hm : mx.size < 2 ^ 29) (hnh : nh.toNat < 2 ^ 29)
    (ys : Array UInt64) (hys : ys.size = nh.toNat) (blocks block : Nat) (hpos : 0 < block)
    (hblock : block < 2 ^ 32) (hblocks : blocks < 2 ^ 32) (hcover : nh.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchSeq headSumKernel [Arg.array (floatWords s), Arg.array (floatWords mx), Arg.word p, Arg.word nh] nh.toNat ys blocks block (floatWords (headSum32 s mx p nh)) ∧
      LaunchMeets headSumKernel [Arg.array (floatWords s), Arg.array (floatWords mx), Arg.word p, Arg.word nh] nh.toNat ys blocks block (floatWords (headSum32 s mx p nh)) := by
  have hWgsl : _root_.Verified.WGSL.compile (e := .float32) Verified.compiled.headSum32.func.body =
      some Verified.headSumGpu := (Option.some_get _).symm
  have hPtx : _root_.Verified.PTX.compile (e := .float32) Verified.compiled.headSum32.func.body =
      some headSumPtx := (Option.some_get _).symm
  obtain ⟨hspec, hargs, hencode⟩ := _root_.Verified.PTX.Compiled.of_wgsl hWgsl hPtx
  have fits : headSumPtx.spec.Fits (headSumPtx.args (.cons s (.cons mx (.cons p (.cons nh (.nil)))))) nh.toNat := by
    rw [hspec, hargs]
    exact Verified.headSumGpu_fits s mx p nh hs hm hnh
  have hval : headSumPtx.encode = fun x => x.toBits.toUInt64 := hencode
  refine ⟨?_, ?_⟩
  · have hl := headSumPtx.launch_value _ (.cons s (.cons mx (.cons p (.cons nh (.nil))))) _ (Verified.compiled.headSum32.denote_eq s mx p nh) nh.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl
  · have hl := headSumPtx.executions_eq _ (.cons s (.cons mx (.cons p (.cons nh (.nil))))) _ (Verified.compiled.headSum32.denote_eq s mx p nh) nh.toNat fits ys hys blocks
      block hpos hblock hblocks hcover hthreads
    rw [hargs, hval] at hl
    exact hl

end Demos.Gpt32.VerifiedPtx

#print axioms Demos.Gpt32.VerifiedPtx.expKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.embedKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.linearKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.logitsKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.mixKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.scoresKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.addKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.appendKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.geluKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.probsKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.layerNormKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.headMaxKernel_launch
#print axioms Demos.Gpt32.VerifiedPtx.headSumKernel_launch
