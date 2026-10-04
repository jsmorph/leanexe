import Project.Binary32.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Run
import Project.ProofKit.F32Bits
import Project.IR.DenoteStmt
import Project.Encoding.RoundTrip

namespace Project.Binary32

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Binary32

/-- `axpy32` with its three arguments as one tuple. -/
def axpy32Tuple (x : Float32 × Float32 × Float32) : Float32 := axpy32 x.1 x.2.1 x.2.2

/-- `hypot32` with its two arguments as one pair. -/
def hypot32Pair (x : Float32 × Float32) : Float32 := hypot32 x.1 x.2

/-- `ratio32` with its three arguments as one tuple. -/
def ratio32Tuple (x : Float32 × Float32 × Float32) : Float32 := ratio32 x.1 x.2.1 x.2.2

theorem axpy32_implements : Implements binary32.module 2 axpy32Tuple :=
  Func.implements binary32.funcs 0 binary32.axpy32.ir "axpy32" rfl axpy32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.axpy32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, axpy32Tuple, axpy32, F32Bits.toBits_add, F32Bits.toBits_mul]⟩)
      fun _ _ h => h

theorem hypot32_implements : Implements binary32.module 3 hypot32Pair :=
  Func.implements binary32.funcs 1 binary32.hypot32.ir "hypot32" rfl hypot32Pair
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, y⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.hypot32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        F32UnOp.apply, Scalar.values, hypot32Pair, hypot32, F32Bits.toBits_add,
        F32Bits.toBits_mul, F32Bits.toBits_sqrt]⟩)
      fun _ _ h => h

theorem ratio32_implements : Implements binary32.module 4 ratio32Tuple :=
  Func.implements binary32.funcs 2 binary32.ratio32.ir "ratio32" rfl ratio32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨a, b, c⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨_, _, rfl, ?_⟩
      simp [binary32.ratio32.ir, Expr.evalResults, Func.state, Func.locals, Func.width,
        Func.scratch, Expr.eval, Expr.scratchWidth, IR.Stmt.scratchWidth, State.get, F32Op.apply,
        Scalar.values, ratio32Tuple, ratio32, F32Bits.toBits_sub, F32Bits.toBits_div]⟩)
      fun _ _ h => h

/-- `matVec32` with its four arguments as one tuple. -/
def matVec32Tuple (x : Array Float32 × Array Float32 × UInt64 × UInt64) : Array Float32 :=
  matVec32 x.1 x.2.1 x.2.2.1 x.2.2.2

/-- One step of the loop over row `r`. -/
def rowStep32 (m v : Array Float32) (cols r c : UInt64) (acc : Float32) : Float32 :=
  acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- Element `r` of the product. -/
def row32 (m v : Array Float32) (cols r : UInt64) : Float32 :=
  LeanExe.loop cols 0.0 (rowStep32 m v cols r)

theorem matVec32_eq (m v : Array Float32) (rows cols : UInt64) :
    matVec32 m v rows cols = LeanExe.build rows (row32 m v cols) := rfl

/-- The compiled loop body over a row. -/
def rowBody32 : Stmt :=
  .seq (.assign 10 (.binF32 .add (.getF32 7) (.binF32 .mul
    (.ofBits32 (.read 0 (.bin .add (.bin .mul (.get 6) (.get 3)) (.get 9))))
    (.ofBits32 (.read 1 (.get 9)))))) (.assign 7 (.getF32 10))

/-- The statements of `matVec32`'s build for one row. -/
def matVecBody : Stmt := .seq (.assign 7 (.constF32 0)) (.loop 8 9 (.get 3) rowBody32)

/-- The element of `matVec32`'s build. -/
def matVecElement : Expr .u64 := .toBits32 (.getF32 7)

/-- The element lemma that the Wasm proof and the WGSL kernel proof share: for row `r`, the
statements leave element `r` of the product in local 7. -/
theorem matVecRow_denote (m v : Array Float32) (cols r : UInt64)
    (L : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (h3 : L 3 = some (.i64 cols)) (h6 : L 6 = some (.i64 r))
    (h0 : arrays 0 = some (m.map fun x : Float32 => x.toBits.toUInt64))
    (h1 : arrays 1 = some (v.map fun x : Float32 => x.toBits.toUInt64))
    (hNone : ∀ j, 7 ≤ j → j ≤ 10 → arrays j = none) :
    ∃ L', matVecBody.denote arrays L = some L' ∧
      matVecElement.denote L' arrays = some (row32 m v cols r).toBits.toUInt64 := by
  let L1 : Nat → Option Wasm.Value := fun i => if i = 7 then some (.f32 0) else L i
  have hL1 : (Stmt.assign 7 (.constF32 0)).denote arrays L = some L1 := by
    simp only [Stmt.denote, hNone 7 (by omega) (by omega), ↓reduceIte, Expr.denote,
      Option.map_some]
    rfl
  have hZero : (0.0 : Float32).toBits = 0 := by decide +kernel
  have hBody : ∀ (c : Nat) (acc : Float32) (Lc : Nat → Option Wasm.Value), c < cols.toNat →
      (∀ j, j ∉ 8 :: 9 :: rowBody32.writes → Lc j = L1 j) →
      Lc 9 = some (.i64 (UInt64.ofNat c)) → Lc 8 = some (.i64 cols) →
      LocalsHold Lc [7] (Scalar.values acc) →
      ∃ L2, rowBody32.denote arrays Lc = some L2 ∧
        LocalsHold L2 [7] (Scalar.values (rowStep32 m v cols r (UInt64.ofNat c) acc)) := by
    intro c acc Lc _ hFrame h9 _ hHold
    have hKeep : ∀ j, j = 3 ∨ j = 6 → Lc j = L j := fun j hj => by
      rw [hFrame j (by rcases hj with rfl | rfl <;> decide)]
      rcases hj with rfl | rfl <;> rfl
    have h7 : Lc 7 = some (.f32 acc.toBits) := by simpa [LocalsHold, Scalar.values] using hHold
    simp [rowBody32, Stmt.denote, Expr.denote, hNone, hKeep 3 (Or.inl rfl), hKeep 6 (Or.inr rfl),
      h3, h6, h0, h1, h7, h9, getElem!_map_toBits32, F32Op.apply, U64Op.apply, LocalsHold,
      Scalar.values, rowStep32, F32Bits.toBits_add, F32Bits.toBits_mul]
  obtain ⟨L', hLoop, hHold⟩ := Stmt.denote_loop (limit := 8) (index := 9) (count := .get 3)
    (body := rowBody32) (vars := [7]) (init := (0.0 : Float32))
    (n := cols) (L := L1) (arrays := arrays) (rowStep32 m v cols r) (by decide)
    ⟨hNone 8 (by omega) (by omega), hNone 9 (by omega) (by omega)⟩ (by decide) (by simp)
    (by simp [Expr.denote, L1, h3]) (by simp [LocalsHold, Scalar.values, L1, hZero]) hBody
  refine ⟨L', ?_, ?_⟩
  · show ((Stmt.assign 7 (.constF32 0)).denote arrays L).bind
      (Stmt.denote arrays (.loop 8 9 (.get 3) rowBody32)) = _
    rw [hL1, Option.bind_some]
    exact hLoop
  · have h7 : L' 7 = some (.f32 (row32 m v cols r).toBits) := by
      simpa [LocalsHold, Scalar.values, row32] using hHold
    simp [matVecElement, Expr.denote, h7]

theorem matVec32_implements : Implements binary32.module 5 matVec32Tuple := by
  refine Func.implements_heap binary32.funcs 3 binary32.matVec32.ir "matVec32" rfl matVec32Tuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨m, v, rows, cols⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pm, rfl, hMs⟩, _, _, rfl, ⟨pv, rfl, hVs⟩, rfl⟩ hCap
  change heap.Borrowed initial pm (m.map fun x : Float32 => x.toBits.toUInt64) at hMs
  change heap.Borrowed initial pv (v.map fun x : Float32 => x.toBits.toUInt64) at hVs
  have hMemory32 : binary32.module.memIs64 = false := rfl
  have hImports : binary32.module.imports = [] := rfl
  have hAlloc : binary32.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 pm, .i64 pv, .i64 rows, .i64 cols]
      locals := [.i64 0, .i64 0, .i64 0, .f32 0, .i64 0, .i64 0, .f32 0, .i64 0] }
  show Triple _ (.buildWith 4 5 6 (.get 2) matVecBody matVecElement) 11
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.buildWith_spec (writes := matVecBody.writes) (n := rows)
    (fun r => (row32 m v cols r).toBits.toUInt64) hMemory32 hImports hAlloc (by decide)
    (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 8 :=
      ⟨hFrame.params, hFrame.locals⟩
    have hGet : ∀ j, j < 4 → state.get j = start.get j := fun j hj =>
      hFrame.get j (by omega) (by simp [matVecBody, Stmt.loop, rowBody32, Stmt.writes]; omega)
    let L : Nat → Option Wasm.Value := fun j =>
      if j = 3 then some (.i64 cols) else if j = 6 then some (.i64 (UInt64.ofNat k)) else none
    let arrays : Nat → Option (Array UInt64) := fun j =>
      if j = 0 then some (m.map fun x : Float32 => x.toBits.toUInt64)
      else if j = 1 then some (v.map fun x : Float32 => x.toBits.toUInt64) else none
    have hAgree : Agrees L arrays store 11 state := by
      refine ⟨fun j w hj => ?_, fun j ys hj => ?_⟩
      · simp only [L] at hj
        split at hj
        · rename_i h3; subst h3
          cases hj
          exact ⟨by decide, (hGet 3 (by decide)).trans rfl⟩
        · split at hj
          · rename_i h6; subst h6
            cases hj
            exact ⟨by decide, hIndex⟩
          · cases hj
      · simp only [arrays] at hj
        split at hj
        · rename_i h0; subst h0
          cases hj
          exact ⟨by decide, pm, (hGet 0 (by decide)).trans rfl, hAt pm _ hMs⟩
        · split at hj
          · rename_i h1; subst h1
            cases hj
            exact ⟨by decide, pv, (hGet 1 (by decide)).trans rfl, hAt pv _ hVs⟩
          · cases hj
    obtain ⟨L', hDen, hEl⟩ := matVecRow_denote m v cols (UInt64.ofNat k) L arrays (by simp [L])
      (by simp [L]) (by simp [arrays]) (by simp [arrays])
      (fun j hj1 hj2 => by
        simp only [arrays, show j ≠ 0 by omega, show j ≠ 1 by omega, ↓reduceIte])
    refine (Stmt.denote_spec matVecBody L L' state hAgree hDen (by decide)
      (by rw [hState.1, hState.2]; decide)).mono (fun _ _ h => h) ?_
    rintro st s1 ⟨rfl, hF, hA⟩
    obtain ⟨next, hEval⟩ := Expr.eval_denote matVecElement 11 s1 _ hA
      (by rw [hF.params, hF.locals, hState.1, hState.2]; decide) hEl
    exact ⟨rfl, hF, next, hEval⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [binary32.matVec32.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  rw [matVec32Tuple, matVec32_eq, build_map]
  exact hNew.owned

/-- `piecewise32` with its three arguments as one tuple. -/
def piecewise32Tuple (x : Float32 × Float32 × Float32) : Float32 := piecewise32 x.1 x.2.1 x.2.2

theorem piecewise32_implements : Implements binary32.module 6 piecewise32Tuple :=
  Func.implements binary32.funcs 4 binary32.piecewise32.ir "piecewise32" rfl piecewise32Tuple
    (fun _ _ _ _ h => by rw [Scalar.borrowed.mp h]; rfl) fun ⟨x, lo, hi⟩ _ _ _ _ h =>
    Stmt.skip_spec.mono (fun _ _ ⟨hStore, hState⟩ => ⟨hStore, by
      rw [Scalar.borrowed.mp h] at hState
      subst hState
      refine ⟨[.f32 (piecewise32 x lo hi).toBits],
        binary32.piecewise32.ir.state (Scalar.values (x, lo, hi)), ?_, rfl⟩
      have h0 : (0.0 : Float32).toBits = 0 := by decide
      have h05 : (0.5 : Float32).toBits = 0x3f000000 := by decide
      have h15 : (1.5 : Float32).toBits = 0x3fc00000 := by decide
      have hx : binary32.piecewise32.ir.state (Scalar.values (x, lo, hi)) =
          { params := [.f32 x.toBits, .f32 lo.toBits, .f32 hi.toBits], locals := [] } := rfl
      rw [hx]
      dsimp only [binary32.piecewise32.ir, Func.scratch]
      simp [Expr.evalResults, Expr.eval, State.get, F32Op.apply, F32UnOp.apply, piecewise32,
        F32Bits.beq_eq, F32Bits.lt_iff, F32Bits.le_iff]
      cases h1 : Wasm.IEEE32.eq x.toBits lo.toBits <;>
        cases h2 : Wasm.IEEE32.lt x.toBits lo.toBits <;>
        cases h3 : Wasm.IEEE32.le hi.toBits x.toBits <;>
        cases h4 : Wasm.IEEE32.le x.toBits hi.toBits <;>
        cases h5 : Wasm.IEEE32.le lo.toBits x.toBits <;>
        cases h6 : Wasm.IEEE32.le lo.toBits hi.toBits <;>
        simp [h1, h2, h3, h4, h5, h6, F32Bits.toBits_add, F32Bits.toBits_sub, F32Bits.toBits_mul,
          F32Bits.toBits_neg, F32Bits.toBits_abs, F32Bits.toBits_min, F32Bits.toBits_max, h0, h05,
          h15]⟩) fun _ _ h => h

/-- The element of `scale32`'s build. -/
def scaleElement : Expr .u64 := .toBits32 (.binF32 .mul (.getF32 0) (.ofBits32 (.read 1 (.get 5))))

/-- The element lemma that the Wasm proof and the WGSL kernel proof share. -/
theorem scaleElement_denote (a : Float32) (x : Array Float32) (k : Nat) (hk : k < 2 ^ 64)
    (locals : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (h0 : locals 0 = some (.f32 a.toBits)) (h5 : locals 5 = some (.i64 (UInt64.ofNat k)))
    (h1 : arrays 1 = some (x.map fun v : Float32 => v.toBits.toUInt64)) :
    scaleElement.denote locals arrays = some ((a * x[k]!).toBits.toUInt64) := by
  have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
  simp [scaleElement, Expr.denote, h0, h5, h1, hkn, getElem!_map_toBits32, F32Op.apply,
    F32Bits.toBits_mul]

/-- `scale32` with its two arguments as one pair. -/
def scale32Pair (v : Float32 × Array Float32) : Array Float32 := scale32 v.1 v.2

theorem scale32_implements : Implements binary32.module 7 scale32Pair := by
  refine Func.implements_heap binary32.funcs 5 binary32.scale32.ir "scale32" rfl scale32Pair
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨a, x⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, ⟨px, rfl, hXs⟩⟩ hCap
  change heap.Borrowed initial px (x.map fun v : Float32 => v.toBits.toUInt64) at hXs
  have hMemory32 : binary32.module.memIs64 = false := rfl
  have hImports : binary32.module.imports = [] := rfl
  have hAlloc : binary32.module.funcs[0]? = some (allocFunction 0) := rfl
  have hX := hXs.values
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  let start : State :=
    { params := [.f32 a.toBits, .i64 px], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  let s1 := start.update 2 (.i64 (UInt64.ofNat x.size))
  show Triple _ (.seq (.arraySize 2 1) (.build 3 4 5 (.get 2) scaleElement)) 6
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hLength, hX.lengthRead, State.set?_eq_update, s1,
      start, State.get]
  refine (Stmt.build_spec (n := UInt64.ofNat x.size)
    (fun i => (a * x[i.toNat]!).toBits.toUInt64) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [s1, start]) hHeap hCap
    ⟨s1, by simp [Expr.eval, s1, State.get_update_same (by simp [start] :
      2 < start.params.length + start.locals.length)]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 2 ∧ state.locals.length = 5 :=
      ⟨by rw [hFrame.params]; simp [s1, start], by rw [hFrame.locals]; simp [s1, start]⟩
    have hKeep : ∀ j, j < 2 → state.get j = start.get j := fun j hj => by
      rw [hFrame.get j (by omega) (by simp; omega)]
      simp only [s1]
      rw [State.get_update_ne (by omega)]
    have hk64 : k < 2 ^ 64 := by simp at hk; omega
    have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
    let locals : Nat → Option Wasm.Value := fun j =>
      if j = 0 then some (.f32 a.toBits) else if j = 5 then some (.i64 (UInt64.ofNat k)) else none
    let arrays : Nat → Option (Array UInt64) := fun j =>
      if j = 1 then some (x.map fun v : Float32 => v.toBits.toUInt64) else none
    have hAgree : Agrees locals arrays store 6 state := by
      refine ⟨fun j v hj => ?_, fun j ys hj => ?_⟩
      · simp only [locals] at hj
        split at hj
        · rename_i h0; subst h0
          cases hj
          exact ⟨by decide, (hKeep 0 (by decide)).trans rfl⟩
        · split at hj
          · rename_i h5; subst h5
            cases hj
            exact ⟨by decide, hIndex⟩
          · cases hj
      · simp only [arrays] at hj
        split at hj
        · rename_i h1; subst h1
          cases hj
          exact ⟨by decide, px, (hKeep 1 (by decide)).trans rfl, hAt px _ hXs⟩
        · cases hj
    have hden := scaleElement_denote a x k hk64 locals arrays (by simp [locals])
      (by simp [locals]) (by simp [arrays])
    obtain ⟨next, hEval⟩ := Expr.eval_denote scaleElement 6 state _ hAgree
      (by simp [scaleElement, Expr.scratchWidth, hState.1, hState.2]) hden
    exact ⟨next, by rw [hEval, hkn]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [binary32.scale32.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  rw [scale32Pair, show scale32 a x = LeanExe.build (UInt64.ofNat x.size)
    (fun i => a * x[i.toNat]!) from rfl, build_map]
  exact hNew.owned

/-- The element of `axpyArray32`'s build. -/
def axpyArrayElement : Expr .u64 :=
  .toBits32 (.binF32 .add (.binF32 .mul (.getF32 0) (.ofBits32 (.read 1 (.get 6))))
    (.ofBits32 (.read 2 (.get 6))))

/-- The element lemma that the Wasm proof and the WGSL kernel proof share. -/
theorem axpyArrayElement_denote (a : Float32) (x y : Array Float32) (k : Nat) (hk : k < 2 ^ 64)
    (locals : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (h0 : locals 0 = some (.f32 a.toBits)) (h6 : locals 6 = some (.i64 (UInt64.ofNat k)))
    (h1 : arrays 1 = some (x.map fun v : Float32 => v.toBits.toUInt64))
    (h2 : arrays 2 = some (y.map fun v : Float32 => v.toBits.toUInt64)) :
    axpyArrayElement.denote locals arrays = some ((a * x[k]! + y[k]!).toBits.toUInt64) := by
  have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
  simp [axpyArrayElement, Expr.denote, h0, h6, h1, h2, hkn, getElem!_map_toBits32, F32Op.apply,
    F32Bits.toBits_add, F32Bits.toBits_mul]

/-- `axpyArray32` with its three arguments as one tuple. -/
def axpyArray32Tuple (v : Float32 × Array Float32 × Array Float32) : Array Float32 :=
  axpyArray32 v.1 v.2.1 v.2.2

theorem axpyArray32_implements : Implements binary32.module 8 axpyArray32Tuple := by
  refine Func.implements_heap binary32.funcs 6 binary32.axpyArray32.ir "axpyArray32" rfl
    axpyArray32Tuple
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, _, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨a, x, y⟩ heap initial _ hHeap
    ⟨_, _, rfl, rfl, _, _, rfl, ⟨px, rfl, hXs⟩, ⟨py, rfl, hYs⟩⟩ hCap
  change heap.Borrowed initial px (x.map fun v : Float32 => v.toBits.toUInt64) at hXs
  change heap.Borrowed initial py (y.map fun v : Float32 => v.toBits.toUInt64) at hYs
  have hMemory32 : binary32.module.memIs64 = false := rfl
  have hImports : binary32.module.imports = [] := rfl
  have hAlloc : binary32.module.funcs[0]? = some (allocFunction 0) := rfl
  have hX := hXs.values
  have hLength := hX.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hxsize := hX.size_lt
  simp only [Array.size_map] at hxsize
  let start : State :=
    { params := [.f32 a.toBits, .i64 px, .i64 py], locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  let s1 := start.update 3 (.i64 (UInt64.ofNat x.size))
  show Triple _ (.seq (.arraySize 3 1) (.build 4 5 6 (.get 3) axpyArrayElement)) 7
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hLength, hX.lengthRead, State.set?_eq_update, s1,
      start, State.get]
  refine (Stmt.build_spec (n := UInt64.ofNat x.size)
    (fun i => (a * x[i.toNat]! + y[i.toNat]!).toBits.toUInt64) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [s1, start]) hHeap hCap
    ⟨s1, by simp [Expr.eval, s1, State.get_update_same (by simp [start] : 3 < start.params.length + start.locals.length)]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro k store state hk hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 5 :=
      ⟨by rw [hFrame.params]; simp [s1, start], by rw [hFrame.locals]; simp [s1, start]⟩
    have hKeep : ∀ j, j < 3 → state.get j = start.get j := fun j hj => by
      rw [hFrame.get j (by omega) (by simp; omega)]
      simp only [s1]
      rw [State.get_update_ne (by omega)]
    have hk64 : k < 2 ^ 64 := by simp at hk; omega
    have hkn : (UInt64.ofNat k).toNat = k := by simp; omega
    let locals : Nat → Option Wasm.Value := fun j =>
      if j = 0 then some (.f32 a.toBits) else if j = 6 then some (.i64 (UInt64.ofNat k)) else none
    let arrays : Nat → Option (Array UInt64) := fun j =>
      if j = 1 then some (x.map fun v : Float32 => v.toBits.toUInt64)
      else if j = 2 then some (y.map fun v : Float32 => v.toBits.toUInt64) else none
    have hAgree : Agrees locals arrays store 7 state := by
      refine ⟨fun j v hj => ?_, fun j ys hj => ?_⟩
      · simp only [locals] at hj
        split at hj
        · rename_i h0; subst h0
          cases hj
          exact ⟨by decide, (hKeep 0 (by decide)).trans rfl⟩
        · split at hj
          · rename_i h6; subst h6
            cases hj
            exact ⟨by decide, hIndex⟩
          · cases hj
      · simp only [arrays] at hj
        split at hj
        · rename_i h1; subst h1
          cases hj
          exact ⟨by decide, px, (hKeep 1 (by decide)).trans rfl, hAt px _ hXs⟩
        · split at hj
          · rename_i h2; subst h2
            cases hj
            exact ⟨by decide, py, (hKeep 2 (by decide)).trans rfl, hAt py _ hYs⟩
          · cases hj
    have hden := axpyArrayElement_denote a x y k hk64 locals arrays (by simp [locals])
      (by simp [locals]) (by simp [arrays]) (by simp [arrays])
    obtain ⟨next, hEval⟩ := Expr.eval_denote axpyArrayElement 7 state _ hAgree
      (by simp [axpyArrayElement, Expr.scratchWidth, hState.1, hState.2]) hden
    exact ⟨next, by rw [hEval, hkn]⟩
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [binary32.axpyArray32.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, hNew.keeps⟩
  rw [axpyArray32Tuple, show axpyArray32 a x y = LeanExe.build (UInt64.ofNat x.size)
    (fun i => a * x[i.toNat]! + y[i.toNat]!) from rfl, build_map]
  exact hNew.owned

/-- `encode` succeeds on `binary32.module`, and its bytes decode to a module that computes
`axpy32`, `hypot32`, `ratio32`, `matVec32`, `piecewise32`, `scale32`, and `axpyArray32` bit
for bit. -/
theorem binary32_bytes : ∃ bytes, Wasm.Encoding.encode binary32.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 axpy32Tuple ∧
      Implements m 3 hypot32Pair ∧ Implements m 4 ratio32Tuple ∧
      Implements m 5 matVec32Tuple ∧ Implements m 6 piecewise32Tuple ∧
      Implements m 7 scale32Pair ∧ Implements m 8 axpyArray32Tuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip binary32.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, binary32.module, decoded, axpy32_implements, hypot32_implements,
    ratio32_implements, matVec32_implements, piecewise32_implements, scale32_implements,
    axpyArray32_implements⟩

#print axioms binary32_bytes

end Project.Binary32
