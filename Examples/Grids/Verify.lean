import Examples.Grids.Module
import Project.IR.Correct
import Project.IR.Run
import Project.IR.RecordRead
import Project.IR.BuildRecord
import Project.ProofKit.F64Bits
import Project.Encoding.RoundTrip

/-! The compiled reads and builds of arrays of records compute their Lean definitions.  An array
of `Cell` is stored as `flatWords`, nine words for each cell; `flatWords_read` gives each word
the compiled code reads, and `Stmt.buildRecords_spec` gives the array a record build stores. -/

namespace Examples.Grids

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Grids

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩
instance : Flat Conserved (Float × Float × Float × Float) :=
  ⟨fun s => (s.density, s.mx, s.my, s.energy)⟩
instance : Flat Cell (UInt64 × Conserved × Float × UInt64 × Bool × Phase) :=
  ⟨fun c => (c.index, c.state, c.pressure, c.status, c.ok, c.phase)⟩
instance : Flat Mass Float := ⟨Mass.value⟩

def densityTuple : Array Cell × UInt64 → Float := fun (g, i) => density g i
def pressureTuple : Array Cell × UInt64 → Float := fun (g, i) => pressure g i
def indexAtTuple : Array Cell × UInt64 → UInt64 := fun (g, i) => indexAt g i
def okAtTuple : Array Cell × UInt64 → Bool := fun (g, i) => okAt g i
def energySumTuple : Array Cell × UInt64 × UInt64 → Float := fun (g, i, j) => energySum g i j
def isGasTuple : Array Cell × UInt64 → Bool := fun (g, i) => isGas g i
def flagAtTuple : Array Bool × UInt64 → Bool := fun (xs, i) => flagAt xs i
def massAtTuple : Array Mass × UInt64 → Float := fun (xs, i) => massAt xs i

theorem zero_toBits : (default : Float).toBits = 0 := by
  change (UInt64.toFloat 0).toBits = 0
  rw [F64Convert.toBits_toFloat]
  decide +kernel

theorem cell_length (c : Cell) : (Scalar.values c).length = 9 := rfl

theorem cell_default : (Scalar.values (default : Cell)).map Value.word = List.replicate 9 0 := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map, List.cons_append, List.nil_append]
  rw [show (default : Cell) = ⟨0, ⟨default, default, default, default⟩, default, 0, false, .solid⟩
    from rfl]
  simp [zero_toBits]

theorem bool_length (b : Bool) : (Scalar.values b).length = 1 := rfl

theorem bool_default : (Scalar.values (default : Bool)).map Value.word = [0] := rfl

theorem mass_length (x : Mass) : (Scalar.values x).length = 1 := rfl

theorem mass_default : (Scalar.values (default : Mass)).map Value.word = [0] := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map]
  rw [show (default : Mass).value = default from rfl, zero_toBits]

/-- Evaluates a compiled body and its results, with the given lemmas. -/
macro "evaluate" "[" args:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? :
    tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
    Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get, State.update,
    U64Op.apply, F64Op.apply, Scalar.values, ScalarType.valueType, Expr.evalResults,
    ScalarType.value, Flat.flat, Value.word, $args,*] $[$loc]?)

/-- `hRead` gives component `j` of cell `i` of `grid`, laid out as `hW` states, read as the
compiled code reads it. -/
macro "cell_read" hRead:ident hW:ident grid:ident i:ident j:num : tactic =>
  `(tactic| have $hRead := flatWords_read cell_length (j := $j) (by decide) (by decide)
    cell_default (xs := $grid) (by have := ($hW).1; omega) $i)

theorem density_implements : Implements grids.module 2 densityTuple := by
  refine Func.implements grids.funcs 0 grids.density.ir "density" rfl densityTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 1
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.density.ir, Expr.readValue_at hW, densityTuple, density, hi] at hRead ⊢ <;>
    simpa using hRead

theorem pressure_implements : Implements grids.module 3 pressureTuple := by
  refine Func.implements grids.funcs 1 grids.pressure.ir "pressure" rfl pressureTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 5
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.pressure.ir, Expr.readValue_at hW, pressureTuple, pressure, hi] at hRead ⊢ <;>
    simpa using hRead

theorem indexAt_implements : Implements grids.module 4 indexAtTuple := by
  refine Func.implements grids.funcs 2 grids.indexAt.ir "indexAt" rfl indexAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 0
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.indexAt.ir, Expr.readValue_at hW, indexAtTuple, indexAt, hi] at hRead ⊢ <;>
    simpa using hRead

theorem okAt_implements : Implements grids.module 5 okAtTuple := by
  refine Func.implements grids.funcs 3 grids.okAt.ir "okAt" rfl okAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 7
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.okAt.ir, Expr.readValue_at hW, okAtTuple, okAt, hi] at hRead ⊢ <;>
    simpa using hRead

theorem count_implements : Implements grids.module 6 count := by
  refine Func.implements grids.funcs 4 grids.count.ir "count" rfl count
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro grid heap initial _ - ⟨ptr, rfl, hGrid⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  have hCount := flatWords_count cell_length (by decide) (by decide) grid hW.size_lt
  refine Stmt.run_triple ?_
  evaluate [grids.count.ir, hLength, hW.lengthRead, count]
  exact hCount

theorem energySum_implements : Implements grids.module 7 energySumTuple := by
  refine Func.implements grids.funcs 5 grids.energySum.ir "energySum" rfl energySumTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i, j⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead1 hW grid i 4
  cell_read hRead2 hW grid j 4
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;> by_cases hj : j < 536870912 <;>
    evaluate [grids.energySum.ir, Expr.readValue_at hW, energySumTuple, energySum, hi, hj,
      F64Bits.toBits_add] at hRead1 hRead2 ⊢ <;>
    rw [← hRead1, ← hRead2]

theorem isGas_implements : Implements grids.module 8 isGasTuple := by
  refine Func.implements grids.funcs 6 grids.isGas.ir "isGas" rfl isGasTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨grid, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hGrid⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords grid) at hGrid
  have hW := hGrid.values
  cell_read hRead hW grid i 8
  refine Stmt.run_triple ?_
  by_cases hi : i < 536870912 <;>
    evaluate [grids.isGas.ir, Expr.readValue_at hW, isGasTuple, isGas, hi] at hRead ⊢ <;>
    revert hRead <;> cases grid[i.toNat]!.phase <;> simp_all

theorem flagAt_implements : Implements grids.module 9 flagAtTuple := by
  refine Func.implements grids.funcs 7 grids.flagAt.ir "flagAt" rfl flagAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨flags, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hFlags⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords flags) at hFlags
  have hW := hFlags.values
  refine Stmt.run_triple ?_
  evaluate [grids.flagAt.ir, Expr.readValue_at hW, flagAtTuple, flagAt,
    flatWords_getElem!_one bool_length bool_default]

theorem flagCount_implements : Implements grids.module 10 flagCount := by
  refine Func.implements grids.funcs 8 grids.flagCount.ir "flagCount" rfl flagCount
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro flags heap initial _ - ⟨ptr, rfl, hFlags⟩
  change heap.Borrowed initial ptr (flatWords flags) at hFlags
  have hW := hFlags.values
  have hLength := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.run_triple ?_
  evaluate [grids.flagCount.ir, hLength, hW.lengthRead, flagCount, flatWords_size bool_length]

theorem massAt_implements : Implements grids.module 11 massAtTuple := by
  refine Func.implements grids.funcs 9 grids.massAt.ir "massAt" rfl massAtTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨masses, i⟩ heap initial _ - ⟨_, _, rfl, ⟨ptr, rfl, hMasses⟩, rfl⟩
  change heap.Borrowed initial ptr (flatWords masses) at hMasses
  have hW := hMasses.values
  refine Stmt.run_triple ?_
  evaluate [grids.massAt.ir, Expr.readValue_at hW, massAtTuple, massAt,
    flatWords_getElem!_one mass_length mass_default]

theorem conserved_length (c : Conserved) : (Scalar.values c).length = 4 := rfl

/-- Element `i` of `ramp`. -/
def rampElement (i : UInt64) : Conserved := ⟨i.toFloat, 0, 0, 1⟩

theorem rampElement_words (i : UInt64) : (Scalar.values (rampElement i)).map Value.word =
    [IEEE64.convertI64U i, 0, 0, 4607182418800017408] := by
  have hZero : (0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1 : Float).toBits = 4607182418800017408 := by decide +kernel
  simp only [rampElement, Scalar.values, Flat.flat, List.map, List.cons_append, List.nil_append,
    Value.word, F64Convert.toBits_toFloat, hZero, hOne]

theorem ramp_implements : Implements grids.module 13 ramp := by
  refine Func.implements_heap grids.funcs 11 grids.ramp.ir "ramp" rfl ramp
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  show Triple _ (Stmt.buildRecords 1 2 3 (.get 0) _
    [.toBits (.getF 4), .toBits (.getF 5), .toBits (.getF 6), .toBits (.getF 7)]) _ _ _
  refine (Stmt.buildRecords_spec (writes := [4, 5, 6, 7]) (n := n) (scratch := 8)
    (elements := [.toBits (.getF 4), .toBits (.getF 5), .toBits (.getF 6), .toBits (.getF 7)])
    rampElement conserved_length (by decide) rfl rfl rfl (by decide) (by decide) (by decide)
    (Nat.le_of_eq rfl) hHeap hCap ⟨_, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 8 := by
      rw [hFrame.params, hFrame.locals]; rfl
    let final := (((state.update 4 (.f64 (IEEE64.convertI64U (UInt64.ofNat i)))).update 5
      (.f64 0)).update 6 (.f64 0)).update 7 (.f64 4607182418800017408)
    refine Stmt.run_triple ⟨final, ?_, rfl, ?_, fun j hj => ?_⟩
    · set_option maxHeartbeats 100000 in
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, hIndex, final]
    · set_option maxHeartbeats 100000 in
      (repeat refine State.Frame.update ?_ (by simp)
       exact State.Frame.refl _ _ _)
    · rw [rampElement_words]
      simp only [List.length_cons, List.length_nil] at hj
      obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      all_goals
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem!_cons_zero,
          List.getElem!_cons_succ]
        exact Expr.yields_toBits (by simp [final, hLength])
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [grids.ramp.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    hNew.keeps⟩
  exact hNew.owned

theorem flags_implements : Implements grids.module 14 Examples.Grids.flags := by
  refine Func.implements_heap grids.funcs 12 grids.flags.ir "flags" rfl
    Examples.Grids.flags (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  show Triple _ (Stmt.buildRecords 1 2 3 (.get 0) _ [.get 4]) _ _ _
  refine (Stmt.buildRecords_spec (writes := [4]) (n := n) (scratch := 5) (elements := [.get 4])
    (before := grids.flags.ir.state (Scalar.values n))
    (fun i : UInt64 => i % 3 == 1) bool_length (by decide) rfl rfl rfl (by decide) (by decide)
    (by decide) (Nat.le_add_right 5 2) hHeap hCap ⟨_, rfl⟩ ?_).mono (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 7 := by
      rw [hFrame.params, hFrame.locals]; rfl
    let final := ((state.update 5 (.i64 (UInt64.ofNat i))).update 6 (.i64 3)).update 4
      (.i64 (if UInt64.ofNat i % 3 = 1 then 1 else 0))
    refine Stmt.run_triple ⟨final, ?_, rfl, ?_, fun j hj => ?_⟩
    · simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, hIndex, final, U64Op.apply]
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · obtain rfl : j = 0 := by simpa using hj
      exact Expr.yields_get (by simp [final, hLength, Scalar.values, Flat.flat, Value.word])
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [grids.flags.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    hNew.keeps⟩
  exact hNew.owned

def scaledTuple : Array Conserved × Float → Array Conserved := fun (xs, a) => scaled xs a

/-- Element `i` of `scaled xs a`. -/
def scaledElement (xs : Array Conserved) (a : Float) (i : UInt64) : Conserved :=
  let c := xs[i.toNat]!
  { c with density := a * c.density, energy := a * c.energy }

theorem conserved_default :
    (Scalar.values (default : Conserved)).map Value.word = List.replicate 4 0 := by
  simp only [Scalar.values, Flat.flat, Value.word, List.map, List.cons_append, List.nil_append]
  rw [show (default : Conserved) = ⟨default, default, default, default⟩ from rfl]
  simp [zero_toBits]

theorem scaledElement_words (xs : Array Conserved) (a : Float) (i : UInt64) :
    (Scalar.values (scaledElement xs a i)).map Value.word =
      [IEEE64.mul a.toBits xs[i.toNat]!.density.toBits, xs[i.toNat]!.mx.toBits,
        xs[i.toNat]!.my.toBits, IEEE64.mul a.toBits xs[i.toNat]!.energy.toBits] := by
  simp only [scaledElement, Scalar.values, Flat.flat, List.map, List.cons_append,
    List.nil_append, Value.word, F64Bits.toBits_mul]

theorem scaled_implements : Implements grids.module 12 scaledTuple := by
  refine Func.implements_heap grids.funcs 10 grids.scaled.ir "scaled" rfl scaledTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨xs, a⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ptr, rfl, hXs⟩, rfl⟩ hCap
  change heap.Borrowed initial ptr (flatWords xs) at hXs
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count conserved_length (by decide) (by decide) xs hW.size_lt
  have hSize : (flatWords xs).size < 536870912 := by have := hW.1; omega
  have hWords := flatWords_size conserved_length xs
  set start := grids.scaled.ir.state ([.i64 ptr] ++ Scalar.values a) with hStartDef
  let s1 := start.update 2 (.i64 (UInt64.ofNat (flatWords xs).size))
  have hStart : start.params.length + start.locals.length = 17 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  have hGet1 : start.get 1 = some (.f64 a.toBits) := rfl
  show Triple _ (.seq (.load .u64 2 (.get 0)) (Stmt.buildRecords 3 4 5
    (.bin .divU (.get 2) (.const 4)) _
    [.toBits (.getF 11), .toBits (.getF 12), .toBits (.getF 13), .toBits (.getF 14)])) _ _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  refine (Stmt.buildRecords_spec (writes := [6, 7, 8, 9, 10, 11, 12, 13, 14])
    (n := xs.size.toUInt64) (scratch := 15)
    (elements := [.toBits (.getF 11), .toBits (.getF 12), .toBits (.getF 13), .toBits (.getF 14)])
    (before := s1) (scaledElement xs a) conserved_length (by decide) rfl rfl rfl (by decide)
    (by decide) (by decide) (by simp [s1, hStart]) hHeap hCap
    ⟨(s1.update 15 (.i64 (UInt64.ofNat (flatWords xs).size))).update 16 (.i64 4),
      by simp [Expr.eval, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    have hLength : state.params.length + state.locals.length = 17 := by
      rw [hFrame.params, hFrame.locals]; simpa [s1] using hStart
    have hS0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s1, hGet0])
    have hS1 : state.get 1 = some (.f64 a.toBits) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s1, hGet1])
    have hX := hAt ptr _ hXs
    have hi' : i < xs.size := by
      have : xs.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hGuard : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    set c := xs[(UInt64.ofNat i).toNat]! with hc
    have hR : ∀ j, j < 4 → ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue store.mem 0 (UInt64.ofNat i * UInt64.ofNat 4 + UInt64.ofNat j) st =
          some (((Scalar.values c).map Value.word)[j]!, st) := fun j hj st h0 =>
      Expr.readValue_record conserved_length hj (by decide) conserved_default hX hGuard h0
    have hR0 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue store.mem 0 (UInt64.ofNat i * 4) st = some (c.density.toBits, st) :=
      fun st h0 => by simpa [Scalar.values, Flat.flat, Value.word] using hR 0 (by decide) st h0
    have hR1 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue store.mem 0 (UInt64.ofNat i * 4 + 1) st = some (c.mx.toBits, st) :=
      fun st h0 => by simpa [Scalar.values, Flat.flat, Value.word] using hR 1 (by decide) st h0
    have hR2 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue store.mem 0 (UInt64.ofNat i * 4 + 2) st = some (c.my.toBits, st) :=
      fun st h0 => by simpa [Scalar.values, Flat.flat, Value.word] using hR 2 (by decide) st h0
    have hR3 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue store.mem 0 (UInt64.ofNat i * 4 + 3) st = some (c.energy.toBits, st) :=
      fun st h0 => by simpa [Scalar.values, Flat.flat, Value.word] using hR 3 (by decide) st h0
    simp only [scaledElement_words, ← hc]
    refine Stmt.run_triple ?_
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, hIndex, hS0, hS1, hGuard, hR0, hR1,
      hR2, hR3, U64Op.apply, F64Op.apply]
    refine ⟨?_, fun j hj => ?_⟩
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      all_goals
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some]
        exact Expr.yields_toBits (by simp [hLength])
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
    by simp [grids.scaled.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    hNew.keeps⟩
  exact hNew.owned

/-- One step of `totalDensity`'s loop. -/
def totalDensityStep (xs : Array Conserved) (i : UInt64) (acc : Float) : Float :=
  acc + xs[i.toNat]!.density

theorem totalDensity_implements : Implements grids.module 15 totalDensity := by
  refine Func.implements grids.funcs 13 grids.totalDensity.ir "totalDensity" rfl totalDensity
    (by rintro _ _ _ _ ⟨_, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ - ⟨ptr, rfl, hXs⟩
  change heap.Borrowed initial ptr (flatWords xs) at hXs
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hCount := flatWords_count conserved_length (by decide) (by decide) xs hW.size_lt
  have hSize : (flatWords xs).size < 536870912 := by have := hW.1; omega
  have hWords := flatWords_size conserved_length xs
  have hZero : (0 : Float).toBits = 0 := by decide +kernel
  set start := grids.totalDensity.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let s1 := start.update 1 (.i64 (UInt64.ofNat (flatWords xs).size))
  let s2 := s1.update 2 (.f64 0)
  show Triple _ (.seq (.load .u64 1 (.get 0)) (.seq (.assign 2 (.constF 0))
    (.loop 3 4 (.bin .divU (.get 1) (.const 4)) _))) 8 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2]
  have hS2 : s2.params.length + s2.locals.length = 10 := by simp [s2, s1, hStart]
  refine (Stmt.loop_spec (vars := [2]) (writes := [2, 5, 6, 7]) (init := (0 : Float))
    (n := xs.size.toUInt64) (totalDensityStep xs) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    ⟨(s2.update 8 (.i64 (UInt64.ofNat (flatWords xs).size))).update 9 (.i64 4),
      by simp [Expr.eval, s2, s1, hStart, U64Op.apply, State.set?_eq_update, ← hCount]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hStart, hZero]) ?_).mono
      (fun _ _ h => h) ?_
  · intro i acc state hi hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hFrame.params, hFrame.locals]; exact hS2
    have hS0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have hAcc : state.get 2 = some (.f64 acc.toBits) := by
      simpa [State.Holds, Scalar.values] using hHolds
    have hi' : i < xs.size := by
      have : xs.size < 2 ^ 64 := by omega
      simpa [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' this] using hi
    have hGuard : UInt64.ofNat i < 536870912 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
      simp; omega
    set c := xs[(UInt64.ofNat i).toNat]! with hc
    have hR0 : ∀ st : State, st.get 0 = some (.i64 ptr) →
        Expr.readValue initial.mem 0 (UInt64.ofNat i * 4) st = some (c.density.toBits, st) :=
      fun st h0 => by
        have := Expr.readValue_record (j := 0) conserved_length (by decide) (by decide)
          conserved_default hW hGuard h0
        rw [← hc] at this
        simpa [Scalar.values, Flat.flat, Value.word] using this
    refine Stmt.run_triple ?_
    simp [Stmt.run, Expr.eval, State.set?_eq_update, hLength, hIndex, hS0, hAcc, hGuard, hR0,
      U64Op.apply, F64Op.apply]
    refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by simp)
      exact State.Frame.refl _ _ _
    · simp only [totalDensityStep, ← hc]
      simp [State.Holds, Scalar.values, F64Bits.toBits_add, hLength]
  · rintro store state ⟨rfl, -, hHolds⟩
    refine ⟨rfl, _, state, ?_, rfl⟩
    have g2 : state.get 2 = some (.f64 (totalDensity xs).toBits) := by
      rw [show totalDensity xs = LeanExe.loop xs.size.toUInt64 0 (totalDensityStep xs) from rfl]
      simpa [State.Holds, Scalar.values] using hHolds
    simp [grids.totalDensity.ir, Func.scratch, Expr.evalResults, Expr.eval, g2, Scalar.values]

/-- `encode` succeeds on `grids.module`, and its bytes decode to a module that computes each
function exactly. -/
theorem grids_bytes : ∃ bytes, Wasm.Encoding.encode grids.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 densityTuple ∧
      Implements m 3 pressureTuple ∧ Implements m 4 indexAtTuple ∧ Implements m 5 okAtTuple ∧
      Implements m 6 count ∧ Implements m 7 energySumTuple ∧ Implements m 8 isGasTuple ∧
      Implements m 9 flagAtTuple ∧ Implements m 10 flagCount ∧ Implements m 11 massAtTuple ∧
      Implements m 12 scaledTuple ∧ Implements m 13 ramp ∧
      Implements m 14 Examples.Grids.flags ∧ Implements m 15 totalDensity := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip grids.module (by decide +kernel) (by decide +kernel)
  exact ⟨bytes, success, grids.module, decoded, density_implements, pressure_implements,
    indexAt_implements, okAt_implements, count_implements, energySum_implements,
    isGas_implements, flagAt_implements, flagCount_implements, massAt_implements,
    scaled_implements, ramp_implements, flags_implements, totalDensity_implements⟩

end Examples.Grids
