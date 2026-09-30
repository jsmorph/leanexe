import Project.Clob.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Call
import Project.Encoding.RoundTrip

namespace Project.Clob

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

/-- `marketBuy` with its three arguments as one tuple. -/
def marketBuyTuple (x : Array UInt64 × Array UInt64 × UInt64) : Array UInt64 :=
  LeanExe.Examples.Clob.marketBuy x.1 x.2.1 x.2.2

/-- One step of `marketBuy`'s loop over the ask levels. -/
def step (prices sizes : Array UInt64) (i : UInt64) (s : UInt64 × UInt64) : UInt64 × UInt64 :=
  (s.1 - min s.1 sizes[i.toNat]!, s.2 + min s.1 sizes[i.toNat]! * prices[i.toNat]!)

theorem marketBuy_eq (prices sizes : Array UInt64) (qty : UInt64) :
    LeanExe.Examples.Clob.marketBuy prices sizes qty =
      #[qty - (LeanExe.loop prices.size.toUInt64 (qty, 0) (step prices sizes)).1,
        (LeanExe.loop prices.size.toUInt64 (qty, 0) (step prices sizes)).2] := rfl

/-- The compiled loop body: `take`, the next state in two temporaries, and the
copies. -/
def body : Stmt :=
  .seq (.assign 8 (.ite (.leU (.get 4) (.read 1 (.get 7))) (.get 4) (.read 1 (.get 7)))) <|
  .seq (.assign 9 (.bin .sub (.get 4) (.get 8))) <|
  .seq (.assign 10 (.bin .add (.get 5) (.bin .mul (.get 8) (.read 0 (.get 7))))) <|
  .seq (.assign 4 (.get 9)) (.assign 5 (.get 10))

example : clob.marketBuy.ir.body = .seq (.arraySize 3 0) (.seq (.assign 4 (.get 2))
    (.seq (.assign 5 (.const 0)) (.seq (.loop 6 7 (.get 3) body)
      (.arrayLiteral 11 [.bin .sub (.get 2) (.get 4), .get 5])))) := rfl

theorem body_run {initial : Store Unit} {pp ps : UInt64} {prices sizes : Array UInt64}
    (hP : UInt64Array.At initial pp prices) (hS : UInt64Array.At initial ps sizes)
    {state : State} {k : Nat} {r c : UInt64}
    (hParams : state.params.length = 3) (hLocals : state.locals.length = 10)
    (h0 : state.get 0 = some (.i64 pp)) (h1 : state.get 1 = some (.i64 ps))
    (h4 : state.get 4 = some (.i64 r)) (h5 : state.get 5 = some (.i64 c))
    (h7 : state.get 7 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, body.run initial.mem 12 state = some final ∧
      State.Frame 12 [4, 5, 8, 9, 10] state final ∧
      final.Holds [4, 5] (Scalar.values (step prices sizes (UInt64.ofNat k) (r, c))) := by
  simp [body, Stmt.run, Expr.eval, h4, h5, h7, Expr.readValue_at hS, Expr.readValue_at hP, h0, h1,
    State.set?_eq_update, hParams, hLocals, U64Op.apply]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, step, hParams, hLocals, min]

theorem marketBuy_implements :
    Implements clob.module 3 marketBuyTuple (fun _ => 72) := by
  refine Func.implements_heap clob.funcs 0 clob.marketBuy.ir "marketBuy" rfl marketBuyTuple (fun _ => 72)
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, qty⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  have hP := hPrices.values
  have hS := hSizes.values
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 qty], locals := List.replicate 10 (.i64 0) }
  let s1 := start.update 3 (.i64 (UInt64.ofNat prices.size))
  let s2 := s1.update 4 (.i64 qty)
  let s3 := s2.update 5 (.i64 0)
  show Triple _ (.seq (.arraySize 3 0) (.seq (.assign 4 (.get 2)) (.seq (.assign 5 (.const 0))
    (.seq (.loop 6 7 (.get 3) body) (.arrayLiteral 11 [.bin .sub (.get 2) (.get 4), .get 5])))))
    12 (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 10 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hGet2 : start.get 2 = some (.i64 qty) := rfl
  have hLength := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, hGet2, State.set?_eq_update, hParams, hLocals, s1, s2]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2, s3]
  have hGet3 : s3.get 3 = some (.i64 prices.size.toUInt64) := by
    simp [s3, s2, s1, hParams, hLocals]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [4, 5]) (writes := [4, 5, 8, 9, 10])
    (init := (qty, (0 : UInt64))) (n := prices.size.toUInt64) (step prices sizes)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [s3, s2, s1, hParams, hLocals]) ⟨s3, by simp [Expr.eval, hGet3]⟩
    (by simp [State.Holds, Scalar.values, s3, s2, s1, hParams, hLocals]) ?_) ?_
  · intro k ⟨r, c⟩ state hk hFrame hHolds hIndex hLimit
    have hStateParams : state.params.length = 3 := by rw [hFrame.params]; simp [s3, s2, s1, hParams]
    have hStateLocals : state.locals.length = 10 := by rw [hFrame.locals]; simp [s3, s2, s1, hLocals]
    have h0 : state.get 0 = some (.i64 pp) := (hFrame.get 0 (by decide) (by decide)).trans
      (by simp [s3, s2, s1, hGet0])
    have h1 : state.get 1 = some (.i64 ps) := (hFrame.get 1 (by decide) (by decide)).trans
      (by simp [s3, s2, s1]; rfl)
    obtain ⟨h4, h5⟩ : state.get 4 = some (.i64 r) ∧ state.get 5 = some (.i64 c) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      body_run hP hS hStateParams hStateLocals h0 h1 h4 h5 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  apply Triple.of_forall
  rintro store s4 ⟨rfl, hFrame4, hHolds4⟩
  generalize hResult : LeanExe.loop prices.size.toUInt64 (qty, 0) (step prices sizes) = result
    at hHolds4
  obtain ⟨h4, h5⟩ : s4.get 4 = some (.i64 result.1) ∧ s4.get 5 = some (.i64 result.2) := by
    simpa [State.Holds, Scalar.values] using hHolds4
  have h2 : s4.get 2 = some (.i64 qty) := (hFrame4.get 2 (by decide) (by decide)).trans
    (by simp [s3, s2, s1, hGet2])
  refine (Stmt.arrayLiteral_spec (values := [.bin .sub (.get 2) (.get 4), .get 5])
    (words := [qty - result.1, result.2]) hMemory32 hImports hAlloc (by decide)
    (by rw [hFrame4.params, hFrame4.locals]; simp [s3, s2, s1, hParams, hLocals]) hHeap hRoom ?_).mono
      (fun _ _ h => h) ?_
  · refine .cons (fun _ state hFrame => ⟨state, ?_⟩) (.cons (fun _ state hFrame => ⟨state, ?_⟩) .nil)
    · simp [Expr.eval, hFrame.get 2 (by decide) (by decide), hFrame.get 4 (by decide) (by decide),
        h2, h4, U64Op.apply]
    · simp [Expr.eval, hFrame.get 5 (by decide) (by decide), h5]
  · rintro store state ⟨ptr, -, hPtr, hNew⟩
    have hOwned := hNew.owned
    refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨pp, rfl, hNew.borrowed pp prices hPrices⟩, _, _, rfl,
      ⟨ps, rfl, hNew.borrowed ps sizes hSizes⟩, rfl⟩, hNew.top, hNew.pages, hNew.borrowed,
      fun p ws h => (hNew.ownedKeep p ws h).1, [.i64 ptr], state,
      by simp [clob.marketBuy.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
    rw [marketBuyTuple, marketBuy_eq, hResult]
    simpa using hOwned

/-- `fillLevel` with its three arguments as one tuple. -/
def fillTuple (x : Array UInt64 × UInt64 × UInt64) : Array UInt64 :=
  LeanExe.Examples.Clob.fillLevel x.1 x.2.1 x.2.2

/-- The bytes `fillLevel` may allocate: one array of the input's length. -/
def fillNeed (x : Array UInt64 × UInt64 × UInt64) : Nat := 48 + 8 * (x.1.size + 1)

theorem fillLevel_implements : Implements clob.module 4 fillTuple fillNeed := by
  refine Func.implements_heap clob.funcs 1 clob.fillLevel.ir "fillLevel" rfl fillTuple fillNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨sizes, k, amount⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  have hS := hSizes.values
  have hSize64 := hS.size_lt
  let value := sizes[k.toNat]! - amount
  let start : State :=
    { params := [.i64 ps, .i64 k, .i64 amount], locals := List.replicate 7 (.i64 0) }
  let s1 := start.update 3 (.i64 k)
  let s2 := (s1.update 9 (.i64 k)).update 4 (.i64 value)
  let s3 := s2.update 5 (.i64 (UInt64.ofNat sizes.size))
  show Triple _ (.seq (.assign 3 (.get 1)) (.seq (.assign 4 (.bin .sub (.read 0 (.get 1)) (.get 2)))
    (.seq (.arraySize 5 0) (.build 6 7 8 (.get 5)
      (.ite (.eq (.get 8) (.get 3)) (.get 4) (.read 0 (.get 8))))))) 9
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 7 := rfl
  have hGet0 : start.get 0 = some (.i64 ps) := rfl
  have hGet1 : start.get 1 = some (.i64 k) := rfl
  have hGet2 : start.get 2 = some (.i64 amount) := rfl
  have hLength := hS.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet1, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, hGet1, hGet2, Expr.readValue_at hS, hGet0, State.set?_eq_update,
      hParams, hLocals, s1, s2, U64Op.apply, value]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hS.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1, s2, s3]
  have hn : (UInt64.ofNat sizes.size).toNat = sizes.size := UInt64.toNat_ofNat_of_lt' hSize64
  refine (Stmt.build_spec (n := UInt64.ofNat sizes.size)
    (fun j => if j = k then value else sizes[j.toNat]!) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [s3, s2, s1, hParams, hLocals]) hHeap
    (by rw [hn]; exact hRoom) ⟨s3, by simp [Expr.eval, s3, s2, s1, hParams, hLocals]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 7 := by
      rw [hFrame.params, hFrame.locals]; simp [s3, s2, s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 ps) := (hFrame.get 0 (by decide) (by decide)).trans
      (by simp [s3, s2, s1, hGet0])
    have h3 : state.get 3 = some (.i64 k) := (hFrame.get 3 (by decide) (by decide)).trans
      (by simp [s3, s2, s1, hParams, hLocals])
    have h4 : state.get 4 = some (.i64 value) := (hFrame.get 4 (by decide) (by decide)).trans
      (by simp [s3, s2, s1, hParams, hLocals])
    by_cases hjk : UInt64.ofNat j = k
    · simp [Expr.eval, hIndex, h3, h4, hjk]
    · simp [Expr.eval, hIndex, h3, hjk, Expr.readValue_at (hAt ps sizes hSizes), h0,
        State.set?_eq_update, hState.1, hState.2]
  · rintro store state ⟨ptr, -, hPtr, hNew⟩
    have hOwned := hNew.owned
    refine ⟨_, hNew.at_, ⟨_, _, rfl, ⟨ps, rfl, hNew.borrowed ps sizes hSizes⟩, rfl⟩,
      le_of_le_of_eq hNew.top (by simp [fillNeed, hn]),
      le_of_le_of_eq hNew.pages (by simp [fillNeed, hn]), hNew.borrowed,
      fun p ws h => (hNew.ownedKeep p ws h).1, [.i64 ptr], state,
      by simp [clob.fillLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
    rw [fillTuple, LeanExe.Examples.Clob.fillLevel, set!_eq_build sizes k value hSize64]
    exact hOwned

/-- `insertLevel` with its five arguments as one tuple. -/
def insertTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.insertLevel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The bytes `insertLevel` may allocate: two arrays, each one longer than its input. -/
def insertNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 2) + 8 * (x.2.1.size + 2)

/-- The element function of `insertIdx!` on bit patterns. -/
def insertAt (xs : Array UInt64) (k v : UInt64) (j : UInt64) : UInt64 :=
  if j < k then xs[j.toNat]! else if j = k then v else xs[(j - 1).toNat]!

/-- The length of the array `insertIdx!` returns. -/
def insertCount (size : Nat) (k : UInt64) : UInt64 :=
  if k.toNat ≤ size then UInt64.ofNat (size + 1) else 0

theorem insertCount_eval (size : Nat) (k : UInt64) (hSize : size + 1 < 2 ^ 64) :
    (if k ≤ UInt64.ofNat size then UInt64.ofNat size + 1 else 0) = insertCount size k := by
  have hU : UInt64.size = 2 ^ 64 := rfl
  unfold insertCount
  have hIff : k ≤ UInt64.ofNat size ↔ k.toNat ≤ size := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by omega)]
  by_cases h : k.toNat ≤ size
  · simp only [hIff.mpr h, h, ite_true, UInt64.ofNat_add]; rfl
  · simp only [hIff, h, ite_false]

theorem insertCount_toNat (size : Nat) (k : UInt64) (hSize : size + 1 < 2 ^ 64) :
    (insertCount size k).toNat ≤ size + 1 := by
  unfold insertCount
  split
  · rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
  · simp

/-- The element code of `insertIdx!` evaluates to `insertAt` when the array local
holds a laid-out array. -/
theorem insert_element {store : Store Unit} {ptr k v : UInt64} {xs : Array UInt64}
    (hArray : UInt64Array.At store ptr xs) {array kLocal vLocal index scratch : Nat}
    {state : State} {j : UInt64}
    (hLength : scratch < state.params.length + state.locals.length)
    (hArrayGet : state.get array = some (.i64 ptr)) (hArrayNe : array ≠ scratch)
    (hIndex : state.get index = some (.i64 j)) (hK : state.get kLocal = some (.i64 k))
    (hV : state.get vLocal = some (.i64 v)) :
    ∃ next, (Expr.ite (.ltU (.get index) (.get kLocal)) (.read array (.get index))
      (.ite (.eq (.get index) (.get kLocal)) (.get vLocal)
        (.read array (.bin .sub (.get index) (.const 1))))).eval store.mem scratch state =
      some (insertAt xs k v j, next) := by
  unfold insertAt
  by_cases h1 : j < k
  · simp [Expr.eval, hIndex, hK, h1, Expr.readValue_at hArray, hArrayGet, hArrayNe,
      State.set?_eq_update, hLength]
  · by_cases h2 : j = k
    · simp [Expr.eval, hIndex, hK, hV, h2]
    · simp [Expr.eval, hIndex, hK, h1, h2, Expr.readValue_at hArray, hArrayGet, hArrayNe,
        State.set?_eq_update, hLength, U64Op.apply]

theorem insertLevel_implements : Implements clob.module 5 insertTuple insertNeed := by
  refine Func.implements_heap clob.funcs 2 clob.insertLevel.ir "insertLevel" rfl insertTuple insertNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hP := hPrices.values
  have hS := hSizes.values
  have hPFit := hP.1
  have hSFit := hS.1
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k, .i64 price, .i64 size],
      locals := List.replicate 13 (.i64 0) }
  let s1 := start.update 5 (.i64 k)
  let s2 := s1.update 6 (.i64 price)
  let s3 := s2.update 7 (.i64 (UInt64.ofNat prices.size))
  let element (array kLocal vLocal index : Nat) : Expr .u64 :=
    .ite (.ltU (.get index) (.get kLocal)) (.read array (.get index))
      (.ite (.eq (.get index) (.get kLocal)) (.get vLocal)
        (.read array (.bin .sub (.get index) (.const 1))))
  let count (kLocal size : Nat) : Expr .u64 :=
    .ite (.leU (.get kLocal) (.get size)) (.bin .add (.get size) (.const 1)) (.const 0)
  show Triple _ (.seq (.assign 5 (.get 2)) (.seq (.assign 6 (.get 3)) (.seq (.arraySize 7 0)
    (.seq (.build 8 9 10 (count 5 7) (element 0 5 6 10))
      (.seq (.assign 11 (.get 2)) (.seq (.assign 12 (.get 4)) (.seq (.arraySize 13 1)
        (.build 14 15 16 (count 11 13) (element 1 11 12 16))))))))) 17
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 5 := rfl
  have hLocals : start.locals.length = 13 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hGet2 : start.get 2 = some (.i64 k) := rfl
  have hGet3 : start.get 3 = some (.i64 price) := rfl
  have hLengthP := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthP
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet2, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, hGet3, State.set?_eq_update, hParams, hLocals, s1, s2]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLengthP, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1, s2, s3]
  -- The first array.
  have hn1 := insertCount_toNat prices.size k (by omega)
  have hRoom1 : heap.Room initial clob.module
      (48 + 8 * ((insertCount prices.size k).toNat + 1)) :=
    ⟨by have := hRoom.address; simp only [insertNeed] at this; omega,
      by have := hRoom.cap; simp only [insertNeed] at this; omega⟩
  refine Stmt.seq_spec (Stmt.build_spec (n := insertCount prices.size k)
    (insertAt prices k price) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [s3, s2, s1, hParams, hLocals]) hHeap hRoom1
    ⟨s3, by simp [Expr.eval, count, s3, s2, s1, hParams, hLocals, U64Op.apply,
      insertCount_eval prices.size k (by omega)]⟩ ?_) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 5 ∧ state.locals.length = 13 := by
      rw [hFrame.params, hFrame.locals]; simp [s3, s2, s1, hParams, hLocals]
    exact insert_element (hAt pp prices hPrices) (by omega)
      ((hFrame.get 0 (by decide) (by decide)).trans (by simp [s3, s2, s1, hGet0])) (by decide)
      hIndex ((hFrame.get 5 (by decide) (by decide)).trans (by simp [s3, s2, s1, hParams, hLocals]))
      ((hFrame.get 6 (by decide) (by decide)).trans (by simp [s3, s2, s1, hParams, hLocals]))
  apply Triple.of_forall
  rintro store1 t1 ⟨ptr1, hFrame1, hPtr1, hNew1⟩
  have hAt1 := hNew1.at_
  have hOwned1 := hNew1.owned
  have hTop1 := hNew1.top
  have hPages1 := hNew1.pages
  have hKeep1 := hNew1.borrowed
  have hCaps1 := hNew1.caps
  -- The second array.
  have hS1 := (hKeep1 ps sizes hSizes).values
  have hLengthS := hS1.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthS
  have hT1 : t1.params.length = 5 ∧ t1.locals.length = 13 := by
    rw [hFrame1.params, hFrame1.locals]; simp [s3, s2, s1, hParams, hLocals]
  have hT1Get : ∀ j, j < 17 → j ∉ [8, 9, 10] → t1.get j = s3.get j := fun j hj hOut =>
    hFrame1.get j hj hOut
  have h1Get1 : t1.get 1 = some (.i64 ps) := (hT1Get 1 (by decide) (by decide)).trans
    (by simp [s3, s2, s1]; rfl)
  have h1Get2 : t1.get 2 = some (.i64 k) := (hT1Get 2 (by decide) (by decide)).trans
    (by simp [s3, s2, s1, hGet2])
  have h1Get4 : t1.get 4 = some (.i64 size) := (hT1Get 4 (by decide) (by decide)).trans
    (by simp [s3, s2, s1]; rfl)
  let u1 := t1.update 11 (.i64 k)
  let u2 := u1.update 12 (.i64 size)
  let u3 := u2.update 13 (.i64 (UInt64.ofNat sizes.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get2, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Expr.eval, h1Get4, State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get1, hLengthS, hS1.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2, u3]
  have hn2 := insertCount_toNat sizes.size k (by omega)
  have hRoom2 : (heap.allocate (UInt64.ofNat (8 * ((insertCount prices.size k).toNat + 1)))).Room
      store1 clob.module
      (48 + 8 * ((insertCount sizes.size k).toNat + 1)) := by
    have hNeed : (UInt64.ofNat (8 * ((insertCount prices.size k).toNat + 1))).toNat =
        8 * ((insertCount prices.size k).toNat + 1) :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    refine Heap.Room.after_allocate ⟨?_, ?_⟩ hCaps1
    · have := hRoom.address; simp only [insertNeed] at this; rw [hNeed]; omega
    · have := hRoom.cap; simp only [insertNeed] at this; rw [hNeed]; omega
  refine (Stmt.build_spec (n := insertCount sizes.size k)
    (insertAt sizes k size) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [u3, u2, u1, hT1.1, hT1.2]) hAt1 hRoom2
    ⟨u3, by simp [Expr.eval, count, u3, u2, u1, hT1.1, hT1.2, U64Op.apply,
      insertCount_eval sizes.size k (by omega)]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 5 ∧ state.locals.length = 13 := by
      rw [hFrame.params, hFrame.locals]; simp [u3, u2, u1, hT1.1, hT1.2]
    exact insert_element (hAt ps sizes (hKeep1 ps sizes hSizes)) (by omega)
      ((hFrame.get 1 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get1])) (by decide)
      hIndex ((hFrame.get 11 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2]))
      ((hFrame.get 12 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2]))
  rintro store2 t2 ⟨ptr2, hFrame2, hPtr2, hNew2⟩
  have hAt2 := hNew2.at_
  have hOwned2 := hNew2.owned
  have hTop2 := hNew2.top
  have hPages2 := hNew2.pages
  have hKeep2 := hNew2.borrowed
  have hPtr1' : t2.get 8 = some (.i64 ptr1) := by
    rw [hFrame2.get 8 (by decide) (by decide)]; simp [u3, u2, u1, hPtr1]
  have hNeed1 : (UInt64.ofNat (8 * ((insertCount prices.size k).toNat + 1))).toNat =
      8 * ((insertCount prices.size k).toNat + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine ⟨_, hAt2, ⟨_, _, rfl, ⟨pp, rfl, hKeep2 pp prices (hKeep1 pp prices hPrices)⟩, _, _, rfl,
      ⟨ps, rfl, hKeep2 ps sizes (hKeep1 ps sizes hSizes)⟩, rfl⟩, ?_, ?_,
    fun p ws h => hKeep2 p ws (hKeep1 p ws h),
    fun p ws h => (hNew2.ownedKeep p ws (hNew1.ownedKeep p ws h).1).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.insertLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    [.i64 ptr1], [.i64 ptr2], rfl, ⟨ptr1, rfl, ?_⟩, ⟨ptr2, rfl, ?_⟩⟩
  · have hTop := Heap.allocate_top (heap := heap) (store := initial)
      (need := UInt64.ofNat (8 * ((insertCount prices.size k).toNat + 1))) (by rw [hNeed1]; exact hRoom1)
    simp only [insertNeed]
    omega
  · simp only [insertNeed]
    have hMax1 := Nat.le_max_left initial.mem.pages
      ((heap.top.toNat + (48 + 8 * ((insertCount prices.size k).toNat + 1)) + 65535) / 65536)
    omega
  · have hOwned := (hNew2.ownedKeep ptr1 _ hOwned1).1
    rw [insertTuple, LeanExe.Examples.Clob.insertLevel,
      insertIdx!_eq_build prices k price (by omega)]
    exact hOwned
  · rw [insertTuple, LeanExe.Examples.Clob.insertLevel,
      insertIdx!_eq_build sizes k size (by omega)]
    exact hOwned2

/-- `addToLevel` with its four arguments as one tuple. -/
def addToTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.addToLevel x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `addToLevel` may allocate: a copy of each array. -/
def addToNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 1) + 8 * (x.2.1.size + 1)

theorem addToLevel_implements : Implements clob.module 6 addToTuple addToNeed := by
  refine Func.implements_heap clob.funcs 3 clob.addToLevel.ir "addToLevel" rfl addToTuple addToNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hP := hPrices.values
  have hS := hSizes.values
  have hPFit := hP.1
  have hSFit := hS.1
  let value := sizes[k.toNat]! + size
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k, .i64 size], locals := List.replicate 11 (.i64 0) }
  let s1 := start.update 4 (.i64 (UInt64.ofNat prices.size))
  show Triple _ (.seq (.arraySize 4 0) (.seq (.build 5 6 7 (.get 4) (.read 0 (.get 7)))
    (.seq (.assign 8 (.get 2)) (.seq (.assign 9 (.bin .add (.read 1 (.get 2)) (.get 3)))
      (.seq (.arraySize 10 1) (.build 11 12 13 (.get 10)
        (.ite (.eq (.get 13) (.get 8)) (.get 9) (.read 1 (.get 13))))))))) 14
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 4 := rfl
  have hLocals : start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hLengthP := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthP
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLengthP, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  -- The copy of the prices.
  have hn1 : (UInt64.ofNat prices.size).toNat = prices.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hRoom1 : heap.Room initial clob.module (48 + 8 * ((UInt64.ofNat prices.size).toNat + 1)) :=
    ⟨by have := hRoom.address; simp only [addToNeed] at this; omega,
      by have := hRoom.cap; simp only [addToNeed] at this; omega⟩
  refine Stmt.seq_spec (Stmt.build_spec (n := UInt64.ofNat prices.size)
    (fun j => prices[j.toNat]!) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [s1, hParams, hLocals]) hHeap hRoom1
    ⟨s1, by simp [Expr.eval, s1, hParams, hLocals]⟩ ?_) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 11 := by
      rw [hFrame.params, hFrame.locals]; simp [s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 pp) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s1, hGet0])
    simp [Expr.eval, hIndex, Expr.readValue_at (hAt pp prices hPrices), h0,
      State.set?_eq_update, hState.1, hState.2]
  apply Triple.of_forall
  rintro store1 t1 ⟨ptr1, hFrame1, hPtr1, hNew1⟩
  -- The sizes with the level updated.
  have hAt1 := hNew1.at_
  have hOwned1 := hNew1.owned
  have hTop1 := hNew1.top
  have hPages1 := hNew1.pages
  have hKeep1 := hNew1.borrowed
  have hS1 := (hKeep1 ps sizes hSizes).values
  have hLengthS := hS1.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthS
  have hT1 : t1.params.length = 4 ∧ t1.locals.length = 11 := by
    rw [hFrame1.params, hFrame1.locals]; simp [s1, hParams, hLocals]
  have h1Get1 : t1.get 1 = some (.i64 ps) :=
    (hFrame1.get 1 (by decide) (by decide)).trans (by simp [s1]; rfl)
  have h1Get2 : t1.get 2 = some (.i64 k) :=
    (hFrame1.get 2 (by decide) (by decide)).trans (by simp [s1]; rfl)
  have h1Get3 : t1.get 3 = some (.i64 size) :=
    (hFrame1.get 3 (by decide) (by decide)).trans (by simp [s1]; rfl)
  let u1 := t1.update 8 (.i64 k)
  let u2 := (u1.update 14 (.i64 k)).update 9 (.i64 value)
  let u3 := u2.update 10 (.i64 (UInt64.ofNat sizes.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get2, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Expr.eval, h1Get1, h1Get2, h1Get3, Expr.readValue_at hS1,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2, U64Op.apply, value]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get1, hLengthS, hS1.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2, u3]
  have hn2 : (UInt64.ofNat sizes.size).toNat = sizes.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hRoom2 : (heap.allocate (UInt64.ofNat (8 * ((UInt64.ofNat prices.size).toNat + 1)))).Room
      store1 clob.module (48 + 8 * ((UInt64.ofNat sizes.size).toNat + 1)) := by
    have hNeed : (UInt64.ofNat (8 * ((UInt64.ofNat prices.size).toNat + 1))).toNat =
        8 * ((UInt64.ofNat prices.size).toNat + 1) :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    refine Heap.Room.after_allocate ⟨?_, ?_⟩ hNew1.caps
    · have := hRoom.address; simp only [addToNeed] at this; rw [hNeed]; omega
    · have := hRoom.cap; simp only [addToNeed] at this; rw [hNeed]; omega
  refine (Stmt.build_spec (n := UInt64.ofNat sizes.size)
    (fun j => if j = k then value else sizes[j.toNat]!) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [u3, u2, u1, hT1.1, hT1.2]) hAt1 hRoom2
    ⟨u3, by simp [Expr.eval, u3, u2, u1, hT1.1, hT1.2]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 11 := by
      rw [hFrame.params, hFrame.locals]; simp [u3, u2, u1, hT1.1, hT1.2]
    have h1 : state.get 1 = some (.i64 ps) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get1])
    have h8 : state.get 8 = some (.i64 k) :=
      (hFrame.get 8 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    have h9 : state.get 9 = some (.i64 value) :=
      (hFrame.get 9 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    by_cases hjk : UInt64.ofNat j = k
    · simp [Expr.eval, hIndex, h8, h9, hjk]
    · simp [Expr.eval, hIndex, h8, hjk, Expr.readValue_at (hAt ps sizes (hKeep1 ps sizes hSizes)),
        h1, State.set?_eq_update, hState.1, hState.2]
  rintro store2 t2 ⟨ptr2, hFrame2, hPtr2, hNew2⟩
  have hTop2 := hNew2.top
  have hPages2 := hNew2.pages
  have hPtr1' : t2.get 5 = some (.i64 ptr1) := by
    rw [hFrame2.get 5 (by decide) (by decide)]; simp [u3, u2, u1, hPtr1]
  have hNeed1 : (UInt64.ofNat (8 * ((UInt64.ofNat prices.size).toNat + 1))).toNat =
      8 * ((UInt64.ofNat prices.size).toNat + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  refine ⟨_, hNew2.at_, ⟨_, _, rfl, ⟨pp, rfl, hNew2.borrowed pp prices (hKeep1 pp prices hPrices)⟩,
      _, _, rfl, ⟨ps, rfl, hNew2.borrowed ps sizes (hKeep1 ps sizes hSizes)⟩, rfl⟩, ?_, ?_,
    fun p ws h => hNew2.borrowed p ws (hKeep1 p ws h),
    fun p ws h => (hNew2.ownedKeep p ws (hNew1.ownedKeep p ws h).1).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.addToLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    [.i64 ptr1], [.i64 ptr2], rfl, ⟨ptr1, rfl, ?_⟩, ⟨ptr2, rfl, ?_⟩⟩
  · have hTop := Heap.allocate_top (heap := heap) (store := initial)
      (need := UInt64.ofNat (8 * ((UInt64.ofNat prices.size).toNat + 1)))
      (by rw [hNeed1]; exact hRoom1)
    simp only [addToNeed]
    omega
  · simp only [addToNeed]
    have hMax1 := Nat.le_max_left initial.mem.pages
      ((heap.top.toNat + (48 + 8 * ((UInt64.ofNat prices.size).toNat + 1)) + 65535) / 65536)
    omega
  · have hOwned := (hNew2.ownedKeep ptr1 _ hOwned1).1
    rw [addToTuple, LeanExe.Examples.Clob.addToLevel]
    rw [← copy_eq_build prices (by omega)] at hOwned
    exact hOwned
  · rw [addToTuple, LeanExe.Examples.Clob.addToLevel, set!_eq_build sizes k value (by omega)]
    exact hNew2.owned

/-- `addBid` with its four arguments as one tuple. -/
def addBidTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.addBid x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `addBid` may allocate: those of `insertLevel`, which bound those of
`addToLevel`. -/
def addBidNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 2) + 8 * (x.2.1.size + 2)

/-- One step of `addBid`'s search: count the levels priced above `price`. -/
def searchStep (prices : Array UInt64) (price : UInt64) (i k : UInt64) : UInt64 :=
  if prices[i.toNat]! > price then k + 1 else k

/-- The position `addBid` inserts at. -/
def bidPosition (prices : Array UInt64) (price : UInt64) : UInt64 :=
  LeanExe.loop prices.size.toUInt64 0 (searchStep prices price)

theorem addBid_eq (prices sizes : Array UInt64) (price size : UInt64) :
    LeanExe.Examples.Clob.addBid prices sizes price size =
      if bidPosition prices price < prices.size.toUInt64 ∧
          prices[(bidPosition prices price).toNat]! = price then
        LeanExe.Examples.Clob.addToLevel prices sizes (bidPosition prices price) size
      else LeanExe.Examples.Clob.insertLevel prices sizes (bidPosition prices price) price size :=
  rfl

/-- The compiled search loop's body. -/
def searchBody : Stmt :=
  .seq (.assign 8 (.ite (.ltU (.get 2) (.read 0 (.get 7))) (.bin .add (.get 5) (.const 1))
    (.get 5))) (.assign 5 (.get 8))

theorem searchBody_run {initial : Store Unit} {pp : UInt64} {prices : Array UInt64}
    (hP : UInt64Array.At initial pp prices) {state : State} {k : Nat} {c price : UInt64}
    (hParams : state.params.length = 4) (hLocals : state.locals.length = 14)
    (h0 : state.get 0 = some (.i64 pp)) (h2 : state.get 2 = some (.i64 price))
    (h5 : state.get 5 = some (.i64 c)) (h7 : state.get 7 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, searchBody.run initial.mem 17 state = some final ∧
      State.Frame 17 [5, 8] state final ∧
      final.Holds [5] (Scalar.values (searchStep prices price (UInt64.ofNat k) c)) := by
  simp [searchBody, Stmt.run, Expr.eval, h0, h2, h5, h7, Expr.readValue_at hP,
    State.set?_eq_update, hParams, hLocals, U64Op.apply]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, searchStep, hParams, hLocals]

/-- An owned pair of arrays is two pointers, each to an owned array. -/
theorem owned_pair {heap : Heap} {store : Store Unit} {values : List Value}
    {xs ys : Array UInt64} (h : Represent.owned heap store values (xs, ys)) :
    ∃ p1 p2, values = [.i64 p1, .i64 p2] ∧ heap.Owned store p1 xs ∧ heap.Owned store p2 ys := by
  obtain ⟨_, _, rfl, ⟨p1, rfl, h1⟩, ⟨p2, rfl, h2⟩⟩ := h
  exact ⟨p1, p2, rfl, h1, h2⟩

theorem addBid_implements : Implements clob.module 7 addBidTuple addBidNeed := by
  refine Func.implements_heap clob.funcs 4 clob.addBid.ir "addBid" rfl addBidTuple addBidNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hP := hPrices.values
  have hPFit := hP.1
  have hSFit := hSizes.values.1
  let K := bidPosition prices price
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 price, .i64 size], locals := List.replicate 14 (.i64 0) }
  let s1 := start.update 4 (.i64 (UInt64.ofNat prices.size))
  let s2 := s1.update 5 (.i64 0)
  let condition : Expr .bool := .and (.ltU (.get 9) (.get 10)) (.eq (.read 0 (.get 9)) (.get 2))
  let thenStmt : Stmt := .seq (.call 6 [.get 0, .get 1, .get 9, .get 3] [11, 12])
    (.seq (.assign 13 (.get 11)) (.assign 14 (.get 12)))
  let elseStmt : Stmt := .seq (.call 5 [.get 0, .get 1, .get 9, .get 2, .get 3] [15, 16])
    (.seq (.assign 13 (.get 15)) (.assign 14 (.get 16)))
  show Triple _ (.seq (.arraySize 4 0) (.seq (.assign 5 (.const 0))
    (.seq (.loop 6 7 (.get 4) searchBody) (.seq (.assign 9 (.get 5)) (.seq (.arraySize 10 0)
      (.ite condition thenStmt elseStmt)))))) 17
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 4 := rfl
  have hLocals : start.locals.length = 14 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hLengthP := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthP
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLengthP, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2]
  -- The search.
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [5]) (writes := [5, 8]) (init := (0 : UInt64))
    (n := prices.size.toUInt64) (searchStep prices price)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) ⟨s2, by simp [Expr.eval, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals]) ?_) ?_
  · intro k c state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 4 ∧ state.locals.length = 14 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 pp) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have h2 : state.get 2 = some (.i64 price) :=
      (hFrame.get 2 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have h5 : state.get 5 = some (.i64 c) := by simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      searchBody_run hP hState.1 hState.2 h0 h2 h5 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  apply Triple.of_forall
  rintro store t1 ⟨hStore, hFrame1, hHolds1⟩
  subst store
  have hT1 : t1.params.length = 4 ∧ t1.locals.length = 14 := by
    rw [hFrame1.params, hFrame1.locals]; simp [s2, s1, hParams, hLocals]
  have h1Get0 : t1.get 0 = some (.i64 pp) :=
    (hFrame1.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
  have h1Get1 : t1.get 1 = some (.i64 ps) :=
    (hFrame1.get 1 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
  have h1Get2 : t1.get 2 = some (.i64 price) :=
    (hFrame1.get 2 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
  have h1Get3 : t1.get 3 = some (.i64 size) :=
    (hFrame1.get 3 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
  have hK : t1.get 5 = some (.i64 K) := (List.forall₂_cons.mp hHolds1).1
  let u1 := t1.update 9 (.i64 K)
  let u2 := u1.update 10 (.i64 (UInt64.ofNat prices.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hK, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get0, hLengthP,
      hP.lengthRead, State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  -- The condition.
  have hU2 : u2.params.length = 4 ∧ u2.locals.length = 14 := by simp [u2, u1, hT1.1, hT1.2]
  let found := decide (K < UInt64.ofNat prices.size) && (prices[K.toNat]! == price)
  let afterCondition := if K < UInt64.ofNat prices.size then u2.update 17 (.i64 K) else u2
  have hAC : ∀ j, j ≠ 17 → afterCondition.get j = u2.get j := fun j hj => by
    by_cases hlt : K < UInt64.ofNat prices.size <;> simp [afterCondition, hlt, hj]
  have hACLength : afterCondition.params.length = 4 ∧ afterCondition.locals.length = 14 := by
    by_cases hlt : K < UInt64.ofNat prices.size <;> simp [afterCondition, hlt, hU2.1, hU2.2]
  have hu : ∀ j, j < 4 → u2.get j = t1.get j := fun j hj => by
    simp only [u2, u1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega)]
  have hCondition : condition.eval initial.mem 17 u2 = some (found, afterCondition) := by
    by_cases hlt : K < UInt64.ofNat prices.size
    · simp [condition, Expr.eval, u2, u1, hT1.1, hT1.2, hlt, Expr.readValue_at hP, h1Get0,
        h1Get2, State.set?_eq_update, found, afterCondition]
    · simp [condition, Expr.eval, u2, u1, hT1.1, hT1.2, hlt, found, afterCondition]
  have hArgsGet : afterCondition.get 0 = some (.i64 pp) ∧ afterCondition.get 1 = some (.i64 ps) ∧
      afterCondition.get 2 = some (.i64 price) ∧ afterCondition.get 3 = some (.i64 size) ∧
      afterCondition.get 9 = some (.i64 K) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hAC 0 (by decide), hu 0 (by decide), h1Get0]
    · rw [hAC 1 (by decide), hu 1 (by decide), h1Get1]
    · rw [hAC 2 (by decide), hu 2 (by decide), h1Get2]
    · rw [hAC 3 (by decide), hu 3 (by decide), h1Get3]
    · rw [hAC 9 (by decide)]; simp [u2, u1, hT1.1, hT1.2]
  obtain ⟨g0, g1, g2, g3, g9⟩ := hArgsGet
  have hSetPair : ∀ (a b : Nat), a < 18 → b < 18 → ∀ (values : List Value) (xs ys : Array UInt64)
      (heap' : Heap) (store' : Store Unit), Represent.owned heap' store' values (xs, ys) →
      ∃ next, afterCondition.setAll [b, a] values.reverse = some next := by
    intro a b ha hb values xs ys heap' store' hOwned
    obtain ⟨p1, p2, rfl, -, -⟩ := owned_pair hOwned
    have hb' : b < afterCondition.params.length + afterCondition.locals.length := by omega
    have ha' : a < (afterCondition.update b (.i64 p2)).params.length +
        (afterCondition.update b (.i64 p2)).locals.length := by simp; omega
    exact ⟨(afterCondition.update b (.i64 p2)).update a (.i64 p1), by
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        State.setAll, State.set?_eq_update _ hb', State.set?_eq_update _ ha', Option.bind_eq_bind,
        Option.bind_some]⟩
  have hNeedAddTo : addToNeed (prices, sizes, K, size) ≤ addBidNeed (prices, sizes, price, size) := by
    simp only [addToNeed, addBidNeed]; omega
  have hNeedInsert : insertNeed (prices, sizes, K, price, size) ≤
      addBidNeed (prices, sizes, price, size) := by
    simp only [insertNeed, addBidNeed]; omega
  have hNoImports : clob.module.imports.length = 0 := rfl
  refine (Stmt.ite_spec
    (PThen := fun s st => s = initial ∧ st = afterCondition ∧ found = true)
    (PElse := fun s st => s = initial ∧ st = afterCondition ∧ found = false) ?_ ?_).mono
      ?_ fun _ _ h => h
  rotate_left 2
  · rintro s st ⟨rfl, rfl⟩
    exact ⟨found, afterCondition, hCondition, by cases found <;> simp⟩
  -- A branch calls a function and copies its two results.
  all_goals
    apply Triple.of_forall
    rintro s st ⟨rfl, rfl, hFound⟩
  · -- An existing level: `addToLevel`.
    have hTaken : K < prices.size.toUInt64 ∧ prices[K.toNat]! = price := by
      simpa [found] using hFound
    refine Stmt.seq_spec (Stmt.callImplements_spec addToLevel_implements
      (f := clob.addToLevel.ir.function (2 + 3)) rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 3) rfl) rfl
      (words := [pp, ps, K, size]) (x := (prices, sizes, K, size))
      (by simp [Expr.evalAll, Expr.eval, g0, g1, g9, g3]) hHeap
      ⟨[.i64 pp], [.i64 ps, .i64 K, .i64 size], rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps],
        [.i64 K, .i64 size], rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
      ⟨by have := hRoom.address; omega, by have := hRoom.cap; omega⟩
      fun heap' store' values h => hSetPair 11 12 (by decide) (by decide) values _ _ heap' store' h)
      ?_
    apply Triple.of_forall
    rintro store' st' ⟨heap', values, hAt', hOwned', -, hTop', hPages', hKeepB, hKeepO, hSet'⟩
    obtain ⟨p1, p2, rfl, -, -⟩ := owned_pair hOwned'
    have hState' : st' = (afterCondition.update 12 (.i64 p2)).update 11 (.i64 p1) := by
      have hb' : 12 < afterCondition.params.length + afterCondition.locals.length := by omega
      have ha' : 11 < (afterCondition.update 12 (.i64 p2)).params.length +
          (afterCondition.update 12 (.i64 p2)).locals.length := by simp; omega
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        State.setAll, State.set?_eq_update _ hb', State.set?_eq_update _ ha', Option.bind_eq_bind,
        Option.bind_some, Option.some.injEq] at hSet'
      exact hSet'.symm
    subst hState'
    let final := (((afterCondition.update 12 (.i64 p2)).update 11 (.i64 p1)).update 13
      (.i64 p1)).update 14 (.i64 p2)
    refine (Stmt.run_spec (final := final) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hACLength.1, hACLength.2, final])).mono
        (fun _ _ h => h) ?_
    rintro s f ⟨rfl, rfl⟩
    refine ⟨heap', hAt', ⟨_, _, rfl, ⟨pp, rfl, hKeepB pp prices hPrices⟩, _, _, rfl,
        ⟨ps, rfl, hKeepB ps sizes hSizes⟩, rfl⟩, by omega, ?_, hKeepB, hKeepO,
      [.i64 p1, .i64 p2], final,
      by simp [clob.addBid.ir, Func.scratch, Expr.evalResults, Expr.eval, final,
        hACLength.1, hACLength.2], ?_⟩
    · refine le_trans hPages' (max_le_max (le_refl _) (Nat.div_le_div_right ?_))
      omega
    · rw [addBidTuple, addBid_eq, ite_eq_left hTaken]
      exact hOwned'
  · -- A new level: `insertLevel`.
    have hTaken : ¬(K < prices.size.toUInt64 ∧ prices[K.toNat]! = price) := by
      simpa [found] using hFound
    refine Stmt.seq_spec (Stmt.callImplements_spec insertLevel_implements
      (f := clob.insertLevel.ir.function (2 + 2)) rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 2) rfl) rfl
      (words := [pp, ps, K, price, size]) (x := (prices, sizes, K, price, size))
      (by simp [Expr.evalAll, Expr.eval, g0, g1, g9, g2, g3]) hHeap
      ⟨[.i64 pp], [.i64 ps, .i64 K, .i64 price, .i64 size], rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps],
        [.i64 K, .i64 price, .i64 size], rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
      ⟨by have := hRoom.address; omega, by have := hRoom.cap; omega⟩
      fun heap' store' values h => hSetPair 15 16 (by decide) (by decide) values _ _ heap' store' h)
      ?_
    apply Triple.of_forall
    rintro store' st' ⟨heap', values, hAt', hOwned', -, hTop', hPages', hKeepB, hKeepO, hSet'⟩
    obtain ⟨p1, p2, rfl, -, -⟩ := owned_pair hOwned'
    have hState' : st' = (afterCondition.update 16 (.i64 p2)).update 15 (.i64 p1) := by
      have hb' : 16 < afterCondition.params.length + afterCondition.locals.length := by omega
      have ha' : 15 < (afterCondition.update 16 (.i64 p2)).params.length +
          (afterCondition.update 16 (.i64 p2)).locals.length := by simp; omega
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        State.setAll, State.set?_eq_update _ hb', State.set?_eq_update _ ha', Option.bind_eq_bind,
        Option.bind_some, Option.some.injEq] at hSet'
      exact hSet'.symm
    subst hState'
    let final := (((afterCondition.update 16 (.i64 p2)).update 15 (.i64 p1)).update 13
      (.i64 p1)).update 14 (.i64 p2)
    refine (Stmt.run_spec (final := final) (by
      simp [Stmt.run, Expr.eval, State.set?_eq_update, hACLength.1, hACLength.2, final])).mono
        (fun _ _ h => h) ?_
    rintro s f ⟨rfl, rfl⟩
    refine ⟨heap', hAt', ⟨_, _, rfl, ⟨pp, rfl, hKeepB pp prices hPrices⟩, _, _, rfl,
        ⟨ps, rfl, hKeepB ps sizes hSizes⟩, rfl⟩, by omega, ?_, hKeepB, hKeepO,
      [.i64 p1, .i64 p2], final,
      by simp [clob.addBid.ir, Func.scratch, Expr.evalResults, Expr.eval, final,
        hACLength.1, hACLength.2], ?_⟩
    · refine le_trans hPages' (max_le_max (le_refl _) (Nat.div_le_div_right ?_))
      omega
    · rw [addBidTuple, addBid_eq, ite_eq_right hTaken]
      exact hOwned'

/-- `depth` with its three arguments as one tuple. -/
def depthTuple (x : Array UInt64 × Array UInt64 × UInt64) : UInt64 :=
  LeanExe.Examples.Clob.depth x.1 x.2.1 x.2.2

/-- One step of `depth`'s loop. -/
def depthStep (prices sizes : Array UInt64) (limit i total : UInt64) : UInt64 :=
  if prices[i.toNat]! ≥ limit then total + sizes[i.toNat]! else total

/-- The compiled loop body of `depth`. -/
def depthBody : Stmt :=
  .seq (.assign 7 (.ite (.leU (.get 2) (.read 0 (.get 6)))
    (.bin .add (.get 4) (.read 1 (.get 6))) (.get 4))) (.assign 4 (.get 7))

theorem depthBody_run {initial : Store Unit} {pp ps : UInt64} {prices sizes : Array UInt64}
    (hP : UInt64Array.At initial pp prices) (hS : UInt64Array.At initial ps sizes)
    {state : State} {k : Nat} {limit total : UInt64}
    (hParams : state.params.length = 3) (hLocals : state.locals.length = 6)
    (h0 : state.get 0 = some (.i64 pp)) (h1 : state.get 1 = some (.i64 ps))
    (h2 : state.get 2 = some (.i64 limit)) (h4 : state.get 4 = some (.i64 total))
    (h6 : state.get 6 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, depthBody.run initial.mem 8 state = some final ∧
      State.Frame 8 [4, 7] state final ∧
      final.Holds [4] (Scalar.values (depthStep prices sizes limit (UInt64.ofNat k) total)) := by
  simp [depthBody, Stmt.run, Expr.eval, h0, h1, h2, h4, h6, Expr.readValue_at hP,
    Expr.readValue_at hS, State.set?_eq_update, hParams, hLocals, U64Op.apply]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, depthStep, hParams, hLocals]

theorem depth_implements : Implements clob.module 8 depthTuple (fun _ => 0) := by
  refine Func.implements clob.funcs 5 clob.depth.ir "depth" rfl depthTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, limit⟩ heap initial _ -
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  have hP := hPrices.values
  have hS := hSizes.values
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 limit], locals := List.replicate 6 (.i64 0) }
  let s1 := start.update 3 (.i64 (UInt64.ofNat prices.size))
  let s2 := s1.update 4 (.i64 0)
  show Triple _ (.seq (.arraySize 3 0) (.seq (.assign 4 (.const 0))
    (.loop 5 6 (.get 3) depthBody))) 8 (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hLength := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2]
  refine (Stmt.loop_spec (vars := [4]) (writes := [4, 7]) (init := (0 : UInt64))
    (n := prices.size.toUInt64) (depthStep prices sizes limit)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) ⟨s2, by simp [Expr.eval, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals]) ?_).mono
      (fun _ _ h => h) ?_
  · intro k total state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 3 ∧ state.locals.length = 6 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 pp) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have h1 : state.get 1 = some (.i64 ps) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have h2 : state.get 2 = some (.i64 limit) :=
      (hFrame.get 2 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have h4 : state.get 4 = some (.i64 total) := by
      simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      depthBody_run hP hS hState.1 hState.2 h0 h1 h2 h4 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  rintro store state ⟨rfl, -, hHolds⟩
  have h4 : state.get 4 = some (.i64 (depthTuple (prices, sizes, limit))) :=
    (List.forall₂_cons.mp hHolds).1
  exact ⟨rfl, [.i64 _], state, by
    simp [clob.depth.ir, Func.scratch, Expr.evalResults, Expr.eval, h4], rfl⟩

/-- `encode` succeeds on `clob.module`, and its bytes decode to a module whose
exports compute the CLOB operations exactly. -/
theorem clob_bytes : ∃ bytes, Encoding.encode clob.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧
      Implements m 3 marketBuyTuple (fun _ => 72) ∧ Implements m 4 fillTuple fillNeed ∧
      Implements m 5 insertTuple insertNeed ∧ Implements m 6 addToTuple addToNeed ∧
      Implements m 7 addBidTuple addBidNeed ∧ Implements m 8 depthTuple (fun _ => 0) := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip clob.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, clob.module, decoded, marketBuy_implements, fillLevel_implements,
    insertLevel_implements, addToLevel_implements, addBid_implements,
    depth_implements⟩

end Project.Clob
