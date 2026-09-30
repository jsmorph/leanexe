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
      ⟨ps, rfl, hNew.borrowed ps sizes hSizes⟩, rfl⟩, hNew.top, hNew.pages, hNew.caps, hNew.borrowed,
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
      le_of_le_of_eq hNew.pages (by simp [fillNeed, hn]), hNew.caps, hNew.borrowed,
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
      ⟨ps, rfl, hKeep2 ps sizes (hKeep1 ps sizes hSizes)⟩, rfl⟩, ?_, ?_, hNew2.caps.trans hNew1.caps,
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

/-- `setLevel` with its four arguments as one tuple. -/
def setTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.setLevel x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `setLevel` may allocate: a copy of each array. -/
def setNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 1) + 8 * (x.2.1.size + 1)

theorem setLevel_implements : Implements clob.module 6 setTuple setNeed := by
  refine Func.implements_heap clob.funcs 3 clob.setLevel.ir "setLevel" rfl setTuple setNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hPFit := hPrices.values.1
  have hSFit := hSizes.values.1
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k, .i64 size], locals := List.replicate 11 (.i64 0) }
  show Triple _ (.seq (.copy 5 6 7 4 0) (.seq (.assign 8 (.get 2)) (.seq (.assign 9 (.get 3))
    (.seq (.arraySize 10 1) (.build 11 12 13 (.get 10)
      (.ite (.eq (.get 13) (.get 8)) (.get 9) (.read 1 (.get 13)))))))) 14
    (fun store state => store = initial ∧ state = start) _
  -- The copy of the prices.
  have hRoom1 : heap.Room initial clob.module (48 + 8 * (prices.size + 1)) :=
    hRoom.after (used := 0) (by omega) (by simp only [setNeed]; omega) rfl
  refine Stmt.seq_spec (Stmt.copy_spec hMemory32 hImports hAlloc (by decide) (by decide)
    (by decide) (by decide) (by simp [start]) hHeap hRoom1 rfl hPrices) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨ptr1, hFrame1, hPtr1, hNew1⟩
  -- The sizes with level `k` set.
  have hKeep1 := hNew1.borrowed
  have hS1 := (hKeep1 ps sizes hSizes).values
  have hLengthS := hS1.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthS
  have hT1 : t1.params.length = 4 ∧ t1.locals.length = 11 := ⟨hFrame1.params, hFrame1.locals⟩
  have h1Get1 : t1.get 1 = some (.i64 ps) := (hFrame1.get 1 (by decide) (by decide)).trans rfl
  have h1Get2 : t1.get 2 = some (.i64 k) := (hFrame1.get 2 (by decide) (by decide)).trans rfl
  have h1Get3 : t1.get 3 = some (.i64 size) := (hFrame1.get 3 (by decide) (by decide)).trans rfl
  let u1 := t1.update 8 (.i64 k)
  let u2 := u1.update 9 (.i64 size)
  let u3 := u2.update 10 (.i64 (UInt64.ofNat sizes.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get2, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Expr.eval, h1Get3, State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get1, hLengthS, hS1.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2, u3]
  have hn2 : (UInt64.ofNat sizes.size).toNat = sizes.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hNeed1 : (UInt64.ofNat (8 * (prices.size + 1))).toNat = 8 * (prices.size + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hRoom2 : (heap.allocate (UInt64.ofNat (8 * (prices.size + 1)))).Room
      store1 clob.module (48 + 8 * ((UInt64.ofNat sizes.size).toNat + 1)) :=
    Heap.Room.after_allocate (hRoom.after (used := 0) (by omega)
      (by rw [hNeed1, hn2]; simp only [setNeed]; omega) rfl) hNew1.caps
  refine (Stmt.build_spec (n := UInt64.ofNat sizes.size)
    (fun j => if j = k then size else sizes[j.toNat]!) hMemory32 hImports hAlloc
    (by decide) (by decide) (by simp [u3, u2, u1, hT1.1, hT1.2]) hNew1.at_ hRoom2
    ⟨u3, by simp [Expr.eval, u3, u2, u1, hT1.1, hT1.2]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 4 ∧ state.locals.length = 11 := by
      rw [hFrame.params, hFrame.locals]; simp [u3, u2, u1, hT1.1, hT1.2]
    have h1 : state.get 1 = some (.i64 ps) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [u3, u2, u1, h1Get1])
    have h8 : state.get 8 = some (.i64 k) :=
      (hFrame.get 8 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    have h9 : state.get 9 = some (.i64 size) :=
      (hFrame.get 9 (by decide) (by decide)).trans (by simp [u3, u2, u1, hT1.1, hT1.2])
    by_cases hjk : UInt64.ofNat j = k
    · simp [Expr.eval, hIndex, h8, h9, hjk]
    · simp [Expr.eval, hIndex, h8, hjk, Expr.readValue_at (hAt ps sizes (hKeep1 ps sizes hSizes)),
        h1, State.set?_eq_update, hState.1, hState.2]
  rintro store2 t2 ⟨ptr2, hFrame2, hPtr2, hNew2⟩
  have hTop1 := hNew1.top
  have hPages1 := hNew1.pages
  have hTop2 := hNew2.top
  have hPages2 := hNew2.pages
  have hPtr1' : t2.get 5 = some (.i64 ptr1) := by
    rw [hFrame2.get 5 (by decide) (by decide)]; simp [u3, u2, u1, hPtr1]
  refine ⟨_, hNew2.at_, ⟨_, _, rfl, ⟨pp, rfl, hNew2.borrowed pp prices (hKeep1 pp prices hPrices)⟩,
      _, _, rfl, ⟨ps, rfl, hNew2.borrowed ps sizes (hKeep1 ps sizes hSizes)⟩, rfl⟩,
    by simp only [setNeed]; omega, by simp only [setNeed]; omega, hNew2.caps.trans hNew1.caps,
    fun p ws h => hNew2.borrowed p ws (hKeep1 p ws h),
    fun p ws h => (hNew2.ownedKeep p ws (hNew1.ownedKeep p ws h).1).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.setLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    [.i64 ptr1], [.i64 ptr2], rfl, ⟨ptr1, rfl, (hNew2.ownedKeep ptr1 _ hNew1.owned).1⟩,
    ⟨ptr2, rfl, ?_⟩⟩
  rw [setTuple, LeanExe.Examples.Clob.setLevel, set!_eq_build sizes k size (by omega)]
  exact hNew2.owned

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

/-- `findLevel` with its two arguments as one tuple. -/
def findTuple (x : Array UInt64 × UInt64) : UInt64 :=
  LeanExe.Examples.Clob.findLevel x.1 x.2

/-- One step of `findLevel`'s search: count the levels priced above `price`. -/
def searchStep (prices : Array UInt64) (price : UInt64) (i k : UInt64) : UInt64 :=
  if prices[i.toNat]! > price then k + 1 else k

/-- The compiled loop body of `findLevel`. -/
def findBody : Stmt :=
  .seq (.assign 6 (.ite (.ltU (.get 1) (.read 0 (.get 5))) (.bin .add (.get 3) (.const 1))
    (.get 3))) (.assign 3 (.get 6))

theorem findBody_run {initial : Store Unit} {pp : UInt64} {prices : Array UInt64}
    (hP : UInt64Array.At initial pp prices) {state : State} {k : Nat} {c price : UInt64}
    (hParams : state.params.length = 2) (hLocals : state.locals.length = 6)
    (h0 : state.get 0 = some (.i64 pp)) (h1 : state.get 1 = some (.i64 price))
    (h3 : state.get 3 = some (.i64 c)) (h5 : state.get 5 = some (.i64 (UInt64.ofNat k))) :
    ∃ final, findBody.run initial.mem 7 state = some final ∧
      State.Frame 7 [3, 6] state final ∧
      final.Holds [3] (Scalar.values (searchStep prices price (UInt64.ofNat k) c)) := by
  simp [findBody, Stmt.run, Expr.eval, h0, h1, h3, h5, Expr.readValue_at hP,
    State.set?_eq_update, hParams, hLocals, U64Op.apply]
  constructor
  · repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  · simp [State.Holds, Scalar.values, searchStep, hParams, hLocals]

theorem findLevel_implements : Implements clob.module 9 findTuple (fun _ => 0) := by
  refine Func.implements clob.funcs 6 clob.findLevel.ir "findLevel" rfl findTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, price⟩ heap initial _ - ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, rfl⟩
  change heap.Borrowed initial pp prices at hPrices
  have hP := hPrices.values
  let start : State := { params := [.i64 pp, .i64 price], locals := List.replicate 6 (.i64 0) }
  let s1 := start.update 2 (.i64 (UInt64.ofNat prices.size))
  let s2 := s1.update 3 (.i64 0)
  show Triple _ (.seq (.arraySize 2 0) (.seq (.assign 3 (.const 0))
    (.loop 4 5 (.get 2) findBody))) 7 (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 2 := rfl
  have hLocals : start.locals.length = 6 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hLength := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLength, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2]
  refine (Stmt.loop_spec (vars := [3]) (writes := [3, 6]) (init := (0 : UInt64))
    (n := prices.size.toUInt64) (searchStep prices price)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) ⟨s2, by simp [Expr.eval, s2, s1, hParams, hLocals]⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals]) ?_).mono
      (fun _ _ h => h) ?_
  · intro k c state hk hFrame hHolds hIndex hLimit
    have hState : state.params.length = 2 ∧ state.locals.length = 6 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, s1, hParams, hLocals]
    have h0 : state.get 0 = some (.i64 pp) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])
    have h1 : state.get 1 = some (.i64 price) :=
      (hFrame.get 1 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have h3 : state.get 3 = some (.i64 c) := by simpa [State.Holds, Scalar.values] using hHolds
    obtain ⟨final, hRun, hFinalFrame, hFinalHolds⟩ :=
      findBody_run hP hState.1 hState.2 h0 h1 h3 hIndex
    refine (Stmt.run_spec hRun).mono (fun _ _ h => h) ?_
    rintro store st ⟨rfl, rfl⟩
    exact ⟨rfl, hFinalFrame, hFinalHolds⟩
  rintro store state ⟨rfl, -, hHolds⟩
  have h3 : state.get 3 = some (.i64 (findTuple (prices, price))) :=
    (List.forall₂_cons.mp hHolds).1
  exact ⟨rfl, [.i64 _], state, by
    simp [clob.findLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, h3], rfl⟩

/-- `removeLevel` with its three arguments as one tuple. -/
def removeTuple (x : Array UInt64 × Array UInt64 × UInt64) : Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.removeLevel x.1 x.2.1 x.2.2

/-- The bytes `removeLevel` may allocate: two arrays, each no longer than its input. -/
def removeNeed (x : Array UInt64 × Array UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 1) + 8 * (x.2.1.size + 1)

/-- The element function of `eraseIdxIfInBounds` on bit patterns. -/
def eraseAt (xs : Array UInt64) (k j : UInt64) : UInt64 :=
  if j < k then xs[j.toNat]! else xs[(j + 1).toNat]!

/-- The length of the array `eraseIdxIfInBounds` returns. -/
def eraseCount (size : Nat) (k : UInt64) : UInt64 :=
  if k < UInt64.ofNat size then UInt64.ofNat size - 1 else UInt64.ofNat size

theorem eraseCount_toNat (size : Nat) (k : UInt64) (hSize : size < 2 ^ 64) :
    (eraseCount size k).toNat ≤ size := by
  have hn : (UInt64.ofNat size).toNat = size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  unfold eraseCount
  split
  · rename_i h
    rw [UInt64.lt_iff_toNat_lt, hn] at h
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; simp; omega), hn]
    simp
  · rw [hn]

/-- The element code of `eraseIdxIfInBounds` evaluates to `eraseAt` when the array
local holds a laid-out array. -/
theorem erase_element {store : Store Unit} {ptr k : UInt64} {xs : Array UInt64}
    (hArray : UInt64Array.At store ptr xs) {array kLocal index scratch : Nat}
    {state : State} {j : UInt64}
    (hLength : scratch < state.params.length + state.locals.length)
    (hArrayGet : state.get array = some (.i64 ptr)) (hArrayNe : array ≠ scratch)
    (hIndex : state.get index = some (.i64 j)) (hK : state.get kLocal = some (.i64 k)) :
    ∃ next, (Expr.ite (.ltU (.get index) (.get kLocal)) (.read array (.get index))
      (.read array (.bin .add (.get index) (.const 1)))).eval store.mem scratch state =
      some (eraseAt xs k j, next) := by
  unfold eraseAt
  by_cases h1 : j < k
  · simp [Expr.eval, hIndex, hK, h1, Expr.readValue_at hArray, hArrayGet, hArrayNe,
      State.set?_eq_update, hLength]
  · simp [Expr.eval, hIndex, hK, h1, Expr.readValue_at hArray, hArrayGet, hArrayNe,
      State.set?_eq_update, hLength, U64Op.apply]

theorem removeLevel_implements : Implements clob.module 10 removeTuple removeNeed := by
  refine Func.implements_heap clob.funcs 7 clob.removeLevel.ir "removeLevel" rfl removeTuple
    removeNeed (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k⟩ heap initial _ hHeap
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
    { params := [.i64 pp, .i64 ps, .i64 k], locals := List.replicate 11 (.i64 0) }
  let s1 := start.update 3 (.i64 k)
  let s2 := s1.update 4 (.i64 (UInt64.ofNat prices.size))
  let element (array kLocal index : Nat) : Expr .u64 :=
    .ite (.ltU (.get index) (.get kLocal)) (.read array (.get index))
      (.read array (.bin .add (.get index) (.const 1)))
  let count (kLocal size : Nat) : Expr .u64 :=
    .ite (.ltU (.get kLocal) (.get size)) (.bin .sub (.get size) (.const 1)) (.get size)
  show Triple _ (.seq (.assign 3 (.get 2)) (.seq (.arraySize 4 0)
    (.seq (.build 5 6 7 (count 3 4) (element 0 3 7))
      (.seq (.assign 8 (.get 2)) (.seq (.arraySize 9 1)
        (.build 10 11 12 (count 8 9) (element 1 8 12))))))) 13
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 11 := rfl
  have hGet0 : start.get 0 = some (.i64 pp) := rfl
  have hGet2 : start.get 2 = some (.i64 k) := rfl
  have hLengthP := hP.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthP
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet2, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, hLengthP, hP.lengthRead,
      State.set?_eq_update, hParams, hLocals, s1, s2]
  -- The first array.
  have hn1 := eraseCount_toNat prices.size k (by omega)
  have hRoom1 : heap.Room initial clob.module (48 + 8 * ((eraseCount prices.size k).toNat + 1)) :=
    ⟨by have := hRoom.address; simp only [removeNeed] at this; omega,
      by have := hRoom.cap; simp only [removeNeed] at this; omega⟩
  refine Stmt.seq_spec (Stmt.build_spec (n := eraseCount prices.size k)
    (eraseAt prices k) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) hHeap hRoom1
    ⟨s2, by simp [Expr.eval, count, eraseCount, s2, s1, hParams, hLocals, U64Op.apply]⟩ ?_) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 11 := by
      rw [hFrame.params, hFrame.locals]; simp [s2, s1, hParams, hLocals]
    exact erase_element (hAt pp prices hPrices) (by omega)
      ((hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1, hGet0])) (by decide)
      hIndex ((hFrame.get 3 (by decide) (by decide)).trans (by simp [s2, s1, hParams, hLocals]))
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
  have hT1 : t1.params.length = 3 ∧ t1.locals.length = 11 := by
    rw [hFrame1.params, hFrame1.locals]; simp [s2, s1, hParams, hLocals]
  have h1Get1 : t1.get 1 = some (.i64 ps) := (hFrame1.get 1 (by decide) (by decide)).trans
    (by simp [s2, s1]; rfl)
  have h1Get2 : t1.get 2 = some (.i64 k) := (hFrame1.get 2 (by decide) (by decide)).trans
    (by simp [s2, s1, hGet2])
  let u1 := t1.update 8 (.i64 k)
  let u2 := u1.update 9 (.i64 (UInt64.ofNat sizes.size))
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get2, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Stmt.run, Stmt.arraySize, Expr.eval, h1Get1, hLengthS, hS1.lengthRead,
      State.set?_eq_update, hT1.1, hT1.2, u1, u2]
  have hn2 := eraseCount_toNat sizes.size k (by omega)
  have hNeed1 : (UInt64.ofNat (8 * ((eraseCount prices.size k).toNat + 1))).toNat =
      8 * ((eraseCount prices.size k).toNat + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hRoom2 : (heap.allocate (UInt64.ofNat (8 * ((eraseCount prices.size k).toNat + 1)))).Room
      store1 clob.module (48 + 8 * ((eraseCount sizes.size k).toNat + 1)) := by
    refine Heap.Room.after_allocate ⟨?_, ?_⟩ hCaps1
    · have := hRoom.address; simp only [removeNeed] at this; rw [hNeed1]; omega
    · have := hRoom.cap; simp only [removeNeed] at this; rw [hNeed1]; omega
  refine (Stmt.build_spec (n := eraseCount sizes.size k)
    (eraseAt sizes k) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [u2, u1, hT1.1, hT1.2]) hAt1 hRoom2
    ⟨u2, by simp [Expr.eval, count, eraseCount, u2, u1, hT1.1, hT1.2, U64Op.apply]⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hState : state.params.length = 3 ∧ state.locals.length = 11 := by
      rw [hFrame.params, hFrame.locals]; simp [u2, u1, hT1.1, hT1.2]
    exact erase_element (hAt ps sizes (hKeep1 ps sizes hSizes)) (by omega)
      ((hFrame.get 1 (by decide) (by decide)).trans (by simp [u2, u1, h1Get1])) (by decide)
      hIndex ((hFrame.get 8 (by decide) (by decide)).trans (by simp [u2, u1, hT1.1, hT1.2]))
  rintro store2 t2 ⟨ptr2, hFrame2, hPtr2, hNew2⟩
  have hAt2 := hNew2.at_
  have hOwned2 := hNew2.owned
  have hTop2 := hNew2.top
  have hPages2 := hNew2.pages
  have hKeep2 := hNew2.borrowed
  have hPtr1' : t2.get 5 = some (.i64 ptr1) := by
    rw [hFrame2.get 5 (by decide) (by decide)]; simp [u2, u1, hPtr1]
  refine ⟨_, hAt2, ⟨_, _, rfl, ⟨pp, rfl, hKeep2 pp prices (hKeep1 pp prices hPrices)⟩, _, _, rfl,
      ⟨ps, rfl, hKeep2 ps sizes (hKeep1 ps sizes hSizes)⟩, rfl⟩, ?_, ?_, hNew2.caps.trans hNew1.caps,
    fun p ws h => hKeep2 p ws (hKeep1 p ws h),
    fun p ws h => (hNew2.ownedKeep p ws (hNew1.ownedKeep p ws h).1).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.removeLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    [.i64 ptr1], [.i64 ptr2], rfl, ⟨ptr1, rfl, ?_⟩, ⟨ptr2, rfl, ?_⟩⟩
  · have hTop := Heap.allocate_top (heap := heap) (store := initial)
      (need := UInt64.ofNat (8 * ((eraseCount prices.size k).toNat + 1)))
      (by rw [hNeed1]; exact hRoom1)
    simp only [removeNeed]
    omega
  · simp only [removeNeed]
    have hMax1 := Nat.le_max_left initial.mem.pages
      ((heap.top.toNat + (48 + 8 * ((eraseCount prices.size k).toNat + 1)) + 65535) / 65536)
    omega
  · have hOwned := (hNew2.ownedKeep ptr1 _ hOwned1).1
    rw [removeTuple, LeanExe.Examples.Clob.removeLevel,
      eraseIdxIfInBounds_eq_build prices k (by omega)]
    exact hOwned
  · rw [removeTuple, LeanExe.Examples.Clob.removeLevel,
      eraseIdxIfInBounds_eq_build sizes k (by omega)]
    exact hOwned2

/-- An owned pair of arrays is two pointers, each to an owned array. -/
theorem owned_pair {heap : Heap} {store : Store Unit} {values : List Value}
    {xs ys : Array UInt64} (h : Represent.owned heap store values (xs, ys)) :
    ∃ p1 p2, values = [.i64 p1, .i64 p2] ∧ heap.Owned store p1 xs ∧ heap.Owned store p2 ys := by
  obtain ⟨_, _, rfl, ⟨p1, rfl, h1⟩, ⟨p2, rfl, h2⟩⟩ := h
  exact ⟨p1, p2, rfl, h1, h2⟩

/-- What a call that allocates nothing leaves: a heap over `store1` that keeps every
earlier array, with `top` and the memory no larger than before. -/
structure Kept (heap : Heap) (initial : Store Unit) (heap1 : Heap) (store1 : Store Unit) :
    Prop where
  at_ : heap1.At store1
  top : heap1.top.toNat ≤ heap.top.toNat
  pages : store1.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + 65535) / 65536)
  caps : store1.memoryCaps = initial.memoryCaps
  borrowed : ∀ p ws, heap.Borrowed initial p ws → heap1.Borrowed store1 p ws
  owned : ∀ p ws, heap.Owned initial p ws → heap1.Owned store1 p ws

theorem Kept.refl {heap : Heap} {initial : Store Unit} (hHeap : heap.At initial) :
    Kept heap initial heap initial :=
  ⟨hHeap, le_refl _, le_max_left _ _, rfl, fun _ _ h => h, fun _ _ h => h⟩

/-- The postcondition of `Func.implements_heap` for a function whose arguments
`params` represent `input` and whose result, a pair of arrays, is in locals `a`
and `b`. -/
def PairPost [Represent γ] (heap : Heap) (initial : Store Unit) (params : List Value)
    (input : γ) (need scratch a b : Nat) (result : Array UInt64 × Array UInt64)
    (store : Store Unit) (state : State) : Prop :=
  ∃ heap' : Heap, heap'.At store ∧ Represent.borrowed heap' store params input ∧
    heap'.top.toNat ≤ heap.top.toNat + need ∧
    store.mem.pages ≤ max initial.mem.pages ((heap.top.toNat + need + 65535) / 65536) ∧
    store.memoryCaps = initial.memoryCaps ∧
    (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store p ws) ∧
    (∀ p ws, heap.Owned initial p ws → heap'.Owned store p ws) ∧
    ∃ values next,
      Expr.evalResults store.mem scratch [⟨.u64, .get a⟩, ⟨.u64, .get b⟩] state =
        some (values, next) ∧ Represent.owned heap' store values result

/-- A call of entry `idx`, which implements `g`, that leaves the two arrays of
`g x = result` in locals `a` and `b` as the caller's result. -/
theorem pairCall_spec [Represent α] [Represent γ] {idx : Nat}
    {g : α → Array UInt64 × Array UInt64} {gNeed : α → Nat}
    (hImpl : Implements clob.module idx g gNeed) {f : Wasm.Function}
    (hFunc : clob.module.funcs[idx]? = some f) {scratch a b : Nat} (hab : a ≠ b)
    {args : List ((type : ScalarType) × Expr type)} (hParams : args.length = f.numParams) {heap heap1 : Heap}
    {initial store1 : Store Unit} {params : List Value} {input : γ} {need : Nat}
    {state afterArgs : State} {x : α} {vals : List Value}
    {result : Array UInt64 × Array UInt64} (hKept : Kept heap initial heap1 store1)
    (hInput : ∀ heap' store', (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' params input)
    (hRoom : heap.Room initial clob.module need)
    (hArgs : Expr.evalResults store1.mem scratch args state = some (vals, afterArgs))
    (hBorrowed : Represent.borrowed heap1 store1 vals x) (hNeed : gNeed x ≤ need)
    (hA : a < afterArgs.params.length + afterArgs.locals.length)
    (hB : b < afterArgs.params.length + afterArgs.locals.length) (hResult : g x = result) :
    Triple clob.module (.call idx args [a, b]) scratch (fun s st => s = store1 ∧ st = state)
      (PairPost heap initial params input need scratch a b result) := by
  have hA' : ∀ v : Value,
      a < (afterArgs.update b v).params.length + (afterArgs.update b v).locals.length := by
    intro v; simp only [State.update_params_length, State.update_locals_length]; exact hA
  have hTop1 := hKept.top
  have hPages1 := hKept.pages
  refine (Stmt.callImplements_spec hImpl (f := f) rfl
    (by rw [show clob.module.imports.length = 0 from rfl]; exact hFunc) hParams hArgs
    hKept.at_ hBorrowed (hRoom.after (used := 0) (by omega) (by omega) hKept.caps)
    fun heap' store' values h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨p1, p2, rfl, -, -⟩ := owned_pair h
    exact ⟨(afterArgs.update b (.i64 p2)).update a (.i64 p1), by
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        State.setAll, State.set?_eq_update _ hB, State.set?_eq_update _ (hA' _),
        Option.bind_eq_bind, Option.bind_some]⟩
  rintro store' st' ⟨heap', values, hAt', hOwned', -, hTop', hPages', hCaps', hKeepB, hKeepO,
    hSet'⟩
  obtain ⟨p1, p2, rfl, -, -⟩ := owned_pair hOwned'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    State.setAll, State.set?_eq_update _ hB, State.set?_eq_update _ (hA' _),
    Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet'
  subst hSet' hResult
  have hGetA : ((afterArgs.update b (.i64 p2)).update a (.i64 p1)).get a = some (.i64 p1) :=
    State.get_update_same (hA' _)
  have hGetB : ((afterArgs.update b (.i64 p2)).update a (.i64 p1)).get b = some (.i64 p2) := by
    rw [State.get_update_ne (Ne.symm hab)]; exact State.get_update_same hB
  exact ⟨heap', hAt', hInput heap' store' fun p ws h => hKeepB p ws (hKept.borrowed p ws h),
    by omega, by omega, hCaps'.trans hKept.caps, fun p ws h => hKeepB p ws (hKept.borrowed p ws h),
    fun p ws h => hKeepO p ws (hKept.owned p ws h), [.i64 p1, .i64 p2],
    (afterArgs.update b (.i64 p2)).update a (.i64 p1),
    by simp [Expr.evalResults, Expr.eval, hGetA, hGetB], hOwned'⟩

/-- Copies of the arrays in locals `src1` and `src2`, left in locals `a` and `b` as
the caller's result. -/
theorem pairCopy_spec [Represent γ] {scratch a b l1 i1 s1 l2 i2 s2 src1 src2 : Nat}
    (h1 : [s1, a, l1, i1].Nodup) (h2 : [s2, b, l2, i2].Nodup)
    (hBelow1 : ∀ j ∈ [s1, a, l1, i1], j < scratch) (hBelow2 : ∀ j ∈ [s2, b, l2, i2], j < scratch)
    (hSrc1 : src1 ∉ [s1, a, l1, i1]) (hSrc2 : src2 ∉ [s1, a, l1, i1])
    (hSrc2' : src2 ∉ [s2, b, l2, i2]) (hAKept : a ∉ [s2, b, l2, i2])
    (hSrcBelow : src1 < scratch ∧ src2 < scratch) {heap heap1 : Heap}
    {initial store1 : Store Unit} {state : State} {params : List Value} {input : γ} {need : Nat}
    {p1 p2 : UInt64} {xs ys : Array UInt64} (hKept : Kept heap initial heap1 store1)
    (hInput : ∀ heap' store', (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' params input)
    (hRoom : heap.Room initial clob.module need)
    (hNeed : 96 + 8 * (xs.size + 1) + 8 * (ys.size + 1) ≤ need)
    (hLength : scratch < state.params.length + state.locals.length)
    (hGet1 : state.get src1 = some (.i64 p1)) (hGet2 : state.get src2 = some (.i64 p2))
    (hXs : heap.Borrowed initial p1 xs) (hYs : heap.Borrowed initial p2 ys) :
    Triple clob.module (.seq (.copy a l1 i1 s1 src1) (.copy b l2 i2 s2 src2)) scratch
      (fun s st => s = store1 ∧ st = state)
      (PairPost heap initial params input need scratch a b (xs, ys)) := by
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  have hX1 := hKept.borrowed p1 xs hXs
  have hY1 := hKept.borrowed p2 ys hYs
  have hXFit := hX1.values.1
  have hYFit := hY1.values.1
  have hTop1 := hKept.top
  have hPages1 := hKept.pages
  have hNeed1 : (UInt64.ofNat (8 * (xs.size + 1))).toNat = 8 * (xs.size + 1) :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hRoomBoth : heap1.Room store1 clob.module
      (48 + (UInt64.ofNat (8 * (xs.size + 1))).toNat + (48 + 8 * (ys.size + 1))) :=
    hRoom.after (used := 0) (by omega) (by rw [hNeed1]; omega) hKept.caps
  refine Stmt.seq_spec (Stmt.copy_spec hMemory32 hImports hAlloc h1 hBelow1 hSrc1 hSrcBelow.1
    hLength hKept.at_ (hRoomBoth.after (used := 0) (by omega) (by rw [hNeed1]; omega) rfl)
    hGet1 hX1) ?_
  apply Triple.of_forall
  rintro store2 t2 ⟨q1, hFrame2, hPtr1, hNew1⟩
  refine (Stmt.copy_spec hMemory32 hImports hAlloc h2 hBelow2 hSrc2' hSrcBelow.2
    (by rw [hFrame2.params, hFrame2.locals]; exact hLength) hNew1.at_
    (Heap.Room.after_allocate hRoomBoth hNew1.caps)
    ((hFrame2.get src2 hSrcBelow.2 hSrc2).trans hGet2) (hNew1.borrowed p2 ys hY1)).mono
      (fun _ _ h => h) ?_
  rintro store3 t3 ⟨q2, hFrame3, hPtr2, hNew2⟩
  have hTop2 := hNew1.top
  have hTop3 := hNew2.top
  have hPages2 := hNew1.pages
  have hPages3 := hNew2.pages
  have hPtr1' : t3.get a = some (.i64 q1) :=
    (hFrame3.get a (hBelow1 a (by simp)) hAKept).trans hPtr1
  exact ⟨_, hNew2.at_, hInput _ _ fun p ws h =>
      hNew2.borrowed p ws (hNew1.borrowed p ws (hKept.borrowed p ws h)),
    by omega, by omega, hNew2.caps.trans (hNew1.caps.trans hKept.caps),
    fun p ws h => hNew2.borrowed p ws (hNew1.borrowed p ws (hKept.borrowed p ws h)),
    fun p ws h => (hNew2.ownedKeep p ws (hNew1.ownedKeep p ws (hKept.owned p ws h)).1).1,
    [.i64 q1, .i64 q2], t3, by simp [Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    [.i64 q1], [.i64 q2], rfl, ⟨q1, rfl, (hNew2.ownedKeep q1 _ hNew1.owned).1⟩,
    ⟨q2, rfl, hNew2.owned⟩⟩

/-- The locals that the branches of `addBid` and `cancelBid` read: the arguments,
and the position `k` in local 5. -/
structure BidLocals (pp ps price size : UInt64) (n : Nat) (k : UInt64) (state : State) :
    Prop where
  params : state.params.length = 4
  locals : state.locals.length = n
  get0 : state.get 0 = some (.i64 pp)
  get1 : state.get 1 = some (.i64 ps)
  get2 : state.get 2 = some (.i64 price)
  get3 : state.get 3 = some (.i64 size)
  get5 : state.get 5 = some (.i64 k)

/-- The entry state of `addBid` and `cancelBid`, with `n` locals. -/
def bidStart (pp ps price size : UInt64) (n : Nat) : State :=
  { params := [.i64 pp, .i64 ps, .i64 price, .i64 size], locals := List.replicate n (.i64 0) }

/-- The code of `addBid` and `cancelBid`: the search, the number of levels, and a
branch on whether the level at the position has the price. -/
def bidBody (thenStmt elseStmt : Stmt) : Stmt :=
  .seq (.call 9 [⟨.u64, .get 0⟩, ⟨.u64, .get 2⟩] [4]) (.seq (.assign 5 (.get 4))
    (.seq (.arraySize 8 0)
      (.ite (.and (.ltU (.get 5) (.get 8)) (.eq (.read 0 (.get 5)) (.get 2))) thenStmt elseStmt)))

/-- The search and the condition of `addBid` and `cancelBid`: each branch starts
from a store that `Kept` describes and a state that `BidLocals` describes,
knowing whether level `findLevel prices price` has the price. -/
theorem bid_spec {n : Nat} (hn : 6 ≤ n) {thenStmt elseStmt : Stmt}
    {Q : Store Unit → State → Prop} {heap : Heap} {initial : Store Unit} {need : Nat}
    {pp ps price size : UInt64} {prices : Array UInt64}
    (hHeap : heap.At initial) (hPrices : heap.Borrowed initial pp prices)
    (hRoom : heap.Room initial clob.module need)
    (hThen : ∀ heap1 store1 state, Kept heap initial heap1 store1 →
      BidLocals pp ps price size n (findTuple (prices, price)) state →
      findTuple (prices, price) < prices.size.toUInt64 ∧
        prices[(findTuple (prices, price)).toNat]! = price →
      Triple clob.module thenStmt (n + 3) (fun s st => s = store1 ∧ st = state) Q)
    (hElse : ∀ heap1 store1 state, Kept heap initial heap1 store1 →
      BidLocals pp ps price size n (findTuple (prices, price)) state →
      ¬(findTuple (prices, price) < prices.size.toUInt64 ∧
        prices[(findTuple (prices, price)).toNat]! = price) →
      Triple clob.module elseStmt (n + 3) (fun s st => s = store1 ∧ st = state) Q) :
    Triple clob.module (bidBody thenStmt elseStmt) (n + 3)
      (fun s st => s = initial ∧ st = bidStart pp ps price size n) Q := by
  have hNoImports : clob.module.imports.length = 0 := rfl
  set K := findTuple (prices, price) with hK
  set start := bidStart pp ps price size n with hStartDef
  have hStart : start.params.length = 4 ∧ start.locals.length = n := ⟨rfl, by simp [start, bidStart]⟩
  have hs0 : start.get 0 = some (.i64 pp) := rfl
  have hs2 : start.get 2 = some (.i64 price) := rfl
  have hLength : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length = s.params.length ∧
        (s.update j v).locals.length = s.locals.length :=
    fun s j v => ⟨State.update_params_length s j v, State.update_locals_length s j v⟩
  have h4 : 4 < start.params.length + start.locals.length := by omega
  refine Stmt.seq_spec (Stmt.callImplements_spec findLevel_implements
    (f := clob.findLevel.ir.function (2 + 6)) rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 6) rfl) rfl
    (vals := [.i64 pp, .i64 price]) (x := (prices, price)) (afterArgs := start)
    (by simp [Expr.evalResults, Expr.eval, hs0, hs2]) hHeap
    ⟨[.i64 pp], [.i64 price], rfl, ⟨pp, rfl, hPrices⟩, rfl⟩
    (hRoom.after (used := 0) (by omega) (by simp) rfl)
    fun _ _ values h => ⟨start.update 4 (.i64 K), by
      rw [show values = [.i64 K] from h]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
        State.set?_eq_update _ h4, Option.bind_eq_bind, Option.bind_some]⟩) ?_
  apply Triple.of_forall
  rintro store1 t1 ⟨heap1, values, hAt1, hValues, -, hTop1, hPages1, hCaps1, hKeepB1, hKeepO1,
    hSet1⟩
  have hFacts : Kept heap initial heap1 store1 :=
    ⟨hAt1, by simpa using hTop1, by simpa using hPages1, hCaps1, hKeepB1, hKeepO1⟩
  rw [show values = [.i64 K] from hValues] at hSet1
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, State.setAll,
    State.set?_eq_update _ h4, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hSet1
  subst hSet1
  have hP1 := (hKeepB1 pp prices hPrices).values
  have hLengthP := hP1.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLengthP
  let u1 := (start.update 4 (.i64 K)).update 5 (.i64 K)
  let u2 := u1.update 8 (.i64 (UInt64.ofNat prices.size))
  have hU1 : u1.params.length = 4 ∧ u1.locals.length = n := by
    simp only [u1, (hLength _ _ _).1, (hLength _ _ _).2, hStart]; exact ⟨trivial, trivial⟩
  have hU2 : u2.params.length = 4 ∧ u2.locals.length = n := by
    simp only [u2, (hLength _ _ _).1, (hLength _ _ _).2, hU1]; exact ⟨trivial, trivial⟩
  have hGet : ∀ j, j < 4 → u2.get j = start.get j := fun j hj => by
    simp only [u2, u1]
    rw [State.get_update_ne (by omega), State.get_update_ne (by omega),
      State.get_update_ne (by omega)]
  have hGet5 : u2.get 5 = some (.i64 K) := by
    simp only [u2, u1]
    rw [State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [(hLength _ _ _).1, (hLength _ _ _).2]; omega)
  have hGet8 : u2.get 8 = some (.i64 (UInt64.ofNat prices.size)) :=
    State.get_update_same (by rw [hU1.1, hU1.2]; omega)
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · have hGet4 : (start.update 4 (.i64 K)).get 4 = some (.i64 K) := State.get_update_same h4
    simp only [Stmt.run, Expr.eval, hGet4, Option.bind_eq_bind, Option.bind_some]
    exact State.set?_eq_update _ (by rw [(hLength _ _ _).1, (hLength _ _ _).2]; omega)
  · have hGet0 : u1.get 0 = some (.i64 pp) := by
      simp only [u1]
      rw [State.get_update_ne (by decide), State.get_update_ne (by decide)]; rfl
    simp only [Stmt.run, Stmt.arraySize, Expr.eval, hGet0, Option.bind_eq_bind, Option.bind_some]
    simp [hLengthP, hP1.lengthRead, State.set?_eq_update _ (show 8 < u1.params.length +
      u1.locals.length by omega), u2]
  -- The condition.
  let found := decide (K < UInt64.ofNat prices.size) && (prices[K.toNat]! == price)
  let after := if K < UInt64.ofNat prices.size then u2.update (n + 3) (.i64 K) else u2
  have hScratch : n + 3 < u2.params.length + u2.locals.length := by omega
  have hAfter : BidLocals pp ps price size n K after := by
    by_cases hlt : K < UInt64.ofNat prices.size
    · have hL := hLength u2 (n + 3) (.i64 K)
      simp only [after, hlt, ite_true]
      exact ⟨hL.1.trans hU2.1, hL.2.trans hU2.2,
        by rw [State.get_update_ne (by omega), hGet 0 (by decide)]; rfl,
        by rw [State.get_update_ne (by omega), hGet 1 (by decide)]; rfl,
        by rw [State.get_update_ne (by omega), hGet 2 (by decide)]; rfl,
        by rw [State.get_update_ne (by omega), hGet 3 (by decide)]; rfl,
        by rw [State.get_update_ne (by omega), hGet5]⟩
    · simp only [after, hlt, ite_false]
      exact ⟨hU2.1, hU2.2, by rw [hGet 0 (by decide)]; rfl, by rw [hGet 1 (by decide)]; rfl,
        by rw [hGet 2 (by decide)]; rfl, by rw [hGet 3 (by decide)]; rfl, hGet5⟩
  have hCondition : (Expr.and (.ltU (.get 5) (.get 8)) (.eq (.read 0 (.get 5)) (.get 2))).eval
      store1.mem (n + 3) u2 = some (found, after) := by
    by_cases hlt : K < UInt64.ofNat prices.size
    · have hRead0 : (u2.update (n + 3) (.i64 K)).get 0 = some (.i64 pp) := by
        rw [State.get_update_ne (by omega), hGet 0 (by decide)]; rfl
      have hRead2 : (u2.update (n + 3) (.i64 K)).get 2 = some (.i64 price) := by
        rw [State.get_update_ne (by omega), hGet 2 (by decide)]; rfl
      simp [Expr.eval, hGet5, hGet8, hlt, State.set?_eq_update _ hScratch,
        Expr.readValue_at hP1 hRead0, hRead2, found, after]
    · simp [Expr.eval, hGet5, hGet8, hlt, found, after]
  refine (Stmt.ite_spec
    (PThen := fun s st => s = store1 ∧ st = after ∧ found = true)
    (PElse := fun s st => s = store1 ∧ st = after ∧ found = false) ?_ ?_).mono
      ?_ fun _ _ h => h
  rotate_left 2
  · rintro s st ⟨rfl, rfl⟩
    exact ⟨found, after, hCondition, by cases found <;> simp⟩
  all_goals
    apply Triple.of_forall
    rintro s st ⟨rfl, rfl, hFound⟩
  · exact hThen heap1 s after hFacts hAfter (by simpa [found] using hFound)
  · exact hElse heap1 s after hFacts hAfter (by simpa [found] using hFound)

/-- `addBid` with its four arguments as one tuple. -/
def addBidTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.addBid x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `addBid` may allocate: those of `insertLevel`, which bound those of
`setLevel`. -/
def addBidNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 2) + 8 * (x.2.1.size + 2)

theorem addBid_implements : Implements clob.module 7 addBidTuple addBidNeed := by
  refine Func.implements_heap clob.funcs 4 clob.addBid.ir "addBid" rfl addBidTuple addBidNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hInput : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 pp, .i64 ps, .i64 price, .i64 size]
        (prices, sizes, price, size) := fun _ _ hKeep =>
    ⟨_, _, rfl, ⟨pp, rfl, hKeep pp prices hPrices⟩, _, _, rfl, ⟨ps, rfl, hKeep ps sizes hSizes⟩, rfl⟩
  show Triple _ (bidBody
    (.call 6 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩,
      ⟨.u64, .bin .add (.read 1 (.get 5)) (.get 3)⟩] [6, 7])
    (.call 5 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 2⟩, ⟨.u64, .get 3⟩]
      [6, 7])) (6 + 3)
    (fun store state => store = initial ∧ state = bidStart pp ps price size 6)
    (PairPost heap initial [.i64 pp, .i64 ps, .i64 price, .i64 size] (prices, sizes, price, size)
      (addBidNeed (prices, sizes, price, size)) 9 6 7 (addBidTuple (prices, sizes, price, size)))
  refine bid_spec (by decide) hHeap hPrices hRoom ?_ ?_
  · -- An existing level: `setLevel` with the size increased.
    intro heap1 store1 state hKept hL hFound
    set K := findTuple (prices, price) with hK
    have hS1 := hKept.borrowed ps sizes hSizes
    have hRead1 : (state.update 9 (.i64 K)).get 1 = some (.i64 ps) := by
      rw [State.get_update_ne (by decide), hL.get1]
    have hLength : (state.update 9 (.i64 K)).params.length +
        (state.update 9 (.i64 K)).locals.length = 10 := by
      simp only [State.update_params_length, State.update_locals_length, hL.params, hL.locals]
    exact pairCall_spec setLevel_implements (compile_funcs (funcs := clob.funcs) (i := 3) rfl)
      (by decide) rfl hKept hInput hRoom
      (vals := [.i64 pp, .i64 ps, .i64 K, .i64 (sizes[K.toNat]! + size)])
      (x := (prices, sizes, K, sizes[K.toNat]! + size)) (afterArgs := state.update 9 (.i64 K))
      (by simp [Expr.evalResults, Expr.eval, hL.get0, hL.get1, hL.get3, hL.get5, U64Op.apply,
        State.set?_eq_update _ (show 9 < state.params.length + state.locals.length by
          rw [hL.params, hL.locals]; decide), Expr.readValue_at hS1.values hRead1])
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hKept.borrowed pp prices hPrices⟩, [.i64 ps], _, rfl,
        ⟨ps, rfl, hS1⟩, rfl⟩
      (by simp only [setNeed, addBidNeed]; omega) (by omega) (by omega)
      (by unfold addBidTuple LeanExe.Examples.Clob.addBid; exact (ite_eq_left hFound).symm)
  · -- A new level: `insertLevel`.
    intro heap1 store1 state hKept hL hFound
    set K := findTuple (prices, price) with hK
    exact pairCall_spec insertLevel_implements (compile_funcs (funcs := clob.funcs) (i := 2) rfl)
      (by decide) rfl hKept hInput hRoom (vals := [.i64 pp, .i64 ps, .i64 K, .i64 price, .i64 size])
      (x := (prices, sizes, K, price, size)) (afterArgs := state)
      (by simp [Expr.evalResults, Expr.eval, hL.get0, hL.get1, hL.get2, hL.get3, hL.get5])
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hKept.borrowed pp prices hPrices⟩, [.i64 ps], _, rfl,
        ⟨ps, rfl, hKept.borrowed ps sizes hSizes⟩, rfl⟩
      (by simp only [insertNeed, addBidNeed]; omega) (by rw [hL.params, hL.locals]; decide)
      (by rw [hL.params, hL.locals]; decide)
      (by unfold addBidTuple LeanExe.Examples.Clob.addBid; exact (ite_eq_right hFound).symm)

/-- `cancelBid` with its four arguments as one tuple. -/
def cancelTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.cancelBid x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The bytes `cancelBid` may allocate: a new array no longer than each input. -/
def cancelNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 1) + 8 * (x.2.1.size + 1)

theorem cancelBid_implements : Implements clob.module 11 cancelTuple cancelNeed := by
  refine Func.implements_heap clob.funcs 8 clob.cancelBid.ir "cancelBid" rfl cancelTuple
    cancelNeed (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hInput : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 pp, .i64 ps, .i64 price, .i64 size]
        (prices, sizes, price, size) := fun _ _ hKeep =>
    ⟨_, _, rfl, ⟨pp, rfl, hKeep pp prices hPrices⟩, _, _, rfl, ⟨ps, rfl, hKeep ps sizes hSizes⟩, rfl⟩
  show Triple _ (bidBody
    (.ite (.leU (.read 1 (.get 5)) (.get 3))
      (.call 10 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩] [6, 7])
      (.call 6 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩,
        ⟨.u64, .bin .sub (.read 1 (.get 5)) (.get 3)⟩] [6, 7]))
    (.seq (.copy 6 10 11 9 0) (.copy 7 13 14 12 1))) (12 + 3)
    (fun store state => store = initial ∧ state = bidStart pp ps price size 12)
    (PairPost heap initial [.i64 pp, .i64 ps, .i64 price, .i64 size] (prices, sizes, price, size)
      (cancelNeed (prices, sizes, price, size)) 15 6 7 (cancelTuple (prices, sizes, price, size)))
  refine bid_spec (by decide) hHeap hPrices hRoom ?_ ?_
  · -- An existing level: removed, or reduced by `size`.
    intro heap1 store1 state hFacts hL hFound
    set K := findTuple (prices, price) with hK
    have hS1 := hFacts.borrowed ps sizes hSizes
    let read := state.update 15 (.i64 K)
    have hRead : 15 < state.params.length + state.locals.length := by
      rw [hL.params, hL.locals]; decide
    have hRead1 : read.get 1 = some (.i64 ps) := by
      rw [State.get_update_ne (by decide), hL.get1]
    have hReadL : read.params.length = 4 ∧ read.locals.length = 12 :=
      ⟨(State.update_params_length _ _ _).trans hL.params,
        (State.update_locals_length _ _ _).trans hL.locals⟩
    have hReadGet : ∀ j, j < 15 → read.get j = state.get j := fun j hj =>
      State.get_update_ne (by omega)
    refine (Stmt.ite_spec
      (PThen := fun s st => s = store1 ∧ st = read ∧ sizes[K.toNat]! ≤ size)
      (PElse := fun s st => s = store1 ∧ st = read ∧ ¬sizes[K.toNat]! ≤ size) ?_ ?_).mono
        ?_ fun _ _ h => h
    rotate_left 2
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨decide (sizes[K.toNat]! ≤ size), read, ?_, by by_cases h : sizes[K.toNat]! ≤ size <;> simp [h]⟩
      simp [Expr.eval, hL.get3, hL.get5, State.set?_eq_update _ hRead, read,
        Expr.readValue_at hS1.values hRead1, hReadGet 3 (by decide)]
    all_goals
      apply Triple.of_forall
      rintro s st ⟨rfl, rfl, hLe⟩
    · exact pairCall_spec removeLevel_implements (compile_funcs (funcs := clob.funcs) (i := 7) rfl)
        (by decide) rfl hFacts hInput hRoom (vals := [.i64 pp, .i64 ps, .i64 K])
        (x := (prices, sizes, K))
        (afterArgs := read)
        (by simp [Expr.evalResults, Expr.eval, hReadGet 0 (by decide), hReadGet 1 (by decide),
          hReadGet 5 (by decide), hL.get0, hL.get1, hL.get5])
        ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hFacts.borrowed pp prices hPrices⟩, [.i64 ps], _, rfl,
          ⟨ps, rfl, hS1⟩, rfl⟩
        (by simp only [removeNeed, cancelNeed]; omega) (by rw [hReadL.1, hReadL.2]; decide)
        (by rw [hReadL.1, hReadL.2]; decide)
        (by unfold cancelTuple LeanExe.Examples.Clob.cancelBid
            exact ((ite_eq_left hFound).trans (ite_eq_left hLe)).symm)
    · have hRead1' : (read.update 15 (.i64 K)).get 1 = some (.i64 ps) := by
        rw [State.get_update_ne (by decide), hRead1]
      exact pairCall_spec setLevel_implements (compile_funcs (funcs := clob.funcs) (i := 3) rfl)
        (by decide) rfl hFacts hInput hRoom
        (vals := [.i64 pp, .i64 ps, .i64 K, .i64 (sizes[K.toNat]! - size)])
        (x := (prices, sizes, K, sizes[K.toNat]! - size)) (afterArgs := read.update 15 (.i64 K))
        (by simp [Expr.evalResults, Expr.eval, hReadGet 0 (by decide), hReadGet 1 (by decide),
          hReadGet 3 (by decide), hReadGet 5 (by decide), hL.get0, hL.get1, hL.get3, hL.get5,
          U64Op.apply, State.set?_eq_update _ (show 15 < read.params.length +
            read.locals.length by rw [hReadL.1, hReadL.2]; decide),
          Expr.readValue_at hS1.values hRead1'])
        ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hFacts.borrowed pp prices hPrices⟩, [.i64 ps], _, rfl,
          ⟨ps, rfl, hS1⟩, rfl⟩
        (by simp only [setNeed, cancelNeed]; omega)
        (by simp only [State.update_params_length, State.update_locals_length, hReadL.1,
          hReadL.2]; decide)
        (by simp only [State.update_params_length, State.update_locals_length, hReadL.1,
          hReadL.2]; decide)
        (by unfold cancelTuple LeanExe.Examples.Clob.cancelBid
            exact ((ite_eq_left hFound).trans (ite_eq_right hLe)).symm)
  · -- No level at the price: copies of both arrays.
    intro heap1 store1 state hKept hL hFound
    rw [show cancelTuple (prices, sizes, price, size) = (prices, sizes) by
      unfold cancelTuple LeanExe.Examples.Clob.cancelBid; exact ite_eq_right hFound]
    exact pairCopy_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hKept hInput hRoom (by simp only [cancelNeed]; omega)
      (by rw [hL.params, hL.locals]; decide) hL.get0 hL.get1 hPrices hSizes

/-- `applyCommand` with its five arguments as one tuple. -/
def applyTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.applyCommand x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The bytes `applyCommand` may allocate: those of `addBid`, which bound those of
`cancelBid` and of the copies. -/
def applyNeed (x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64) : Nat :=
  96 + 8 * (x.1.size + 2) + 8 * (x.2.1.size + 2)

theorem applyCommand_implements : Implements clob.module 12 applyTuple applyNeed := by
  refine Func.implements_heap clob.funcs 9 clob.applyCommand.ir "applyCommand" rfl applyTuple
    applyNeed (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, kind, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
  change heap.Room initial clob.module _ at hRoom
  have hInput : ∀ (heap' : Heap) (store' : Store Unit),
      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →
      Represent.borrowed heap' store' [.i64 pp, .i64 ps, .i64 kind, .i64 price, .i64 size]
        (prices, sizes, kind, price, size) := fun _ _ hKeep =>
    ⟨_, _, rfl, ⟨pp, rfl, hKeep pp prices hPrices⟩, _, _, rfl, ⟨ps, rfl, hKeep ps sizes hSizes⟩, rfl⟩
  have hKept := Kept.refl hHeap
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 kind, .i64 price, .i64 size]
      locals := List.replicate 9 (.i64 0) }
  have hGet : start.get 0 = some (.i64 pp) ∧ start.get 1 = some (.i64 ps) ∧
      start.get 2 = some (.i64 kind) ∧ start.get 3 = some (.i64 price) ∧
      start.get 4 = some (.i64 size) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hLength : start.params.length + start.locals.length = 14 := rfl
  show Triple _ (.ite (.eq (.get 2) (.const 0))
      (.call 7 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5, 6])
      (.ite (.eq (.get 2) (.const 1))
        (.call 11 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5, 6])
        (.seq (.copy 5 8 9 7 0) (.copy 6 11 12 10 1)))) 13
    (fun store state => store = initial ∧ state = start)
    (PairPost heap initial [.i64 pp, .i64 ps, .i64 kind, .i64 price, .i64 size]
      (prices, sizes, kind, price, size) (applyNeed (prices, sizes, kind, price, size)) 13 5 6
      (applyTuple (prices, sizes, kind, price, size)))
  have hArgs : Expr.evalResults initial.mem 13
      [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] start =
      some ([.i64 pp, .i64 ps, .i64 price, .i64 size], start) := by
    simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.1, hGet.2.2.2.1, hGet.2.2.2.2]
  have hBorrowed : Represent.borrowed heap initial
      [.i64 pp, .i64 ps, .i64 price, .i64 size] (prices, sizes, price, size) :=
    ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
  refine (Stmt.ite_spec
    (PThen := fun s st => s = initial ∧ st = start ∧ kind = 0)
    (PElse := fun s st => s = initial ∧ st = start ∧ kind ≠ 0) ?_ ?_).mono ?_ fun _ _ h => h
  rotate_left 2
  · rintro s st ⟨hs, rfl⟩
    subst s
    exact ⟨kind == 0, start, by simp [Expr.eval, hGet.2.2.1],
      by by_cases h : kind = 0 <;> simp [h]⟩
  all_goals
    apply Triple.of_forall
    rintro s st ⟨hs, rfl, hKind⟩
    subst s
  · -- Kind 0: add a bid.
    exact pairCall_spec addBid_implements (compile_funcs (funcs := clob.funcs) (i := 4) rfl)
      (by decide) rfl hKept hInput hRoom hArgs hBorrowed (by simp only [addBidNeed, applyNeed]; omega)
      (by rw [hLength]; decide) (by rw [hLength]; decide)
      (by unfold applyTuple LeanExe.Examples.Clob.applyCommand; exact (ite_eq_left hKind).symm)
  refine (Stmt.ite_spec
    (PThen := fun s st => s = initial ∧ st = start ∧ kind = 1)
    (PElse := fun s st => s = initial ∧ st = start ∧ kind ≠ 1) ?_ ?_).mono ?_ fun _ _ h => h
  rotate_left 2
  · rintro s st ⟨hs, rfl⟩
    subst s
    exact ⟨kind == 1, start, by simp [Expr.eval, hGet.2.2.1],
      by by_cases h : kind = 1 <;> simp [h]⟩
  all_goals
    apply Triple.of_forall
    rintro s st ⟨hs, rfl, hKind1⟩
    subst s
  · -- Kind 1: cancel a bid.
    exact pairCall_spec cancelBid_implements (compile_funcs (funcs := clob.funcs) (i := 8) rfl)
      (by decide) rfl hKept hInput hRoom hArgs hBorrowed
      (by simp only [cancelNeed, applyNeed]; omega) (by rw [hLength]; decide)
      (by rw [hLength]; decide)
      (by unfold applyTuple LeanExe.Examples.Clob.applyCommand
          exact ((ite_eq_right hKind).trans (ite_eq_left hKind1)).symm)
  · -- Any other kind: copies of both arrays.
    rw [show applyTuple (prices, sizes, kind, price, size) = (prices, sizes) by
      unfold applyTuple LeanExe.Examples.Clob.applyCommand
      exact (ite_eq_right hKind).trans (ite_eq_right hKind1)]
    exact pairCopy_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hKept hInput hRoom (by simp only [applyNeed]; omega)
      (by rw [hLength]; decide) hGet.1 hGet.2.1 hPrices hSizes

/-- `encode` succeeds on `clob.module`, and its bytes decode to a module whose
exports compute the CLOB operations exactly. -/
theorem clob_bytes : ∃ bytes, Encoding.encode clob.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧
      Implements m 3 marketBuyTuple (fun _ => 72) ∧ Implements m 4 fillTuple fillNeed ∧
      Implements m 5 insertTuple insertNeed ∧ Implements m 6 setTuple setNeed ∧
      Implements m 7 addBidTuple addBidNeed ∧ Implements m 8 depthTuple (fun _ => 0) ∧
      Implements m 9 findTuple (fun _ => 0) ∧ Implements m 10 removeTuple removeNeed ∧
      Implements m 11 cancelTuple cancelNeed ∧ Implements m 12 applyTuple applyNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip clob.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, clob.module, decoded, marketBuy_implements, fillLevel_implements,
    insertLevel_implements, setLevel_implements, addBid_implements,
    depth_implements, findLevel_implements, removeLevel_implements, cancelBid_implements,
    applyCommand_implements⟩

end Project.Clob
