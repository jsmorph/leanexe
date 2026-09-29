import Project.Clob.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
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

example : marketBuy.ir.body = .seq (.arraySize 3 0) (.seq (.assign 4 (.get 2))
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
    Implements marketBuy.module 3 marketBuyTuple (fun _ => 72) := by
  refine Func.implements_heap [(marketBuy.ir, "marketBuy")] 0 marketBuy.ir "marketBuy" rfl marketBuyTuple (fun _ => 72)
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, qty⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : (compile [(marketBuy.ir, "marketBuy")]).memIs64 = false := rfl
  have hImports : (compile [(marketBuy.ir, "marketBuy")]).imports = [] := rfl
  have hAlloc : (compile [(marketBuy.ir, "marketBuy")]).funcs[0]? = some (allocFunction 0) := rfl
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
      by simp [marketBuy.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
    rw [marketBuyTuple, marketBuy_eq, hResult]
    simpa using hOwned

/-- `encode` succeeds on `marketBuy.module`, and its bytes decode to a module that
computes `marketBuy` exactly, returning an array the caller owns. -/
theorem marketBuy_bytes : ∃ bytes, Encoding.encode marketBuy.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 marketBuyTuple (fun _ => 72) := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip marketBuy.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, marketBuy.module, decoded, marketBuy_implements⟩

/-- `fillLevel` with its three arguments as one tuple. -/
def fillTuple (x : Array UInt64 × UInt64 × UInt64) : Array UInt64 :=
  LeanExe.Examples.Clob.fillLevel x.1 x.2.1 x.2.2

/-- The bytes `fillLevel` may allocate: one array of the input's length. -/
def fillNeed (x : Array UInt64 × UInt64 × UInt64) : Nat := 48 + 8 * (x.1.size + 1)

theorem fillLevel_implements : Implements fillLevel.module 3 fillTuple fillNeed := by
  refine Func.implements_heap [(fillLevel.ir, "fillLevel")] 0 fillLevel.ir "fillLevel" rfl fillTuple fillNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨sizes, k, amount⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : (compile [(fillLevel.ir, "fillLevel")]).memIs64 = false := rfl
  have hImports : (compile [(fillLevel.ir, "fillLevel")]).imports = [] := rfl
  have hAlloc : (compile [(fillLevel.ir, "fillLevel")]).funcs[0]? = some (allocFunction 0) := rfl
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
      by simp [fillLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ptr, rfl, ?_⟩
    rw [fillTuple, LeanExe.Examples.Clob.fillLevel, set!_eq_build sizes k value hSize64]
    exact hOwned

/-- `encode` succeeds on `fillLevel.module`, and its bytes decode to a module that
computes `fillLevel` exactly, returning a new array the caller owns. -/
theorem fillLevel_bytes : ∃ bytes, Encoding.encode fillLevel.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 fillTuple fillNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip fillLevel.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, fillLevel.module, decoded, fillLevel_implements⟩

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

theorem insertLevel_implements : Implements insertLevel.module 3 insertTuple insertNeed := by
  refine Func.implements_heap [(insertLevel.ir, "insertLevel")] 0 insertLevel.ir "insertLevel" rfl insertTuple insertNeed
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hRoom
  have hMemory32 : (compile [(insertLevel.ir, "insertLevel")]).memIs64 = false := rfl
  have hImports : (compile [(insertLevel.ir, "insertLevel")]).imports = [] := rfl
  have hAlloc : (compile [(insertLevel.ir, "insertLevel")]).funcs[0]? = some (allocFunction 0) := rfl
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
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
  have hRoom1 : heap.Room initial (compile [(insertLevel.ir, "insertLevel")])
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
      store1 (compile [(insertLevel.ir, "insertLevel")])
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
    by simp [insertLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
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

/-- `encode` succeeds on `insertLevel.module`, and its bytes decode to a module that
computes `insertLevel` exactly, returning two new arrays the caller owns. -/
theorem insertLevel_bytes : ∃ bytes, Encoding.encode insertLevel.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧ Implements m 3 insertTuple insertNeed := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip insertLevel.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, insertLevel.module, decoded, insertLevel_implements⟩

end Project.Clob
