import Project.Clob.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Update
import Project.IR.Call
import Project.IR.ArrayLoop
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
    Implements clob.module 2 marketBuyTuple := by
  refine Func.implements_heap clob.funcs 0 clob.marketBuy.ir "marketBuy" rfl marketBuyTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, qty⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hCap
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
    (by rw [hFrame4.params, hFrame4.locals]; simp [s3, s2, s1, hParams, hLocals]) hHeap hCap (by decide) ?_).mono
      (fun _ _ h => h) ?_
  · refine .cons (fun _ state hFrame => ⟨state, ?_⟩) (.cons (fun _ state hFrame => ⟨state, ?_⟩) .nil)
    · simp [Expr.eval, hFrame.get 2 (by decide) (by decide), hFrame.get 4 (by decide) (by decide),
        h2, h4, U64Op.apply]
    · simp [Expr.eval, hFrame.get 5 (by decide) (by decide), h5]
  · rintro store state ⟨ptr, -, hPtr, hNew⟩
    have hOwned := hNew.owned
    refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed,
      hNew.ownedKeep, [.i64 ptr], state,
      by simp [clob.marketBuy.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
    fun p ws h => Represent.outside_array.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_array.mpr (hNew.ownedApart p ws h)⟩
    rw [marketBuyTuple, marketBuy_eq, hResult]
    simpa using hOwned

/-- `fillLevel` with its three arguments as one tuple, the sizes handed over. -/
def fillTuple (x : Moved (Array UInt64) × UInt64 × UInt64) : Array UInt64 :=
  LeanExe.Examples.Clob.fillLevel x.1.val x.2.1 x.2.2

theorem fillLevel_implements : Implements clob.module 3 fillTuple := by
  refine Func.implements_moves clob.funcs 1 clob.fillLevel.ir "fillLevel" rfl fillTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨sizes⟩, k, amount⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ - -
  have hS := hSizes.values
  let value := sizes[k.toNat]! - amount
  let start : State :=
    { params := [.i64 ps, .i64 k, .i64 amount], locals := List.replicate 4 (.i64 0) }
  let s1 := start.update 3 (.i64 k)
  let s2 := (s1.update 6 (.i64 k)).update 4 (.i64 value)
  show Triple _ (.seq (.assign 3 (.get 1)) (.seq (.assign 4 (.bin .sub (.read 0 (.get 1)) (.get 2)))
    (Stmt.setInPlace 0 5 3 4))) 6
    (fun store state => store = initial ∧ state = start) _
  have hParams : start.params.length = 3 := rfl
  have hLocals : start.locals.length = 4 := rfl
  have hGet0 : start.get 0 = some (.i64 ps) := rfl
  have hGet1 : start.get 1 = some (.i64 k) := rfl
  have hGet2 : start.get 2 = some (.i64 amount) := rfl
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet1, State.set?_eq_update, hParams, hLocals, s1]
  · simp [Stmt.run, Expr.eval, hGet1, hGet2, Expr.readValue_at hS, hGet0, State.set?_eq_update,
      hParams, hLocals, s1, s2, U64Op.apply, value]
  refine (Stmt.setInPlace_spec (p := ps) (kw := k) (vw := value) (by decide)
    (by simp [s2, s1, hParams, hLocals]) (by simp [s2, s1, hGet0])
    (by simp [s2, s1, hParams, hLocals])
    (by simp [s2, s1, hParams, hLocals]) (by decide) (by decide) (by decide) hHeap
    hSizes).mono (fun _ _ h => h) ?_
  rintro store state ⟨heap', p, -, hPtr, hAt, hOwned, hCaps, hBorrowed, hOwnedKeep⟩
  have hApart : ∀ r, Apart initial [ps] r → regionsDisjoint r (block initial ps) :=
    fun r h => h ps (List.mem_singleton_self _)
  refine ⟨heap', hAt, hCaps, fun q ws hq ha => (hBorrowed q ws hq (hApart _ ha)).1,
    fun q ws hq ha => (hOwnedKeep q ws hq (hApart _ ha)).imp_right And.left, [.i64 p], state,
    by simp [clob.fillLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨p, rfl, hOwned⟩,
    fun q ws hq ha => Represent.outside_array.mpr (hBorrowed q ws hq (hApart _ ha)).2,
    fun q ws hq ha => Represent.outside_array.mpr (hOwnedKeep q ws hq (hApart _ ha)).2.2⟩

/-- `insertLevel` with its five arguments as one tuple. -/
def insertTuple (x : Array UInt64 × Array UInt64 × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.insertLevel x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

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

theorem insertLevel_implements : Implements clob.module 4 insertTuple := by
  refine Func.implements_heap clob.funcs 2 clob.insertLevel.ir "insertLevel" rfl insertTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hCap
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
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
  refine Stmt.seq_spec (Stmt.build_spec (n := insertCount prices.size k)
    (insertAt prices k price) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [s3, s2, s1, hParams, hLocals]) hHeap hCap
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
  refine (Stmt.build_spec (n := insertCount sizes.size k)
    (insertAt sizes k size) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [u3, u2, u1, hT1.1, hT1.2]) hAt1 (memoryCap_le_of_caps hNew1.caps hCap)
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
  have hKeep2 := hNew2.borrowed
  have hPtr1' : t2.get 8 = some (.i64 ptr1) := by
    rw [hFrame2.get 8 (by decide) (by decide)]; simp [u3, u2, u1, hPtr1]
  refine ⟨_, hAt2, hNew2.caps.trans hNew1.caps,
    fun p ws h => hKeep2 p ws (hKeep1 p ws h),
    (hNew1.two hNew2).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.insertLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    Represent.owned_pair.mpr ⟨?_, ?_, hNew1.two_apart hNew2⟩,
    fun p ws h => Represent.outside_pair.mpr ((hNew1.two hNew2).2.1 p ws h),
    fun p ws h => Represent.outside_pair.mpr ((hNew1.two hNew2).2.2 p ws h)⟩
  · have hOwned := (hNew2.ownedKeep ptr1 _ hOwned1).1
    rw [insertIdx!_eq_build prices k price (by omega)]
    exact hOwned
  · rw [insertIdx!_eq_build sizes k size (by omega)]
    exact hOwned2

/-- `setLevel` with its four arguments as one tuple, both arrays handed over. -/
def setTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.setLevel x.1.val x.2.1.val x.2.2.1 x.2.2.2

theorem setLevel_implements : Implements clob.module 5 setTuple := by
  refine Func.implements_moves clob.funcs 3 clob.setLevel.ir "setLevel" rfl setTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, k, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hSeparate -
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  have hMoved : Represent.moves initial ([.i64 pp] ++ ([.i64 ps] ++ Scalar.values (k, size)))
      (Moved.mk prices, Moved.mk sizes, k, size) = [pp, ps] := rfl
  rw [hMoved] at hSeparate ⊢
  have hPS : regionsDisjoint (block initial pp) (block initial ps) := by
    have := hSeparate.1
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq] at this
    exact this.1
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k, .i64 size], locals := List.replicate 3 (.i64 0) }
  show Triple _ (.seq (.assign 4 (.get 2)) (.seq (.assign 5 (.get 3))
    (Stmt.setInPlace 1 6 4 5))) 7
    (fun store state => store = initial ∧ state = start) _
  have hStart : start.params.length = 4 ∧ start.locals.length = 3 := ⟨rfl, rfl⟩
  have sg0 : start.get 0 = some (.i64 pp) := rfl
  have sg1 : start.get 1 = some (.i64 ps) := rfl
  have sg2 : start.get 2 = some (.i64 k) := rfl
  have sg3 : start.get 3 = some (.i64 size) := rfl
  let u1 := start.update 4 (.i64 k)
  let u2 := u1.update 5 (.i64 size)
  have g1_3 : u1.get 3 = some (.i64 size) := by rw [State.get_update_ne (by decide), sg3]
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · simp [Stmt.run, Expr.eval, sg2, State.set?_eq_update, hStart.1, hStart.2, u1]
  · simp [Stmt.run, Expr.eval, g1_3, State.set?_eq_update, hStart.1, hStart.2, u1, u2]
  refine (Stmt.setInPlace_spec (p := ps) (kw := k) (vw := size) (by decide)
    (by simp [u2, u1, hStart.1, hStart.2]) (by simp [u2, u1, sg1])
    (by simp [u2, u1, hStart.1, hStart.2]) (by simp [u2, u1, hStart.1, hStart.2])
    (by decide) (by decide) (by decide) hHeap hSizes).mono (fun _ _ h => h) ?_
  rintro store state ⟨heap', p, hFrame, hPtr, hAt, hOwned, hCaps, hBorrowed, hOwnedKeep⟩
  have hPtr0 : state.get 0 = some (.i64 pp) := by
    rw [hFrame.get 0 (by decide) (by decide)]; simp [u2, u1, sg0]
  obtain ⟨hKeptP, hCapP, hApartP⟩ := hOwnedKeep pp prices hPrices hPS
  have hBlockP : block store pp = block initial pp := block_eq hCapP
  have hPart : ∀ r, Apart initial [pp, ps] r →
      regionsDisjoint r (block initial pp) ∧ regionsDisjoint r (block initial ps) :=
    fun r hA => ⟨hA pp (by simp), hA ps (by simp)⟩
  refine ⟨heap', hAt, hCaps, fun q ws hq hA => (hBorrowed q ws hq (hPart _ hA).2).1,
    fun q ws hq hA => (hOwnedKeep q ws hq (hPart _ hA).2).imp_right And.left,
    [.i64 pp, .i64 p], state,
    by simp [clob.setLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr0, hPtr],
    Represent.owned_pair.mpr ⟨hKeptP, hOwned, by rw [hBlockP]; exact hApartP⟩,
    fun q ws hq hA => Represent.outside_pair.mpr
      ⟨by rw [hBlockP]; exact (hPart _ hA).1, (hBorrowed q ws hq (hPart _ hA).2).2⟩,
    fun q ws hq hA => Represent.outside_pair.mpr
      ⟨by rw [hBlockP]; exact (hPart _ hA).1, (hOwnedKeep q ws hq (hPart _ hA).2).2.2⟩⟩

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

theorem depth_implements : Implements clob.module 7 depthTuple := by
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

theorem findLevel_implements : Implements clob.module 8 findTuple := by
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

theorem removeLevel_implements : Implements clob.module 9 removeTuple := by
  refine Func.implements_heap clob.funcs 7 clob.removeLevel.ir "removeLevel" rfl removeTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨prices, sizes, k⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hCap
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hImports : clob.module.imports = [] := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  change heap.Borrowed initial pp prices at hPrices
  change heap.Borrowed initial ps sizes at hSizes
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
  refine Stmt.seq_spec (Stmt.build_spec (n := eraseCount prices.size k)
    (eraseAt prices k) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [s2, s1, hParams, hLocals]) hHeap hCap
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
  refine (Stmt.build_spec (n := eraseCount sizes.size k)
    (eraseAt sizes k) hMemory32 hImports hAlloc (by decide) (by decide)
    (by simp [u2, u1, hT1.1, hT1.2]) hAt1 (memoryCap_le_of_caps hNew1.caps hCap)
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
  have hKeep2 := hNew2.borrowed
  have hPtr1' : t2.get 5 = some (.i64 ptr1) := by
    rw [hFrame2.get 5 (by decide) (by decide)]; simp [u2, u1, hPtr1]
  refine ⟨_, hAt2, hNew2.caps.trans hNew1.caps,
    fun p ws h => hKeep2 p ws (hKeep1 p ws h),
    (hNew1.two hNew2).1,
    [.i64 ptr1, .i64 ptr2], t2,
    by simp [clob.removeLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr1', hPtr2],
    Represent.owned_pair.mpr ⟨?_, ?_, hNew1.two_apart hNew2⟩,
    fun p ws h => Represent.outside_pair.mpr ((hNew1.two hNew2).2.1 p ws h),
    fun p ws h => Represent.outside_pair.mpr ((hNew1.two hNew2).2.2 p ws h)⟩
  · have hOwned := (hNew2.ownedKeep ptr1 _ hOwned1).1
    rw [eraseIdxIfInBounds_eq_build prices k (by omega)]
    exact hOwned
  · rw [eraseIdxIfInBounds_eq_build sizes k (by omega)]
    exact hOwned2

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
  .seq (.call 8 [⟨.u64, .get 0⟩, ⟨.u64, .get 2⟩] [4]) (.seq (.assign 5 (.get 4))
    (.seq (.arraySize 8 0)
      (.ite (.and (.ltU (.get 5) (.get 8)) (.eq (.read 0 (.get 5)) (.get 2))) thenStmt elseStmt)))

/-- The search and the condition of `addBid` and `cancelBid`: each branch starts
from a store with the same live temporaries and a state that `BidLocals` describes,
knowing whether level `findLevel prices price` has the price. -/
theorem bid_spec {n : Nat} (hn : 6 ≤ n) {thenStmt elseStmt : Stmt}
    {Q : Store Unit → State → Prop} {heap0 heap : Heap} {initial store : Store Unit}
    {moved : List UInt64} {temps : List (UInt64 × Array UInt64)}
    {pp ps price size : UInt64} {prices : Array UInt64}
    (hLive : Live heap0 initial moved heap store temps)
    (hPrices : ∀ heap1 store1, Live heap0 initial moved heap1 store1 temps →
      heap1.Borrowed store1 pp prices)
    (hCap : initial.memoryCap clob.module 0 ≤ 65535)
    (hThen : ∀ heap1 store1 state, Live heap0 initial moved heap1 store1 temps →
      BidLocals pp ps price size n (findTuple (prices, price)) state →
      findTuple (prices, price) < prices.size.toUInt64 ∧
        prices[(findTuple (prices, price)).toNat]! = price →
      Triple clob.module thenStmt (n + 3) (fun s st => s = store1 ∧ st = state) Q)
    (hElse : ∀ heap1 store1 state, Live heap0 initial moved heap1 store1 temps →
      BidLocals pp ps price size n (findTuple (prices, price)) state →
      ¬(findTuple (prices, price) < prices.size.toUInt64 ∧
        prices[(findTuple (prices, price)).toNat]! = price) →
      Triple clob.module elseStmt (n + 3) (fun s st => s = store1 ∧ st = state) Q) :
    Triple clob.module (bidBody thenStmt elseStmt) (n + 3)
      (fun s st => s = store ∧ st = bidStart pp ps price size n) Q := by
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
  refine Live.callScalar_seq findLevel_implements (f := clob.findLevel.ir.function (2 + 6)) rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 6) rfl) rfl hLive hCap
    (vals := [.i64 pp, .i64 price]) (x := (prices, price)) (afterArgs := start)
    (after := start.update 4 (.i64 K)) (by simp [Expr.evalResults, Expr.eval, hs0, hs2])
    ⟨[.i64 pp], [.i64 price], rfl, ⟨pp, rfl, hPrices heap store hLive⟩, rfl⟩
    (by simp only [Scalar.values, List.reverse_cons, List.reverse_nil, List.nil_append,
      State.setAll, State.set?_eq_update _ h4, Option.bind_eq_bind, Option.bind_some]; rfl)
    fun heap1 store1 hFacts => ?_
  have hP1 := (hPrices heap1 store1 hFacts).values
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

/-- The obligation of `Func.implements_moves` for a CLOB function that consumes the arrays at
`moved` and returns the pair in locals `a` and `b`. -/
def MovesPost (heap : Heap) (initial : Store Unit) (moved : List UInt64) (scratch a b : Nat)
    (result : Array UInt64 × Array UInt64) (store : Store Unit) (state : State) : Prop :=
  ∃ heap' : Heap, heap'.At store ∧ store.memoryCaps = initial.memoryCaps ∧
    (∀ p ws, heap.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
      heap'.Borrowed store p ws) ∧
    (∀ p ws, heap.Owned initial p ws → Apart initial moved (block initial p) →
      heap'.Owned store p ws ∧ capacityAt store p = capacityAt initial p) ∧
    ∃ values next,
      Expr.evalResults store.mem scratch [⟨.u64, .get a⟩, ⟨.u64, .get b⟩] state =
        some (values, next) ∧ Represent.owned heap' store values result ∧
      (∀ p ws, heap.Borrowed initial p ws → Apart initial moved (p.toNat, 8 * (ws.size + 1)) →
        Represent.outside store values result (p.toNat, 8 * (ws.size + 1))) ∧
      (∀ p ws, heap.Owned initial p ws → Apart initial moved (block initial p) →
        Represent.outside store values result (block initial p))

/-- A body whose live temporaries are its two results, in locals `a` and `b`, ends with
`MovesPost`. -/
theorem movesPost_of_live {heap heap1 : Heap} {initial store : Store Unit} {moved : List UInt64}
    {p1 p2 : UInt64} {xs ys : Array UInt64} {scratch a b : Nat} {state : State}
    (hLive : Live heap initial moved heap1 store [(p1, xs), (p2, ys)])
    (hA : state.get a = some (.i64 p1)) (hB : state.get b = some (.i64 p2)) :
    MovesPost heap initial moved scratch a b (xs, ys) store state := by
  obtain ⟨heap', hAt, hCaps, hKB, hKO, hOwned, hOB, hOO⟩ := hLive.finish_pair
  exact ⟨heap', hAt, hCaps, hKB, hKO, [.i64 p1, .i64 p2], state,
    by simp [Expr.evalResults, Expr.eval, hA, hB], hOwned, hOB, hOO⟩

/-- `addBid` with its four arguments as one tuple: the call consumes both arrays. -/
def addBidTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.addBid x.1.val x.2.1.val x.2.2.1 x.2.2.2

/-- Two owned arrays whose blocks are apart start the live temporaries of a body that consumes
both. -/
theorem live_two {heap : Heap} {initial : Store Unit} {pp ps : UInt64}
    {prices sizes : Array UInt64} (hHeap : heap.At initial) (hPrices : heap.Owned initial pp prices)
    (hSizes : heap.Owned initial ps sizes)
    (hPS : regionsDisjoint (block initial pp) (block initial ps)) :
    Live heap initial [pp, ps] heap initial [(pp, prices), (ps, sizes)] :=
  Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [hPrices, hSizes])
    (.cons (by simpa using hPS) (.cons (by simp) .nil))

theorem addBid_implements : Implements clob.module 6 addBidTuple := by
  refine Func.implements_moves clob.funcs 4 clob.addBid.ir "addBid" rfl addBidTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ ⟨hPair, -⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  have hPS : regionsDisjoint (block initial pp) (block initial ps) := by
    change ([pp, ps].map (block initial)).Pairwise regionsDisjoint at hPair
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq] at hPair
    exact hPair.1
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hImports : clob.module.imports = [] := rfl
  have hRelease : clob.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  show Triple _ (bidBody
    (.call 5 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩,
      ⟨.u64, .bin .add (.read 1 (.get 5)) (.get 3)⟩] [6, 7])
    (.seq (.call 4 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 2⟩,
      ⟨.u64, .get 3⟩] [6, 7]) (.seq (.release 1) (.release 0)))) (6 + 3)
    (fun store state => store = initial ∧ state = bidStart pp ps price size 6)
    (MovesPost heap initial [pp, ps] 9 6 7 (addBidTuple (⟨prices⟩, ⟨sizes⟩, price, size)))
  refine bid_spec (by decide) (live_two hHeap hPrices hSizes hPS)
    (fun _ _ hL => (hL.tempsOwned (pp, prices) (by simp)).borrowed) hCap ?_ ?_
  · -- An existing level: `setLevel` consumes both arrays and adds to the size.
    intro heap1 store1 state hL hB hFound
    set K := findTuple (prices, price) with hK
    have hS1 := (hL.tempsOwned (ps, sizes) (by simp)).borrowed
    have hRead1 : (state.update 9 (.i64 K)).get 1 = some (.i64 ps) := by
      rw [State.get_update_ne (by decide), hB.get1]
    have hLength : (state.update 9 (.i64 K)).params.length +
        (state.update 9 (.i64 K)).locals.length = 10 := by
      simp only [State.update_params_length, State.update_locals_length, hB.params, hB.locals]
    refine (Live.callPair setLevel_implements rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 3) rfl) rfl
      (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
      (vals := [.i64 pp, .i64 ps, .i64 K, .i64 (sizes[K.toNat]! + size)])
      (x := (⟨prices⟩, ⟨sizes⟩, K, sizes[K.toNat]! + size)) (afterArgs := state.update 9 (.i64 K))
      (by simp [Expr.evalResults, Expr.eval, hB.get0, hB.get1, hB.get3, hB.get5, U64Op.apply,
        State.set?_eq_update _ (show 9 < state.params.length + state.locals.length by
          rw [hB.params, hB.locals]; decide), Expr.readValue_at hS1.values hRead1])
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hL.tempsOwned (pp, prices) (by simp)⟩, [.i64 ps], _,
        rfl, ⟨ps, rfl, hL.tempsOwned (ps, sizes) (by simp)⟩, rfl⟩ rfl
      (fun q hq => by simp [Represent.reads] at hq)
      (by omega) (by omega)).mono (fun _ _ h => h) ?_
    rintro s st ⟨heap2, p1, p2, hL2, rfl⟩
    have hResult : addBidTuple (⟨prices⟩, ⟨sizes⟩, price, size) =
        setTuple (⟨prices⟩, ⟨sizes⟩, K, sizes[K.toNat]! + size) := by
      unfold addBidTuple LeanExe.Examples.Clob.addBid; exact ite_eq_left hFound
    rw [hResult]
    exact movesPost_of_live hL2 (State.get_update_same (by rw [hLenU, hLength]; decide))
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
  · -- A new level: `insertLevel` copies both arrays, and both are released.
    intro heap1 store1 state hL hB hFound
    set K := findTuple (prices, price) with hK
    have hP1 := (hL.tempsOwned (pp, prices) (by simp)).borrowed
    have hS1 := (hL.tempsOwned (ps, sizes) (by simp)).borrowed
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hB.params, hB.locals]
    refine Stmt.seq_spec (Live.callPair insertLevel_implements rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 2) rfl) rfl
      (consumed := []) (rest := [(pp, prices), (ps, sizes)]) hL hCap
      (vals := [.i64 pp, .i64 ps, .i64 K, .i64 price, .i64 size])
      (x := (prices, sizes, K, price, size)) (afterArgs := state)
      (by simp [Expr.evalResults, Expr.eval, hB.get0, hB.get1, hB.get2, hB.get3, hB.get5])
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hP1⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hS1⟩, rfl⟩ rfl
      (fun _ _ _ ht => nomatch ht) (by omega) (by omega)) ?_
    apply Triple.of_forall
    rintro s st ⟨heap2, p1, p2, hL2, rfl⟩
    have hResult : addBidTuple (⟨prices⟩, ⟨sizes⟩, price, size) =
        insertTuple (prices, sizes, K, price, size) := by
      unfold addBidTuple LeanExe.Examples.Clob.addBid; exact ite_eq_right hFound
    have hGet0 : ((state.update 7 (.i64 p2)).update 6 (.i64 p1)).get 0 = some (.i64 pp) := by
      rw [State.get_update_ne (by decide), State.get_update_ne (by decide), hB.get0]
    have hGet1 : ((state.update 7 (.i64 p2)).update 6 (.i64 p1)).get 1 = some (.i64 ps) := by
      rw [State.get_update_ne (by decide), State.get_update_ne (by decide), hB.get1]
    refine Stmt.seq_spec (Live.releaseAt (pre := [_, _, _]) (post := []) hL2 hImports hRelease
      hGet1) ?_
    apply Triple.of_forall
    rintro s' st' ⟨hL3, rfl⟩
    refine (Live.releaseAt (pre := [_, _]) (post := []) hL3 hImports hRelease hGet0).mono
      (fun _ _ h => h) ?_
    rintro s'' st'' ⟨hL4, rfl⟩
    rw [hResult]
    exact movesPost_of_live hL4 (State.get_update_same (by rw [hLenU, hLength]; decide))
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))

/-- `cancelBid` with its four arguments as one tuple: the call consumes both arrays. -/
def cancelTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.cancelBid x.1.val x.2.1.val x.2.2.1 x.2.2.2

theorem cancelBid_implements : Implements clob.module 10 cancelTuple := by
  refine Func.implements_moves clob.funcs 8 clob.cancelBid.ir "cancelBid" rfl cancelTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ ⟨hSepPair, -⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  change ([pp, ps].map (block initial)).Pairwise regionsDisjoint at hSepPair
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hImports : clob.module.imports = [] := rfl
  have hRelease : clob.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  show Triple _ (bidBody
    (.ite (.leU (.read 1 (.get 5)) (.get 3))
      (.seq (.call 9 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩] [6, 7])
        (.seq (.release 1) (.release 0)))
      (.call 5 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩,
        ⟨.u64, .bin .sub (.read 1 (.get 5)) (.get 3)⟩] [6, 7]))
    (.seq (.assign 6 (.get 0)) (.assign 7 (.get 1)))) (6 + 3)
    (fun store state => store = initial ∧ state = bidStart pp ps price size 6)
    (MovesPost heap initial [pp, ps] 9 6 7 (cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size)))
  have hMemP : (pp, prices) ∈ [(pp, prices), (ps, sizes)] := List.mem_cons_self ..
  have hMemS : (ps, sizes) ∈ [(pp, prices), (ps, sizes)] :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hStart := Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [hPrices, hSizes])
    (List.pairwise_pair.mpr ((List.pairwise_cons.mp hSepPair).1 _ (List.mem_singleton_self _)))
  refine bid_spec (by decide) hStart (fun _ _ hL => (hL.tempsOwned _ hMemP).borrowed) hCap ?_ ?_
  · -- An existing level: removed, or reduced by `size`.
    intro heap1 store1 state hL hB hFound
    set K := findTuple (prices, price) with hK
    have hS1 := (hL.tempsOwned _ hMemS).borrowed
    have hP1 := (hL.tempsOwned _ hMemP).borrowed
    let read := state.update 9 (.i64 K)
    have hRead : 9 < state.params.length + state.locals.length := by
      rw [hB.params, hB.locals]; decide
    have hRead1 : read.get 1 = some (.i64 ps) := by
      rw [State.get_update_ne (by decide), hB.get1]
    have hReadLen : read.params.length + read.locals.length = 10 := by
      rw [hLenU, hB.params, hB.locals]
    have hReadGet : ∀ j, j < 9 → read.get j = state.get j := fun j hj =>
      State.get_update_ne (by omega)
    refine (Stmt.ite_spec
      (PThen := fun s st => s = store1 ∧ st = read ∧ sizes[K.toNat]! ≤ size)
      (PElse := fun s st => s = store1 ∧ st = read ∧ ¬sizes[K.toNat]! ≤ size) ?_ ?_).mono
        ?_ fun _ _ h => h
    rotate_left 2
    · rintro s st ⟨rfl, hst⟩
      subst st
      refine ⟨decide (sizes[K.toNat]! ≤ size), read, ?_,
        by by_cases h : sizes[K.toNat]! ≤ size <;> simp [h]⟩
      simp [Expr.eval, hB.get3, hB.get5, State.set?_eq_update _ hRead, read,
        Expr.readValue_at hS1.values hRead1, hReadGet 3 (by decide)]
    all_goals
      apply Triple.of_forall
      rintro s st ⟨rfl, rfl, hLe⟩
    · -- `removeLevel` copies both arrays, which are then released.
      refine Stmt.seq_spec (Live.callPair removeLevel_implements rfl
        (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 7) rfl) rfl
        (consumed := []) (rest := [(pp, prices), (ps, sizes)]) hL hCap
        (vals := [.i64 pp, .i64 ps, .i64 K]) (x := (prices, sizes, K)) (afterArgs := read)
        (by simp [Expr.evalResults, Expr.eval, hReadGet 0 (by decide), hReadGet 1 (by decide),
          hReadGet 5 (by decide), hB.get0, hB.get1, hB.get5])
        ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hP1⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hS1⟩, rfl⟩ rfl
        (fun _ _ _ ht => nomatch ht) (by omega) (by omega)) ?_
      apply Triple.of_forall
      rintro s2 st2 ⟨heap2, p1, p2, hL2, rfl⟩
      have hGet : ∀ j, j < 6 → ((read.update 7 (.i64 p2)).update 6 (.i64 p1)).get j =
          state.get j := fun j hj => by
        rw [State.get_update_ne (by omega), State.get_update_ne (by omega), hReadGet j (by omega)]
      refine Stmt.seq_spec (Live.releaseAt (pre := [_, _, _]) (post := []) hL2 hImports hRelease
        ((hGet 1 (by decide)).trans hB.get1)) ?_
      apply Triple.of_forall
      rintro s3 st3 ⟨hL3, rfl⟩
      refine (Live.releaseAt (pre := [_, _]) (post := []) hL3 hImports hRelease
        ((hGet 0 (by decide)).trans hB.get0)).mono (fun _ _ h => h) ?_
      rintro s4 st4 ⟨hL4, rfl⟩
      have hResult : cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size) = removeTuple (prices, sizes, K) := by
        unfold cancelTuple LeanExe.Examples.Clob.cancelBid
        exact (ite_eq_left hFound).trans (ite_eq_left hLe)
      rw [hResult]
      exact movesPost_of_live hL4 (State.get_update_same (by rw [hLenU, hReadLen]; decide))
        (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
    · -- `setLevel` consumes both arrays and reduces the size.
      let read2 := read.update 9 (.i64 K)
      have hRead1' : read2.get 1 = some (.i64 ps) := by
        rw [State.get_update_ne (by decide), hRead1]
      have hRead2Len : read2.params.length + read2.locals.length = 10 := by
        rw [hLenU, hReadLen]
      refine (Live.callPair setLevel_implements rfl
        (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 3) rfl) rfl
        (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
        (vals := [.i64 pp, .i64 ps, .i64 K, .i64 (sizes[K.toNat]! - size)])
        (x := (⟨prices⟩, ⟨sizes⟩, K, sizes[K.toNat]! - size)) (afterArgs := read2)
        (by simp [Expr.evalResults, Expr.eval, hReadGet 0 (by decide), hReadGet 1 (by decide),
          hReadGet 3 (by decide), hReadGet 5 (by decide), hB.get0, hB.get1, hB.get3, hB.get5,
          U64Op.apply, State.set?_eq_update _ (show 9 < read.params.length + read.locals.length by
            omega), Expr.readValue_at hS1.values hRead1', read2])
        ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hL.tempsOwned _ hMemP⟩, [.i64 ps], _, rfl,
          ⟨ps, rfl, hL.tempsOwned _ hMemS⟩, rfl⟩ rfl
        (fun q hq => by simp [Represent.reads] at hq) (by omega) (by omega)).mono
          (fun _ _ h => h) ?_
      rintro s2 st2 ⟨heap2, p1, p2, hL2, rfl⟩
      have hResult : cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size) =
          setTuple (⟨prices⟩, ⟨sizes⟩, K, sizes[K.toNat]! - size) := by
        unfold cancelTuple LeanExe.Examples.Clob.cancelBid
        exact (ite_eq_left hFound).trans (ite_eq_right hLe)
      rw [hResult]
      exact movesPost_of_live hL2 (State.get_update_same (by rw [hLenU, hRead2Len]; decide))
        (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
  · -- No level at the price: both arrays are returned.
    intro heap1 store1 state hL hB hFound
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hB.params, hB.locals]
    let final := (state.update 6 (.i64 pp)).update 7 (.i64 ps)
    refine (Stmt.run_spec (final := final) ?_).mono (fun _ _ h => h) ?_
    · simp [Stmt.run, Expr.eval, hB.get0, hB.get1, State.set?_eq_update, hB.params, hB.locals,
        final]
    rintro s st ⟨rfl, rfl⟩
    rw [show cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size) = (prices, sizes) by
      unfold cancelTuple LeanExe.Examples.Clob.cancelBid; exact ite_eq_right hFound]
    exact movesPost_of_live hL
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
      (State.get_update_same (by rw [hLenU]; omega))

/-- `applyCommand` with its five arguments as one tuple: the call consumes both arrays. -/
def applyTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.applyCommand x.1.val x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem applyCommand_implements : Implements clob.module 11 applyTuple := by
  refine Func.implements_moves clob.funcs 9 clob.applyCommand.ir "applyCommand" rfl applyTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, kind, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ ⟨hSepPair, -⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  change ([pp, ps].map (block initial)).Pairwise regionsDisjoint at hSepPair
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hImports : clob.module.imports = [] := rfl
  have hRelease : clob.module.funcs[1]? = some (releaseFunction 1) := rfl
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 kind, .i64 price, .i64 size]
      locals := [.i64 0, .i64 0] }
  have hGet : start.get 0 = some (.i64 pp) ∧ start.get 1 = some (.i64 ps) ∧
      start.get 2 = some (.i64 kind) ∧ start.get 3 = some (.i64 price) ∧
      start.get 4 = some (.i64 size) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hLength : start.params.length + start.locals.length = 7 := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  show Triple _ (.ite (.eq (.get 2) (.const 0))
      (.call 6 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5, 6])
      (.ite (.eq (.get 2) (.const 1))
        (.call 10 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] [5, 6])
        (.seq (.assign 5 (.get 0)) (.assign 6 (.get 1))))) 7
    (fun store state => store = initial ∧ state = start)
    (MovesPost heap initial [pp, ps] 7 5 6
      (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)))
  have hMemP : (pp, prices) ∈ [(pp, prices), (ps, sizes)] := List.mem_cons_self ..
  have hMemS : (ps, sizes) ∈ [(pp, prices), (ps, sizes)] :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hPS : regionsDisjoint (block initial pp) (block initial ps) :=
    (List.pairwise_cons.mp hSepPair).1 _ (List.mem_singleton_self _)
  have hL := Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [hPrices, hSizes])
    (List.pairwise_pair.mpr hPS)
  have hArgs : Expr.evalResults initial.mem 7
      [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩] start =
      some ([.i64 pp, .i64 ps, .i64 price, .i64 size], start) := by
    simp [Expr.evalResults, Expr.eval, hGet.1, hGet.2.1, hGet.2.2.2.1, hGet.2.2.2.2]
  have hFinal : ∀ (heap1 : Heap) (s : Store Unit) (p1 p2 : UInt64)
      (result : Array UInt64 × Array UInt64),
      Live heap initial ([(pp, prices), (ps, sizes)].map (·.1)) heap1 s
        [(p1, result.1), (p2, result.2)] →
      MovesPost heap initial [pp, ps] 7 5 6 result s
        ((start.update 6 (.i64 p2)).update 5 (.i64 p1)) := fun heap1 s p1 p2 result hL' =>
    movesPost_of_live hL' (State.get_update_same (by rw [hLenU, hLength]; decide))
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
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
  · -- Kind 0: `addBid` consumes both arrays.
    refine (Live.callPair addBid_implements rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 4) rfl) rfl
      (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
      (vals := [.i64 pp, .i64 ps, .i64 price, .i64 size]) (x := (⟨prices⟩, ⟨sizes⟩, price, size))
      hArgs
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ rfl
      (fun _ hq => absurd hq List.not_mem_nil)
      (by rw [hLength]; decide) (by rw [hLength]; decide)).mono (fun _ _ h => h) ?_
    rintro s2 st2 ⟨heap2, p1, p2, hL2, rfl⟩
    rw [show applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size) =
        addBidTuple (⟨prices⟩, ⟨sizes⟩, price, size) by
      unfold applyTuple LeanExe.Examples.Clob.applyCommand; exact ite_eq_left hKind]
    exact hFinal _ _ p1 p2 _ hL2
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
  · -- Kind 1: `cancelBid` consumes both arrays.
    refine (Live.callPair cancelBid_implements rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 8) rfl) rfl
      (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
      (vals := [.i64 pp, .i64 ps, .i64 price, .i64 size]) (x := (⟨prices⟩, ⟨sizes⟩, price, size))
      hArgs
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ rfl
      (fun _ hq => absurd hq List.not_mem_nil)
      (by rw [hLength]; decide) (by rw [hLength]; decide)).mono (fun _ _ h => h) ?_
    rintro s2 st2 ⟨heap2, p1, p2, hL2, rfl⟩
    rw [show applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size) =
        cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size) by
      unfold applyTuple LeanExe.Examples.Clob.applyCommand
      exact (ite_eq_right hKind).trans (ite_eq_left hKind1)]
    exact hFinal _ _ p1 p2 _ hL2
  · -- Any other kind: both arrays are returned.
    refine (Stmt.run_spec (final := (start.update 5 (.i64 pp)).update 6 (.i64 ps)) ?_).mono
      (fun _ _ h => h) ?_
    · simp [Stmt.run, Expr.eval, hGet.1, hGet.2.1, State.set?_eq_update, start]
    rintro s st ⟨rfl, rfl⟩
    rw [show applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size) = (prices, sizes) by
      unfold applyTuple LeanExe.Examples.Clob.applyCommand
      exact (ite_eq_right hKind).trans (ite_eq_right hKind1)]
    exact movesPost_of_live hL
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
      (State.get_update_same (by rw [hLenU, hLength]; decide))

/-- `runCommands` with its three arguments as one tuple: the call consumes the book. -/
def runTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × Array UInt64) :
    Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.runCommands x.1.val x.2.1.val x.2.2

/-- The arguments of the call in `runCommands`'s loop: the book, and the command at the
loop index. -/
def runArgs : List ((type : ScalarType) × Expr type) :=
  [⟨.u64, .get 4⟩, ⟨.u64, .get 5⟩, ⟨.u64, .read 2 (.bin .mul (.const 3) (.get 7))⟩,
    ⟨.u64, .read 2 (.bin .add (.bin .mul (.const 3) (.get 7)) (.const 1))⟩,
    ⟨.u64, .read 2 (.bin .add (.bin .mul (.const 3) (.get 7)) (.const 2))⟩]

/-- Command `l` of `commands`: its kind, price, and size. -/
def command (commands : Array UInt64) (l : UInt64) : UInt64 × UInt64 × UInt64 :=
  (commands[(3 * l).toNat]!, commands[(3 * l + 1).toNat]!, commands[(3 * l + 2).toNat]!)

/-- A fold of `step` over the whole commands of `commands`. -/
def foldCommands (step : UInt64 × UInt64 × UInt64 → σ → σ) (commands : Array UInt64)
    (x : σ) : σ :=
  Nat.fold (commands.size / 3) (fun i _ x => step (command commands (UInt64.ofNat i)) x) x

/-- The step of `runCommands` as `applyCommand`'s input: the book, and command `l`. -/
def runStep (commands : Array UInt64) (l : UInt64) (book : Array UInt64 × Array UInt64) :
    Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64 × UInt64 :=
  (⟨book.1⟩, ⟨book.2⟩, command commands l)

theorem runTuple_eq (prices sizes commands : Array UInt64) :
    runTuple (⟨prices⟩, ⟨sizes⟩, commands) =
      LeanExe.loop (UInt64.ofNat commands.size / 3) (prices, sizes)
        fun l x => applyTuple (runStep commands l x) := rfl

theorem runCommands_eq_fold (prices sizes cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    LeanExe.Examples.Clob.runCommands prices sizes cs =
      foldCommands (fun c book => applyTuple (⟨book.1⟩, ⟨book.2⟩, c)) cs (prices, sizes) := by
  have hn : (UInt64.ofNat cs.size / 3).toNat = cs.size / 3 := by
    rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    rfl
  show runTuple (⟨prices⟩, ⟨sizes⟩, cs) = _
  rw [runTuple_eq]
  exact Nat.fold_congr hn _ _

theorem command_append_left {c1 c2 : Array UInt64} {i : Nat} (hi : i < c1.size / 3)
    (hs : (c1 ++ c2).size < 2 ^ 62) :
    command (c1 ++ c2) (UInt64.ofNat i) = command c1 (UInt64.ofNat i) := by
  rw [Array.size_append] at hs
  have hj : ∀ j : Nat, j < 3 → (3 * UInt64.ofNat i + UInt64.ofNat j).toNat = 3 * i + j := by
    intro j hj
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hRead : ∀ j : Nat, j < 3 →
      (c1 ++ c2)[3 * i + j]! = c1[3 * i + j]! := fun j hj' => by
    rw [getElem!_pos (c1 ++ c2) _ (by simp; omega), getElem!_pos c1 _ (by omega),
      Array.getElem_append_left (by omega)]
  have h0 := hj 0 (by decide)
  have h1 := hj 1 (by decide)
  have h2 := hj 2 (by decide)
  simp only [UInt64.reduceOfNat, add_zero] at h0
  simp only [command] at *
  rw [show (3 * UInt64.ofNat i).toNat = 3 * i + 0 by simpa using h0,
    show (3 * UInt64.ofNat i + 1).toNat = 3 * i + 1 from h1,
    show (3 * UInt64.ofNat i + 2).toNat = 3 * i + 2 from h2,
    hRead 0 (by decide), hRead 1 (by decide), hRead 2 (by decide)]

theorem command_append_right {c1 c2 : Array UInt64} {i : Nat} (h3 : c1.size % 3 = 0)
    (hi : i < c2.size / 3) (hs : (c1 ++ c2).size < 2 ^ 62) :
    command (c1 ++ c2) (UInt64.ofNat (c1.size / 3 + i)) = command c2 (UInt64.ofNat i) := by
  rw [Array.size_append] at hs
  have hj : ∀ (a j : Nat), a < 2 ^ 61 → j < 3 →
      (3 * UInt64.ofNat a + UInt64.ofNat j).toNat = 3 * a + j := by
    intro a j ha hj
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hRead : ∀ j : Nat, j < 3 →
      (c1 ++ c2)[3 * (c1.size / 3 + i) + j]! = c2[3 * i + j]! := fun j hj' => by
    rw [getElem!_pos (c1 ++ c2) _ (by simp; omega), getElem!_pos c2 _ (by omega),
      Array.getElem_append_right (by omega)]
    congr 1
    omega
  have h0 := hj (c1.size / 3 + i) 0 (by omega) (by decide)
  have h1 := hj (c1.size / 3 + i) 1 (by omega) (by decide)
  have h2 := hj (c1.size / 3 + i) 2 (by omega) (by decide)
  have g0 := hj i 0 (by omega) (by decide)
  have g1 := hj i 1 (by omega) (by decide)
  have g2 := hj i 2 (by omega) (by decide)
  simp only [UInt64.reduceOfNat, add_zero] at h0 g0
  simp only [command] at *
  rw [show (3 * UInt64.ofNat (c1.size / 3 + i)).toNat = 3 * (c1.size / 3 + i) + 0 by
      simpa using h0,
    show (3 * UInt64.ofNat (c1.size / 3 + i) + 1).toNat = 3 * (c1.size / 3 + i) + 1 from h1,
    show (3 * UInt64.ofNat (c1.size / 3 + i) + 2).toNat = 3 * (c1.size / 3 + i) + 2 from h2,
    show (3 * UInt64.ofNat i).toNat = 3 * i + 0 by simpa using g0,
    show (3 * UInt64.ofNat i + 1).toNat = 3 * i + 1 from g1,
    show (3 * UInt64.ofNat i + 2).toNat = 3 * i + 2 from g2,
    hRead 0 (by decide), hRead 1 (by decide), hRead 2 (by decide)]

/-- A fold over two chunks of commands, the first of whole commands, is the fold over both. -/
theorem foldCommands_append (step : UInt64 × UInt64 × UInt64 → σ → σ) (x : σ)
    {c1 c2 : Array UInt64} (h3 : c1.size % 3 = 0) (hs : (c1 ++ c2).size < 2 ^ 62) :
    foldCommands step c2 (foldCommands step c1 x) = foldCommands step (c1 ++ c2) x := by
  unfold foldCommands
  rw [Nat.fold_congr (show (c1 ++ c2).size / 3 = c1.size / 3 + c2.size / 3 by
    rw [Array.size_append]; omega), Nat.fold_add]
  congr 1
  · funext i hi y
    rw [command_append_right h3 hi hs]
  · exact Nat.fold_congr rfl _ _ |>.trans (by
      congr 1
      funext i hi y
      rw [command_append_left hi hs])

/-- A map that commutes with each step commutes with the fold. -/
theorem foldCommands_map {step : UInt64 × UInt64 × UInt64 → σ → σ}
    {step' : UInt64 × UInt64 × UInt64 → τ → τ} (π : σ → τ)
    (h : ∀ c x, π (step c x) = step' c (π x)) (cs : Array UInt64) (x : σ) :
    π (foldCommands step cs x) = foldCommands step' cs (π x) := by
  unfold foldCommands
  generalize cs.size / 3 = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.fold_succ, h, ih]

/-- Running the commands in two chunks, the first of whole commands, gives the book of one
run over both chunks.  This is what lets a host pass the commands in chunks of any size. -/
theorem runCommands_append (prices sizes c1 c2 : Array UInt64) (h3 : c1.size % 3 = 0)
    (hs : (c1 ++ c2).size < 2 ^ 62) :
    LeanExe.Examples.Clob.runCommands
        (LeanExe.Examples.Clob.runCommands prices sizes c1).1
        (LeanExe.Examples.Clob.runCommands prices sizes c1).2 c2 =
      LeanExe.Examples.Clob.runCommands prices sizes (c1 ++ c2) := by
  have hs' := hs
  rw [Array.size_append] at hs'
  rw [runCommands_eq_fold _ _ c2 (by omega), runCommands_eq_fold _ _ (c1 ++ c2) (by omega),
    runCommands_eq_fold _ _ c1 (by omega), Prod.mk.eta]
  exact foldCommands_append _ _ h3 hs

theorem runCommands_implements : Implements clob.module 12 runTuple := by
  refine Func.implements_moves clob.funcs 10 clob.runCommands.ir "runCommands" rfl runTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, commands⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, ⟨pc, rfl, hCmds⟩⟩
    ⟨hSepPair, hSep⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  change heap.Borrowed initial pc commands at hCmds
  change ([pp, ps].map (block initial)).Pairwise regionsDisjoint at hSepPair
  have hAC : Apart initial [pp, ps] (pc.toNat, 8 * (commands.size + 1)) :=
    hSep _ (List.mem_singleton_self _)
  have hPS : regionsDisjoint (block initial pp) (block initial ps) :=
    (List.pairwise_cons.mp hSepPair).1 _ (List.mem_singleton_self _)
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 pc], locals := List.replicate 7 (.i64 0) }
  have hStartLen : start.params.length + start.locals.length = 10 := rfl
  show Triple _ (.seq (.arraySize 3 2)
      (Stmt.tupleLoop [4, 5] 6 7 [0, 1] 11 (.bin .divU (.get 3) (.const 3)) runArgs)) 8
    (fun store state => store = initial ∧ state = start)
    (MovesPost heap initial [pp, ps] 8 4 5 (runTuple (⟨prices⟩, ⟨sizes⟩, commands)))
  have hL := Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      exacts [hPrices, hSizes])
    (List.pairwise_pair.mpr hPS)
  have hCv := hCmds.values
  let st0 := start.update 3 (.i64 (UInt64.ofNat commands.size))
  have hSt0Len : st0.params.length + st0.locals.length = 10 := by rw [hLenU, hStartLen]
  refine Stmt.seq_spec (Stmt.arraySize_spec (before := start) hCv rfl (by rw [hStartLen]; decide))
    ?_
  apply Triple.of_forall
  rintro s st ⟨rfl, hSet⟩
  rw [State.set?_eq_update _ (show 3 < start.params.length + start.locals.length by
    rw [hStartLen]; decide), Option.some.injEq] at hSet
  subst hSet
  have hCount : ∀ (mem : Mem) (st : State), State.Frame 8 [4, 5] st0 st →
      ∃ after, (Expr.bin .divU (.get 3) (.const 3)).eval mem 8 st =
        some (UInt64.ofNat commands.size / 3, after) := fun mem st hF => by
    have g3 : st.get 3 = some (.i64 (UInt64.ofNat commands.size)) :=
      (hF.get 3 (by decide) (by decide)).trans (State.get_update_same (by rw [hStartLen]; decide))
    have hLen : 9 < st.params.length + st.locals.length := by
      rw [hF.params, hF.locals]; omega
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := st) (index := 8)
      (.i64 (UInt64.ofNat commands.size)) (by omega)
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 9) (.i64 3) (by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1
      rw [hLenU]; omega)
    exact ⟨m2, by simp [Expr.eval, g3, hm1, hm2, U64Op.apply]⟩
  refine (Live.tupleLoop applyCommand_implements (f := clob.applyCommand.ir.function (2 + 9)) rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 9) rfl) rfl
    (states := [4, 5]) (limit := 6) (index := 7) (srcs := [0, 1])
    (ts := [(pp, prices), (ps, sizes)]) (rest := []) (x0 := (prices, sizes))
    (by decide) (by decide) (by decide) rfl (by rw [hSt0Len]; decide) rfl hL hCap
    (.cons rfl (.cons rfl .nil)) hCount (runStep commands)
    fun k us heap' store' st hk hF hIdx hHolds hUs hL' => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨⟨q1, _⟩, us, rfl, rfl, hUs1⟩ := List.map_eq_cons_iff.mp hUs
    obtain ⟨⟨q2, _⟩, us, rfl, rfl, hUs2⟩ := List.map_eq_cons_iff.mp hUs1
    obtain rfl := List.map_eq_nil_iff.mp hUs2
    simp only [List.append_nil] at hL'
    have g4 : st.get 4 = some (.i64 q1) := (List.forall₂_cons.mp hHolds).1
    have g5 : st.get 5 = some (.i64 q2) :=
      (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds).2).1
    have hC' := (hL'.borrowed pc commands hCmds hAC).values
    have hLen : st.params.length + st.locals.length = 10 := by
      rw [hF.params, hF.locals]; exact hSt0Len
    have g2 : st.get 2 = some (.i64 pc) := (hF.get 2 (by decide) (by decide)).trans rfl
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := st) (index := 8) (.i64 (3 * UInt64.ofNat k)) (by omega)
    have hm1Len : m1.params.length + m1.locals.length = 10 := by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1; rw [hLenU, hLen]
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 8) (.i64 (3 * UInt64.ofNat k + 1)) (by omega)
    have hm2Len : m2.params.length + m2.locals.length = 10 := by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm2; subst hm2; rw [hLenU, hm1Len]
    obtain ⟨m3, hm3⟩ := State.exists_set? (state := m2) (index := 8) (.i64 (3 * UInt64.ofNat k + 2)) (by omega)
    have k1 : ∀ j, j ≠ 8 → m1.get j = st.get j := fun j hj => State.get_set?_ne hj hm1
    have k2 : ∀ j, j ≠ 8 → m2.get j = st.get j := fun j hj =>
      (State.get_set?_ne hj hm2).trans (k1 j hj)
    have k3 : ∀ j, j ≠ 8 → m3.get j = st.get j := fun j hj =>
      (State.get_set?_ne hj hm3).trans (k2 j hj)
    refine ⟨[.i64 q1, .i64 q2, .i64 commands[(3 * UInt64.ofNat k).toNat]!, .i64 commands[(3 * UInt64.ofNat k + 1).toNat]!,
      .i64 commands[(3 * UInt64.ofNat k + 2).toNat]!], m3, ?_,
      ⟨[.i64 q1], _, rfl, ⟨q1, rfl, hL'.tempsOwned _ (List.mem_cons_self ..)⟩, [.i64 q2], _, rfl,
        ⟨q2, rfl, hL'.tempsOwned _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩, rfl⟩,
      rfl, fun _ hq => absurd hq List.not_mem_nil⟩
    refine Expr.evalResults_get g4 <| Expr.evalResults_get g5 <|
      Expr.evalResults_cons (Expr.read_spec hC' (by simp [Expr.eval, hIdx, U64Op.apply]) hm1
        (by rw [k1 2 (by decide), g2])) <|
      Expr.evalResults_cons (Expr.read_spec hC'
        (by simp [Expr.eval, k1 7 (by decide), hIdx, U64Op.apply]) hm2
        (by rw [k2 2 (by decide), g2])) <|
      Expr.evalResults_cons (Expr.read_spec hC'
        (by simp [Expr.eval, k2 7 (by decide), hIdx, U64Op.apply]) hm3
        (by rw [k3 2 (by decide), g2])) Expr.evalResults_nil
  · rintro s' st' ⟨heap', us, hUs, hL', -, hHolds⟩
    obtain ⟨⟨q1, _⟩, us, rfl, rfl, hUs1⟩ := List.map_eq_cons_iff.mp hUs
    obtain ⟨⟨q2, _⟩, us, rfl, rfl, hUs2⟩ := List.map_eq_cons_iff.mp hUs1
    obtain rfl := List.map_eq_nil_iff.mp hUs2
    simp only [List.append_nil] at hL'
    rw [runTuple_eq]
    exact movesPost_of_live hL' (List.forall₂_cons.mp hHolds).1
      (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds).2).1

/-- `stepCommand` with its six arguments as one tuple: the call consumes the book and the
output array. -/
def stepTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64) : Array UInt64 × Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.stepCommand x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1
    x.2.2.2.2.2

theorem stepTuple_eq (prices sizes out : Array UInt64) (kind price size : UInt64) :
    stepTuple (⟨prices⟩, ⟨sizes⟩, ⟨out⟩, kind, price, size) =
      ((applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).1,
        (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).2,
        out ++ #[(applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).1[(0 : UInt64).toNat]!,
          (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).2[(0 : UInt64).toNat]!]) := rfl

theorem stepCommand_implements : Implements clob.module 13 stepTuple := by
  refine Func.implements_moves clob.funcs 11 clob.stepCommand.ir "stepCommand" rfl stepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, ⟨out⟩, kind, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, _, _, rfl, ⟨po, rfl, hOut⟩,
      rfl⟩ ⟨hSepAll, -⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  change heap.Owned initial po out at hOut
  change ([pp, ps, po].map (block initial)).Pairwise regionsDisjoint at hSepAll
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hImports : clob.module.imports = [] := rfl
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : clob.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 po, .i64 kind, .i64 price, .i64 size]
      locals := List.replicate 15 (.i64 0) }
  have hStartLen : start.params.length + start.locals.length = 21 := rfl
  show Triple _ (.seq (.call 11 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩,
        ⟨.u64, .get 5⟩] [6, 7]) <|
      .seq (.assign 8 (.read 6 (.const 0))) <| .seq (.assign 9 (.read 7 (.const 0))) <|
      .seq (Stmt.arrayLiteral 10 [.get 8, .get 9]) <|
      .seq (Stmt.append 11 12 13 14 15 16 2 10) <|
      .seq (.assign 17 (.get 6)) <| .seq (.assign 18 (.get 7)) <|
      .seq (.assign 19 (.get 11)) (.release 10)) 20
    (fun store state => store = initial ∧ state = start) _
  have hL := Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes), (po, out)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      exacts [hPrices, hSizes, hOut])
    (by
      have h := List.pairwise_map.mp hSepAll
      exact (List.pairwise_map (f := Prod.fst) (l := [(pp, prices), (ps, sizes), (po, out)])).mp h)
  -- `applyCommand` consumes the book.
  refine Stmt.seq_spec (Live.callPair applyCommand_implements rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 9) rfl) rfl
    (consumed := [(pp, prices), (ps, sizes)]) (rest := [(po, out)]) hL hCap
    (x := (⟨prices⟩, ⟨sizes⟩, kind, price, size)) (before := start) rfl
    ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hPrices⟩, [.i64 ps], _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
    rfl (fun _ hq => absurd hq List.not_mem_nil) (by rw [hStartLen]; decide)
    (by rw [hStartLen]; decide)) ?_
  apply Triple.of_forall
  rintro s1 st1 ⟨heap1, p1, p2, hL1, hst1⟩
  generalize hA : applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size) = A at hL1
  obtain ⟨P, S⟩ := A
  have hLen1 : st1.params.length + st1.locals.length = 21 := by rw [hst1, hLenU, hLenU, hStartLen]
  have g1 : ∀ j, j ≠ 6 → j ≠ 7 → st1.get j = start.get j := fun j h6 h7 => by
    rw [hst1, State.get_update_ne h6, State.get_update_ne h7]
  have g16 : st1.get 6 = some (.i64 p1) := by
    rw [hst1]; exact State.get_update_same (by rw [hLenU, hStartLen]; decide)
  have g17 : st1.get 7 = some (.i64 p2) := by
    rw [hst1, State.get_update_ne (by decide)]; exact State.get_update_same (by rw [hStartLen]; decide)
  have hP := hL1.tempsOwned (p1, P) List.mem_cons_self
  have hS := hL1.tempsOwned (p2, S) (List.mem_cons_of_mem _ List.mem_cons_self)
  -- The best bid: the first price and size.
  obtain ⟨st2, hst2⟩ : ∃ st2, st2 = (st1.update 20 (.i64 0)).update 8 (.i64 P[(0 : UInt64).toNat]!) :=
    ⟨_, rfl⟩
  have hLen2 : st2.params.length + st2.locals.length = 21 := by rw [hst2, hLenU, hLenU, hLen1]
  refine Stmt.seq_spec (Stmt.run_spec (final := st2) ?_) ?_
  · have hRead := Expr.read_spec (scratch := 20) (array := 6) (position := .const 0) (state := st1)
      hP.values rfl (State.set?_eq_update _ (by rw [hLen1]; decide))
      (by rw [State.get_update_ne (by decide)]; exact g16)
    rw [hst2]
    simp only [Stmt.run, hRead, Option.bind_eq_bind, Option.bind_some]
    exact State.set?_eq_update _ (by rw [hLenU, hLen1]; decide)
  obtain ⟨st3, hst3⟩ : ∃ st3, st3 = (st2.update 20 (.i64 0)).update 9 (.i64 S[(0 : UInt64).toNat]!) :=
    ⟨_, rfl⟩
  have hLen3 : st3.params.length + st3.locals.length = 21 := by rw [hst3, hLenU, hLenU, hLen2]
  refine Stmt.seq_spec (Stmt.run_spec (final := st3) ?_) ?_
  · have hRead := Expr.read_spec (scratch := 20) (array := 7) (position := .const 0) (state := st2)
      hS.values rfl (State.set?_eq_update _ (by rw [hLen2]; decide))
      (by rw [State.get_update_ne (by decide), hst2, State.get_update_ne (by decide),
        State.get_update_ne (by decide)]; exact g17)
    rw [hst3]
    simp only [Stmt.run, hRead, Option.bind_eq_bind, Option.bind_some]
    exact State.set?_eq_update _ (by rw [hLenU, hLen2]; decide)
  have g3 : ∀ j, j ≠ 8 → j ≠ 9 → j ≠ 20 → st3.get j = st1.get j := fun j h8 h9 h20 => by
    rw [hst3, State.get_update_ne h9, State.get_update_ne h20, hst2, State.get_update_ne h8,
      State.get_update_ne h20]
  have g36 : st3.get 6 = some (.i64 p1) := by rw [g3 6 (by decide) (by decide) (by decide), g16]
  have g37 : st3.get 7 = some (.i64 p2) := by rw [g3 7 (by decide) (by decide) (by decide), g17]
  have g38 : st3.get 8 = some (.i64 P[(0 : UInt64).toNat]!) := by
    rw [hst3, State.get_update_ne (by decide), State.get_update_ne (by decide), hst2]
    exact State.get_update_same (by rw [hLenU, hLen1]; decide)
  have g39 : st3.get 9 = some (.i64 S[(0 : UInt64).toNat]!) := by
    rw [hst3]; exact State.get_update_same (by rw [hLenU, hLen2]; decide)
  -- The literal of the best bid.
  refine Stmt.seq_spec (Stmt.arrayLiteral_spec (values := [.get 8, .get 9])
    (words := [P[(0 : UInt64).toNat]!, S[(0 : UInt64).toNat]!]) (before := st3) hMemory32 hImports
    hAlloc (by decide) (by rw [hLen3]; decide) hL1.at_ (hL1.cap hCap) (by decide)
    (.cons (fun _ state hF => ⟨state, by simp [Expr.eval, hF.get 8 (by decide) (by decide), g38]⟩)
      (.cons (fun _ state hF => ⟨state, by simp [Expr.eval, hF.get 9 (by decide) (by decide), g39]⟩)
        .nil))) ?_
  apply Triple.of_forall
  rintro s4 st4 ⟨pw, hF4, g4w, hNew⟩
  have hL4 := hL1.push hNew
  -- `out ++ best` consumes the output array.
  have hW := hL4.tempsOwned _ List.mem_cons_self
  have hWO : regionsDisjoint (block s4 pw) (block s4 po) :=
    (List.pairwise_cons.mp hL4.pairwise).1 (po, out) (by simp)
  have g42 : st4.get 2 = some (.i64 po) := by
    rw [hF4.get 2 (by decide) (by decide), g3 2 (by decide) (by decide) (by decide),
      g1 2 (by decide) (by decide)]; rfl
  refine Stmt.seq_spec (Live.append (pre := [(pw, _), (p1, P), (p2, S)]) (t := (po, out))
    (post := []) hMemory32 hImports hAlloc hRelease (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hF4.params, hF4.locals, hLen3]; decide) hL4 hCap
    hW.borrowed (hW.region_apart hWO) g42 g4w) ?_
  apply Triple.of_forall
  rintro s5 st5 ⟨heap5, pd, hL5, hF5, g5d⟩
  have hLen5 : st5.params.length + st5.locals.length = 21 := by
    rw [hF5.params, hF5.locals, hF4.params, hF4.locals, hLen3]
  have g510 : st5.get 10 = some (.i64 pw) := by
    rw [hF5.get 10 (by decide) (by decide), g4w]
  -- The results, then the release of the literal.
  have g56 : st5.get 6 = some (.i64 p1) := by
    rw [hF5.get 6 (by decide) (by decide), hF4.get 6 (by decide) (by decide), g36]
  have g57 : st5.get 7 = some (.i64 p2) := by
    rw [hF5.get 7 (by decide) (by decide), hF4.get 7 (by decide) (by decide), g37]
  refine Stmt.seq_spec (Stmt.run_spec (final := st5.update 17 (.i64 p1))
    (by simp [Stmt.run, Expr.eval, g56, State.set?_eq_update (state := st5) (index := 17) _
      (by rw [hLen5]; decide), ScalarType.value])) ?_
  refine Stmt.seq_spec (Stmt.run_spec (final := (st5.update 17 (.i64 p1)).update 18 (.i64 p2))
    (by simp [Stmt.run, Expr.eval, State.get_update_ne, g57,
      State.set?_eq_update (state := st5.update 17 (.i64 p1)) (index := 18) _
        (by rw [hLenU, hLen5]; decide), ScalarType.value])) ?_
  refine Stmt.seq_spec (Stmt.run_spec
    (final := ((st5.update 17 (.i64 p1)).update 18 (.i64 p2)).update 19 (.i64 pd))
    (by simp [Stmt.run, Expr.eval, State.get_update_ne, g5d,
      State.set?_eq_update (state := (st5.update 17 (.i64 p1)).update 18 (.i64 p2)) (index := 19) _
        (by rw [hLenU, hLenU, hLen5]; decide), ScalarType.value])) ?_
  refine (Live.releaseAt
    (pre := [(pd, out ++ #[P[(0 : UInt64).toNat]!, S[(0 : UInt64).toNat]!])])
    (t := (pw, #[P[(0 : UInt64).toNat]!, S[(0 : UInt64).toNat]!])) (post := [(p1, P), (p2, S)])
    hL5 hImports hRelease (by simp [State.get_update_ne, g510])).mono (fun _ _ h => h) ?_
  rintro s7 st7 ⟨hL7, rfl⟩
  have hHolds : (((st5.update 17 (.i64 p1)).update 18 (.i64 p2)).update 19 (.i64 pd)).Holds
      [17, 18, 19] (pointers [(p1, P), (p2, S),
        (pd, out ++ #[P[(0 : UInt64).toNat]!, S[(0 : UInt64).toNat]!])]) :=
    .cons (by simp [State.get_update_ne, State.get_update_same, hLen5])
      (.cons (by simp [State.get_update_ne, State.get_update_same, hLen5])
        (.cons (by simp [State.get_update_same, hLen5]) .nil))
  rw [stepTuple_eq, hA]
  exact Live.finish_results (y := (P, S, out ++ #[P[(0 : UInt64).toNat]!, S[(0 : UInt64).toNat]!]))
    rfl (hL7.perm List.perm_append_comm) hHolds

/-- `runOut` with its four arguments as one tuple: the call consumes the book and the output
array. -/
def outTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × Moved (Array UInt64) ×
    Array UInt64) : Array UInt64 × Array UInt64 × Array UInt64 :=
  LeanExe.Examples.Clob.runOut x.1.val x.2.1.val x.2.2.1.val x.2.2.2

/-- The arguments of the call in `runOut`'s loop: the book, the output array, and the command
at the loop index. -/
def outArgs : List ((type : ScalarType) × Expr type) :=
  [⟨.u64, .get 5⟩, ⟨.u64, .get 6⟩, ⟨.u64, .get 7⟩,
    ⟨.u64, .read 3 (.bin .mul (.const 3) (.get 9))⟩,
    ⟨.u64, .read 3 (.bin .add (.bin .mul (.const 3) (.get 9)) (.const 1))⟩,
    ⟨.u64, .read 3 (.bin .add (.bin .mul (.const 3) (.get 9)) (.const 2))⟩]

/-- The step of `runOut` as `stepCommand`'s input: the book, the output array, and command
`l`. -/
def outStep (commands : Array UInt64) (l : UInt64)
    (x : Array UInt64 × Array UInt64 × Array UInt64) :
    Moved (Array UInt64) × Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64 ×
      UInt64 :=
  (⟨x.1⟩, ⟨x.2.1⟩, ⟨x.2.2⟩, command commands l)

theorem outTuple_eq (prices sizes out commands : Array UInt64) :
    outTuple (⟨prices⟩, ⟨sizes⟩, ⟨out⟩, commands) =
      LeanExe.loop (UInt64.ofNat commands.size / 3) (prices, sizes, out)
        fun l x => stepTuple (outStep commands l x) := rfl

theorem runOut_implements : Implements clob.module 14 outTuple := by
  refine Func.implements_moves clob.funcs 12 clob.runOut.ir "runOut" rfl outTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩,
      ⟨_, rfl, -⟩⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, ⟨out⟩, commands⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, _, _, rfl, ⟨po, rfl, hOut⟩,
      ⟨pc, rfl, hCmds⟩⟩ ⟨hSepAll, hSep⟩ hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  change heap.Owned initial po out at hOut
  change heap.Borrowed initial pc commands at hCmds
  change ([pp, ps, po].map (block initial)).Pairwise regionsDisjoint at hSepAll
  have hAC : Apart initial [pp, ps, po] (pc.toNat, 8 * (commands.size + 1)) :=
    hSep _ (List.mem_singleton_self _)
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hLenU : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 po, .i64 pc], locals := List.replicate 8 (.i64 0) }
  have hStartLen : start.params.length + start.locals.length = 12 := rfl
  show Triple _ (.seq (.arraySize 4 3)
      (Stmt.tupleLoop [5, 6, 7] 8 9 [0, 1, 2] 13 (.bin .divU (.get 4) (.const 3)) outArgs)) 10
    (fun store state => store = initial ∧ state = start) _
  have hL := Live.start_moved hHeap (temps := [(pp, prices), (ps, sizes), (po, out)])
    (fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      exacts [hPrices, hSizes, hOut])
    (by
      have h := List.pairwise_map.mp hSepAll
      exact (List.pairwise_map (f := Prod.fst) (l := [(pp, prices), (ps, sizes), (po, out)])).mp h)
  have hCv := hCmds.values
  let st0 := start.update 4 (.i64 (UInt64.ofNat commands.size))
  have hSt0Len : st0.params.length + st0.locals.length = 12 := by rw [hLenU, hStartLen]
  refine Stmt.seq_spec (Stmt.arraySize_spec (before := start) hCv rfl (by rw [hStartLen]; decide))
    ?_
  apply Triple.of_forall
  rintro s st ⟨rfl, hSet⟩
  rw [State.set?_eq_update _ (show 4 < start.params.length + start.locals.length by
    rw [hStartLen]; decide), Option.some.injEq] at hSet
  subst hSet
  have hCount : ∀ (mem : Mem) (st : State), State.Frame 10 [5, 6, 7] st0 st →
      ∃ after, (Expr.bin .divU (.get 4) (.const 3)).eval mem 10 st =
        some (UInt64.ofNat commands.size / 3, after) := fun mem st hF => by
    have g4 : st.get 4 = some (.i64 (UInt64.ofNat commands.size)) :=
      (hF.get 4 (by decide) (by decide)).trans (State.get_update_same (by rw [hStartLen]; decide))
    have hLen : 11 < st.params.length + st.locals.length := by
      rw [hF.params, hF.locals]; omega
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := st) (index := 10)
      (.i64 (UInt64.ofNat commands.size)) (by omega)
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 11) (.i64 3) (by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1
      rw [hLenU]; omega)
    exact ⟨m2, by simp [Expr.eval, g4, hm1, hm2, U64Op.apply]⟩
  refine (Live.tupleLoop stepCommand_implements (f := clob.stepCommand.ir.function (2 + 11)) rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 11) rfl) rfl
    (states := [5, 6, 7]) (limit := 8) (index := 9) (srcs := [0, 1, 2])
    (ts := [(pp, prices), (ps, sizes), (po, out)]) (rest := []) (x0 := (prices, sizes, out))
    (by decide) (by decide) (by decide) rfl (by rw [hSt0Len]; decide) rfl hL hCap
    (.cons rfl (.cons rfl (.cons rfl .nil))) hCount (outStep commands)
    fun k us heap' store' st hk hF hIdx hHolds hUs hL' => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨⟨q1, _⟩, us, rfl, rfl, hUs1⟩ := List.map_eq_cons_iff.mp hUs
    obtain ⟨⟨q2, _⟩, us, rfl, rfl, hUs2⟩ := List.map_eq_cons_iff.mp hUs1
    obtain ⟨⟨q3, _⟩, us, rfl, rfl, hUs3⟩ := List.map_eq_cons_iff.mp hUs2
    obtain rfl := List.map_eq_nil_iff.mp hUs3
    simp only [List.append_nil] at hL'
    have g5 : st.get 5 = some (.i64 q1) := (List.forall₂_cons.mp hHolds).1
    have g6 : st.get 6 = some (.i64 q2) :=
      (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds).2).1
    have g7 : st.get 7 = some (.i64 q3) :=
      (List.forall₂_cons.mp (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds).2).2).1
    have hC' := (hL'.borrowed pc commands hCmds hAC).values
    have hLen : st.params.length + st.locals.length = 12 := by
      rw [hF.params, hF.locals]; exact hSt0Len
    have g3 : st.get 3 = some (.i64 pc) := (hF.get 3 (by decide) (by decide)).trans rfl
    obtain ⟨m1, hm1⟩ := State.exists_set? (state := st) (index := 10)
      (.i64 (3 * UInt64.ofNat k)) (by omega)
    have hm1Len : m1.params.length + m1.locals.length = 12 := by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm1; subst hm1; rw [hLenU, hLen]
    obtain ⟨m2, hm2⟩ := State.exists_set? (state := m1) (index := 10)
      (.i64 (3 * UInt64.ofNat k + 1)) (by omega)
    have hm2Len : m2.params.length + m2.locals.length = 12 := by
      rw [State.set?_eq_update _ (by omega), Option.some.injEq] at hm2; subst hm2; rw [hLenU, hm1Len]
    obtain ⟨m3, hm3⟩ := State.exists_set? (state := m2) (index := 10)
      (.i64 (3 * UInt64.ofNat k + 2)) (by omega)
    have k1 : ∀ j, j ≠ 10 → m1.get j = st.get j := fun j hj => State.get_set?_ne hj hm1
    have k2 : ∀ j, j ≠ 10 → m2.get j = st.get j := fun j hj =>
      (State.get_set?_ne hj hm2).trans (k1 j hj)
    have k3 : ∀ j, j ≠ 10 → m3.get j = st.get j := fun j hj =>
      (State.get_set?_ne hj hm3).trans (k2 j hj)
    refine ⟨[.i64 q1, .i64 q2, .i64 q3, .i64 commands[(3 * UInt64.ofNat k).toNat]!,
      .i64 commands[(3 * UInt64.ofNat k + 1).toNat]!,
      .i64 commands[(3 * UInt64.ofNat k + 2).toNat]!], m3, ?_,
      ⟨[.i64 q1], _, rfl, ⟨q1, rfl, hL'.tempsOwned _ List.mem_cons_self⟩, [.i64 q2], _, rfl,
        ⟨q2, rfl, hL'.tempsOwned _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩, [.i64 q3], _, rfl,
        ⟨q3, rfl, hL'.tempsOwned _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self))⟩, rfl⟩,
      rfl, fun _ hq => absurd hq List.not_mem_nil⟩
    refine Expr.evalResults_get g5 <| Expr.evalResults_get g6 <| Expr.evalResults_get g7 <|
      Expr.evalResults_cons (Expr.read_spec hC' (by simp [Expr.eval, hIdx, U64Op.apply]) hm1
        (by rw [k1 3 (by decide), g3])) <|
      Expr.evalResults_cons (Expr.read_spec hC'
        (by simp [Expr.eval, k1 9 (by decide), hIdx, U64Op.apply]) hm2
        (by rw [k2 3 (by decide), g3])) <|
      Expr.evalResults_cons (Expr.read_spec hC'
        (by simp [Expr.eval, k2 9 (by decide), hIdx, U64Op.apply]) hm3
        (by rw [k3 3 (by decide), g3])) Expr.evalResults_nil
  · rintro s' st' ⟨heap', us, hUs, hL', -, hHolds⟩
    simp only [List.append_nil] at hL'
    rw [outTuple_eq]
    exact Live.finish_results hUs hL' hHolds

theorem runOut_eq_fold (prices sizes out cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    LeanExe.Examples.Clob.runOut prices sizes out cs =
      foldCommands (fun c x => stepTuple (⟨x.1⟩, ⟨x.2.1⟩, ⟨x.2.2⟩, c)) cs
        (prices, sizes, out) := by
  have hn : (UInt64.ofNat cs.size / 3).toNat = cs.size / 3 := by
    rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    rfl
  show outTuple (⟨prices⟩, ⟨sizes⟩, ⟨out⟩, cs) = _
  rw [outTuple_eq]
  exact Nat.fold_congr hn _ _

/-- Running the commands in two chunks, the first of whole commands, gives the book and the
outputs of one run over both chunks. -/
theorem runOut_append (prices sizes out c1 c2 : Array UInt64) (h3 : c1.size % 3 = 0)
    (hs : (c1 ++ c2).size < 2 ^ 62) :
    LeanExe.Examples.Clob.runOut (LeanExe.Examples.Clob.runOut prices sizes out c1).1
        (LeanExe.Examples.Clob.runOut prices sizes out c1).2.1
        (LeanExe.Examples.Clob.runOut prices sizes out c1).2.2 c2 =
      LeanExe.Examples.Clob.runOut prices sizes out (c1 ++ c2) := by
  have hs' := hs
  rw [Array.size_append] at hs'
  rw [runOut_eq_fold _ _ _ c2 (by omega), runOut_eq_fold _ _ _ (c1 ++ c2) (by omega),
    runOut_eq_fold _ _ _ c1 (by omega)]
  exact foldCommands_append _ _ h3 hs

/-- The book that `runOut` leaves is the book of `runCommands`. -/
theorem runOut_book (prices sizes out cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    ((LeanExe.Examples.Clob.runOut prices sizes out cs).1,
        (LeanExe.Examples.Clob.runOut prices sizes out cs).2.1) =
      LeanExe.Examples.Clob.runCommands prices sizes cs := by
  rw [runOut_eq_fold _ _ _ _ hs, runCommands_eq_fold _ _ _ hs]
  exact foldCommands_map (fun x : Array UInt64 × Array UInt64 × Array UInt64 => (x.1, x.2.1))
    (fun _ _ => rfl) cs _

/-- `encode` succeeds on `clob.module`, and its bytes decode to a module whose
exports compute the CLOB operations exactly. -/
theorem clob_bytes : ∃ bytes, Encoding.encode clob.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧
      Implements m 2 marketBuyTuple ∧ Implements m 3 fillTuple ∧
      Implements m 4 insertTuple ∧ Implements m 5 setTuple ∧
      Implements m 6 addBidTuple ∧ Implements m 7 depthTuple ∧
      Implements m 8 findTuple ∧ Implements m 9 removeTuple ∧
      Implements m 10 cancelTuple ∧ Implements m 11 applyTuple ∧ Implements m 12 runTuple ∧
      Implements m 13 stepTuple ∧ Implements m 14 outTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip clob.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, clob.module, decoded, marketBuy_implements, fillLevel_implements,
    insertLevel_implements, setLevel_implements, addBid_implements,
    depth_implements, findLevel_implements, removeLevel_implements, cancelBid_implements,
    applyCommand_implements, runCommands_implements, stepCommand_implements,
    runOut_implements⟩

end Project.Clob
