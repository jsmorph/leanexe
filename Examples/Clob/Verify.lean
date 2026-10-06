import Examples.Clob.Module
import Project.IR.Correct
import Project.IR.Loop
import Project.IR.Read
import Project.IR.Build
import Project.IR.Update
import Project.IR.Call
import Project.IR.ArrayLoop
import Project.IR.Tuple
import Project.Encoding.RoundTrip

namespace Examples.Clob

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

/-- `marketBuy` with its three arguments as one tuple. -/
def marketBuyTuple (x : Array UInt64 × Array UInt64 × UInt64) : Array UInt64 :=
  Examples.Clob.marketBuy x.1 x.2.1 x.2.2

/-- One step of `marketBuy`'s loop over the ask levels. -/
def step (prices sizes : Array UInt64) (i : UInt64) (s : UInt64 × UInt64) : UInt64 × UInt64 :=
  (s.1 - min s.1 sizes[i.toNat]!, s.2 + min s.1 sizes[i.toNat]! * prices[i.toNat]!)

theorem marketBuy_eq (prices sizes : Array UInt64) (qty : UInt64) :
    Examples.Clob.marketBuy prices sizes qty =
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
    refine ⟨_, hNew.at_, hNew.caps, [.i64 ptr], state,
      by simp [clob.marketBuy.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨ptr, rfl, ?_⟩,
      hNew.keeps⟩
    rw [marketBuyTuple, marketBuy_eq, hResult]
    simpa using hOwned

/-- `fillLevel` with its three arguments as one tuple, the sizes handed over. -/
def fillTuple (x : Moved (Array UInt64) × UInt64 × UInt64) : Array UInt64 :=
  Examples.Clob.fillLevel x.1.val x.2.1 x.2.2

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
  rintro store state ⟨heap', p, -, hPtr, hAt, hOwned, hCaps, hKeeps⟩
  exact ⟨heap', hAt, hCaps, [.i64 p], state,
    by simp [clob.fillLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr], ⟨p, rfl, hOwned⟩,
    hKeeps⟩

/-- Two in-place updates in a row, of the array at `pp` and then of the array at `ps`, whose
blocks are apart: both results are owned and apart, and every region apart from both blocks
keeps its bytes, stays a region, and lies apart from both results. -/
theorem two_updates {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {pp ps q1 q2 : UInt64} {sizes xs1 xs2 : Array UInt64}
    (hSizes : heap.Owned initial ps sizes)
    (hPS : regionsDisjoint (block initial pp) (block initial ps))
    (hK1 : heap.Keeps initial [block initial pp] heap1 store1 [block store1 q1])
    (hAt1 : heap1.At store1) (hOwned1 : heap1.Owned store1 q1 xs1)
    (hK2 : heap1.Keeps store1 [block store1 ps] heap2 store2 [block store2 q2])
    (hAt2 : heap2.At store2) (hOwned2 : heap2.Owned store2 q2 xs2) :
    Represent.owned heap2 store2 [.i64 q1, .i64 q2] (xs1, xs2) ∧
      heap.Keeps initial ([pp, ps].map (block initial)) heap2 store2
        (Represent.blocks store2 [.i64 q1, .i64 q2] (xs1, xs2)) := by
  obtain ⟨⟨-, hCapS⟩, hApartS⟩ := hK1.owned hAt1 hSizes fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact regionsDisjoint_symm hPS
  have hBlockS : block store1 ps = block initial ps := block_eq hCapS
  obtain ⟨⟨hPrices2, hCapP2⟩, hApartP2⟩ := hK2.owned hAt2 hOwned1 fun b hb => by
    rw [List.mem_singleton.mp hb, hBlockS]
    exact regionsDisjoint_symm (hApartS _ (List.mem_singleton_self _))
  have hBlockP : block store2 q1 = block store1 q1 := block_eq hCapP2
  refine ⟨Represent.owned_pair.mpr ⟨hPrices2, hOwned2, by
    rw [hBlockP]; exact hApartP2 _ (List.mem_singleton_self _)⟩, fun g hg hpos hA => ?_⟩
  obtain ⟨hB1, hR1, hF1⟩ := hK1 g hg hpos fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact hA _ (by simp)
  obtain ⟨hB2, hR2, hF2⟩ := hK2 g hR1 hpos fun b hb => by
    rw [List.mem_singleton.mp hb, hBlockS]
    exact hA _ (by simp)
  refine ⟨fun a hl hh => (hB2 a hl hh).trans (hB1 a hl hh), hR2, fun b hb => ?_⟩
  change b ∈ [block store2 q1, block store2 q2] at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · rw [hBlockP]
    exact hF1 _ (List.mem_singleton_self _)
  · exact hF2 b hb

/-- `insertLevel` with its five arguments as one tuple, both arrays handed over. -/
def insertTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.insertLevel x.1.val x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2

theorem insertLevel_implements : Implements clob.module 4 insertTuple := by
  refine Func.implements_moves clob.funcs 2 clob.insertLevel.ir "insertLevel" rfl insertTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, k, price, size⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hSeparate hCap
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  have hMemory32 : (compile clob.funcs).memIs64 = false := rfl
  have hImports : (compile clob.funcs).imports = [] := rfl
  have hAlloc : (compile clob.funcs).funcs[0]? = some (allocFunction 0) := rfl
  have hRelease : (compile clob.funcs).funcs[1]? = some (releaseFunction 1) := rfl
  have hMoved : Represent.moves initial ([.i64 pp] ++ ([.i64 ps] ++ Scalar.values (k, price, size)))
      (Moved.mk prices, Moved.mk sizes, k, price, size) = [pp, ps] := rfl
  rw [hMoved] at hSeparate ⊢
  have hPS : regionsDisjoint (block initial pp) (block initial ps) := by
    have := hSeparate.1
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq] at this
    exact this.1
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k, .i64 price, .i64 size]
      locals := List.replicate 15 (.i64 0) }
  show Triple _ (.seq (.assign 5 (.get 2)) (.seq (.assign 6 (.get 3))
    (.seq (Stmt.insertInPlace 0 7 5 6 8 9 10 11) (.seq (.assign 12 (.get 2))
      (.seq (.assign 13 (.get 4)) (Stmt.insertInPlace 1 14 12 13 15 16 17 18)))))) 19
    (fun store state => store = initial ∧ state = start) _
  have hStart : start.params.length = 5 ∧ start.locals.length = 15 := ⟨rfl, rfl⟩
  have sg0 : start.get 0 = some (.i64 pp) := rfl
  have sg1 : start.get 1 = some (.i64 ps) := rfl
  have sg2 : start.get 2 = some (.i64 k) := rfl
  have sg3 : start.get 3 = some (.i64 price) := rfl
  have sg4 : start.get 4 = some (.i64 size) := rfl
  let u1 := start.update 5 (.i64 k)
  let u2 := u1.update 6 (.i64 price)
  have ug0 : u2.get 0 = some (.i64 pp) := by
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide), sg0]
  have ug5 : u2.get 5 = some (.i64 k) := by
    rw [State.get_update_ne (by decide)]; exact State.get_update_same (by simp [hStart.1, hStart.2])
  have ug6 : u2.get 6 = some (.i64 price) :=
    State.get_update_same (by simp [u1, State.update_params_length, State.update_locals_length,
      hStart.1, hStart.2])
  have hLen2 : u2.params.length + u2.locals.length = 20 := by
    simp [u2, u1, State.update_params_length, State.update_locals_length, hStart.1, hStart.2]
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · simp [Stmt.run, Expr.eval, sg2, State.set?_eq_update, hStart.1, hStart.2, u1]
  · have g13 : u1.get 3 = some (.i64 price) := by rw [State.get_update_ne (by decide), sg3]
    simp [Stmt.run, Expr.eval, g13, State.set?_eq_update, u1, u2, State.update_params_length,
      State.update_locals_length, hStart.1, hStart.2]
  refine Stmt.seq_spec (Stmt.insertInPlace_spec (p := pp) (kw := k) (vw := price) hMemory32
    hImports hAlloc hRelease (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) ug0 ug5 ug6 hHeap
    hCap hPrices) ?_
  apply Triple.of_forall
  rintro store1 st1 ⟨heap1, q1, hFr1, hD1, hAt1, hOwned1, hCaps1, hK1⟩
  obtain ⟨⟨hSizes1, -⟩, -⟩ := hK1.owned hAt1 hSizes fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact regionsDisjoint_symm hPS
  have hKeep1 : ∀ j, j < 19 → j ∉ [0, 7, 8, 9, 10, 11] → st1.get j = u2.get j :=
    fun j hj hjn => hFr1.get j hj hjn
  have hLen1 : st1.params.length + st1.locals.length = 20 := by
    rw [hFr1.params, hFr1.locals]; exact hLen2
  have tg1 : st1.get 1 = some (.i64 ps) := by
    rw [hKeep1 1 (by decide) (by decide), State.get_update_ne (by decide),
      State.get_update_ne (by decide), sg1]
  have tg2 : st1.get 2 = some (.i64 k) := by
    rw [hKeep1 2 (by decide) (by decide), State.get_update_ne (by decide),
      State.get_update_ne (by decide), sg2]
  have tg4 : st1.get 4 = some (.i64 size) := by
    rw [hKeep1 4 (by decide) (by decide), State.get_update_ne (by decide),
      State.get_update_ne (by decide), sg4]
  let u3 := st1.update 12 (.i64 k)
  let u4 := u3.update 13 (.i64 size)
  have vg1 : u4.get 1 = some (.i64 ps) := by
    rw [State.get_update_ne (by decide), State.get_update_ne (by decide), tg1]
  have vg12 : u4.get 12 = some (.i64 k) := by
    rw [State.get_update_ne (by decide)]
    exact State.get_update_same (by rw [← Nat.add_zero 12]; omega)
  have vg13 : u4.get 13 = some (.i64 size) :=
    State.get_update_same (by simp [u3, State.update_params_length, State.update_locals_length]; omega)
  have hLen4 : u4.params.length + u4.locals.length = 20 := by
    simp [u4, u3, State.update_params_length, State.update_locals_length]; omega
  refine Stmt.seq_spec (Stmt.run_spec (final := u3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u4) ?_) ?_
  · simp [Stmt.run, Expr.eval, tg2, State.set?_eq_update _ (show 12 < st1.params.length +
      st1.locals.length by omega), u3]
  · have g34 : u3.get 4 = some (.i64 size) := by rw [State.get_update_ne (by decide), tg4]
    have hLen3 : u3.params.length + u3.locals.length = 20 := by
      simp [u3, State.update_params_length, State.update_locals_length]; omega
    simp [Stmt.run, Expr.eval, g34, State.set?_eq_update _ (show 13 < u3.params.length +
      u3.locals.length by omega), u4]
  refine (Stmt.insertInPlace_spec (p := ps) (kw := k) (vw := size) hMemory32 hImports hAlloc
    hRelease (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) vg1 vg12 vg13 hAt1
    (memoryCap_le_of_caps hCaps1 hCap) hSizes1).mono (fun _ _ h => h) ?_
  rintro store2 st2 ⟨heap2, q2, hFr2, hD2, hAt2, hOwned2, hCaps2, hK2⟩
  have hD1' : st2.get 0 = some (.i64 q1) := by
    rw [hFr2.get 0 (by decide) (by decide), State.get_update_ne (by decide),
      State.get_update_ne (by decide), hD1]
  obtain ⟨hOwnedPair, hKeeps⟩ := two_updates hSizes hPS hK1 hAt1 hOwned1 hK2 hAt2 hOwned2
  exact ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 q1, .i64 q2], st2,
    by simp [clob.insertLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hD1', hD2],
    hOwnedPair, hKeeps⟩

/-- `setLevel` with its four arguments as one tuple, both arrays handed over. -/
def setTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.setLevel x.1.val x.2.1.val x.2.2.1 x.2.2.2

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
  rintro store state ⟨heap', p, hFrame, hPtr, hAt, hOwned, hCaps, hKeeps⟩
  have hPtr0 : state.get 0 = some (.i64 pp) := by
    rw [hFrame.get 0 (by decide) (by decide)]; simp [u2, u1, sg0]
  obtain ⟨⟨hKeptP, hCapP⟩, hApartP⟩ := hKeeps.owned hAt hPrices fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact hPS
  have hBlockP : block store pp = block initial pp := block_eq hCapP
  refine ⟨heap', hAt, hCaps, [.i64 pp, .i64 p], state,
    by simp [clob.setLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr0, hPtr],
    Represent.owned_pair.mpr ⟨hKeptP, hOwned, by
      rw [hBlockP]; exact hApartP _ (List.mem_singleton_self _)⟩, fun g hg hpos hA => ?_⟩
  obtain ⟨hB, hR, hF⟩ := hKeeps g hg hpos fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact hA _ (by simp)
  refine ⟨hB, hR, fun b hb => ?_⟩
  change b ∈ [block store pp, block store p] at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · rw [hBlockP]
    exact hA _ (by simp)
  · exact hF b hb

/-- `depth` with its three arguments as one tuple. -/
def depthTuple (x : Array UInt64 × Array UInt64 × UInt64) : UInt64 :=
  Examples.Clob.depth x.1 x.2.1 x.2.2

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
  Examples.Clob.findLevel x.1 x.2

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

/-- `removeLevel` with its three arguments as one tuple, both arrays handed over. -/
def removeTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.removeLevel x.1.val x.2.1.val x.2.2

theorem removeLevel_implements : Implements clob.module 9 removeTuple := by
  refine Func.implements_moves clob.funcs 7 clob.removeLevel.ir "removeLevel" rfl removeTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, _, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨prices⟩, ⟨sizes⟩, k⟩ heap initial _ hHeap
    ⟨_, _, rfl, ⟨pp, rfl, hPrices⟩, _, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ hSeparate -
  change heap.Owned initial pp prices at hPrices
  change heap.Owned initial ps sizes at hSizes
  have hMoved : Represent.moves initial ([.i64 pp] ++ ([.i64 ps] ++ Scalar.values k))
      (Moved.mk prices, Moved.mk sizes, k) = [pp, ps] := rfl
  rw [hMoved] at hSeparate ⊢
  have hPS : regionsDisjoint (block initial pp) (block initial ps) := by
    have := hSeparate.1
    simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton,
      forall_eq] at this
    exact this.1
  let start : State :=
    { params := [.i64 pp, .i64 ps, .i64 k], locals := List.replicate 9 (.i64 0) }
  show Triple _ (.seq (.assign 3 (.get 2)) (.seq (Stmt.eraseInPlace 0 4 3 5 6)
    (.seq (.assign 7 (.get 2)) (Stmt.eraseInPlace 1 8 7 9 10)))) 11
    (fun store state => store = initial ∧ state = start) _
  have hStart : start.params.length = 3 ∧ start.locals.length = 9 := ⟨rfl, rfl⟩
  have sg0 : start.get 0 = some (.i64 pp) := rfl
  have sg1 : start.get 1 = some (.i64 ps) := rfl
  have sg2 : start.get 2 = some (.i64 k) := rfl
  let u1 := start.update 3 (.i64 k)
  have ug0 : u1.get 0 = some (.i64 pp) := by rw [State.get_update_ne (by decide), sg0]
  have ug1 : u1.get 1 = some (.i64 ps) := by rw [State.get_update_ne (by decide), sg1]
  have ug2 : u1.get 2 = some (.i64 k) := by rw [State.get_update_ne (by decide), sg2]
  have ug3 : u1.get 3 = some (.i64 k) := State.get_update_same (by simp [hStart.1, hStart.2])
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) ?_
  · simp [Stmt.run, Expr.eval, sg2, State.set?_eq_update, hStart.1, hStart.2, u1]
  refine Stmt.seq_spec (Stmt.eraseInPlace_spec (p := pp) (kw := k) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [u1, hStart.1, hStart.2]) ug0 ug3 hHeap
    hPrices) ?_
  apply Triple.of_forall
  rintro store1 st1 ⟨heap1, p1, hFr1, hPtr1, hAt1, hOwned1, hCaps1, hK1⟩
  have hP1 : p1 = pp := by
    rw [hFr1.get 0 (by decide) (by decide), ug0] at hPtr1
    exact (Value.i64.inj (Option.some.inj hPtr1)).symm
  subst hP1
  obtain ⟨⟨hSizes1, -⟩, -⟩ := hK1.owned hAt1 hSizes fun b hb => by
    rw [List.mem_singleton.mp hb]
    exact regionsDisjoint_symm hPS
  have hLen1 : st1.params.length = 3 ∧ st1.locals.length = 9 := by
    rw [hFr1.params, hFr1.locals]; exact ⟨State.update_params_length .., by
      rw [State.update_locals_length]; exact hStart.2⟩
  let u2 := st1.update 7 (.i64 k)
  have hGet2 : st1.get 2 = some (.i64 k) := by rw [hFr1.get 2 (by decide) (by decide), ug2]
  have hGet1 : st1.get 1 = some (.i64 ps) := by rw [hFr1.get 1 (by decide) (by decide), ug1]
  have vg1 : u2.get 1 = some (.i64 ps) := by rw [State.get_update_ne (by decide), hGet1]
  have vg7 : u2.get 7 = some (.i64 k) := State.get_update_same (by omega)
  refine Stmt.seq_spec (Stmt.run_spec (final := u2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet2, State.set?_eq_update, hLen1.1, hLen1.2, u2]
  refine (Stmt.eraseInPlace_spec (p := ps) (kw := k) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by simp [u2, State.update_params_length,
      State.update_locals_length, hLen1.1, hLen1.2]) vg1 vg7 hAt1 hSizes1).mono
    (fun _ _ h => h) ?_
  rintro store2 st2 ⟨heap2, p2, hFr2, hPtr2, hAt2, hOwned2, hCaps2, hK2⟩
  have hPtr0 : st2.get 0 = some (.i64 p1) := by
    rw [hFr2.get 0 (by decide) (by decide), State.get_update_ne (by decide),
      hFr1.get 0 (by decide) (by decide), ug0]
  obtain ⟨hOwnedPair, hKeeps⟩ := two_updates hSizes hPS hK1 hAt1 hOwned1 hK2 hAt2 hOwned2
  exact ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 p1, .i64 p2], st2,
    by simp [clob.removeLevel.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr0, hPtr2],
    hOwnedPair, hKeeps⟩

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
    ∃ values next,
      Expr.evalResults store.mem scratch [⟨.u64, .get a⟩, ⟨.u64, .get b⟩] state =
        some (values, next) ∧ Represent.owned heap' store values result ∧
      heap.Keeps initial (moved.map (block initial)) heap' store
        (Represent.blocks store values result)

/-- A body whose live temporaries are its two results, in locals `a` and `b`, ends with
`MovesPost`. -/
theorem movesPost_of_live {heap heap1 : Heap} {initial store : Store Unit} {moved : List UInt64}
    {p1 p2 : UInt64} {xs ys : Array UInt64} {scratch a b : Nat} {state : State}
    (hLive : Live heap initial moved heap1 store [(p1, xs), (p2, ys)])
    (hA : state.get a = some (.i64 p1)) (hB : state.get b = some (.i64 p2)) :
    MovesPost heap initial moved scratch a b (xs, ys) store state := by
  obtain ⟨heap', hAt, hCaps, hOwned, hKeeps⟩ := hLive.finish_pair
  exact ⟨heap', hAt, hCaps, [.i64 p1, .i64 p2], state,
    by simp [Expr.evalResults, Expr.eval, hA, hB], hOwned, hKeeps⟩

/-- `addBid` with its four arguments as one tuple: the call consumes both arrays. -/
def addBidTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.addBid x.1.val x.2.1.val x.2.2.1 x.2.2.2

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
    (.call 4 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩, ⟨.u64, .get 2⟩,
      ⟨.u64, .get 3⟩] [6, 7])) (6 + 3)
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
      unfold addBidTuple Examples.Clob.addBid; exact ite_eq_left hFound
    rw [hResult]
    exact movesPost_of_live hL2 (State.get_update_same (by rw [hLenU, hLength]; decide))
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
  · -- A new level: `insertLevel` consumes both arrays.
    intro heap1 store1 state hL hB hFound
    set K := findTuple (prices, price) with hK
    have hLength : state.params.length + state.locals.length = 10 := by
      rw [hB.params, hB.locals]
    refine (Live.callPair insertLevel_implements rfl
      (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 2) rfl) rfl
      (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
      (vals := [.i64 pp, .i64 ps, .i64 K, .i64 price, .i64 size])
      (x := (⟨prices⟩, ⟨sizes⟩, K, price, size)) (afterArgs := state)
      (by simp [Expr.evalResults, Expr.eval, hB.get0, hB.get1, hB.get2, hB.get3, hB.get5])
      ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hL.tempsOwned (pp, prices) (by simp)⟩, [.i64 ps], _, rfl,
        ⟨ps, rfl, hL.tempsOwned (ps, sizes) (by simp)⟩, rfl⟩ rfl
      (fun q hq => by simp [Represent.reads] at hq) (by omega) (by omega)).mono
        (fun _ _ h => h) ?_
    rintro s st ⟨heap2, p1, p2, hL2, rfl⟩
    have hResult : addBidTuple (⟨prices⟩, ⟨sizes⟩, price, size) =
        insertTuple (⟨prices⟩, ⟨sizes⟩, K, price, size) := by
      unfold addBidTuple Examples.Clob.addBid; exact ite_eq_right hFound
    rw [hResult]
    exact movesPost_of_live hL2 (State.get_update_same (by rw [hLenU, hLength]; decide))
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))

/-- `cancelBid` with its four arguments as one tuple: the call consumes both arrays. -/
def cancelTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.cancelBid x.1.val x.2.1.val x.2.2.1 x.2.2.2

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
      (.call 9 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 5⟩] [6, 7])
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
    · -- `removeLevel` consumes both arrays.
      refine (Live.callPair removeLevel_implements rfl
        (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 7) rfl) rfl
        (consumed := [(pp, prices), (ps, sizes)]) (rest := []) hL hCap
        (vals := [.i64 pp, .i64 ps, .i64 K]) (x := (⟨prices⟩, ⟨sizes⟩, K)) (afterArgs := read)
        (by simp [Expr.evalResults, Expr.eval, hReadGet 0 (by decide), hReadGet 1 (by decide),
          hReadGet 5 (by decide), hB.get0, hB.get1, hB.get5])
        ⟨[.i64 pp], _, rfl, ⟨pp, rfl, hL.tempsOwned _ hMemP⟩, [.i64 ps], _, rfl,
          ⟨ps, rfl, hL.tempsOwned _ hMemS⟩, rfl⟩ rfl
        (fun q hq => by simp [Represent.reads] at hq) (by omega) (by omega)).mono
          (fun _ _ h => h) ?_
      rintro s2 st2 ⟨heap2, p1, p2, hL2, rfl⟩
      have hResult : cancelTuple (⟨prices⟩, ⟨sizes⟩, price, size) =
          removeTuple (⟨prices⟩, ⟨sizes⟩, K) := by
        unfold cancelTuple Examples.Clob.cancelBid
        exact (ite_eq_left hFound).trans (ite_eq_left hLe)
      rw [hResult]
      exact movesPost_of_live hL2 (State.get_update_same (by rw [hLenU, hReadLen]; decide))
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
        unfold cancelTuple Examples.Clob.cancelBid
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
      unfold cancelTuple Examples.Clob.cancelBid; exact ite_eq_right hFound]
    exact movesPost_of_live hL
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
      (State.get_update_same (by rw [hLenU]; omega))

/-- `applyCommand` with its five arguments as one tuple: the call consumes both arrays. -/
def applyTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × UInt64 × UInt64 × UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.applyCommand x.1.val x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2

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
      unfold applyTuple Examples.Clob.applyCommand; exact ite_eq_left hKind]
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
      unfold applyTuple Examples.Clob.applyCommand
      exact (ite_eq_right hKind).trans (ite_eq_left hKind1)]
    exact hFinal _ _ p1 p2 _ hL2
  · -- Any other kind: both arrays are returned.
    refine (Stmt.run_spec (final := (start.update 5 (.i64 pp)).update 6 (.i64 ps)) ?_).mono
      (fun _ _ h => h) ?_
    · simp [Stmt.run, Expr.eval, hGet.1, hGet.2.1, State.set?_eq_update, start]
    rintro s st ⟨rfl, rfl⟩
    rw [show applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size) = (prices, sizes) by
      unfold applyTuple Examples.Clob.applyCommand
      exact (ite_eq_right hKind).trans (ite_eq_right hKind1)]
    exact movesPost_of_live hL
      (by rw [State.get_update_ne (by decide)]; exact State.get_update_same (by omega))
      (State.get_update_same (by rw [hLenU, hLength]; decide))

/-- `runCommands` with its three arguments as one tuple: the call consumes the book. -/
def runTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × Array UInt64) :
    Array UInt64 × Array UInt64 :=
  Examples.Clob.runCommands x.1.val x.2.1.val x.2.2

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
    Examples.Clob.runCommands prices sizes cs =
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
    Examples.Clob.runCommands
        (Examples.Clob.runCommands prices sizes c1).1
        (Examples.Clob.runCommands prices sizes c1).2 c2 =
      Examples.Clob.runCommands prices sizes (c1 ++ c2) := by
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
  Examples.Clob.stepCommand x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1 x.2.2.2.2.1
    x.2.2.2.2.2

theorem stepTuple_eq (prices sizes out : Array UInt64) (kind price size : UInt64) :
    stepTuple (⟨prices⟩, ⟨sizes⟩, ⟨out⟩, kind, price, size) =
      ((applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).1,
        (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).2,
        (out.push (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).1[(0 : UInt64).toNat]!).push
          (applyTuple (⟨prices⟩, ⟨sizes⟩, kind, price, size)).2[(0 : UInt64).toNat]!) := rfl

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
      locals := List.replicate 17 (.i64 0) }
  have hStartLen : start.params.length + start.locals.length = 23 := rfl
  show Triple _ (.seq (.call 11 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩, ⟨.u64, .get 4⟩,
        ⟨.u64, .get 5⟩] [6, 7]) <|
      .seq (.assign 8 (.read 6 (.const 0))) <| .seq (.assign 9 (.read 7 (.const 0))) <|
      .seq (.assign 10 (.get 9)) <| .seq (.assign 11 (.get 8)) <|
      .seq (Stmt.pushInPlace 2 12 11 13 14 15 16) (Stmt.pushInPlace 2 17 10 18 19 20 21)) 22
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
  have hLen1 : st1.params.length + st1.locals.length = 23 := by rw [hst1, hLenU, hLenU, hStartLen]
  have g1 : ∀ j, j ≠ 6 → j ≠ 7 → st1.get j = start.get j := fun j h6 h7 => by
    rw [hst1, State.get_update_ne h6, State.get_update_ne h7]
  have g16 : st1.get 6 = some (.i64 p1) := by
    rw [hst1]; exact State.get_update_same (by rw [hLenU, hStartLen]; decide)
  have g17 : st1.get 7 = some (.i64 p2) := by
    rw [hst1, State.get_update_ne (by decide)]; exact State.get_update_same (by rw [hStartLen]; decide)
  have hP := hL1.tempsOwned (p1, P) List.mem_cons_self
  have hS := hL1.tempsOwned (p2, S) (List.mem_cons_of_mem _ List.mem_cons_self)
  -- The best bid: the first price and size.
  obtain ⟨st2, hst2⟩ : ∃ st2, st2 = (st1.update 22 (.i64 0)).update 8 (.i64 P[(0 : UInt64).toNat]!) :=
    ⟨_, rfl⟩
  have hLen2 : st2.params.length + st2.locals.length = 23 := by rw [hst2, hLenU, hLenU, hLen1]
  refine Stmt.seq_spec (Stmt.run_spec (final := st2) ?_) ?_
  · have hRead := Expr.read_spec (scratch := 22) (array := 6) (position := .const 0) (state := st1)
      hP.values rfl (State.set?_eq_update _ (by rw [hLen1]; decide))
      (by rw [State.get_update_ne (by decide)]; exact g16)
    rw [hst2]
    simp only [Stmt.run, hRead, Option.bind_eq_bind, Option.bind_some]
    exact State.set?_eq_update _ (by rw [hLenU, hLen1]; decide)
  obtain ⟨st3, hst3⟩ : ∃ st3, st3 = (st2.update 22 (.i64 0)).update 9 (.i64 S[(0 : UInt64).toNat]!) :=
    ⟨_, rfl⟩
  have hLen3 : st3.params.length + st3.locals.length = 23 := by rw [hst3, hLenU, hLenU, hLen2]
  refine Stmt.seq_spec (Stmt.run_spec (final := st3) ?_) ?_
  · have hRead := Expr.read_spec (scratch := 22) (array := 7) (position := .const 0) (state := st2)
      hS.values rfl (State.set?_eq_update _ (by rw [hLen2]; decide))
      (by rw [State.get_update_ne (by decide), hst2, State.get_update_ne (by decide),
        State.get_update_ne (by decide)]; exact g17)
    rw [hst3]
    simp only [Stmt.run, hRead, Option.bind_eq_bind, Option.bind_some]
    exact State.set?_eq_update _ (by rw [hLenU, hLen2]; decide)
  have g3 : ∀ j, j ≠ 8 → j ≠ 9 → j ≠ 22 → st3.get j = st1.get j := fun j h8 h9 h22 => by
    rw [hst3, State.get_update_ne h9, State.get_update_ne h22, hst2, State.get_update_ne h8,
      State.get_update_ne h22]
  have g36 : st3.get 6 = some (.i64 p1) := by rw [g3 6 (by decide) (by decide) (by decide), g16]
  have g37 : st3.get 7 = some (.i64 p2) := by rw [g3 7 (by decide) (by decide) (by decide), g17]
  have g38 : st3.get 8 = some (.i64 P[(0 : UInt64).toNat]!) := by
    rw [hst3, State.get_update_ne (by decide), State.get_update_ne (by decide), hst2]
    exact State.get_update_same (by rw [hLenU, hLen1]; decide)
  have g39 : st3.get 9 = some (.i64 S[(0 : UInt64).toNat]!) := by
    rw [hst3]; exact State.get_update_same (by rw [hLenU, hLen2]; decide)
  -- The pushed values.
  let P0 := P[(0 : UInt64).toNat]!
  let S0 := S[(0 : UInt64).toNat]!
  obtain ⟨st4, hst4⟩ : ∃ st4, st4 = (st3.update 10 (.i64 S0)).update 11 (.i64 P0) := ⟨_, rfl⟩
  have hLen4 : st4.params.length + st4.locals.length = 23 := by rw [hst4, hLenU, hLenU, hLen3]
  refine Stmt.seq_spec (Stmt.run_spec (final := st3.update 10 (.i64 S0))
    (by simp [Stmt.run, Expr.eval, g39, State.set?_eq_update (state := st3) (index := 10) _
      (by rw [hLen3]; decide), ScalarType.value, S0])) ?_
  refine Stmt.seq_spec (Stmt.run_spec (final := st4)
    (by simp [hst4, Stmt.run, Expr.eval, State.get_update_ne, g38,
      State.set?_eq_update (state := st3.update 10 (.i64 S0)) (index := 11) _
        (by rw [hLenU, hLen3]; decide), ScalarType.value, P0])) ?_
  have g42 : st4.get 2 = some (.i64 po) := by
    rw [hst4, State.get_update_ne (by decide), State.get_update_ne (by decide),
      g3 2 (by decide) (by decide) (by decide), g1 2 (by decide) (by decide)]; rfl
  have g410 : st4.get 10 = some (.i64 S0) := by
    rw [hst4, State.get_update_ne (by decide)]; exact State.get_update_same (by rw [hLen3]; decide)
  have g411 : st4.get 11 = some (.i64 P0) := by
    rw [hst4]; exact State.get_update_same (by rw [hLenU, hLen3]; decide)
  -- Two pushes in place onto the output array.
  refine Stmt.seq_spec ((Stmt.pushInPlace_spec (before := st4) hMemory32 hImports hAlloc hRelease
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hLen4]; decide) g42 g411 hL1.at_ (hL1.cap hCap)
    (hL1.tempsOwned (po, out) (by simp))).mono (fun _ _ h => h)
      fun _ _ h => Live.appendPost (pre := [(p1, P), (p2, S)]) (t := (po, out)) (post := []) hL1 h) ?_
  apply Triple.of_forall
  rintro s5 st5 ⟨heap5, q1, hL5, hF5, g52⟩
  have hLen5 : st5.params.length + st5.locals.length = 23 := by
    rw [hF5.params, hF5.locals, hLen4]
  have g510 : st5.get 10 = some (.i64 S0) := by rw [hF5.get 10 (by decide) (by decide), g410]
  refine ((Stmt.pushInPlace_spec (before := st5) hMemory32 hImports hAlloc hRelease
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hLen5]; decide) g52 g510 hL5.at_ (hL5.cap hCap)
    (hL5.tempsOwned _ List.mem_cons_self)).mono (fun _ _ h => h)
      fun _ _ h => Live.appendPost (pre := []) (t := (q1, out.push P0))
        (post := [(p1, P), (p2, S)]) hL5 h).mono (fun _ _ h => h) ?_
  rintro s6 st6 ⟨heap6, q2, hL6, hF6, g62⟩
  have g66 : st6.get 6 = some (.i64 p1) := by
    rw [hF6.get 6 (by decide) (by decide), hF5.get 6 (by decide) (by decide), hst4,
      State.get_update_ne (by decide), State.get_update_ne (by decide), g36]
  have g67 : st6.get 7 = some (.i64 p2) := by
    rw [hF6.get 7 (by decide) (by decide), hF5.get 7 (by decide) (by decide), hst4,
      State.get_update_ne (by decide), State.get_update_ne (by decide), g37]
  have hHolds : st6.Holds [6, 7, 2] (pointers [(p1, P), (p2, S), (q2, (out.push P0).push S0)]) :=
    .cons g66 (.cons g67 (.cons g62 .nil))
  rw [stepTuple_eq, hA]
  exact Live.finish_results (y := (P, S, (out.push P0).push S0)) rfl
    (hL6.perm (List.perm_append_comm (l₁ := [(q2, (out.push P0).push S0)])
      (l₂ := [(p1, P), (p2, S)]))) hHolds

/-- `runOut` with its four arguments as one tuple: the call consumes the book and the output
array. -/
def outTuple (x : Moved (Array UInt64) × Moved (Array UInt64) × Moved (Array UInt64) ×
    Array UInt64) : Array UInt64 × Array UInt64 × Array UInt64 :=
  Examples.Clob.runOut x.1.val x.2.1.val x.2.2.1.val x.2.2.2

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
    Examples.Clob.runOut prices sizes out cs =
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
    Examples.Clob.runOut (Examples.Clob.runOut prices sizes out c1).1
        (Examples.Clob.runOut prices sizes out c1).2.1
        (Examples.Clob.runOut prices sizes out c1).2.2 c2 =
      Examples.Clob.runOut prices sizes out (c1 ++ c2) := by
  have hs' := hs
  rw [Array.size_append] at hs'
  rw [runOut_eq_fold _ _ _ c2 (by omega), runOut_eq_fold _ _ _ (c1 ++ c2) (by omega),
    runOut_eq_fold _ _ _ c1 (by omega)]
  exact foldCommands_append _ _ h3 hs

/-- The book that `runOut` leaves is the book of `runCommands`. -/
theorem runOut_book (prices sizes out cs : Array UInt64) (hs : cs.size < 2 ^ 64) :
    ((Examples.Clob.runOut prices sizes out cs).1,
        (Examples.Clob.runOut prices sizes out cs).2.1) =
      Examples.Clob.runCommands prices sizes cs := by
  rw [runOut_eq_fold _ _ _ _ hs, runCommands_eq_fold _ _ _ hs]
  exact foldCommands_map (fun x : Array UInt64 × Array UInt64 × Array UInt64 => (x.1, x.2.1))
    (fun _ _ => rfl) cs _

/-- `fillTwice` with its four arguments as one tuple, the sizes handed over. -/
def fillTwiceTuple (x : Moved (Array UInt64) × UInt64 × UInt64 × UInt64) : Array UInt64 :=
  Examples.Clob.fillTwice x.1.val x.2.1 x.2.2.1 x.2.2.2

/-- `fillTwice` binds the array of its first call to `fillLevel` with `let` and hands it to the
second call, which consumes it: the first call's frame leaves the array's block fresh, which
the second call consumes. -/
theorem fillTwice_implements : Implements clob.module 15 fillTwiceTuple := by
  refine Func.implements_moves clob.funcs 13 clob.fillTwice.ir "fillTwice" rfl fillTwiceTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨sizes⟩, k, a, b⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ - hCap
  let ys := Examples.Clob.fillLevel sizes k a
  let ps4 : List Value := [.i64 ps, .i64 k, .i64 a, .i64 b]
  show Triple _ (.seq (.call 3 [⟨.u64, .get 0⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [4])
      (.call 3 [⟨.u64, .get 4⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 3⟩] [5])) 6
    (fun store state => store = initial ∧ state = ⟨ps4, [.i64 0, .i64 0]⟩) _
  refine Stmt.seq_spec (Stmt.callImplements_spec fillLevel_implements rfl
    (compile_funcs (i := 1) rfl) rfl (before := ⟨ps4, [.i64 0, .i64 0]⟩)
    (afterArgs := ⟨ps4, [.i64 0, .i64 0]⟩) (results := [4]) (x := (⟨sizes⟩, k, a))
    (vals := [.i64 ps, .i64 k, .i64 a]) (by simp [Expr.evalResults, Expr.eval, State.get, ps4])
    hHeap ⟨[.i64 ps], [.i64 k, .i64 a], rfl, ⟨ps, rfl, hSizes⟩, rfl⟩
    ⟨List.pairwise_singleton _ _, fun _ h => by simp [Represent.reads] at h⟩ hCap
    fun _ _ _ ⟨q, hq, _⟩ => by subst hq; exact ⟨_, rfl⟩) ?_
  refine Triple.of_forall fun store1 st
    ⟨heap1, values1, hAt1, ⟨q1, hq1, hOwned1⟩, hCaps1, hK1, hSet1⟩ => ?_
  subst hq1
  obtain rfl : st = ⟨ps4, [.i64 q1, .i64 0]⟩ := (Option.some.inj (hSet1.symm.trans rfl))
  refine (Stmt.callImplements_spec fillLevel_implements rfl (compile_funcs (i := 1) rfl) rfl
    (before := ⟨ps4, [.i64 q1, .i64 0]⟩) (afterArgs := ⟨ps4, [.i64 q1, .i64 0]⟩)
    (results := [5]) (x := (⟨ys⟩, k, b)) (vals := [.i64 q1, .i64 k, .i64 b])
    (by simp [Expr.evalResults, Expr.eval, State.get, ps4]) hAt1
    ⟨[.i64 q1], [.i64 k, .i64 b], rfl, ⟨q1, rfl, hOwned1⟩, rfl⟩
    ⟨List.pairwise_singleton _ _, fun _ h => by simp [Represent.reads] at h⟩
    (memoryCap_le_of_caps hCaps1 hCap)
    fun _ _ _ ⟨q, hq, _⟩ => by subst hq; exact ⟨_, rfl⟩).mono (fun _ _ h => h) ?_
  rintro store2 st2 ⟨heap2, values2, hAt2, ⟨q2, hq2, hOwned2⟩, hCaps2, hK2, hSet2⟩
  subst hq2
  obtain rfl : st2 = ⟨ps4, [.i64 q1, .i64 q2]⟩ := (Option.some.inj (hSet2.symm.trans rfl))
  exact ⟨heap2, hAt2, hCaps2.trans hCaps1, [.i64 q2], _, rfl, ⟨q2, rfl, hOwned2⟩,
    hK1.trans hK2 fun _ _ hFresh => hFresh⟩

/-- `fillKeep` with its three arguments as one tuple, the sizes handed over. -/
def fillKeepTuple (x : Moved (Array UInt64) × UInt64 × UInt64) : Array UInt64 × Array UInt64 :=
  Examples.Clob.fillKeep x.1.val x.2.1 x.2.2

/-- `fillKeep` copies the sizes into a fresh block, which `fillLevel` consumes, and returns the
call's result with the handed-over sizes. -/
theorem fillKeep_implements : Implements clob.module 16 fillKeepTuple := by
  refine Func.implements_moves clob.funcs 14 clob.fillKeep.ir "fillKeep" rfl fillKeepTuple
    (by rintro _ _ _ _ ⟨_, _, rfl, ⟨_, rfl, -⟩, rfl⟩; rfl) ?_
  rintro ⟨⟨sizes⟩, k, a⟩ heap initial _ hHeap ⟨_, _, rfl, ⟨ps, rfl, hSizes⟩, rfl⟩ - hCap
  change heap.Owned initial ps sizes at hSizes
  rw [show Represent.moves initial ([.i64 ps] ++ Scalar.values (k, a)) (Moved.mk sizes, k, a) = [ps]
    from rfl]
  have hNoImports : clob.module.imports.length = 0 := rfl
  have hImports : clob.module.imports = [] := rfl
  have hMemory32 : clob.module.memIs64 = false := rfl
  have hAlloc : clob.module.funcs[0]? = some (allocFunction 0) := rfl
  let start : State :=
    { params := [.i64 ps, .i64 k, .i64 a], locals := List.replicate 6 (.i64 0) }
  have hStartLen : start.params.length + start.locals.length = 9 := rfl
  show Triple _ (.seq (Stmt.copy 4 5 6 3 0)
      (.call 3 [⟨.u64, .get 4⟩, ⟨.u64, .get 1⟩, ⟨.u64, .get 2⟩] [7])) 8
    (fun store state => store = initial ∧ state = start) _
  have hL := Live.start_moved hHeap (temps := [(ps, sizes)])
    (fun t ht => by rw [List.mem_singleton.mp ht]; exact hSizes) (List.pairwise_singleton _ _)
  -- The copy joins the live temporaries.
  refine Stmt.seq_spec (Live.copy hMemory32 hImports hAlloc (by decide) (by decide) (by decide)
    (by decide) (before := start) (by rw [hStartLen]; decide) hL hCap (ptr := ps) (xs := sizes)
    rfl (hL.tempsOwned _ List.mem_cons_self).borrowed) ?_
  apply Triple.of_forall
  rintro s1 st1 ⟨heap1, p, hL1, hF1, g14⟩
  have hLen1 : st1.params.length + st1.locals.length = 9 := by
    rw [hF1.params, hF1.locals, hStartLen]
  have g11 : st1.get 1 = some (.i64 k) := hF1.get 1 (by decide) (by decide)
  have g12 : st1.get 2 = some (.i64 a) := hF1.get 2 (by decide) (by decide)
  have g10 : st1.get 0 = some (.i64 ps) := hF1.get 0 (by decide) (by decide)
  -- `fillLevel` consumes the copy.
  refine (Live.callTuple (β := Array UInt64) fillLevel_implements rfl
    (by rw [hNoImports]; exact compile_funcs (funcs := clob.funcs) (i := 1) rfl) rfl
    (results := [7]) (consumed := [(p, sizes)]) (rest := [(ps, sizes)]) hL1 hCap
    (x := (⟨sizes⟩, k, a)) (before := st1) (afterArgs := st1)
    (vals := [.i64 p, .i64 k, .i64 a])
    (by simp [Expr.evalResults, Expr.eval, g14, g11, g12])
    ⟨[.i64 p], _, rfl, ⟨p, rfl, hL1.tempsOwned _ List.mem_cons_self⟩, rfl⟩
    rfl (fun _ hq => absurd hq List.not_mem_nil) rfl
    (fun r hr => by rw [List.mem_singleton.mp hr, hLen1]; decide)).mono (fun _ _ h => h) ?_
  rintro s2 st2 ⟨heap2, ts, hTs, hL2, hSet⟩
  obtain ⟨⟨q, _⟩, ts, rfl, rfl, hTs1⟩ := List.map_eq_cons_iff.mp hTs
  obtain rfl := List.map_eq_nil_iff.mp hTs1
  have hst2 : st2 = st1.update 7 (.i64 q) := by
    simp only [pointers, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, State.setAll, State.set?_eq_update _ (show 7 < st1.params.length +
        st1.locals.length by rw [hLen1]; decide), Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq] at hSet
    exact hSet.symm
  have hHolds : st2.Holds [7, 0] (pointers [(q, fillTuple (⟨sizes⟩, k, a)), (ps, sizes)]) := by
    rw [hst2]
    exact .cons (State.get_update_same (by rw [hLen1]; decide))
      (.cons (by rw [State.get_update_ne (by decide), g10]) .nil)
  exact Live.finish_results (y := (fillTuple (⟨sizes⟩, k, a), sizes)) rfl hL2 hHolds

/-- `encode` succeeds on `clob.module`, and its bytes decode to a module whose
exports compute the CLOB operations exactly. -/
theorem clob_bytes : ∃ bytes, Encoding.encode clob.module = .ok bytes ∧
    ∃ m, Encoding.decode bytes = .ok m ∧
      Implements m 2 marketBuyTuple ∧ Implements m 3 fillTuple ∧
      Implements m 4 insertTuple ∧ Implements m 5 setTuple ∧
      Implements m 6 addBidTuple ∧ Implements m 7 depthTuple ∧
      Implements m 8 findTuple ∧ Implements m 9 removeTuple ∧
      Implements m 10 cancelTuple ∧ Implements m 11 applyTuple ∧ Implements m 12 runTuple ∧
      Implements m 13 stepTuple ∧ Implements m 14 outTuple ∧
      Implements m 15 fillTwiceTuple ∧ Implements m 16 fillKeepTuple := by
  obtain ⟨bytes, success, decoded⟩ :=
    Encoding.round_trip clob.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, clob.module, decoded, marketBuy_implements, fillLevel_implements,
    insertLevel_implements, setLevel_implements, addBid_implements,
    depth_implements, findLevel_implements, removeLevel_implements, cancelBid_implements,
    applyCommand_implements, runCommands_implements, stepCommand_implements,
    runOut_implements, fillTwice_implements, fillKeep_implements⟩

end Examples.Clob
