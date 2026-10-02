import Project.Gpt.Verify
import Project.Prng.Verify

/-! The `Implements` theorems of top-k sampling: the kernels `negInfs`, `insertTop`, and
`sampleFrom`, the buffer loop `topKBuffer`, and `sampleTopK`. -/

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

theorem negInfs_implements :
    Implements gpt.module 45 LeanExe.Examples.Gpt.negInfs := by
  refine Func.implements_heap gpt.funcs 43 gpt.negInfs.ir "negInfs" rfl
    LeanExe.Examples.Gpt.negInfs (by rintro _ _ _ _ rfl; rfl) ?_
  rintro k heap initial _ hHeap rfl hCap
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel
  let start : State := { params := [.i64 k], locals := [.i64 0, .i64 0, .i64 0] }
  show Triple _ (.build 1 2 3 (.get 0) (.toBits (.binF .sub (.constF 9223372036854775808)
      (.binF .div (.constF 4607182418800017408) (.constF 0))))) 4
    (fun store state => store = initial ∧ state = start) _
  refine (Stmt.build_spec (n := k) (fun _ => (-(1.0 / 0.0) : Float).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by simp [start]) hHeap hCap ⟨start, rfl⟩ ?_).mono
      (fun _ _ h => h) ?_
  · intro i store state hi hAt hFrame hIndex
    simp [Expr.eval, F64Op.apply, F64Bits.toBits_neg, F64Bits.toBits_div, hZero, hOne]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep,
    [.i64 ptr], state, by simp [gpt.negInfs.ir, Func.scratch, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : LeanExe.Examples.Gpt.negInfs k = LeanExe.build k (fun _ => -(1.0 / 0.0)) := rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `insertTop` with its four arguments as one tuple. -/
def insertTopTuple (x : Array Float × Array Float × UInt64 × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.insertTop x.1 x.2.1 x.2.2.1 x.2.2.2

/-- One step of the loop that finds the insertion position: the count of the entries not
below `x`. -/
def posStep (buf : Array Float) (x : Float) (j p : UInt64) : UInt64 :=
  if buf[j.toNat]! < x then p else p + 1

/-- Element `j` of the buffer after the insertion of `x` at `pos`. -/
def insertElem (buf : Array Float) (x : Float) (pos j : UInt64) : Float :=
  if j < pos then buf[j.toNat]! else if j = pos then x else buf[(j - 1).toNat]!

theorem insertTop_eq (buf s : Array Float) (i k : UInt64) :
    LeanExe.Examples.Gpt.insertTop buf s i k =
      LeanExe.build k (insertElem buf s[i.toNat]! (LeanExe.loop k 0 (posStep buf s[i.toNat]!))) :=
  rfl

theorem insertTop_implements : Implements gpt.module 46 insertTopTuple := by
  refine Func.implements_heap gpt.funcs 44 gpt.insertTop.ir "insertTop" rfl insertTopTuple (by
      rintro _ _ _ ⟨_, _, _, _⟩ h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain rfl := h
      rfl) ?_
  rintro ⟨buf, s, i, k⟩ heap initial _ hHeap hArgs hCap
  obtain ⟨pb, _, rfl, hBuf, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain ⟨ps, _, rfl, hS, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain rfl := hArgs
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hImports : gpt.module.imports = [] := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hB := hBuf.values
  have hSv := hS.values
  let x := s[i.toNat]!
  let start : State :=
    { params := [.i64 pb, .i64 ps, .i64 i, .i64 k]
      locals := [.f64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hParams : start.params.length = 4 := rfl
  have hLocals : start.locals.length = 10 := rfl
  have hGet1 : start.get 1 = some (.i64 ps) := rfl
  have hGet2 : start.get 2 = some (.i64 i) := rfl
  let s1 := (start.update 13 (.i64 i)).update 4 (.f64 x.toBits)
  let s2 := s1.update 5 (.i64 0)
  show Triple _ (.seq (.assign 4 (.ofBits (.read 1 (.get 2))))
    (.seq (.assign 5 (.const 0))
    (.seq (.loop 6 7 (.get 3) (.seq (.assign 8 (.ite (.ltF (.ofBits (.read 0 (.get 7))) (.getF 4))
        (.get 5) (.bin .add (.get 5) (.const 1)))) (.assign 5 (.get 8))))
    (.seq (.assign 9 (.get 5))
    (.build 10 11 12 (.get 3) (.toBits (.iteF (.ltU (.get 12) (.get 9)) (.ofBits (.read 0 (.get 12)))
      (.iteF (.eq (.get 12) (.get 9)) (.getF 4)
        (.ofBits (.read 0 (.bin .sub (.get 12) (.const 1)))))))))))) 13
    (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) ?_
  · simp [Stmt.run, Expr.eval, hGet1, hGet2, Expr.readValue_at hSv, State.set?_eq_update,
      hParams, hLocals, s1, x, getElem!_map_toBits]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s1, s2]
  have hS2 : s2.params.length = 4 ∧ s2.locals.length = 10 := by simp [s2, s1, hParams, hLocals]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [5]) (writes := [5, 8]) (init := (0 : UInt64))
    (n := k) (posStep buf x) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hS2.1, hS2.2]) ⟨s2, by simp [Expr.eval, s2, s1]; rfl⟩
    (by simp [State.Holds, Scalar.values, s2, s1, hParams, hLocals]) ?_) ?_
  · intro j p state hj hFrame hHolds hIndex hLimit
    have hState : state.params.length = 4 ∧ state.locals.length = 10 :=
      ⟨hFrame.params.trans hS2.1, hFrame.locals.trans hS2.2⟩
    have g0 : state.get 0 = some (.i64 pb) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
    have g4 : state.get 4 = some (.f64 x.toBits) :=
      (hFrame.get 4 (by decide) (by decide)).trans (by simp [s2, s1, hParams, hLocals])
    have g5 : state.get 5 = some (.i64 p) := by simpa [State.Holds, Scalar.values] using hHolds
    let a := (state.update 13 (.i64 (UInt64.ofNat j))).update 8
      (.i64 (posStep buf x (UInt64.ofNat j) p))
    let b := a.update 5 (.i64 (posStep buf x (UInt64.ofNat j) p))
    refine (Stmt.run_spec (final := b) ?_).mono (fun _ _ h => h) ?_
    · by_cases hlt : buf[(UInt64.ofNat j).toNat]! < x
      · simp [Stmt.run, Expr.eval, g0, g4, g5, hIndex, Expr.readValue_at hB, State.set?_eq_update,
          hState.1, hState.2, getElem!_map_toBits, a, b, posStep, ← F64Bits.lt_iff,
          U64Op.apply]
      · have hNot : Wasm.IEEE64.lt (buf[(UInt64.ofNat j).toNat]!).toBits x.toBits = false := by
          rw [F64Bits.lt_iff] at hlt
          simpa using hlt
        simp [Stmt.run, Expr.eval, g0, g4, g5, hIndex, Expr.readValue_at hB, State.set?_eq_update,
          hState.1, hState.2, getElem!_map_toBits, a, b, posStep, ← F64Bits.lt_iff,
          U64Op.apply]
    rintro store st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, by simp [State.Holds, Scalar.values, b, a, hState.1, hState.2]⟩
    simp only [b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  apply Triple.of_forall
  rintro store t1 ⟨hStore, hFrame1, hHolds1⟩
  subst store
  generalize hPos : LeanExe.loop k 0 (posStep buf x) = pos at hHolds1
  have h1Get5 : t1.get 5 = some (.i64 pos) := by simpa [State.Holds, Scalar.values] using hHolds1
  have hT1 : t1.params.length = 4 ∧ t1.locals.length = 10 :=
    ⟨hFrame1.params.trans hS2.1, hFrame1.locals.trans hS2.2⟩
  have h1Get0 : t1.get 0 = some (.i64 pb) :=
    (hFrame1.get 0 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
  have h1Get3 : t1.get 3 = some (.i64 k) :=
    (hFrame1.get 3 (by decide) (by decide)).trans (by simp [s2, s1]; rfl)
  have h1Get4 : t1.get 4 = some (.f64 x.toBits) :=
    (hFrame1.get 4 (by decide) (by decide)).trans (by simp [s2, s1, hParams, hLocals])
  let u1 := t1.update 9 (.i64 pos)
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get5, State.set?_eq_update, hT1.1, hT1.2, u1]
  have hU1 : u1.params.length = 4 ∧ u1.locals.length = 10 := by simp [u1, hT1.1, hT1.2]
  have hU1Get : ∀ j, j < 9 → u1.get j = t1.get j := fun j hj => by
    simp only [u1]
    rw [State.get_update_ne (by omega)]
  have hU1Get9 : u1.get 9 = some (.i64 pos) := by simp [u1, hT1.1, hT1.2]
  refine (Stmt.build_spec (n := k) (fun j => (insertElem buf x pos j).toBits) hMemory32 hImports
    hAlloc (by decide) (by decide) (by simp [hU1.1, hU1.2]) hHeap hCap
    ⟨u1, by simp [Expr.eval, hU1Get 3 (by decide), h1Get3]⟩ ?_).mono (fun _ _ h => h) ?_
  · intro j store state hj hAt hFrame hIndex
    have hKeep : ∀ m, m < 10 → state.get m = u1.get m := fun m hm =>
      hFrame.get m (by omega) (by simp; omega)
    have g0 := (hKeep 0 (by decide)).trans ((hU1Get 0 (by decide)).trans h1Get0)
    have g4 := (hKeep 4 (by decide)).trans ((hU1Get 4 (by decide)).trans h1Get4)
    have g9 := (hKeep 9 (by decide)).trans hU1Get9
    have hBs := hAt pb _ hBuf
    have hState : state.params.length = 4 ∧ state.locals.length = 10 :=
      ⟨hFrame.params.trans hU1.1, hFrame.locals.trans hU1.2⟩
    by_cases hlt : UInt64.ofNat j < pos
    · simp [Expr.eval, g0, g9, hIndex, Expr.readValue_at hBs, getElem!_map_toBits,
        insertElem, hlt, State.set?_eq_update, hState.1, hState.2]
    · by_cases heq : UInt64.ofNat j = pos
      · simp [Expr.eval, g4, g9, hIndex,
          insertElem, heq]
      · simp [Expr.eval, g0, g9, hIndex, Expr.readValue_at hBs, getElem!_map_toBits,
          insertElem, hlt, heq, U64Op.apply, State.set?_eq_update, hState.1, hState.2]
  rintro store state ⟨ptr, -, hPtr, hNew⟩
  refine ⟨_, hNew.at_, hNew.caps, hNew.borrowed, hNew.ownedKeep,
    [.i64 ptr], state, by simp [gpt.insertTop.ir, Expr.evalResults, Expr.eval, hPtr],
    ⟨ptr, rfl, ?_⟩, fun p ws h => Represent.outside_float.mpr (hNew.borrowedApart p ws h),
    fun p ws h => Represent.outside_float.mpr (hNew.ownedApart p ws h)⟩
  have hEq : insertTopTuple (buf, s, i, k) = LeanExe.build k (insertElem buf x pos) := by
    rw [← hPos]; rfl
  rw [hEq, build_map]
  exact hNew.owned

/-- `sampleFrom` with its five arguments as one tuple. -/
def sampleFromTuple (x : Array Float × Array Float × UInt64 × Float × UInt64) : UInt64 × UInt64 :=
  LeanExe.Examples.Gpt.sampleFrom x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- One step of the loop that sums the weights of the kept scores. -/
def totalStep (s : Array Float) (θ m t : Float) (i : UInt64) (acc : Float) : Float :=
  if θ ≤ s[i.toNat]! then acc + LeanExe.Examples.Gpt.exp ((s[i.toNat]! - m) / t) else acc

/-- One step of the loop that chooses the token: the running weight, the first kept token
whose running weight exceeds `target` (or `n` before it), and the last kept token. -/
def pickStep (s : Array Float) (θ m t target : Float) (n i : UInt64)
    (st : Float × UInt64 × UInt64) : Float × UInt64 × UInt64 :=
  let acc := if θ ≤ s[i.toNat]! then st.1 + LeanExe.Examples.Gpt.exp ((s[i.toNat]! - m) / t)
    else st.1
  (acc, if θ ≤ s[i.toNat]! then (if st.2.1 = n then (if target < acc then i else st.2.1) else st.2.1)
      else st.2.1,
    if θ ≤ s[i.toNat]! then i else st.2.2)

theorem sampleFrom_eq (s buf : Array Float) (k : UInt64) (t : Float) (state : UInt64) :
    LeanExe.Examples.Gpt.sampleFrom s buf k t state =
      (if (LeanExe.loop s.size.toUInt64 (0.0, s.size.toUInt64, s.size.toUInt64)
            (pickStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t
              (LeanExe.Examples.Prng.unitFloat (LeanExe.Examples.Prng.splitMix state).2 *
                LeanExe.loop s.size.toUInt64 0.0
                  (totalStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t))
              s.size.toUInt64)).2.1 = s.size.toUInt64
        then (LeanExe.loop s.size.toUInt64 (0.0, s.size.toUInt64, s.size.toUInt64)
            (pickStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t
              (LeanExe.Examples.Prng.unitFloat (LeanExe.Examples.Prng.splitMix state).2 *
                LeanExe.loop s.size.toUInt64 0.0
                  (totalStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t))
              s.size.toUInt64)).2.2
        else (LeanExe.loop s.size.toUInt64 (0.0, s.size.toUInt64, s.size.toUInt64)
            (pickStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t
              (LeanExe.Examples.Prng.unitFloat (LeanExe.Examples.Prng.splitMix state).2 *
                LeanExe.loop s.size.toUInt64 0.0
                  (totalStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t))
              s.size.toUInt64)).2.1,
        (LeanExe.Examples.Prng.splitMix state).1) := rfl

/-- The compiled body of the loop that chooses the token. -/
def pickBody : Stmt :=
  .seq (.call 5 [⟨.f64, .binF .div (.binF .sub (.ofBits (.read 0 (.get 23))) (.getF 6)) (.getF 3)⟩]
    [24])
  (.seq (.assign 25 (.iteF (.leF (.getF 5) (.ofBits (.read 0 (.get 23))))
    (.binF .add (.getF 19) (.getF 24)) (.getF 19)))
  (.seq (.assign 26 (.getF 25))
  (.seq (.assign 27 (.ite (.leF (.getF 5) (.ofBits (.read 0 (.get 23))))
    (.ite (.eq (.get 20) (.get 8)) (.ite (.ltF (.getF 18) (.getF 25)) (.get 23) (.get 20)) (.get 20))
    (.get 20)))
  (.seq (.assign 28 (.ite (.leF (.getF 5) (.ofBits (.read 0 (.get 23)))) (.get 23) (.get 21)))
  (.seq (.assign 19 (.getF 26))
  (.seq (.assign 20 (.get 27))
  (.assign 21 (.get 28))))))))

set_option maxHeartbeats 1000000 in
theorem pickBody_spec {initial : Store Unit} {ps : UInt64} {s : Array Float}
    (hS : UInt64Array.At initial ps (s.map Float.toBits)) {θ m t target : Float} {n : UInt64}
    {state : State} {j : Nat} {acc : Float} {pick last : UInt64}
    (hParams : state.params.length = 5) (hLocals : state.locals.length = 25)
    (g0 : state.get 0 = some (.i64 ps)) (g3 : state.get 3 = some (.f64 t.toBits))
    (g5 : state.get 5 = some (.f64 θ.toBits)) (g6 : state.get 6 = some (.f64 m.toBits))
    (g8 : state.get 8 = some (.i64 n)) (g18 : state.get 18 = some (.f64 target.toBits))
    (g19 : state.get 19 = some (.f64 acc.toBits)) (g20 : state.get 20 = some (.i64 pick))
    (g21 : state.get 21 = some (.i64 last))
    (hIndex : state.get 23 = some (.i64 (UInt64.ofNat j))) (hJ : (UInt64.ofNat j).toNat = j) :
    Triple gpt.module pickBody 29 (fun store st => store = initial ∧ st = state)
      (fun store st => store = initial ∧ State.Frame 29 [19, 20, 21, 24, 25, 26, 27, 28] state st ∧
        st.Holds [19, 20, 21] (Scalar.values (pickStep s θ m t target n (UInt64.ofNat j)
          (acc, pick, last)))) := by
  let x := s[j]!
  let d := (x - m) / t
  let e := LeanExe.Examples.Gpt.exp d
  let r := pickStep s θ m t target n (UInt64.ofNat j) (acc, pick, last)
  let a := state.update 29 (.i64 (UInt64.ofNat j))
  let b := a.update 24 (.f64 e.toBits)
  let c1 := (b.update 29 (.i64 (UInt64.ofNat j))).update 25 (.f64 r.1.toBits)
  let c2 := c1.update 26 (.f64 r.1.toBits)
  let c3 := (c2.update 29 (.i64 (UInt64.ofNat j))).update 27 (.i64 r.2.1)
  let c4 := (c3.update 29 (.i64 (UInt64.ofNat j))).update 28 (.i64 r.2.2)
  let c5 := c4.update 19 (.f64 r.1.toBits)
  let c6 := c5.update 20 (.i64 r.2.1)
  let f := c6.update 21 (.i64 r.2.2)
  have hA : a.params.length = 5 ∧ a.locals.length = 25 := by simp [a, hParams, hLocals]
  refine Stmt.seq_spec (exp_call rfl (afterArgs := a) (next := b) (d := d) ?_ ?_) ?_
  · simp [Expr.evalResults, Expr.eval, g0, g3, g6, hIndex, Expr.readValue_at hS,
      State.set?_eq_update, hParams, hLocals, F64Op.apply, getElem!_map_toBits, d, x, a, hJ,
      F64Bits.toBits_sub, F64Bits.toBits_div]
  · simp [State.setAll, State.set?_eq_update, b, e, hA.1, hA.2]
  have hFrameF : State.Frame 29 [19, 20, 21, 24, 25, 26, 27, 28] state f := by
    simp only [f, c6, c5, c4, c3, c2, c1, b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  have hHoldsF : f.Holds [19, 20, 21] (Scalar.values (pickStep s θ m t target n (UInt64.ofNat j)
      (acc, pick, last))) := by
    show f.Holds [19, 20, 21] (Scalar.values (r.1, r.2.1, r.2.2))
    simp [State.Holds, Scalar.values, f, c6, c5, c4, c3, c2, c1, b, a, hParams, hLocals]
  refine (Stmt.run_spec (final := f) ?_).mono (fun _ _ h => h)
    fun store st h => ⟨h.1, h.2 ▸ hFrameF, h.2 ▸ hHoldsF⟩
  · by_cases hle : θ ≤ x
    · by_cases hp : pick = n
      · by_cases hlt : target < acc + e
        · have hBits : Wasm.IEEE64.lt target.toBits (Wasm.IEEE64.add acc.toBits e.toBits) = true := by
            rw [← F64Bits.toBits_add, ← F64Bits.lt_iff]; exact hlt
          simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
            State.update_locals_length, State.get_update_ne, hParams, hLocals, b, a, c1, c2, c3,
            c4, c5, c6, f, g0, g5, g8, g18, g19, g20, hIndex, Expr.readValue_at hS,
            getElem!_map_toBits, F64Op.apply, r, pickStep, x, hle, hp, hlt, hJ, ← F64Bits.le_iff,
            F64Bits.toBits_add, e, d, hBits]
        · have hBits : Wasm.IEEE64.lt target.toBits (Wasm.IEEE64.add acc.toBits e.toBits) = false := by
            rw [← F64Bits.toBits_add]
            rw [F64Bits.lt_iff] at hlt
            simpa using hlt
          simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
            State.update_locals_length, State.get_update_ne, hParams, hLocals, b, a, c1, c2, c3,
            c4, c5, c6, f, g0, g5, g8, g18, g19, g20, hIndex, Expr.readValue_at hS,
            getElem!_map_toBits, F64Op.apply, r, pickStep, x, hle, hp, hlt, hJ, ← F64Bits.le_iff,
            F64Bits.toBits_add, e, d, hBits]
      · simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
          State.update_locals_length, State.get_update_ne, hParams, hLocals, b, a, c1, c2, c3,
          c4, c5, c6, f, g0, g5, g8, g19, g20, hIndex, Expr.readValue_at hS,
          getElem!_map_toBits, F64Op.apply, r, pickStep, x, hle, hp, hJ, ← F64Bits.le_iff,
          F64Bits.toBits_add, e, d]
    · simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
        State.update_locals_length, State.get_update_ne, hParams, hLocals, b, a, c1, c2, c3,
        c4, c5, c6, f, g0, g5, g19, g20, g21, hIndex, Expr.readValue_at hS,
        getElem!_map_toBits, F64Op.apply, r, pickStep, x, hle, hJ, ← F64Bits.le_iff]

theorem splitMix_gpt : ImplementsPure gpt.module 43 LeanExe.Examples.Prng.splitMix :=
  Project.Prng.splitMix_pure gpt.funcs 41 rfl

theorem unitFloat_gpt : ImplementsPure gpt.module 44 LeanExe.Examples.Prng.unitFloat :=
  Project.Prng.unitFloat_pure gpt.funcs 42 rfl

set_option maxHeartbeats 2000000 in
theorem sampleFrom_implements : Implements gpt.module 48 sampleFromTuple := by
  refine Func.implements gpt.funcs 46 gpt.sampleFrom.ir "sampleFrom" rfl sampleFromTuple
    (by
      rintro _ _ _ ⟨_, _, _, _, _⟩ h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain rfl := h
      rfl) ?_
  rintro ⟨s, buf, k, t, state⟩ heap initial _ hHeap hArgs
  obtain ⟨ps, _, rfl, hS, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain ⟨pb, _, rfl, hBuf, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain rfl := hArgs
  have hZero : (0.0 : Float).toBits = 0 := by decide +kernel
  have hSv := hS.values
  have hBv := hBuf.values
  have hLength := hSv.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength
  let θ := buf[(k - 1).toNat]!
  let m := buf[(0 : UInt64).toNat]!
  let n := s.size.toUInt64
  let start : State :=
    { params := [.i64 ps, .i64 pb, .i64 k, .f64 t.toBits, .i64 state]
      locals := [.f64 0, .f64 0, .i64 0, .i64 0, .f64 0, .i64 0, .i64 0, .f64 0, .f64 0, .f64 0,
        .i64 0, .i64 0, .f64 0, .f64 0, .f64 0, .i64 0, .i64 0, .i64 0, .i64 0, .f64 0, .f64 0,
        .f64 0, .i64 0, .i64 0, .i64 0] }
  have hParams : start.params.length = 5 := rfl
  have hLocals : start.locals.length = 25 := rfl
  have sg0 : start.get 0 = some (.i64 ps) := rfl
  have sg1 : start.get 1 = some (.i64 pb) := rfl
  have sg2 : start.get 2 = some (.i64 k) := rfl
  let s1 := (start.update 29 (.i64 (k - 1))).update 5 (.f64 θ.toBits)
  let s2 := (s1.update 29 (.i64 0)).update 6 (.f64 m.toBits)
  let s3 := s2.update 7 (.i64 (UInt64.ofNat s.size))
  let s4 := s3.update 8 (.i64 (UInt64.ofNat s.size))
  let s5 := s4.update 9 (.f64 (0.0 : Float).toBits)
  have hWidth : gpt.sampleFrom.ir.width = 1 := by decide +kernel
  have hScratch : gpt.sampleFrom.ir.scratch = 29 := by decide +kernel
  simp only [Func.state, Func.locals, hWidth, hScratch]
  show Triple _ gpt.sampleFrom.ir.body _
    (fun store state => store = initial ∧ state = start) _
  -- The threshold, the maximum, and the number of scores.
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s5) ?_) ?_
  · simp [Stmt.run, Expr.eval, sg1, sg2, Expr.readValue_at hBv, State.set?_eq_update, hParams,
      hLocals, s1, θ, getElem!_map_toBits, U64Op.apply]
  · simp [Stmt.run, Expr.eval, sg1, Expr.readValue_at hBv, State.set?_eq_update, hParams, hLocals,
      s2, s1, m, getElem!_map_toBits]
  · simp [Stmt.run, Expr.eval, sg0, hLength, hSv.lengthRead, State.set?_eq_update,
      hParams, hLocals, s3, s2, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s4, s3, s2, s1]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hParams, hLocals, s5, s4, s3, s2, s1, hZero]
  have hS5 : s5.params.length = 5 ∧ s5.locals.length = 25 := by
    simp [s5, s4, s3, s2, s1, hParams, hLocals]
  have hS5Get : ∀ j, j ∈ [0, 1, 2, 3, 4] → s5.get j = start.get j := fun j hj => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    simp only [s5, s4, s3, s2, s1]
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [State.get_update_ne]
  have h5Get5 : s5.get 5 = some (.f64 θ.toBits) := by simp [s5, s4, s3, s2, s1, hParams, hLocals]
  have h5Get6 : s5.get 6 = some (.f64 m.toBits) := by simp [s5, s4, s3, s2, s1, hParams, hLocals]
  have h5Get8 : s5.get 8 = some (.i64 (UInt64.ofNat s.size)) := by
    simp [s5, s4, s3, s2, s1, hParams, hLocals]
  -- The total weight of the kept scores.
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [9]) (writes := [9, 12, 13]) (init := (0.0 : Float))
    (n := n) (totalStep s θ m t) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [hS5.1, hS5.2]) ⟨s5, by simp [Expr.eval, h5Get8]; rfl⟩
    (by simp [State.Holds, Scalar.values, s5, s4, s3, s2, s1, hParams, hLocals]) ?_) ?_
  · intro j acc state hj hFrame hHolds hIndex hLimit
    have hState : state.params.length = 5 ∧ state.locals.length = 25 :=
      ⟨hFrame.params.trans hS5.1, hFrame.locals.trans hS5.2⟩
    have hKeep : ∀ i, i < 9 → state.get i = s5.get i := fun i hi =>
      hFrame.get i (by omega) (by simp; omega)
    have g0 : state.get 0 = some (.i64 ps) := (hKeep 0 (by decide)).trans ((hS5Get 0 (by simp)).trans sg0)
    have g3 : state.get 3 = some (.f64 t.toBits) := (hKeep 3 (by decide)).trans ((hS5Get 3 (by simp)).trans rfl)
    have g5 : state.get 5 = some (.f64 θ.toBits) := (hKeep 5 (by decide)).trans h5Get5
    have g6 : state.get 6 = some (.f64 m.toBits) := (hKeep 6 (by decide)).trans h5Get6
    have g9 : state.get 9 = some (.f64 acc.toBits) := by simpa [State.Holds, Scalar.values] using hHolds
    have hJ : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by
      have := UInt64.toNat_lt n
      omega)
    let x := s[j]!
    let d := (x - m) / t
    let e := LeanExe.Examples.Gpt.exp d
    let v := totalStep s θ m t (UInt64.ofNat j) acc
    let a := state.update 29 (.i64 (UInt64.ofNat j))
    let b := a.update 12 (.f64 e.toBits)
    let c := (b.update 29 (.i64 (UInt64.ofNat j))).update 13 (.f64 v.toBits)
    let f := c.update 9 (.f64 v.toBits)
    have hA : a.params.length = 5 ∧ a.locals.length = 25 := by simp [a, hState.1, hState.2]
    have hB : b.params.length = 5 ∧ b.locals.length = 25 := by simp [b, hA.1, hA.2]
    refine Stmt.seq_spec (exp_call rfl (afterArgs := a) (next := b) (d := d) ?_ ?_) ?_
    · simp [Expr.evalResults, Expr.eval, g0, g3, g6, hIndex, Expr.readValue_at hSv,
        State.set?_eq_update, hState.1, hState.2, F64Op.apply, getElem!_map_toBits, d, x, a, hJ,
        F64Bits.toBits_sub, F64Bits.toBits_div]
    · simp [State.setAll, State.set?_eq_update, b, e, hA.1, hA.2]
    refine (Stmt.run_spec (final := f) ?_).mono (fun _ _ h => h) ?_
    · by_cases hle : θ ≤ x
      · simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
          State.update_locals_length, State.get_update_ne, hState.1, hState.2, b, a, c, f, g0, g5,
          g9, hIndex, Expr.readValue_at hSv, getElem!_map_toBits, F64Op.apply, v, totalStep, x, hle, hJ,
          ← F64Bits.le_iff, F64Bits.toBits_add, e, d]
      · simp [Stmt.run, Expr.eval, State.set?_eq_update, State.update_params_length,
          State.update_locals_length, State.get_update_ne, hState.1, hState.2, b, a, c, f, g0, g5,
          g9, hIndex, Expr.readValue_at hSv, getElem!_map_toBits, F64Op.apply, v, totalStep, x, hle, hJ,
          ← F64Bits.le_iff]
    rintro store st ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, by simp [State.Holds, Scalar.values, f, c, b, a, v, hState.1, hState.2]⟩
    simp only [f, c, b, a]
    repeat refine State.Frame.update ?_ (by simp)
    exact State.Frame.refl _ _ _
  apply Triple.of_forall
  rintro store t1 ⟨hStore, hFrame1, hHolds1⟩
  subst store
  generalize hTotal : LeanExe.loop n 0.0 (totalStep s θ m t) = total at hHolds1
  have h1Get9 : t1.get 9 = some (.f64 total.toBits) := by
    simpa [State.Holds, Scalar.values] using hHolds1
  have hT1 : t1.params.length = 5 ∧ t1.locals.length = 25 :=
    ⟨hFrame1.params.trans hS5.1, hFrame1.locals.trans hS5.2⟩
  have hT1Get : ∀ i, i < 9 → t1.get i = s5.get i := fun i hi =>
    hFrame1.get i (by omega) (by simp; omega)
  have t0 : t1.get 0 = some (.i64 ps) := (hT1Get 0 (by decide)).trans ((hS5Get 0 (by simp)).trans sg0)
  have t3 : t1.get 3 = some (.f64 t.toBits) :=
    (hT1Get 3 (by decide)).trans ((hS5Get 3 (by simp)).trans rfl)
  have t4 : t1.get 4 = some (.i64 state) :=
    (hT1Get 4 (by decide)).trans ((hS5Get 4 (by simp)).trans rfl)
  have t5 : t1.get 5 = some (.f64 θ.toBits) := (hT1Get 5 (by decide)).trans h5Get5
  have t6 : t1.get 6 = some (.f64 m.toBits) := (hT1Get 6 (by decide)).trans h5Get6
  have t8 : t1.get 8 = some (.i64 (UInt64.ofNat s.size)) := (hT1Get 8 (by decide)).trans h5Get8
  -- The draw: one SplitMix64 step and its word as a float in `[0, 1)`.
  let next := (LeanExe.Examples.Prng.splitMix state).1
  let w := (LeanExe.Examples.Prng.splitMix state).2
  let uu := LeanExe.Examples.Prng.unitFloat w
  let target := uu * total
  let u1 := t1.update 14 (.f64 total.toBits)
  let u2 := (u1.update 16 (.i64 w)).update 15 (.i64 next)
  let u3 := u2.update 17 (.f64 uu.toBits)
  let u4 := u3.update 18 (.f64 target.toBits)
  let u5 := u4.update 19 (.f64 (0.0 : Float).toBits)
  let u6 := u5.update 20 (.i64 (UInt64.ofNat s.size))
  let u7 := u6.update 21 (.i64 (UInt64.ofNat s.size))
  have hImports : gpt.module.imports.length = 0 := rfl
  refine Stmt.seq_spec (Stmt.run_spec (final := u1) ?_) <|
    Stmt.seq_spec (Stmt.callPure_spec splitMix_gpt (f := gpt.splitMix.ir.function (2 + 41)) rfl
      (by rw [hImports]; exact compile_funcs (funcs := gpt.funcs) (i := 41) rfl) rfl (x := state)
      (afterArgs := u1) (next := u2) ?_ ?_) <|
    Stmt.seq_spec (Stmt.callPure_spec unitFloat_gpt (f := gpt.unitFloat.ir.function (2 + 42)) rfl
      (by rw [hImports]; exact compile_funcs (funcs := gpt.funcs) (i := 42) rfl) rfl (x := w)
      (afterArgs := u2) (next := u3) ?_ ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u4) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u5) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u6) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := u7) ?_) ?_
  · simp [Stmt.run, Expr.eval, h1Get9, State.set?_eq_update, hT1.1, hT1.2, u1]
  · simp [Expr.evalResults, Expr.eval, u1, t4, Scalar.values]
  · simp [State.setAll, State.set?_eq_update, u2, u1, hT1.1, hT1.2, Scalar.values, next, w]
  · simp [Expr.evalResults, Expr.eval, u2, u1, Scalar.values, hT1.1, hT1.2]
  · simp [State.setAll, State.set?_eq_update, u3, u2, u1, hT1.1, hT1.2, Scalar.values, uu]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, u4, u3, u2, u1, hT1.1, hT1.2, F64Op.apply,
      F64Bits.toBits_mul, target]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, u5, u4, u3, u2, u1, hT1.1, hT1.2, hZero]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2, t8]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, u7, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2, t8]
  have hU7 : u7.params.length = 5 ∧ u7.locals.length = 25 := by
    simp [u7, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2]
  have hU7Get : ∀ i, i < 14 → u7.get i = t1.get i := fun i hi => by
    simp only [u7, u6, u5, u4, u3, u2, u1]
    repeat rw [State.get_update_ne (by omega)]
  have h7Get15 : u7.get 15 = some (.i64 next) := by simp [u7, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2]
  have h7Get18 : u7.get 18 = some (.f64 target.toBits) := by
    simp [u7, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2]
  -- The choice of the token.
  refine (Stmt.loop_spec (vars := [19, 20, 21]) (writes := [19, 20, 21, 24, 25, 26, 27, 28])
    (init := ((0.0 : Float), n, n)) (n := n) (pickStep s θ m t target n) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp [hU7.1, hU7.2])
    ⟨u7, by simp [Expr.eval, hU7Get 8 (by decide), t8]; rfl⟩
    (by simp [State.Holds, Scalar.values, u7, u6, u5, u4, u3, u2, u1, hT1.1, hT1.2]; rfl)
    ?_).mono (fun _ _ h => h) ?_
  · intro j st state hj hFrame hHolds hIndex hLimit
    obtain ⟨acc, pick, last⟩ := st
    have hState : state.params.length = 5 ∧ state.locals.length = 25 :=
      ⟨hFrame.params.trans hU7.1, hFrame.locals.trans hU7.2⟩
    have hKeep : ∀ i, i < 19 → state.get i = u7.get i := fun i hi =>
      hFrame.get i (by omega) (by simp; omega)
    simp [State.Holds, Scalar.values] at hHolds
    obtain ⟨g19, g20, g21⟩ := hHolds
    exact pickBody_spec hSv hState.1 hState.2
      ((hKeep 0 (by decide)).trans ((hU7Get 0 (by decide)).trans t0))
      ((hKeep 3 (by decide)).trans ((hU7Get 3 (by decide)).trans t3))
      ((hKeep 5 (by decide)).trans ((hU7Get 5 (by decide)).trans t5))
      ((hKeep 6 (by decide)).trans ((hU7Get 6 (by decide)).trans t6))
      ((hKeep 8 (by decide)).trans ((hU7Get 8 (by decide)).trans t8))
      ((hKeep 18 (by decide)).trans h7Get18) g19 g20 g21 hIndex
      (UInt64.toNat_ofNat_of_lt' (show j < 2 ^ 64 by
        have := UInt64.toNat_lt n
        omega))
  rintro store t2 ⟨rfl, hFrame2, hHolds2⟩
  generalize hPick : LeanExe.loop n ((0.0 : Float), n, n) (pickStep s θ m t target n) = r at hHolds2
  obtain ⟨acc, pick, last⟩ := r
  simp [State.Holds, Scalar.values] at hHolds2
  obtain ⟨-, h20, h21⟩ := hHolds2
  have hKeep2 : ∀ i, i < 19 → t2.get i = u7.get i := fun i hi =>
    hFrame2.get i (by omega) (by simp; omega)
  have h8 := (hKeep2 8 (by decide)).trans ((hU7Get 8 (by decide)).trans t8)
  have h15 := (hKeep2 15 (by decide)).trans h7Get15
  refine ⟨rfl, [.i64 (if pick = n then last else pick), .i64 next], t2, ?_, ?_⟩
  · simp [gpt.sampleFrom.ir, Expr.evalResults, Expr.eval, h8, h15, h20, h21]
    split_ifs <;> rfl
  · subst hTotal
    have hP : LeanExe.loop s.size.toUInt64 ((0.0 : Float), s.size.toUInt64, s.size.toUInt64)
        (pickStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t
          (LeanExe.Examples.Prng.unitFloat (LeanExe.Examples.Prng.splitMix state).2 *
            LeanExe.loop s.size.toUInt64 0.0
              (totalStep s buf[(k - 1).toNat]! buf[(0 : UInt64).toNat]! t))
          s.size.toUInt64) = (acc, pick, last) := hPick
    rw [sampleFromTuple, sampleFrom_eq, hP]
    rfl

/-- `topKBuffer` with its two arguments as one tuple. -/
def topKBufferTuple (x : Array Float × UInt64) : Array Float :=
  LeanExe.Examples.Gpt.topKBuffer x.1 x.2

theorem topKBuffer_implements : Implements gpt.module 47 topKBufferTuple := by
  refine Func.implements_heap gpt.funcs 45 gpt.topKBuffer.ir "topKBuffer" rfl
    topKBufferTuple
    (by
      rintro _ _ _ ⟨_, _⟩ h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain rfl := h
      rfl) ?_
  rintro ⟨s, top⟩ heap initial _ hHeap hArgs hCap
  obtain ⟨pS, _, rfl, hS, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain rfl := hArgs
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hMemory32 : gpt.module.memIs64 = false := rfl
  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl
  have hNeg : gpt.module.funcs[45 - gpt.module.imports.length]? =
      some (gpt.negInfs.ir.function (2 + 43)) :=
    compile_funcs (funcs := gpt.funcs) (i := 43) rfl
  have hInsert : gpt.module.funcs[46 - gpt.module.imports.length]? =
      some (gpt.insertTop.ir.function (2 + 44)) :=
    compile_funcs (funcs := gpt.funcs) (i := 44) rfl
  let init := LeanExe.Examples.Gpt.negInfs top
  let start : State :=
    { params := [.i64 pS, .i64 top]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 11 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have sg0 : start.get 0 = some (.i64 pS) := rfl
  have sg1 : start.get 1 = some (.i64 top) := rfl
  have hWidth : gpt.topKBuffer.ir.width = 1 := by decide +kernel
  have hScratch : gpt.topKBuffer.ir.scratch = 10 := by decide +kernel
  simp only [Func.state, Func.locals, hWidth, hScratch]
  show Triple _ gpt.topKBuffer.ir.body _
    (fun store state => store = initial ∧ state = start) _
  -- The buffer of negative infinities.
  refine Live.call_seq negInfs_implements rfl hNeg rfl (Live.start hHeap) hCap
    (x := top) (afterArgs := start)
    (vals := [.i64 top])
    (Expr.evalResults_get sg1 Expr.evalResults_nil) rfl
    (by rw [hStart]; decide) fun heap1 pInit store1 hLive1 => ?_
  let s1 := start.update 2 (.i64 pInit)
  have hS1 : s1.params.length + s1.locals.length = 11 := by rw [hLen, hStart]
  have f1_0 : s1.get 0 = some (.i64 pS) :=
    (State.get_update_ne (state := start) (j := 0) (index := 2) (by decide)).trans sg0
  have f1_1 : s1.get 1 = some (.i64 top) :=
    (State.get_update_ne (state := start) (j := 1) (index := 2) (by decide)).trans sg1
  have f1_2 : s1.get 2 = some (.i64 pInit) :=
    State.get_update_same (state := start) (by rw [hStart]; decide)
  -- The number of scores.
  have hA1 := (hLive1.borrowed pS _ hS Apart.nil).values
  have hLength1 := hA1.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength1
  let s2 := s1.update 3 (.i64 (UInt64.ofNat s.size))
  have hS2 : s2.params.length + s2.locals.length = 11 := by rw [hLen, hS1]
  have f2 : ∀ j, j ≠ 3 → s2.get j = s1.get j := fun j hj =>
    State.get_update_ne (state := s1) (j := j) (index := 3) hj
  refine Stmt.seq_spec (Stmt.run_spec (final := s2) (by
    simp [Stmt.run, Expr.eval, sg0, s2, s1, hLength1, hA1.lengthRead,
      State.set?_eq_update _ (show 3 < (start.update 2 (.i64 pInit)).params.length +
        (start.update 2 (.i64 pInit)).locals.length by rw [hLen, hStart]; decide)])) ?_
  -- Each score inserted into the buffer.
  refine Live.arrayLoop insertTop_implements rfl hInsert rfl hMemory32 hImports hAlloc
    hRelease (by decide) (by decide) (by decide) (by decide) (by rw [hS2]; decide)
    hLive1 hCap ((f2 2 (by decide)).trans f1_2)
    (hLive1.tempsOwned _ (List.mem_cons_self ..)).borrowed (init := init)
    (fun _ st hF => ⟨_, Expr.eval_get ((hF.get 3 (by decide) (by decide)).trans
      (State.get_update_same (state := s1) (by rw [hS1]; decide)))⟩)
    (fun l x => (x, s, l, top))
    (fun k p _ _ st _ hF hI hSt hL =>
      ⟨[.i64 p, .i64 pS, .i64 (UInt64.ofNat k), .i64 top], st,
        (Expr.evalResults_get hSt <|
          Expr.evalResults_get ((hF.get 0 (by decide) (by decide)).trans ((f2 0 (by decide)).trans f1_0)) <|
          Expr.evalResults_get hI <|
          Expr.evalResults_get ((hF.get 1 (by decide) (by decide)).trans ((f2 1 (by decide)).trans f1_1)) <|
          Expr.evalResults_nil),
        ⟨[.i64 p], _, rfl, ⟨p, rfl, (hL.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩,
          [.i64 pS], _, rfl, ⟨pS, rfl, hL.borrowed pS _ hS Apart.nil⟩, rfl⟩⟩)
    fun heap3 pl store3 s3 hLive3 hFrame3 hState3 => ?_
  have hS3 : s3.params.length + s3.locals.length = 11 := by
    rw [hFrame3.params, hFrame3.locals]; exact hS2
  let s4 := s3.update 9 (.i64 pl)
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, hState3, s4, State.set?_eq_update _ (show 9 < s3.params.length +
      s3.locals.length by rw [hS3]; decide)])) ?_
  -- The release of the buffer of negative infinities.
  have r2 : s4.get 2 = some (.i64 pInit) :=
    (State.get_update_ne (state := s3) (j := 2) (index := 9) (by decide)).trans
      ((hFrame3.get 2 (by decide) (by decide)).trans ((f2 2 (by decide)).trans f1_2))
  refine hLive3.releaseSecond_last hImports hRelease r2 fun storeR0 hLiveR0 => ?_
  obtain ⟨heap', hAt', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=
    hLiveR0.finish
  exact ⟨heap', hAt', hCaps', hKeepB, hKeepO, [.i64 pl], s4,
    by simp [gpt.topKBuffer.ir, Expr.evalResults, Expr.eval, s4,
      State.get_update_same, hS3], hOwned, hOutB, hOutO⟩


/-- `sampleTopK` with its four arguments as one tuple. -/
def sampleTopKTuple (x : Array Float × UInt64 × Float × UInt64) : UInt64 × UInt64 :=
  LeanExe.Examples.Gpt.sampleTopK x.1 x.2.1 x.2.2.1 x.2.2.2

theorem sampleTopK_implements : Implements gpt.module 49 sampleTopKTuple := by
  refine Func.implements_heap gpt.funcs 47 gpt.sampleTopK.ir "sampleTopK" rfl sampleTopKTuple
    (by
      rintro _ _ _ ⟨_, _, _, _⟩ h
      obtain ⟨_, _, rfl, -, h⟩ := Represent.borrowed_float_pair h
      obtain rfl := h
      rfl) ?_
  rintro ⟨s, top, t, seed⟩ heap initial _ hHeap hArgs hCap
  obtain ⟨pS, _, rfl, hS, hArgs⟩ := Represent.borrowed_float_pair hArgs
  obtain rfl := hArgs
  let k1 : UInt64 := if top = 0 then 1 else top
  let buf := topKBufferTuple (s, k1)
  let r := sampleFromTuple (s, buf, k1, t, seed)
  have hImports : gpt.module.imports = [] := rfl
  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl
  have hBuffer : gpt.module.funcs[47 - gpt.module.imports.length]? =
      some (gpt.topKBuffer.ir.function (2 + 45)) :=
    compile_funcs (funcs := gpt.funcs) (i := 45) rfl
  have hSample : gpt.module.funcs[48 - gpt.module.imports.length]? =
      some (gpt.sampleFrom.ir.function (2 + 46)) :=
    compile_funcs (funcs := gpt.funcs) (i := 46) rfl
  let start : State :=
    { params := [.i64 pS, .i64 top, .f64 t.toBits, .i64 seed]
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0] }
  have hStart : start.params.length + start.locals.length = 10 := rfl
  have hLen : ∀ (s : State) (j : Nat) (v : Value),
      (s.update j v).params.length + (s.update j v).locals.length =
        s.params.length + s.locals.length := fun s j v => by
    simp [State.update_params_length, State.update_locals_length]
  have sg0 : start.get 0 = some (.i64 pS) := rfl
  have sg1 : start.get 1 = some (.i64 top) := rfl
  have sg2 : start.get 2 = some (.f64 t.toBits) := rfl
  have sg3 : start.get 3 = some (.i64 seed) := rfl
  have hWidth : gpt.sampleTopK.ir.width = 0 := by decide +kernel
  simp only [Func.state, Func.locals, hWidth, List.replicate_zero, List.append_nil]
  show Triple _ gpt.sampleTopK.ir.body _
    (fun store state => store = initial ∧ state = start) _
  -- `k`, raised to 1 if it is 0.
  let s1 := start.update 4 (.i64 k1)
  have hS1 : s1.params.length + s1.locals.length = 10 := by rw [hLen, hStart]
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) (by
    by_cases h0 : top = 0 <;> simp [Stmt.run, Expr.eval, sg1, s1, k1, h0,
      State.set?_eq_update _ (show 4 < start.params.length + start.locals.length by
        rw [hStart]; decide)])) ?_
  -- The buffer of the `k1` largest scores.
  have f1_0 : s1.get 0 = some (.i64 pS) :=
    (State.get_update_ne (state := start) (j := 0) (index := 4) (by decide)).trans sg0
  have f1_4 : s1.get 4 = some (.i64 k1) :=
    State.get_update_same (state := start) (by rw [hStart]; decide)
  refine Live.call_seq topKBuffer_implements rfl hBuffer rfl (Live.start hHeap) hCap
    (x := (s, k1)) (afterArgs := s1) (vals := [.i64 pS, .i64 k1])
    (Expr.evalResults_get f1_0 <| Expr.evalResults_get f1_4 <| Expr.evalResults_nil)
    ⟨[.i64 pS], _, rfl, ⟨pS, rfl, hS⟩, rfl⟩
    (by rw [hS1]; decide) fun heap2 pBuf store2 hLive2 => ?_
  -- The draw.
  let s2 := s1.update 5 (.i64 pBuf)
  have hS2 : s2.params.length + s2.locals.length = 10 := by rw [hLen, hS1]
  have f2 : ∀ j, j ≠ 5 → s2.get j = s1.get j := fun j hj =>
    State.get_update_ne (state := s1) (j := j) (index := 5) hj
  have f1 : ∀ j, j ≠ 4 → s1.get j = start.get j := fun j hj =>
    State.get_update_ne (state := start) (j := j) (index := 4) hj
  let s3 := (s2.update 7 (.i64 r.2)).update 6 (.i64 r.1)
  have hS3 : s3.params.length + s3.locals.length = 10 := by rw [hLen, hLen, hS2]
  refine Live.callScalar_seq sampleFrom_implements rfl hSample rfl hLive2 hCap
    (x := (s, buf, k1, t, seed)) (afterArgs := s2) (after := s3)
    (vals := [.i64 pS, .i64 pBuf, .i64 k1, .f64 t.toBits, .i64 seed])
    (Expr.evalResults_get ((f2 0 (by decide)).trans f1_0) <|
      Expr.evalResults_get (State.get_update_same (state := s1) (by rw [hS1]; decide)) <|
      Expr.evalResults_get ((f2 4 (by decide)).trans f1_4) <|
      Expr.evalResults_getF (((f2 2 (by decide)).trans (f1 2 (by decide))).trans sg2) <|
      Expr.evalResults_get (((f2 3 (by decide)).trans (f1 3 (by decide))).trans sg3) <|
      Expr.evalResults_nil)
    ⟨[.i64 pS], _, rfl, ⟨pS, rfl, hLive2.borrowed pS _ hS Apart.nil⟩, [.i64 pBuf], _, rfl,
      ⟨pBuf, rfl, (hLive2.tempsOwned _ (List.mem_cons_self ..)).borrowed⟩, rfl⟩
    (by
      show s2.setAll [7, 6] [.i64 r.2, .i64 r.1] = some s3
      simp [State.setAll, State.set?_eq_update _ (show 7 < s2.params.length + s2.locals.length by
        rw [hS2]; decide), State.set?_eq_update _ (show 6 < (s2.update 7 (.i64 r.2)).params.length +
          (s2.update 7 (.i64 r.2)).locals.length by rw [hLen, hS2]; decide), s3])
    fun heap3 store3 hLive3 => ?_
  -- The token and the state, and the release of the buffer.
  have f3_6 : s3.get 6 = some (.i64 r.1) :=
    State.get_update_same (state := s2.update 7 (.i64 r.2)) (by rw [hLen, hS2]; decide)
  have f3_7 : s3.get 7 = some (.i64 r.2) :=
    (State.get_update_ne (state := s2.update 7 (.i64 r.2)) (j := 7) (index := 6) (by decide)).trans
      (State.get_update_same (state := s2) (by rw [hS2]; decide))
  let s4 := s3.update 8 (.i64 r.1)
  have hS4 : s4.params.length + s4.locals.length = 10 := by rw [hLen, hS3]
  let s5 := s4.update 9 (.i64 r.2)
  refine Stmt.seq_spec (Stmt.run_spec (final := s4) (by
    simp [Stmt.run, Expr.eval, f3_6, s4, State.set?_eq_update _
      (show 8 < s3.params.length + s3.locals.length by rw [hS3]; decide)])) ?_
  have f4_7 : s4.get 7 = some (.i64 r.2) :=
    (State.get_update_ne (state := s3) (j := 7) (index := 8) (by decide)).trans f3_7
  refine Stmt.seq_spec (Stmt.run_spec (final := s5) (by
    simp [Stmt.run, Expr.eval, f4_7, s5, State.set?_eq_update _
      (show 9 < s4.params.length + s4.locals.length by rw [hS4]; decide)])) ?_
  have f5_5 : s5.get 5 = some (.i64 pBuf) :=
    (State.get_update_ne (state := s4) (j := 5) (index := 9) (by decide)).trans <|
      (State.get_update_ne (state := s3) (j := 5) (index := 8) (by decide)).trans <|
      (State.get_update_ne (state := s2.update 7 (.i64 r.2)) (j := 5) (index := 6) (by decide)).trans <|
      (State.get_update_ne (state := s2) (j := 5) (index := 7) (by decide)).trans <|
      State.get_update_same (state := s1) (by rw [hS1]; decide)
  have f5_8 : s5.get 8 = some (.i64 r.1) :=
    (State.get_update_ne (state := s4) (j := 8) (index := 9) (by decide)).trans
      (State.get_update_same (state := s3) (by rw [hS3]; decide))
  have f5_9 : s5.get 9 = some (.i64 r.2) :=
    State.get_update_same (state := s4) (by rw [hS4]; decide)
  refine (hLive3.releaseFirst hImports hRelease f5_5).mono (fun _ _ h => h) ?_
  intro store4 st h
  obtain ⟨hL, hst⟩ := h
  refine ⟨_, hL.at_, hL.caps,
    fun p ws h => hL.borrowed p ws h Apart.nil, fun p ws h => hL.owned p ws h Apart.nil,
    [.i64 r.1, .i64 r.2], s5, ?_, rfl, fun _ _ _ => Represent.outside_scalar,
    fun _ _ _ => Represent.outside_scalar⟩
  · rw [hst]
    exact Expr.evalResults_get f5_8 <| Expr.evalResults_get f5_9 <| Expr.evalResults_nil

end Project.Gpt
