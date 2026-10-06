import Examples.TreeLookup.Module
import Examples.TreeLookup.Spec
import LeanExe.IR.ArrayLiteral
import LeanExe.IR.Correct
import LeanExe.IR.Loop
import LeanExe.IR.Words
import LeanExe.Encoding.RoundTrip

/-! The bytes of `treeLookup.module` compute the specification `expected`. -/

namespace Examples.TreeLookup

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.TreeLookup

theorem search_inner (input : Array UInt64) (query : UInt64) {j : Nat} (hj : j < 3) :
    search input query j =
      if query = input[2 * j + 1]! then #[input[2 * j + 2]!, 1]
      else if query < input[2 * j + 1]! then search input query (2 * j + 1)
      else search input query (2 * j + 2) := by
  rw [search]
  simp [show ¬3 ≤ j by omega]

theorem search_leaf (input : Array UInt64) (query : UInt64) {j : Nat} (hj : 3 ≤ j) :
    search input query j =
      if query = input[2 * j + 1]! then #[input[2 * j + 2]!, 1] else #[0, 0] := by
  rw [search]
  simp [hj]

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  dsimp only
  by_cases hs : xs.size = 15
  · simp only [hs, ite_true, LeanExe.loop, search_inner xs _ (j := 0) (by decide),
      search_inner xs _ (j := 1) (by decide), search_inner xs _ (j := 2) (by decide),
      search_leaf xs _ (j := 3) (by decide), search_leaf xs _ (j := 4) (by decide),
      search_leaf xs _ (j := 5) (by decide), search_leaf xs _ (j := 6) (by decide)]
    simp
    generalize xs[0]! = q
    by_cases h0 : q = xs[1]!
    · subst h0; simp
    by_cases l0 : q < xs[1]!
    · by_cases h1 : q = xs[3]!
      · subst h1; simp [h0, l0]
      by_cases l1 : q < xs[3]!
      · by_cases h3 : q = xs[7]!
        · subst h3; simp [h0, l0, h1, l1]
        · simp [h0, l0, h1, l1, h3]
      · by_cases h4 : q = xs[9]!
        · subst h4; simp [h0, l0, h1, l1]
        · simp [h0, l0, h1, l1, h4]
    · by_cases h2 : q = xs[5]!
      · subst h2; simp [h0, l0]
      by_cases l2 : q < xs[5]!
      · by_cases h5 : q = xs[11]!
        · subst h5; simp [h0, l0, h2, l2]
        · simp [h0, l0, h2, l2, h5]
      · by_cases h6 : q = xs[13]!
        · subst h6; simp [h0, l0, h2, l2]
        · simp [h0, l0, h2, l2, h6]
  · have hok : (xs.size.toUInt64 == 15) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hn]; exact hs
    simp [hok, hs]

/-- One step of the program's loop over the three levels. -/
def treeStep (xs : Array UInt64) (query _k : UInt64) (s : UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 :=
  let key := xs[(2 * s.1 + 1).toNat]!
  let hit := s.2.1 == 0 && query == key
  (if query < key then 2 * s.1 + 1 else 2 * s.1 + 2, if hit then 1 else s.2.1,
    if hit then xs[(2 * s.1 + 2).toNat]! else s.2.2)

set_option maxHeartbeats 2000000 in
theorem compute_implements : Implements treeLookup.module 2 compute := by
  refine Func.implements_heap [(treeLookup.ir, "compute")] 0 treeLookup.ir "compute" rfl compute
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hXs⟩ hCap
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hRead : ∀ (st : State) (k : UInt64), st.get 0 = some (.i64 ptr) →
      Expr.readValue initial.mem 0 k st = some (xs[k.toNat]!, st) :=
    fun _ _ h => Expr.readValue_at hW h
  set start := treeLookup.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 16 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let query := xs[0]!
  let ok : UInt64 := if UInt64.ofNat xs.size = 15 then 1 else 0
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.i64 ok)
  let s3 := (s2.update 15 (.i64 0)).update 3 (.i64 query)
  let s4 := s3.update 4 (.i64 0)
  let s5 := s4.update 5 (.i64 0)
  let s6 := s5.update 6 (.i64 0)
  show Triple _ (.seq (.load .u64 1 (.get 0))
    (.seq (.assign 2 (.ite (.eq (.get 1) (.const 15)) (.const 1) (.const 0)))
    (.seq (.assign 3 (.read 0 (.const 0))) (.seq (.assign 4 (.const 0))
    (.seq (.assign 5 (.const 0)) (.seq (.assign 6 (.const 0)) (.seq (.loop 7 8 (.const 3) _)
      (.arrayLiteral 14 [.ite (.eq (.get 2) (.const 1)) (.get 6) (.const 0),
        .ite (.eq (.get 2) (.const 1)) (.get 5) (.const 0)])))))))) 15 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s5) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s6) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, ok]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, hRead, query, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4, s5]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4, s5, s6]
  have hS6 : s6.params.length + s6.locals.length = 16 := by
    simp [s6, s5, s4, s3, s2, s1, hStart]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [4, 5, 6]) (writes := [4, 5, 6, 9, 10, 11, 12, 13])
    (init := ((0 : UInt64), (0 : UInt64), (0 : UInt64))) (n := 3) (treeStep xs query)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    ⟨s6, by simp [Expr.eval]⟩
    (by simp [State.Holds, Scalar.values, s6, s5, s4, s3, s2, s1, hStart]) ?_) ?_
  · rintro k ⟨j, found, value⟩ state hk hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 16 := by
      rw [hFrame.params, hFrame.locals]; exact hS6
    have g0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, hGet0])
    have g3 : state.get 3 = some (.i64 query) :=
      (hFrame.get 3 (by decide) (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, hStart])
    simp [State.Holds, Scalar.values] at hHolds
    obtain ⟨g4, g5, g6⟩ := hHolds
    refine Stmt.run_triple ?_
    eval_state [hLength, hIndex, g0, g3, g4, g5, g6, hRead]
    split <;> rename_i hc <;> simp [State.set?_eq_update, hLength, hc] <;>
      refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, treeStep]
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, treeStep, hc]
  apply Triple.of_forall
  rintro store s7 ⟨rfl, hFrame7, hHolds7⟩
  let r := LeanExe.loop 3 ((0 : UInt64), (0 : UInt64), (0 : UInt64)) (treeStep xs query)
  simp [State.Holds, Scalar.values] at hHolds7
  obtain ⟨-, g5, g6⟩ := hHolds7
  have g2 : s7.get 2 = some (.i64 ok) :=
    (hFrame7.get 2 (by decide) (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, hStart])
  have hLength7 : s7.params.length + s7.locals.length = 16 := by
    rw [hFrame7.params, hFrame7.locals]; exact hS6
  have hMemory32 : (compile [(treeLookup.ir, "compute")]).memIs64 = false := rfl
  have hImports : (compile [(treeLookup.ir, "compute")]).imports = [] := rfl
  have hAlloc : (compile [(treeLookup.ir, "compute")]).funcs[0]? = some (allocFunction 0) := rfl
  refine (Stmt.arrayLiteral_spec (values := [.ite (.eq (.get 2) (.const 1)) (.get 6) (.const 0),
      .ite (.eq (.get 2) (.const 1)) (.get 5) (.const 0)])
    (words := [if ok = 1 then r.2.2 else 0, if ok = 1 then r.2.1 else 0]) hMemory32 hImports
    hAlloc (by decide) (by omega) hHeap hCap (by decide) ?_).mono (fun _ _ h => h) ?_
  · refine .cons (fun _ state hFrame => ⟨state, ?_⟩)
      (.cons (fun _ state hFrame => ⟨state, ?_⟩) .nil)
    · have h2 : state.get 2 = some (.i64 ok) := (hFrame.get 2 (by decide) (by decide)).trans g2
      have h6 : state.get 6 = some (.i64 r.2.2) :=
        (hFrame.get 6 (by decide) (by decide)).trans g6
      by_cases hk : ok = 1 <;> simp [Expr.eval, h2, h6, hk]
    · have h2 : state.get 2 = some (.i64 ok) := (hFrame.get 2 (by decide) (by decide)).trans g2
      have h5 : state.get 5 = some (.i64 r.2.1) :=
        (hFrame.get 5 (by decide) (by decide)).trans g5
      by_cases hk : ok = 1 <;> simp [Expr.eval, h2, h5, hk]
  · rintro store state ⟨result, -, hResult, hNew⟩
    refine ⟨_, hNew.at_, hNew.caps, [.i64 result], state,
      by simp [treeLookup.ir, Func.scratch, Expr.evalResults, Expr.eval, hResult],
      ⟨result, rfl, ?_⟩, hNew.keeps⟩
    have hok : (xs.size.toUInt64 == 15) = true ↔ ok = 1 := by
      by_cases h : UInt64.ofNat xs.size = 15 <;> simp [ok, h, Nat.toUInt64]
    have hc : compute xs = #[if ok = 1 then r.2.2 else 0, if ok = 1 then r.2.1 else 0] := by
      show #[if (xs.size.toUInt64 == 15) = true then r.2.2 else 0,
        if (xs.size.toUInt64 == 15) = true then r.2.1 else 0] = _
      simp only [hok]
    rw [hc]
    exact hNew.owned

/-- `encode` succeeds on `treeLookup.module`, and its bytes decode to a module that computes the
specification `expected`. -/
theorem treeLookup_bytes : ∃ bytes, Wasm.Encoding.encode treeLookup.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip treeLookup.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, treeLookup.module, decoded, compute_implements.congr
    fun _ _ _ xs ⟨_, _, hXs⟩ => compute_eq xs hXs.values.size_lt⟩

end Examples.TreeLookup
