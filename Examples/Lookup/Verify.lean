import Examples.Lookup.Module
import Examples.Lookup.Spec
import LeanExe.IR.ArrayLiteral
import LeanExe.IR.Correct
import LeanExe.IR.Loop
import LeanExe.IR.Words
import LeanExe.Encoding.RoundTrip

/-! The bytes of `lookup.module` compute the specification `expected`. -/

namespace Examples.Lookup

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Examples.Lookup

/-- One step of the program's loop over the ten pairs. -/
def lookupStep (xs : Array UInt64) (query k : UInt64) (s : UInt64 × UInt64) : UInt64 × UInt64 :=
  let hit := s.1 == 0 && xs[(2 * k + 1).toNat]! == query
  (if hit then 1 else s.1, if hit then xs[(2 * k + 2).toNat]! else s.2)

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  dsimp only
  by_cases hs : xs.size = 21
  · simp only [hs, bne_self_eq_false, Bool.false_eq_true, ite_false, LeanExe.loop]
    by_cases h1 : xs[1]! = xs[0]!
    · simp [h1]
    by_cases h2 : xs[3]! = xs[0]!
    · simp [h1, h2]
    by_cases h3 : xs[5]! = xs[0]!
    · simp [h1, h2, h3]
    by_cases h4 : xs[7]! = xs[0]!
    · simp [h1, h2, h3, h4]
    by_cases h5 : xs[9]! = xs[0]!
    · simp [h1, h2, h3, h4, h5]
    by_cases h6 : xs[11]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6]
    by_cases h7 : xs[13]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7]
    by_cases h8 : xs[15]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7, h8]
    by_cases h9 : xs[17]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    by_cases h10 : xs[19]! = xs[0]! <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · have hok : (xs.size.toUInt64 == 21) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hn]; exact hs
    simp [hok, hs]

set_option maxHeartbeats 2000000 in
theorem compute_implements : Implements lookup.module 2 compute := by
  refine Func.implements_heap [(lookup.ir, "compute")] 0 lookup.ir "compute" rfl compute
    (by rintro _ _ _ _ ⟨ptr, rfl, -⟩; rfl) ?_
  rintro xs heap initial _ hHeap ⟨ptr, rfl, hXs⟩ hCap
  have hW := hXs.values
  have hLength0 := hW.lengthBound
  simp only [UInt64.toNat_toUInt32] at hLength0
  have hRead : ∀ (st : State) (k : UInt64), st.get 0 = some (.i64 ptr) →
      Expr.readValue initial.mem 0 k st = some (xs[k.toNat]!, st) :=
    fun _ _ h => Expr.readValue_at hW h
  set start := lookup.ir.state [.i64 ptr] with hStartDef
  have hStart : start.params.length + start.locals.length = 13 := rfl
  have hGet0 : start.get 0 = some (.i64 ptr) := rfl
  let query := xs[0]!
  let ok : UInt64 := if UInt64.ofNat xs.size = 21 then 1 else 0
  let s1 := start.update 1 (.i64 (UInt64.ofNat xs.size))
  let s2 := s1.update 2 (.i64 ok)
  let s3 := (s2.update 12 (.i64 0)).update 3 (.i64 query)
  let s4 := s3.update 4 (.i64 0)
  let s5 := s4.update 5 (.i64 0)
  show Triple _ (.seq (.load .u64 1 (.get 0))
    (.seq (.assign 2 (.ite (.eq (.get 1) (.const 21)) (.const 1) (.const 0)))
    (.seq (.assign 3 (.read 0 (.const 0))) (.seq (.assign 4 (.const 0))
    (.seq (.assign 5 (.const 0)) (.seq (.loop 6 7 (.const 10) _)
      (.arrayLiteral 11 [.ite (.eq (.get 2) (.const 1)) (.get 5) (.const 0),
        .ite (.eq (.get 2) (.const 1)) (.get 4) (.const 0)]))))))) 12 _ _
  refine Stmt.seq_spec (Stmt.run_spec (final := s1) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s2) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s3) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s4) ?_) <|
    Stmt.seq_spec (Stmt.run_spec (final := s5) ?_) ?_
  · simp [Stmt.run, Expr.eval, hLength0, hW.lengthRead, State.set?_eq_update, hStart, s1, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, ok]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, hRead, query, hGet0]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4]
  · simp [Stmt.run, Expr.eval, State.set?_eq_update, hStart, s1, s2, s3, s4, s5]
  have hS5 : s5.params.length + s5.locals.length = 13 := by simp [s5, s4, s3, s2, s1, hStart]
  refine Stmt.seq_spec (Stmt.loop_spec (vars := [4, 5]) (writes := [4, 5, 8, 9, 10])
    (init := ((0 : UInt64), (0 : UInt64))) (n := 10) (lookupStep xs query) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) ⟨s5, by simp [Expr.eval]⟩
    (by simp [State.Holds, Scalar.values, s5, s4, s3, s2, s1, hStart]) ?_) ?_
  · rintro k ⟨found, value⟩ state hk hFrame hHolds hIndex hLimit
    have hLength : state.params.length + state.locals.length = 13 := by
      rw [hFrame.params, hFrame.locals]; exact hS5
    have g0 : state.get 0 = some (.i64 ptr) :=
      (hFrame.get 0 (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, hGet0])
    have g3 : state.get 3 = some (.i64 query) :=
      (hFrame.get 3 (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, hStart])
    have g4 : state.get 4 = some (.i64 found) := by
      simp only [State.Holds, Scalar.values] at hHolds
      exact (List.forall₂_cons.mp hHolds).1
    have g5 : state.get 5 = some (.i64 value) := by
      simp only [State.Holds, Scalar.values] at hHolds
      exact (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds).2).1
    refine Stmt.run_triple ?_
    eval_state [hLength, hIndex, g0, g3, g4, g5, hRead]
    split <;> rename_i hc <;> simp [State.set?_eq_update, hLength, hc] <;>
      refine ⟨?_, ?_⟩
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, lookupStep, hc]
    · repeat refine State.Frame.update ?_ (by decide)
      exact State.Frame.refl _ _ _
    · simp [State.Holds, hLength, lookupStep, hc]
  apply Triple.of_forall
  rintro store s6 ⟨rfl, hFrame6, hHolds6⟩
  let r := LeanExe.loop 10 ((0 : UInt64), (0 : UInt64)) (lookupStep xs query)
  simp only [State.Holds, Scalar.values] at hHolds6
  have g4 : s6.get 4 = some (.i64 r.1) := (List.forall₂_cons.mp hHolds6).1
  have g5 : s6.get 5 = some (.i64 r.2) :=
    (List.forall₂_cons.mp (List.forall₂_cons.mp hHolds6).2).1
  have g2 : s6.get 2 = some (.i64 ok) :=
    (hFrame6.get 2 (by decide) (by decide)).trans (by simp [s5, s4, s3, s2, s1, hStart])
  have hLength6 : s6.params.length + s6.locals.length = 13 := by
    rw [hFrame6.params, hFrame6.locals]; exact hS5
  have hMemory32 : (compile [(lookup.ir, "compute")]).memIs64 = false := rfl
  have hImports : (compile [(lookup.ir, "compute")]).imports = [] := rfl
  have hAlloc : (compile [(lookup.ir, "compute")]).funcs[0]? = some (allocFunction 0) := rfl
  refine (Stmt.arrayLiteral_spec (values := [.ite (.eq (.get 2) (.const 1)) (.get 5) (.const 0),
      .ite (.eq (.get 2) (.const 1)) (.get 4) (.const 0)])
    (words := [if ok = 1 then r.2 else 0, if ok = 1 then r.1 else 0]) hMemory32 hImports hAlloc
    (by decide) (by omega) hHeap hCap (by decide) ?_).mono (fun _ _ h => h) ?_
  · refine .cons (fun _ state hFrame => ⟨state, ?_⟩)
      (.cons (fun _ state hFrame => ⟨state, ?_⟩) .nil)
    · have h2 : state.get 2 = some (.i64 ok) := (hFrame.get 2 (by decide) (by decide)).trans g2
      have h5 : state.get 5 = some (.i64 r.2) := (hFrame.get 5 (by decide) (by decide)).trans g5
      by_cases hk : ok = 1 <;> simp [Expr.eval, h2, h5, hk]
    · have h2 : state.get 2 = some (.i64 ok) := (hFrame.get 2 (by decide) (by decide)).trans g2
      have h4 : state.get 4 = some (.i64 r.1) := (hFrame.get 4 (by decide) (by decide)).trans g4
      by_cases hk : ok = 1 <;> simp [Expr.eval, h2, h4, hk]
  · rintro store state ⟨result, -, hResult, hNew⟩
    refine ⟨_, hNew.at_, hNew.caps, [.i64 result], state,
      by simp [lookup.ir, Func.scratch, Expr.evalResults, Expr.eval, hResult],
      ⟨result, rfl, ?_⟩,
      hNew.keeps⟩
    have hok : (xs.size.toUInt64 == 21) = true ↔ ok = 1 := by
      by_cases h : UInt64.ofNat xs.size = 21 <;> simp [ok, h, Nat.toUInt64]
    have hc : compute xs = #[if ok = 1 then r.2 else 0, if ok = 1 then r.1 else 0] := by
      show #[if (xs.size.toUInt64 == 21) = true then r.2 else 0,
        if (xs.size.toUInt64 == 21) = true then r.1 else 0] = _
      simp only [hok]
    rw [hc]
    exact hNew.owned

/-- `encode` succeeds on `lookup.module`, and its bytes decode to a module that computes the
specification `expected`. -/
theorem lookup_bytes : ∃ bytes, Wasm.Encoding.encode lookup.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 expected := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip lookup.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, lookup.module, decoded, compute_implements.congr
    fun _ _ _ xs ⟨_, _, hXs⟩ => compute_eq xs hXs.values.size_lt⟩

#print axioms lookup_bytes

end Examples.Lookup
