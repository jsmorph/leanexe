import Project.Words.Module
import Project.Words.Encode
import Project.IR.Correct
import Project.IR.TailLoop
import Project.IR.Loop
import Project.IR.Record
import Project.Pipeline.Records
import Project.Encoding.RoundTrip

/-! The compiled functions over `Words` compute their Lean definitions exactly. -/

namespace Project.Words

open Wasm Project.Pipeline Project.IR Project.Runtime LeanExe.Examples.Words

theorem first_implements : Implements words.module 2 Words.first := by
  refine Func.implements words.funcs 0 words.first.ir "first" rfl _
    (by rintro _ _ _ _ ⟨p, rfl, -⟩; rfl) ?_
  rintro w heap initial _ hHeap ⟨p, rfl, hNode⟩
  let start : State := { params := [.i64 p], locals := List.replicate 3 (.i64 0) }
  show Triple _ (.ite (.eq (.get 0) (.const 0)) (.assign 1 (.const 0))
      (.seq (.load .u64 2 (.bin .add (.get 0) (.const 0)))
        (.seq (.load .u64 3 (.bin .add (.get 0) (.const 8))) (.assign 1 (.get 2))))) 4
    (fun store state => store = initial ∧ state = start) _
  cases w with
  | nil =>
    obtain rfl : p = 0 := hNode
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨0, start, start, rfl, rfl, rfl, [.i64 0], start,
        by simp [words.first.ir, Func.scratch, Expr.evalResults, Expr.eval, start, State.get], rfl⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | cons x rest =>
    obtain ⟨hSlots, hx, hChild, -⟩ := hNode
    have hNonzero := hSlots.nonzero
    have hAddress := hSlots.address
    have hBelow := hSlots.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hAddress hBelow
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    let c := initial.mem.read64 (slotAddress p 1)
    let s1 : State := { params := [.i64 p], locals := [.i64 0, .i64 x, .i64 0] }
    let s2 : State := { params := [.i64 p], locals := [.i64 0, .i64 x, .i64 c] }
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_
        (Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ ?_)
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, ?_, rfl, rfl⟩
        rw [h0, hx]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, by rw [h1]; rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        let s3 : State := { params := [.i64 p], locals := [.i64 x, .i64 x, .i64 c] }
        exact ⟨x, s2, s3, rfl, rfl, rfl, [.i64 x], s3,
          by simp [words.first.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, s3], rfl⟩
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `sumAcc` with its two arguments as one pair. -/
def sumAccTuple (x : UInt64 × Words) : UInt64 := Words.sumAcc x.1 x.2

/-- One iteration of the compiled loop: on `nil` it stores the accumulator, and on `cons x r`
it moves to `(acc + x, r)`, which has the same sum and a smaller list. -/
theorem sumAcc_step : TailStepIn (α := UInt64 × Words) (compile words.funcs)
    (match words.sumAcc.ir.body with | .while _ step => step | _ => .skip)
    words.sumAcc.ir.scratch 4 sumAccTuple (fun x => sizeOf x.2) := by
  rintro heap initial ⟨acc, w⟩ vs result others hHeap ⟨first, second, rfl, rfl, p, rfl, hNode⟩
    hLength
  rw [show Scalar.values acc ++ [Value.i64 p] = [.i64 acc, .i64 p] from rfl]
  match others, hLength with
  | [v0, v1, v2, v3], _ =>
  show Triple _ (.ite (.eq (.get 1) (.const 0)) (.seq (.assign 2 (.get 0)) (.assign 3 (.const 1)))
      (.seq (.load .u64 6 (.bin .add (.get 1) (.const 0)))
        (.seq (.load .u64 7 (.bin .add (.get 1) (.const 8)))
          (.seq (.assign 4 (.bin .add (.get 0) (.get 6)))
            (.seq (.assign 5 (.get 7)) (.seq (.assign 0 (.get 4)) (.assign 1 (.get 5)))))))) 8 _ _
  let start := tailStateIn [.i64 acc, .i64 p] result 0 [v0, v1, v2, v3]
  cases w with
  | nil =>
    obtain rfl : p = 0 := hNode
    let s1 : State := { params := [.i64 acc, .i64 0], locals := [.i64 acc, .i64 0, v0, v1, v2, v3] }
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False)
      (Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ ?_) Triple.of_false).mono ?_
        fun _ _ h => h
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      exact ⟨acc, start, s1, rfl, rfl, rfl, rfl⟩
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨rfl, rfl⟩
      refine ⟨1, s1, tailStateIn [.i64 acc, .i64 0] acc 1 [v0, v1, v2, v3], rfl, rfl, rfl,
        acc, [v0, v1, v2, v3], rfl, Or.inr ?_⟩
      simp only [sumAccTuple, Words.sumAcc]
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, rfl, rfl, rfl⟩
  | cons x rest =>
    obtain ⟨hSlots, hx, hChild, -⟩ := hNode
    have hNonzero := hSlots.nonzero
    have hAddress := hSlots.address
    have hBelow := hSlots.below
    have hTop := hHeap.top
    simp only [List.length_cons, List.length_nil] at hAddress hBelow
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    let c := initial.mem.read64 (slotAddress p 1)
    let ps : List Value := [.i64 acc, .i64 p]
    let s1 : State := { params := ps, locals := [.i64 result, .i64 0, v0, v1, .i64 x, v3] }
    let s2 : State := { params := ps, locals := [.i64 result, .i64 0, v0, v1, .i64 x, .i64 c] }
    let s3 : State :=
      { params := ps, locals := [.i64 result, .i64 0, .i64 (acc + x), v1, .i64 x, .i64 c] }
    let s4 : State :=
      { params := ps, locals := [.i64 result, .i64 0, .i64 (acc + x), .i64 c, .i64 x, .i64 c] }
    let s5 : State :=
      { params := [.i64 (acc + x), .i64 p]
        locals := [.i64 result, .i64 0, .i64 (acc + x), .i64 c, .i64 x, .i64 c] }
    let s6 := tailStateIn [.i64 (acc + x), .i64 c] result 0
      [.i64 (acc + x), .i64 c, .i64 x, .i64 c]
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s4) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s5) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, ?_, rfl, rfl⟩
        rw [h0, hx]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, by rw [h1]; rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨acc + x, s2, s3, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨c, s3, s4, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        exact ⟨acc + x, s4, s5, rfl, rfl, rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨c, s5, s6, rfl, rfl, rfl, result, [.i64 (acc + x), .i64 c, .i64 x, .i64 c],
          rfl, Or.inl ⟨(acc + x, rest), [.i64 (acc + x), .i64 c],
            ⟨[.i64 (acc + x)], [.i64 c], rfl, rfl, c, rfl, hChild⟩, rfl, ?_, ?_⟩⟩
        · simp [sumAccTuple, Words.sumAcc]
        · simp
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, tailStateIn, State.get, hNonzero], rfl, rfl⟩

theorem sumAcc_implements : Implements words.module 3 sumAccTuple :=
  Func.tailIn_implements words.funcs 1 words.sumAcc.ir "sumAcc" rfl sumAccTuple
    (fun x => sizeOf x.2) _
    (by rintro _ _ _ _ ⟨first, second, rfl, rfl, p, rfl, -⟩; rfl)
    (rest := [.u64, .u64, .u64, .u64]) rfl rfl rfl sumAcc_step

theorem range_implements : Implements words.module 4 Words.range := by
  refine Func.implements_heap words.funcs 2 words.range.ir "range" rfl _
    (by rintro _ _ _ _ rfl; rfl) ?_
  rintro n heap initial _ hHeap rfl hCap
  have hMemory32 : (compile words.funcs).memIs64 = false := rfl
  have hImports : (compile words.funcs).imports = [] := rfl
  have hAlloc : (compile words.funcs).funcs[0]? = some (allocFunction 0) := rfl
  let f : UInt64 → Words → Words := fun i w => .cons (n - 1 - i) w
  let start : State := { params := [.i64 n], locals := List.replicate 4 (.i64 0) }
  let Inv : Nat → Store Unit → List Value → Prop := fun k store vals =>
    ∃ heap' p, vals = [.i64 p] ∧ heap.Built initial heap' store p (encode (loopPrefix f .nil k))
  show Triple _ (.seq (.assign 1 (.const 0)) (.loop 2 3 (.get 0)
      (.seq (.record 4 [.bin .sub (.bin .sub (.get 0) (.const 1)) (.get 3), .get 1] 2)
        (.assign 1 (.get 4))))) 5 (fun store state => store = initial ∧ state = start) _
  refine Stmt.seq_spec (M := fun store state => store = initial ∧ state = start) ?_
    ((Stmt.loop_inv (vars := [1]) (writes := [1, 4]) (n := n) (vals0 := [.i64 0]) Inv
      (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [start])
      ⟨start, by simp [Expr.eval, start, State.get]⟩ (.cons (by simp [start, State.get]) .nil)
      ⟨heap, 0, rfl, Heap.Built.null hHeap⟩ ?_).mono (fun _ _ h => h) ?_)
  · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
    rintro store state ⟨hStore, hState⟩
    subst store state
    exact ⟨0, start, start, rfl, rfl, rfl, rfl⟩
  · rintro k store vals state - ⟨heap1, p, rfl, hBuilt⟩ hFrame hHolds hIndex -
    have hP : state.get 1 = some (.i64 p) := by cases hHolds; assumption
    have hN : state.get 0 = some (.i64 n) := (hFrame.get 0 (by decide) (by decide)).trans rfl
    have hRoom : 5 ≤ state.params.length + state.locals.length := by
      rw [hFrame.params, hFrame.locals]; simp [start]
    refine Stmt.seq_spec (Stmt.record_spec hMemory32 hImports hAlloc (by decide) hRoom
      hBuilt.at_ (memoryCap_le_of_caps hBuilt.caps hCap) (by decide) (by decide)
      (words := [n - 1 - UInt64.ofNat k, p]) ?_) ?_
    · refine .cons (fun _ st hF => ⟨st, ?_⟩) (.cons (fun _ st hF => ⟨st, ?_⟩) .nil)
      · have h0 : st.get 0 = some (.i64 n) := (hF.get 0 (by decide) (by decide)).trans hN
        have h3 : st.get 3 = some (.i64 (UInt64.ofNat k)) :=
          (hF.get 3 (by decide) (by decide)).trans hIndex
        simp [Expr.eval, h0, h3, U64Op.apply]
      · have h1 : st.get 1 = some (.i64 p) := (hF.get 1 (by decide) (by decide)).trans hP
        simp [Expr.eval, h1]
    · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
      rintro s st ⟨ptr, hF, hPtr, hNew⟩
      obtain ⟨next, hSet⟩ := State.exists_set? (state := st) (index := 1) (.i64 ptr)
        (by rw [hF.params, hF.locals]; omega)
      refine ⟨ptr, st, next, by simp [Expr.eval, hPtr], hSet,
        (hF.weaken (by simp)).set? hSet (by simp), [.i64 ptr],
        .cons (State.get_set?_same hSet) .nil, heap1.allocate (UInt64.ofNat (8 * 2)), ptr, rfl,
        ?_⟩
      rw [loopPrefix_succ]
      exact hBuilt.cell hNew
  · rintro store state ⟨-, vals, hHolds, heap', p, rfl, hBuilt⟩
    have hP : state.get 1 = some (.i64 p) := by cases hHolds; assumption
    have hLoop : loopPrefix f .nil n.toNat = Words.range n := rfl
    rw [hLoop] at hBuilt
    exact ⟨heap', hBuilt.at_, hBuilt.caps, [.i64 p], state,
      by simp [words.range.ir, Func.scratch, Expr.evalResults, Expr.eval, hP],
      ⟨p, rfl, hBuilt.owned, hBuilt.disjoint⟩, fun r hr _ _ => hBuilt.region r hr⟩

/-- `encode` succeeds on `words.module`, and its bytes decode to a module that computes
`Words.first`, `Words.sumAcc`, and `Words.range` exactly. -/
theorem words_bytes : ∃ bytes, Wasm.Encoding.encode words.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 Words.first ∧
      Implements m 3 sumAccTuple ∧ Implements m 4 Words.range := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip words.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, words.module, decoded, first_implements, sumAcc_implements,
    range_implements⟩

#print axioms words_bytes

end Project.Words
