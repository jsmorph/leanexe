import Project.Trees.Moves
import Project.Trees.Encode
import Project.IR.Correct
import Project.Pipeline.Records
import Project.Encoding.RoundTrip

/-! `KeyTree.setKey`, compiled into `treeMoves.module`, consumes its tree and computes its Lean
definition exactly: it writes the new key into the root's record and returns the record. -/

namespace Project.Trees

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Trees

/-- `setKey` with its two arguments as one pair, the tree consumed. -/
def setKeyMoved (x : UInt64 × Moved KeyTree) : KeyTree := KeyTree.setKey x.1 x.2.val

theorem setKey_implements : Implements treeMoves.module 2 setKeyMoved := by
  refine Func.implements_moves treeMoves.funcs 0 treeMoves.setKey.ir "setKey" rfl _
    (by rintro _ _ _ _ ⟨_, _, rfl, rfl, p, rfl, -⟩; rfl) ?_
  rintro ⟨k, ⟨t⟩⟩ heap initial _ hHeap ⟨_, _, rfl, rfl, p, rfl, hOwned, hDisjoint⟩ - -
  have hMoves : Represent.moves initial (Scalar.values k ++ [.i64 p]) (k, Moved.mk t) =
      Node.pointers initial p (encode t) := rfl
  rw [hMoves]
  rw [show Scalar.values k ++ [Value.i64 p] = [.i64 k, .i64 p] from rfl]
  let start : State := { params := [.i64 k, .i64 p], locals := List.replicate 4 (.i64 0) }
  show Triple _ (.ite (.eq (.get 1) (.const 0)) (.assign 2 (.const 0))
      (.seq (.load .u64 3 (.bin .add (.get 1) (.const 0)))
        (.seq (.load .u64 4 (.bin .add (.get 1) (.const 8)))
          (.seq (.load .u64 5 (.bin .add (.get 1) (.const 16)))
            (.seq (.store (.bin .add (.get 1) (.const 8)) (.get 0)) (.assign 2 (.get 1))))))) 6
    (fun store state => store = initial ∧ state = start) _
  cases t with
  | leaf =>
    obtain rfl : p = 0 := hOwned
    refine (Stmt.ite_spec (PThen := fun s st => s = initial ∧ st = start)
      (PElse := fun _ _ => False) (Stmt.assign_spec.mono ?_ fun _ _ h => h)
      Triple.of_false).mono ?_ fun _ _ h => h
    · rintro s st ⟨rfl, rfl⟩
      refine ⟨0, start, start, rfl, rfl, heap, hHeap, rfl, fun _ _ h _ => h,
        fun _ _ h _ => ⟨h, rfl⟩, [.i64 0], start,
        by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, start, State.get],
        ⟨0, rfl, rfl, .nil⟩, fun _ _ _ _ b hb => ?_, fun _ _ _ _ b hb => ?_⟩
      · change b ∈ Node.blocks _ 0 .null at hb
        cases hb
      · change b ∈ Node.blocks _ 0 .null at hb
        cases hb
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨true, start, by simp [Expr.eval, start, State.get], rfl, rfl⟩
  | node l key r =>
    let slots : List Slot := [.child (encode l), .word key, .child (encode r)]
    have hRecord : NodeOwned heap initial p (.record slots) := hOwned
    obtain ⟨hWrites, hAt, hOwned', hBlocks⟩ :=
      NodeOwned.writeWord (i := 1) (w := k) hHeap hRecord hDisjoint ⟨key, rfl⟩
    have hResult :
        Encode.encode (setKeyMoved (k, ⟨.node l key r⟩)) = .record (slots.set 1 (.word k)) := rfl
    obtain ⟨hHead, -, hKey, -, -⟩ := hRecord
    have hBase := hHead.base
    have hRoom := hHead.capacity
    have hAddress := hHead.address
    have hBelow := hHead.below
    have hTop := hHeap.top
    simp only [slots, List.length_cons, List.length_nil] at hRoom
    have hNonzero : p ≠ 0 := by
      rintro rfl
      simp at hBase
    have h0 : (p + 0).toUInt32 = slotAddress p 0 := by simp [slotAddress]
    have h1 : (p + 8).toUInt32 = slotAddress p 1 := by simp [slotAddress]
    have h2 : (p + 16).toUInt32 = slotAddress p 2 := by simp [slotAddress]
    have hs0 := slotAddress_toNat (p := p) (i := 0) (by omega)
    have hs1 := slotAddress_toNat (p := p) (i := 1) (by omega)
    have hs2 := slotAddress_toNat (p := p) (i := 2) (by omega)
    let pl := initial.mem.read64 (slotAddress p 0)
    let pr := initial.mem.read64 (slotAddress p 2)
    let ps : List Value := [.i64 k, .i64 p]
    let s1 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 0, .i64 0] }
    let s2 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 key, .i64 0] }
    let s3 : State := { params := ps, locals := [.i64 0, .i64 pl, .i64 key, .i64 pr] }
    let s4 : State := { params := ps, locals := [.i64 p, .i64 pl, .i64 key, .i64 pr] }
    let final : Store Unit := { initial with mem := initial.mem.write64 (slotAddress p 1) k }
    have hRoot : p ∈ Node.pointers initial p (encode (.node l key r)) := by
      simp [encode, Node.pointers]
    -- Bytes of a region apart from the root's block keep their values.
    have hKeep : ∀ r : Nat × Nat, regionsDisjoint r (block initial p) →
        ∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = initial.mem.bytes a :=
      fun r hr a hLow hHigh => hWrites.2.2 a (by
        simp only [regionsDisjoint, block] at hr
        omega)
    refine (Stmt.ite_spec (PThen := fun _ _ => False)
      (PElse := fun s st => s = initial ∧ st = start) Triple.of_false ?_).mono ?_ fun _ _ h => h
    · refine Stmt.seq_spec (M := fun s st => s = initial ∧ st = s1) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s2) ?_ <|
        Stmt.seq_spec (M := fun s st => s = initial ∧ st = s3) ?_ <|
        Stmt.seq_spec (M := fun s st => s = final ∧ st = s3) ?_ ?_
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 0, start, s1, rfl, by rw [h0, hs0]; omega, ?_, rfl, rfl⟩
        rw [h0]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s1, s2, rfl, by rw [h1, hs1]; omega, ?_, rfl, rfl⟩
        rw [h1, hKey]
        rfl
      · refine Stmt.load_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 16, s2, s3, rfl, by rw [h2, hs2]; omega, ?_, rfl, rfl⟩
        rw [h2]
        rfl
      · refine Stmt.store_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p + 8, s3, k, s3, rfl, rfl, by rw [h1, hs1]; omega, ?_⟩
        rw [h1]
        exact ⟨rfl, rfl⟩
      · refine Stmt.assign_spec.mono ?_ fun _ _ h => h
        rintro s st ⟨rfl, rfl⟩
        refine ⟨p, s3, s4, rfl, rfl, heap, hAt, rfl, fun q ws hq hApart => ?_,
          fun q ws hq hApart => ?_, [.i64 p], s4,
          by simp [treeMoves.setKey.ir, Func.scratch, Expr.evalResults, Expr.eval, State.get, s4, ps],
          ⟨p, rfl, hResult ▸ hOwned', by rw [hResult, hBlocks]; exact hDisjoint⟩,
          fun q ws hq hApart b hb => ?_, fun q ws hq hApart b hb => ?_⟩
        · exact hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ (hApart p hRoot)) hq.region
        · exact hq.keep (le_of_eq hWrites.2.1.symm) (hKeep _ (hApart p hRoot)) hq.region
        · change b ∈ Node.blocks final p (Encode.encode (setKeyMoved (k, ⟨.node l key r⟩))) at hb
          rw [hResult, hBlocks] at hb
          exact apart_pointers.mp hApart b hb
        · change b ∈ Node.blocks final p (Encode.encode (setKeyMoved (k, ⟨.node l key r⟩))) at hb
          rw [hResult, hBlocks] at hb
          exact apart_pointers.mp hApart b hb
    · rintro s st ⟨rfl, rfl⟩
      exact ⟨false, start, by simp [Expr.eval, start, State.get, hNonzero], rfl, rfl⟩

/-- `encode` succeeds on `treeMoves.module`, and its bytes decode to a module that computes
`KeyTree.setKey` on a consumed tree exactly. -/
theorem treeMoves_bytes : ∃ bytes, Wasm.Encoding.encode treeMoves.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m 2 setKeyMoved := by
  obtain ⟨bytes, success, decoded⟩ :=
    Wasm.Encoding.round_trip treeMoves.module (by decide) (by decide +kernel)
  exact ⟨bytes, success, treeMoves.module, decoded, setKey_implements⟩

#print axioms treeMoves_bytes

end Project.Trees
