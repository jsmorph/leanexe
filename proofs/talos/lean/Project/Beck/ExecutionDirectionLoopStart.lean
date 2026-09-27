import Project.Beck.ExecutionDirectionVector

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionLoopStartLocals (locals : List Value) (root columns : UInt64) (rank : Nat) : List Value :=
  let l := (((locals.set 52 (.i64 root)).set 53 (.i64 root)).set 89 (.i64 0)).set 92 (.i64 columns)
  let l := (((l.set 90 (.i64 rank.toUInt64)).set 91 (.i64 1)).set 54 (.i64 root)).set 55 (.i64 root)
  l.set 110 (.i64 root)

structure DirectionLoopLocals (locals : List Value) (matrix sro srp sco scp : UInt64)
    (basis : Basis) (ro rp co cp original current : UInt64) (free index : Nat) : Prop
    extends DirectionSearchLocals locals matrix sro srp sco scp basis ro rp co cp where
  freeColumn : locals[46]? = some (.i64 free.toUInt64)
  firstOwner : locals[52]? = some (.i64 original)
  firstPointer : locals[53]? = some (.i64 original)
  currentOwner : locals[54]? = some (.i64 current)
  currentPointer : locals[55]? = some (.i64 current)
  position : locals[89]? = some (.i64 index.toUInt64)
  limit : locals[90]? = some (.i64 basis.columns.size.toUInt64)
  step : locals[91]? = some (.i64 1)
  originalOwner : locals[110]? = some (.i64 original)

theorem DirectionLoopLocals.preserved {before after : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals before matrix sro srp sco scp basis ro rp co cp original current free index)
    (size : after.length = before.length) (words : WordLocals after)
    (keeps : ∀ index, index < 56 ∨ (89 ≤ index ∧ index ≤ 91) ∨ index = 110 → after[index]? = before[index]?) :
    DirectionLoopLocals after matrix sro srp sco scp basis ro rp co cp original current free index :=
  ⟨state.toDirectionSearchLocals.preserved size words (fun k bound => keeps k (by omega)),
    (keeps 46 (by omega)).trans state.freeColumn, (keeps 52 (by omega)).trans state.firstOwner,
    (keeps 53 (by omega)).trans state.firstPointer, (keeps 54 (by omega)).trans state.currentOwner,
    (keeps 55 (by omega)).trans state.currentPointer, (keeps 89 (by omega)).trans state.position,
    (keeps 90 (by omega)).trans state.limit, (keeps 91 (by omega)).trans state.step,
    (keeps 110 (by omega)).trans state.originalOwner⟩

theorem DirectionLoopLocals.updated {before after : List Value} {matrix sro srp sco scp : UInt64}
    {basis : Basis} {ro rp co cp original current : UInt64} {free index : Nat}
    (state : DirectionLoopLocals before matrix sro srp sco scp basis ro rp co cp original current free index)
    (update : WordUpdate before after 92 15) :
    DirectionLoopLocals after matrix sro srp sco scp basis ro rp co cp original current free index :=
  state.preserved update.size update.words (fun k bound => update.keeps k (by omega))

theorem directionLoopStart_state (locals : List Value) (matrix sro srp sco scp : UInt64)
    (basis : Basis) (ro rp co cp root : UInt64) (free : Nat)
    (state : DirectionSearchLocals locals matrix sro srp sco scp basis ro rp co cp)
    (freeRead : locals[46]? = some (.i64 free.toUInt64)) :
    DirectionLoopLocals (directionLoopStartLocals locals root cp basis.columns.size)
      matrix sro srp sco scp basis ro rp co cp root root free 0 := by
  have update : WordUpdate locals (directionLoopStartLocals locals root cp basis.columns.size) 52 59 := by
    unfold directionLoopStartLocals
    exact (((((((((WordUpdate.refl state.words 52 59).set 52 root (by omega) (by omega)).set 53 root (by omega) (by omega)).set
      89 0 (by omega) (by omega)).set 92 cp (by omega) (by omega)).set 90 basis.columns.size.toUInt64 (by omega) (by omega)).set
      91 1 (by omega) (by omega)).set 54 root (by omega) (by omega)).set 55 root (by omega) (by omega)).set 110 root (by omega) (by omega)
  refine ⟨state.updated update (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [directionLoopStartLocals, List.length_set, List.getElem?_set, state.size,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, freeRead]
  rfl

set_option maxRecDepth 4096 in
theorem directionLoopStart_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (root columns : UInt64) (words : Array UInt64)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (columnsRead : locals[32]? = some (.i64 columns)) (represented : UInt64Array.At initial columns words)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionLoopStartLocals locals root columns words.size })) :
    wp Project.Beck.«module» ((directionEligible.drop 66).take 19) Q initial
      { params := params, locals := locals, values := [.i64 root] } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (columns.toNat % 2 ^ 32)) = UInt64.ofNat words.size := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (columns.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  simp only [directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, columnsRead,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, reduceIte]
  exact next

#print axioms directionLoopStart_exact

end Project.Beck.Execution
