import Project.ProofKit.FixedArraySearchRead
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ProofKit.FixedArraySearch
open Wasm Project.Runtime

def guardProgram (start : Nat) : Wasm.Program :=
  [.localGet (start + 2), .constI64 0, .eqI64, .br_if 1,
    .localGet (start + 5), .constI64 0, .neI64, .br_if 1]

def body (start : Nat) (fitProgram : Wasm.Program) : Wasm.Program :=
  guardProgram start ++ readProgram start ++
    [.localGet (start + 3), .localGet start, .geUI64,
      .iff 0 0 fitProgram (advanceProgram start), .br 0]

def program (start : Nat) (fitProgram : Wasm.Program) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (body start fitProgram)]]

theorem guardProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (locals : Locals) (start : Nat) (root : UInt64)
    (hValues : locals.values = []) (hRoot : root ≠ 0)
    (hCurrent : locals.get (start + 2) = some (.i64 root))
    (hResult : locals.get (start + 5) = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store locals env) :
    wp module_ (guardProgram start ++ rest) Q store locals env := by
  have hEmpty : { locals with values := [] } = locals := Frame.ext _ _ rfl rfl hValues.symm
  simp only [guardProgram, List.cons_append, List.nil_append, wp_localGet_cons,
    wp_constI64_cons, wp_eqI64_cons, wp_neI64_cons, wp_br_if_cons,
    Frame.withValues_get, hCurrent, hResult, hValues, hRoot, reduceIte]
  simpa [hEmpty] using hNext

def noneInvariant (initial : Store Unit) (params saved tail : List Wasm.Value)
    (need : UInt64) (nodes : List FreeNode) : AssertionF Unit :=
  fun store locals => ∃ previous capacity next : UInt64, ∃ visited remaining : List FreeNode,
    store = initial ∧ nodes = visited ++ remaining ∧ FreeListAt initial.mem remaining ∧
    (∀ node ∈ remaining, node.capacity < need) ∧
    locals = frame params saved tail need previous (freeHead remaining) capacity next 0

def measure (start : Nat) (nodes : List FreeNode) (_ : Store Unit) (locals : Locals) : Nat :=
  match locals.get (start + 2) with
  | some (.i64 root) => scanRemaining nodes root
  | _ => 0

theorem noneProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (need capacity next : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt initial.mem nodes) (hNone : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous capacity next : UInt64, wp module_ rest Q initial
      (frame params saved tail need previous 0 capacity next 0) env) :
    wp module_ (program start fitProgram ++ rest) Q initial
      (frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  subst start
  simp only [program, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons (Inv := noneInvariant initial params saved tail need nodes)
    (μ := measure (params.length + saved.length) nodes)
  · exact ⟨0, capacity, next, [], nodes, rfl, by simp, hList,
      (takeFirstFit_none_iff need nodes).mp hNone, rfl⟩
  · rintro store locals ⟨previous, oldCapacity, oldNext, visited, remaining, rfl,
      hSplit, hRemaining, hSmall, rfl⟩
    cases remaining with
    | nil =>
      simpa [body, guardProgram, wp_simp, frame, freeHead, Nat.add_assoc]
        using hNext previous oldCapacity oldNext
    | cons node restNodes =>
      have hRoot := hRemaining.head_ne_zero
      simp only [freeHead] at hRoot
      cases hRemaining with
      | cons hp h32 hFit hRc hCapacity hNodeNext hSep hTail =>
        have hCapSmall := hSmall node List.mem_cons_self
        have hNotFit : ¬need ≤ node.capacity := by
          rw [UInt64.le_iff_toNat_le]
          rw [UInt64.lt_iff_toNat_lt] at hCapSmall
          omega
        simp only [body, List.append_assoc]
        refine guardProgram_spec module_ env store _ _ node.root rfl hRoot ?_ ?_ _ _ ?_
        · simp [frame, Locals.get, freeHead, Nat.add_assoc]
        · simp [frame, Locals.get, Nat.add_assoc]
        apply readProgram_spec module_ env store params saved tail _ rfl need previous node.root
          node.capacity (freeHead restNodes) 0 oldCapacity oldNext hp (by omega) (by omega)
          hCapacity hNodeNext
        simp [wp_simp, frame, Nat.add_assoc]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp [hNotFit])]
        apply advanceProgram_spec module_ env store params saved tail _ rfl need previous node.root
          node.capacity (freeHead restNodes) 0 _ []
        simp [wp_simp]
        have hSplitNext : nodes = (visited ++ [node]) ++ restNodes := by
          simpa [List.append_assoc] using hSplit
        refine ⟨⟨node.root, node.capacity, freeHead restNodes, visited ++ [node], restNodes,
          rfl, hSplitNext, hTail, ?_, rfl⟩, ?_⟩
        · intro other hOther
          exact hSmall other (List.mem_cons_of_mem _ hOther)
        · have hBefore := hList.scanRemaining_suffix hSplit
          have hAfter := hList.scanRemaining_suffix hSplitNext
          simp only [freeHead, List.length_cons] at hBefore
          simp [measure, frame, Locals.get, Nat.add_assoc, hAfter]
          simpa only [freeHead, hBefore] using Nat.lt_succ_self restNodes.length

#print axioms guardProgram_spec
#print axioms noneProgram_spec

end Project.ProofKit.FixedArraySearch
