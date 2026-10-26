import Verified.Compile
import Verified.TreeSelect

namespace Verified

open Wasm LeanExe.Runtime

/-- `code` runs, at the store `store` and the locals `s`, as the branch of a test followed by
`rest` under `Q`: for every continuation `rest'` and assertion `Q'` that accept what `rest` and
`Q` accept after a fall-through with the stack of `s`, and that accept the traps that `Q`
accepts, `code ++ rest'` meets `Q'`.  A chain of tests nests the branch in blocks, and this form
holds at every depth. -/
def RunsBranch (m : Module) (host : HostEnv Unit) (code rest : Program) (Q : Assertion Unit)
    (store : Store Unit) (s : Locals) : Prop :=
  ∀ (rest' : Program) (Q' : Assertion Unit),
    (∀ st s', s'.values = s.values → wp m rest Q st s' host → wp m rest' Q' st s' host) →
    (∀ st, Q (.Trap st "unreachable") → Q' (.Trap st "unreachable")) →
    wp m (code ++ rest') Q' store s host

theorem RunsBranch.mono {m : Module} {host : HostEnv Unit} {code rest rest2 : Program}
    {Q Q2 : Assertion Unit} {store : Store Unit} {s : Locals}
    (h : RunsBranch m host code rest Q store s)
    (hf : ∀ st s', s'.values = s.values → wp m rest Q st s' host → wp m rest2 Q2 st s' host)
    (ht : ∀ st, Q (.Trap st "unreachable") → Q2 (.Trap st "unreachable")) :
    RunsBranch m host code rest2 Q2 store s :=
  fun rest' Q' hf' ht' => h rest' Q' (fun st s' hv hw => hf' st s' hv (hf st s' hv hw))
    (fun st hq => ht' st (ht st hq))

theorem wp_dispatchChain {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {tag : Program} {t : UInt64} (hTag : PushesWord m host tag store s t) :
    ∀ (pairs : List (UInt64 × Program)) (rest : Program) (Q : Assertion Unit),
      RunsBranch m host (chainPick t [] pairs) rest Q store s →
      wp m (dispatchChain tag pairs ++ rest) Q store s host
  | [], rest, Q, h => by
    simpa only [chainPick, dispatchChain, List.nil_append] using
      h rest Q (fun _ _ _ hw => hw) (fun _ hq => hq)
  | [(_, code)], rest, Q, h => h rest Q (fun _ _ _ hw => hw) (fun _ hq => hq)
  | (i, code) :: p :: more, rest, Q, h => by
    rw [dispatchChain, List.append_assoc]
    apply hTag
    simp only [List.cons_append, List.nil_append, wp_constI64_cons, wp_eqI64_cons]
    apply wp_iff_cons rfl
    rw [chainPick] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0), ← List.append_nil code]
      refine h [] _ (fun st s' hv hw => ?_) (fun _ hq => hq)
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      rw [← hv]
      exact hw
    · rw [ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0),
        ← List.append_nil (dispatchChain tag (p :: more))]
      refine wp_dispatchChain hTag (p :: more) [] _ ?_
      intro rest' Q' hf ht
      refine h rest' Q' (fun st s' hv hw => hf st s' hv ?_) (fun st hq => ht st hq)
      rw [wp_nil]
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      rw [← hv]
      exact hw

/-- The tag tests of a shape run the branch of record constructor `r` when the tag code pushes
`r`'s tag. -/
theorem wp_dispatchCode {m : Module} {host : HostEnv Unit} {store : Store Unit} {s : Locals}
    {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {rest : Program} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsBranch m host (branch r) rest Q store s) :
    wp m (shape.dispatchCode ptr branch ++ rest) Q store s host := by
  apply wp_dispatchChain (PushesWord.tag hPtr hRoom)
  rw [shape.chainPick_tag r branch [] _ hTag]
  exact hBranch

/-- The number of tests that a chain of tests of `t` over `pairs` nests its selected entry in. -/
def chainDepth {α : Type} (t : UInt64) : List (UInt64 × α) → Nat
  | [] => 0
  | [_] => 0
  | (i, _) :: p :: rest => if t = i then 1 else 1 + chainDepth t (p :: rest)

theorem chainDepth_index {α : Type} :
    ∀ (pairs : List (UInt64 × α)), (pairs.map Prod.fst).Nodup →
      ∀ (j : Nat) (hj : j < pairs.length),
        chainDepth (pairs[j]'hj).1 pairs = if j + 1 < pairs.length then j + 1 else j
  | [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | [_], _, j, hj => by
    have : j = 0 := by simp at hj; omega
    subst this
    rfl
  | (i, x) :: p :: rest, hNodup, j, hj => by
    rw [List.map_cons, List.nodup_cons] at hNodup
    rw [chainDepth]
    cases j with
    | zero => simp
    | succ j =>
      have hj' : j < (p :: rest).length := by simp at hj ⊢; omega
      have hNe : ((p :: rest)[j]'hj').1 ≠ i := by
        intro he
        apply hNodup.1
        rw [← he]
        exact List.mem_map.mpr ⟨_, List.getElem_mem hj', rfl⟩
      simp only [List.getElem_cons_succ]
      rw [ite_eq_right hNe, chainDepth_index (p :: rest) hNodup.2 j hj']
      simp only [List.length_cons] at hj ⊢
      split <;> split <;> omega

/-- The branch of record constructor `r` sits in as many tests as `TailBody.codeWith` counts. -/
theorem TreeShape.chainDepth_tag {α : Type} (shape : TreeShape) (r : Fin shape.records)
    (f : Fin shape.records → α) (t : UInt64)
    (ht : shape.tagged = true → t = UInt64.ofNat (shape.ctorIndex r)) :
    chainDepth t (shape.tagPairs f) =
      if r.val + 1 < shape.records then r.val + 1 else r.val := by
  have hLength : (shape.tagPairs f).length = shape.records := by
    simp [TreeShape.tagPairs]
  by_cases hTagged : shape.tagged = true
  · have hNodup : ((shape.tagPairs f).map Prod.fst).Nodup := by
      simp only [TreeShape.tagPairs, List.map_map]
      exact (List.nodup_finRange _).map (fun _ _ h => shape.ctorIndex_injective h)
    have hr : r.val < (shape.tagPairs f).length := by rw [hLength]; exact r.isLt
    have hKey : ((shape.tagPairs f)[r.val]'hr).1 = t := by
      rw [ht hTagged]
      simp [TreeShape.tagPairs]
    rw [← hKey, chainDepth_index _ hNodup r.val hr, hLength]
  · have hOne : shape.records = 1 := by
      simp only [TreeShape.tagged, decide_eq_true_eq, Nat.not_lt] at hTagged
      have := r.isLt
      omega
    have hr : r.val = 0 := by have := r.isLt; omega
    have hLength1 : (shape.tagPairs f).length = 1 := by rw [hLength, hOne]
    match hPairs : shape.tagPairs f, hLength1 with
    | [_], _ => simp [chainDepth, hr, hOne]

/-- `code` runs as a branch nested in `d` blocks for the assertion `Q` of the code around them:
for every assertion `Q'` that accepts, for a break out of `k + d` blocks, what `Q` accepts for a
break out of `k`, and that accepts the traps that `Q` accepts, `code` meets `Q'`. -/
def RunsTailBranch (m : Module) (host : HostEnv Unit) (code : Program) (d : Nat)
    (Q : Assertion Unit) (store : Store Unit) (s : Locals) : Prop :=
  ∀ Q' : Assertion Unit,
    (∀ k st s', Q (.Break k st s') → Q' (.Break (k + d) st s')) →
    (∀ st, Q (.Trap st "unreachable") → Q' (.Trap st "unreachable")) →
    wp m code Q' store s host

theorem RunsTailBranch.dispatchChain {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {tag : Program} {t : UInt64} (hTag : PushesWord m host tag store s t) :
    ∀ (pairs : List (UInt64 × Program)) (d : Nat) (Q : Assertion Unit),
      RunsTailBranch m host (chainPick t [] pairs) (d + chainDepth t pairs) Q store s →
      RunsTailBranch m host (Verified.dispatchChain tag pairs) d Q store s
  | [], d, Q, h => by simpa [chainPick, chainDepth, Verified.dispatchChain] using h
  | [(_, code)], d, Q, h => by simpa [chainPick, chainDepth, Verified.dispatchChain] using h
  | (i, code) :: p :: more, d, Q, h => by
    intro Q' hb ht
    rw [Verified.dispatchChain]
    refine hTag s.values _ Q' ?_
    simp only [List.cons_append, List.nil_append, wp_constI64_cons, wp_eqI64_cons]
    apply wp_iff_cons rfl
    rw [chainPick, chainDepth] at h
    by_cases hi : t = i
    · rw [ite_eq_left hi, ite_eq_left hi] at h
      rw [ite_eq_left hi, ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
      refine h _ (fun k st s' hq => ?_) (fun st hq => ht st hq)
      rw [show k + (d + 1) = k + d + 1 by omega]
      exact hb k st s' hq
    · rw [ite_eq_right hi, ite_eq_right hi] at h
      rw [ite_eq_right hi, ite_eq_right (by decide : ¬(0 : UInt32) ≠ 0)]
      have hRest := RunsTailBranch.dispatchChain hTag (p :: more) (d + 1) Q
        (by rw [show d + 1 + chainDepth t (p :: more) = d + (1 + chainDepth t (p :: more)) by
          omega]; exact h)
      refine hRest _ (fun k st s' hq => ?_) (fun st hq => ht st hq)
      rw [show k + (d + 1) = k + d + 1 by omega]
      exact hb k st s' hq

/-- The tag tests of a shape, as a branch nested in `d` blocks, run the branch of record
constructor `r`, which they nest in `chainDepth` further blocks. -/
theorem RunsTailBranch.dispatchCode {m : Module} {host : HostEnv Unit} {store : Store Unit}
    {s : Locals} {shape : TreeShape} (r : Fin shape.records) {ptr : Nat} {p : UInt64}
    {d : Nat} {Q : Assertion Unit} (branch : Fin shape.records → Program)
    (hPtr : s.get ptr = some (.i64 p))
    (hRoom : p.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hTag : shape.tagged = true →
      store.mem.read64 p.toUInt32 = UInt64.ofNat (shape.ctorIndex r))
    (hBranch : RunsTailBranch m host (branch r)
      (d + if r.val + 1 < shape.records then r.val + 1 else r.val) Q store s) :
    RunsTailBranch m host (shape.dispatchCode ptr branch) d Q store s := by
  apply RunsTailBranch.dispatchChain (PushesWord.tag hPtr hRoom)
  rw [shape.chainPick_tag r branch [] _ hTag, shape.chainDepth_tag r branch _ hTag]
  exact hBranch

#print axioms RunsBranch.mono
#print axioms wp_dispatchChain
#print axioms wp_dispatchCode
#print axioms TreeShape.chainDepth_tag
#print axioms RunsTailBranch.dispatchCode

end Verified
