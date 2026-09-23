import Project.Gpt2QuantizedCached.CachedBlock.Nodes
import Project.Gpt2QuantizedCached.CachedBlock.Attention
import Project.Gpt2QuantizedCached.CachedBlock.KernelState

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open PackedReleaseMany (Bindings)

theorem KernelState.bindings {params : List Value} {before after : Locals}
    {count ownerSlot copiedSlot size : Nat} {root : UInt64}
    (h : KernelState params (before.locals.take count) count ownerSlot copiedSlot root size after)
    {items : List PackedReleaseMany.Item} (hBindings : Bindings items before)
    (hParams : before.params = params) (hLocals : before.locals.length = 193)
    (hCount : count ≤ 193)
    (hIndices : ∀ item ∈ items, item.ownerLocal < params.length + count) : Bindings items after := by
  exact hBindings.prefix (h.1.trans hParams.symm) h.2.2.2.2.1
    (by rw [hLocals]; exact hCount) (by rw [h.2.1]; exact hCount)
    (by simpa only [hParams] using hIndices)

theorem KernelState.owner_get {params saved : List Value} {frame : Locals}
    {count ownerSlot copiedSlot size : Nat} {root : UInt64}
    (h : KernelState params saved count ownerSlot copiedSlot root size frame)
    (hSlot : ownerSlot < 193) : frame.get (params.length + ownerSlot) = some (.i64 root) := by
  simp only [Locals.get, h.1, h.2.1, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false,
    Nat.add_lt_add_iff_left, hSlot, ite_true, Nat.add_sub_cancel_left]
  exact h.2.2.2.2.2.1

theorem KernelState.preserveAttention {params : List Value} {before after : Locals}
    {count ownerSlot copiedSlot size base : Nat} {root normalizedPtr qkvPtr attentionPtr : UInt64}
    (h : KernelState params (before.locals.take count) count ownerSlot copiedSlot root size after)
    (hCount : 54 ≤ count)
    (hOld : AttentionState params base normalizedPtr qkvPtr attentionPtr before) :
    AttentionState params base normalizedPtr qkvPtr attentionPtr after := by
  have read (index : Nat) (hi : index < 54) : after.locals[index]? = before.locals[index]? :=
    Frame.local_of_take_eq h.2.2.2.2.1 (hi.trans_le hCount)
  rcases hOld with ⟨⟨⟨_, _, _, hBase, h10, h11, h12, h13, h14, h15, _⟩,
    h27, h28, h29, h30, h31, h32⟩, h41, h42, h43, h44, h45, h46⟩
  exact ⟨⟨⟨h.1, h.2.1, h.2.2.1, (read 0 (by decide)).trans hBase,
    (read 10 (by decide)).trans h10, (read 11 (by decide)).trans h11,
    (read 12 (by decide)).trans h12, (read 13 (by decide)).trans h13,
    (read 14 (by decide)).trans h14, (read 15 (by decide)).trans h15, h.2.2.2.1⟩,
    (read 34 (by decide)).trans h27, (read 35 (by decide)).trans h28,
    (read 36 (by decide)).trans h29, (read 37 (by decide)).trans h30,
    (read 38 (by decide)).trans h31, (read 39 (by decide)).trans h32⟩,
    (read 48 (by decide)).trans h41, (read 49 (by decide)).trans h42,
    (read 50 (by decide)).trans h43, (read 51 (by decide)).trans h44,
    (read 52 (by decide)).trans h45, (read 53 (by decide)).trans h46⟩

#print axioms KernelState.preserveAttention

end Project.Gpt2QuantizedCached.CachedBlock
