import Project.Gpt2QuantizedCached.CachedBlock.CompositionState

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit

theorem KernelState.transfer {params saved : List Value} {before after : Locals}
    {count ownerSlot copiedSlot size bound : Nat} {root : UInt64}
    (h : KernelState params saved count ownerSlot copiedSlot root size before)
    (hParams : after.params = before.params) (hLocals : after.locals.length = 193)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take bound = before.locals.take bound)
    (hCount : count ≤ bound) (hOwner : ownerSlot + 2 < bound) (hCopy : copiedSlot + 2 < bound) :
    KernelState params saved count ownerSlot copiedSlot root size after := by
  have read (index : Nat) (hi : index < bound) : after.locals[index]? = before.locals[index]? :=
    Frame.local_of_take_eq hPrefix hi
  rcases h with ⟨hParamsOld, _, _, _, hSaved, h0, h1, h2, h3, h4, h5⟩
  refine ⟨hParams.trans hParamsOld, hLocals, hValues, hTyped, ?_,
    (read _ (by omega)).trans h0, (read _ (by omega)).trans h1,
    (read _ hOwner).trans h2, (read _ (by omega)).trans h3,
    (read _ (by omega)).trans h4, (read _ hCopy).trans h5⟩
  have hTake := congrArg (List.take count) hPrefix
  simpa only [List.take_take, Nat.min_eq_left hCount, hSaved] using hTake

theorem NormalizedState.transfer {params : List Value} {before after : Locals}
    {base bound : Nat} {root : UInt64}
    (h : NormalizedState params base root before)
    (hParams : after.params = before.params) (hLocals : after.locals.length = 193)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take bound = before.locals.take bound) (hBound : 16 ≤ bound) :
    NormalizedState params base root after := by
  have read (index : Nat) (hi : index < 16) : after.locals[index]? = before.locals[index]? :=
    Frame.local_of_take_eq hPrefix (hi.trans_le hBound)
  rcases h with ⟨hParamsOld, _, _, h0, h10, h11, h12, h13, h14, h15, _⟩
  exact ⟨hParams.trans hParamsOld, hLocals, hValues, (read 0 (by decide)).trans h0,
    (read 10 (by decide)).trans h10, (read 11 (by decide)).trans h11,
    (read 12 (by decide)).trans h12, (read 13 (by decide)).trans h13,
    (read 14 (by decide)).trans h14, (read 15 (by decide)).trans h15, hTyped⟩

theorem AttentionState.transfer {params : List Value} {before after : Locals}
    {base bound : Nat} {normalizedPtr qkvPtr attentionPtr : UInt64}
    (h : AttentionState params base normalizedPtr qkvPtr attentionPtr before)
    (hParams : after.params = before.params) (hLocals : after.locals.length = 193)
    (hValues : after.values = []) (hTyped : I64Values after.locals)
    (hPrefix : after.locals.take bound = before.locals.take bound) (hBound : 54 ≤ bound) :
    AttentionState params base normalizedPtr qkvPtr attentionPtr after := by
  have read (index : Nat) (hi : index < 54) : after.locals[index]? = before.locals[index]? :=
    Frame.local_of_take_eq hPrefix (hi.trans_le hBound)
  rcases h with ⟨⟨hNorm, h34, h35, h36, h37, h38, h39⟩, h48, h49, h50, h51, h52, h53⟩
  exact ⟨⟨hNorm.transfer hParams hLocals hValues hTyped hPrefix (by omega),
    (read 34 (by decide)).trans h34, (read 35 (by decide)).trans h35,
    (read 36 (by decide)).trans h36, (read 37 (by decide)).trans h37,
    (read 38 (by decide)).trans h38, (read 39 (by decide)).trans h39⟩,
    (read 48 (by decide)).trans h48, (read 49 (by decide)).trans h49,
    (read 50 (by decide)).trans h50, (read 51 (by decide)).trans h51,
    (read 52 (by decide)).trans h52, (read 53 (by decide)).trans h53⟩

#print axioms KernelState.transfer
#print axioms NormalizedState.transfer
#print axioms AttentionState.transfer
end Project.Gpt2QuantizedCached.CachedBlock
