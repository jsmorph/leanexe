import Verified.AlignedTreeCase
import Verified.AlignedFloat32
import Verified.AlignedListFold

/-!
The assembly of the construct proofs under the flag.  `Expr.code_specInX` is `Expr.code_specIn`
with each construct's flagged theorem in place of the original.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- `Expr.code_specIn` under the flag. -/
theorem Expr.code_specInX {strict : Bool} {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host) {pv : List Value}
    {d0 : UInt64} (hCalls : CallsAtX strict m funs flags bounds fits d0 pool) {Γ : List Ty} {t : Ty}
    (expr : Expr S Γ t) :
    expr.Covered pool →
    (expr.depthCalls = true → pv.head? = some (.i64 d0)) →
    ∀ buy env slots paid live, CodeSpecInX strict (pool := pool) buy m funs flags bounds fits host pv expr env
      slots paid live := by
  induction expr with
  | word value =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_word value
  | bool value =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bool value
  | var x =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_var hCopy x
  | treeNil shape hn =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_treeNil shape hn
  | treeNode r reuse words arrays buffers children wordSpec arraySpec bufferSpec childSpec =>
    have wordSpec := fun i c d => specOfX (pool := pool) (wordSpec i c d)
    have arraySpec := fun i c d => specOfX (pool := pool) (arraySpec i c d)
    have bufferSpec := fun i c d => specOfX (pool := pool) (bufferSpec i c d)
    have childSpec := fun i c d => specOfX (pool := pool) (childSpec i c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <|
      specX_treeNode hm hRA hRt hCopy reuse words arrays buffers children
      (fun i => wordSpec i ((Expr.covered_treeNode hCover).1 i) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inl (Or.inl (Or.inl (le_argsAny _ i hd)))))
      (fun i => arraySpec i ((Expr.covered_treeNode hCover).2.1 i) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inl (Or.inr (le_argsAny _ i hd))))
      (fun i => bufferSpec i ((Expr.covered_treeNode hCover).2.2.1 i) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inr (le_argsAny _ i hd)))
      (fun i => childSpec i ((Expr.covered_treeNode hCover).2.2.2 i) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inl (Or.inl (Or.inr (le_argsAny _ i hd)))))
  | treeCase x empty nodes emptySpec nodeSpec =>
    have emptySpec := fun hn c d => specOfX (pool := pool) (emptySpec hn c d)
    have nodeSpec := fun r c d => specOfX (pool := pool) (nodeSpec r c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_treeCase hm hRA hCopy x empty nodes
      (fun hn => emptySpec hn ((Expr.covered_treeCase hCover).1 hn) fun hd => hD (by
        simp only [Expr.depthCalls, dite_eq_left hn, hd, Bool.true_or]))
      (fun r => nodeSpec r ((Expr.covered_treeCase hCover).2 r) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inr (le_argsAny _ r hd)))
  | bin op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bin op (leftSpec ((Expr.covered_bin hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_bin hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | cmp op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_cmp op (leftSpec ((Expr.covered_cmp hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_cmp hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | not e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_not (eSpec ((Expr.covered_not hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | and left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_and (leftSpec ((Expr.covered_and hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_and hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | or left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_or (leftSpec ((Expr.covered_or hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_or hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | ite c thenE elseE cSpec thenSpec elseSpec =>
    have cSpec := fun c d => specOfX (pool := pool) (cSpec c d)
    intro hCover hD
    exact fun buy => specX_ite hm hRA hCopy (cSpec ((Expr.covered_ite hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (thenSpec ((Expr.covered_ite hCover).2.1) (fun h => hD (by simp [Expr.depthCalls, h])) buy)
      (elseSpec ((Expr.covered_ite hCover).2.2) (fun h => hD (by simp [Expr.depthCalls, h])) buy)
  | letE value body valueSpec bodySpec =>
    have valueSpec := fun c d => specOfX (pool := pool) (valueSpec c d)
    intro hCover hD
    exact fun buy => specX_letE hm hRA (valueSpec ((Expr.covered_letE hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec ((Expr.covered_letE hCover).2) (fun h => hD (by simp [Expr.depthCalls, h])) buy)
  | call g args argsSpec =>
    have argsSpec := fun i c d => specOfX (pool := pool) (argsSpec i c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_call hm hRA hCopy hCalls g args (fun i => argsSpec i ((Expr.covered_call hCover) i) fun h => hD (by
      simp only [Expr.depthCalls, Bool.or_eq_true]
      exact Or.inr (le_argsAny _ i h))) hD
  | pair first second firstSpec secondSpec =>
    have firstSpec := fun c d => specOfX (pool := pool) (firstSpec c d)
    have secondSpec := fun c d => specOfX (pool := pool) (secondSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_pair hCopy (firstSpec ((Expr.covered_pair hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (secondSpec ((Expr.covered_pair hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | letPair e body eSpec bodySpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD
    exact fun buy => specX_letPair hm hRA (eSpec ((Expr.covered_letPair hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec ((Expr.covered_letPair hCover).2) (fun h => hD (by simp [Expr.depthCalls, h])) buy)
  | loop count init cond body countSpec initSpec condSpec bodySpec =>
    have countSpec := fun c d => specOfX (pool := pool) (countSpec c d)
    have initSpec := fun c d => specOfX (pool := pool) (initSpec c d)
    have condSpec := fun c d => specOfX (pool := pool) (condSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_loop hm hRA hCopy (countSpec ((Expr.covered_loop hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (initSpec ((Expr.covered_loop hCover).2.1) fun h => hD (by simp [Expr.depthCalls, h]))
      (condSpec ((Expr.covered_loop hCover).2.2.1) fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec ((Expr.covered_loop hCover).2.2.2) fun h => hD (by simp [Expr.depthCalls, h]))
  | fold x init body initSpec bodySpec =>
    have initSpec := fun c d => specOfX (pool := pool) (initSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_fold hm hRA hCopy x (initSpec ((Expr.covered_fold hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (bodySpec ((Expr.covered_fold hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | listFold args body argsSpec bodySpec =>
    have argsSpec := fun i c d => specOfX (pool := pool) (argsSpec i c d)
    have bodySpec := fun c d => specOfX (pool := pool) (bodySpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_listFold hm hRA hCopy args body
      (fun i => argsSpec i ((Expr.covered_listFold hCover).1 i) fun hd => hD (by
        simp only [Expr.depthCalls, Bool.or_eq_true]
        exact Or.inl (le_argsAny _ i hd)))
      (bodySpec ((Expr.covered_listFold hCover).2) fun hd => hD (by simp [Expr.depthCalls, hd]))
  | size x =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_size hm (readReleaseX hm hRA) x
  | bytesLiteral bytes =>
    intro hCover _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bytesLiteral hm hRt bytes hCover
  | bytesEmpty =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bytesEmpty
  | bytesSize x =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bytesSize (readReleaseX hm hRA) x
  | bytesGet x index indexSpec =>
    have indexSpec := fun c d => specOfX (pool := pool) (indexSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bytesGet (readReleaseX hm hRA) x (indexSpec ((Expr.covered_bytesGet hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | leSize x i =>
    intro _ _
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_leSize hm (readReleaseX hm hRA) hCopy x i
  | get x i iSpec =>
    have iSpec := fun c d => specOfX (pool := pool) (iSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_get (readReleaseX hm hRA) x (iSpec ((Expr.covered_get hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | build count elem countSpec elemSpec =>
    have countSpec := fun c d => specOfX (pool := pool) (countSpec c d)
    have elemSpec := fun c d => specOfX (pool := pool) (elemSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_build hm hRA hRt (countSpec ((Expr.covered_build hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (elemSpec ((Expr.covered_build hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | bytesBuild count elem countSpec elemSpec =>
    have countSpec := fun c d => specOfX (pool := pool) (countSpec c d)
    have elemSpec := fun c d => specOfX (pool := pool) (elemSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_bytesBuild hm hRA hRt (countSpec ((Expr.covered_bytesBuild hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (elemSpec ((Expr.covered_bytesBuild hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | set x i v iSpec vSpec =>
    have iSpec := fun c d => specOfX (pool := pool) (iSpec c d)
    have vSpec := fun c d => specOfX (pool := pool) (vSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_set hCopy x (iSpec ((Expr.covered_set hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (vSpec ((Expr.covered_set hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | push x v vSpec =>
    have vSpec := fun c d => specOfX (pool := pool) (vSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_push hm hRA hRt x (vSpec ((Expr.covered_push hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | append x y =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_append hm hRA hRt x y
  | insertAt x i v iSpec vSpec =>
    have iSpec := fun c d => specOfX (pool := pool) (iSpec c d)
    have vSpec := fun c d => specOfX (pool := pool) (vSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_insertAt hm hRA hRt x (iSpec ((Expr.covered_insertAt hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (vSpec ((Expr.covered_insertAt hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | eraseAt x i iSpec =>
    have iSpec := fun c d => specOfX (pool := pool) (iSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_eraseAt hCopy x (iSpec ((Expr.covered_eraseAt hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | float bits =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_float bits
  | float32 bits =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_float32 bits
  | fbin op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_fbin op (leftSpec ((Expr.covered_fbin hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_fbin hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | fbin32 op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_fbin32 op (leftSpec ((Expr.covered_fbin32 hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_fbin32 hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | funary op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_funary op (eSpec ((Expr.covered_funary hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | funary32 op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_funary32 op (eSpec ((Expr.covered_funary32 hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | fcmp op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_fcmp op (leftSpec ((Expr.covered_fcmp hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_fcmp hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | fcmp32 op left right leftSpec rightSpec =>
    have leftSpec := fun c d => specOfX (pool := pool) (leftSpec c d)
    have rightSpec := fun c d => specOfX (pool := pool) (rightSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_fcmp32 op (leftSpec ((Expr.covered_fcmp32 hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (rightSpec ((Expr.covered_fcmp32 hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | toFloat op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_toFloat op (eSpec ((Expr.covered_toFloat hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | toFloat32 op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_toFloat32 op (eSpec ((Expr.covered_toFloat32 hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | toWord op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_toWord op (eSpec ((Expr.covered_toWord hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | toWord32 op e eSpec =>
    have eSpec := fun c d => specOfX (pool := pool) (eSpec c d)
    intro hCover hD; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_toWord32 op (eSpec ((Expr.covered_toWord32 hCover)) fun h => hD (by simp [Expr.depthCalls, h]))
  | mk first second firstSpec secondSpec =>
    have firstSpec := fun c d => specOfX (pool := pool) (firstSpec c d)
    have secondSpec := fun c d => specOfX (pool := pool) (secondSpec c d)
    intro hCover hD
    exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_mk (firstSpec ((Expr.covered_mk hCover).1) fun h => hD (by simp [Expr.depthCalls, h]))
      (secondSpec ((Expr.covered_mk hCover).2) fun h => hD (by simp [Expr.depthCalls, h]))
  | proj x p =>
    intro _ _; exact specInOfX (pool := pool) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) <| specX_proj x p

/-- `Expr.code_spec` under the flag. -/
theorem Expr.code_specX {strict : Bool} {S : List Sig} (m : Module) (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit) (hm : Runtime m)
    (hRA : strict = true → ReleaseAligned m) (hRt : strict = true → AllocAligned m)
    (hCopy : CopyCodeX strict m host) {pv : List Value}
    {d0 : UInt64} (hCalls : CallsAtX strict m funs flags bounds fits d0 pool) {Γ : List Ty} {t : Ty}
    (expr : Expr S Γ t) :
    expr.Covered pool →
    (expr.depthCalls = true → pv.head? = some (.i64 d0)) →
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv expr env slots paid live :=
  fun hCover hD env slots paid live =>
    (Expr.code_specInX m funs flags bounds fits host hm hRA hRt hCopy hCalls expr hCover hD
      false env slots paid live).spec

end Verified
