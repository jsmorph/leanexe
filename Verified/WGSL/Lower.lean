import Verified.WGSL.Loop
import Verified.WGSL.Float32
import Verified.WGSL.Read
import Verified.WGSL.Size

namespace Verified.WGSL

def lower : {Γ : List Ty} → {t : Ty} → (e : Verified.Expr S Γ t) → (ctx : Context Γ) →
    (base : Nat) → ctx.Bounded base →
    Option (Code ctx base (fun funs env => e.denote funs env))
  | _, _, .word v, _, _, _ => some (.word v)
  | _, _, .bool v, _, _, _ => some (.bool v)
  | _, _, .float32 bits, _, _, _ => some (.float32 bits)
  | _, _, .var v, _, _, bound => some (.var v bound)
  | _, _, .bin op left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.bin op a b)
  | _, _, .cmp op left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.cmp op a b)
  | _, _, .not value, ctx, base, bound => do
      pure (← lower value ctx base bound).not
  | _, _, .and left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.and a b)
  | _, _, .or left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.or a b)
  | _, _, .fbin32 op left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.fbin32 op a b)
  | _, _, .fcmp32 op left right, ctx, base, bound => do
      let a ← lower left ctx base bound
      let b ← lower right ctx a.next (bound.mono a.grows)
      pure (.fcmp32 op a b)
  | _, _, .funary32 op value, ctx, base, bound => do
      pure (.funary32 op (← lower value ctx base bound))
  | _, _, .toFloat32 .ofBits value, ctx, base, bound => do
      pure (.ofBits32 (← lower value ctx base bound))
  | _, _, .toWord32 .toBits value, ctx, base, bound => do
      pure (.toBits32 (← lower value ctx base bound))
  | _, _, .get (e := .word) array position, ctx, base, bound => do
      pure (.readWord array (← lower position ctx base bound))
  | _, _, .get (e := .bool) array position, ctx, base, bound => do
      pure (.readBool array (← lower position ctx base bound))
  | _, _, .get (e := .float32) array position, ctx, base, bound => do
      pure (.readFloat32 array (← lower position ctx base bound))
  | _, _, .size array, ctx, base, bound => ctx.size base bound array
  | _, _, .letE value body, ctx, base, bound => do
      let a := (← lower value ctx base bound).cache
      let b ← lower body (.cons a.result ctx) a.next
        ((bound.mono a.grows).cons a.resultBound)
      pure (.bind a b)
  | _, t, .ite condition yes no, ctx, base, bound => do
      let cell ← Cell.ofTy t
      let c ← lower condition ctx base bound
      let a ← lower yes ctx (c.next + 1) (bound.mono (by have := c.grows; omega))
      let b ← lower no ctx a.next (bound.mono (by have := c.grows; have := a.grows; omega))
      pure (.branch cell c a b)
  | _, t, .loop count init (.bool true) body, ctx, base, bound => do
      let cell ← Cell.ofTy t
      let a ← lower count ctx base bound
      let b ← lower init ctx a.next (bound.mono a.grows)
      let bodyCtx := Context.cons (cell.read b.next) (.cons (.word (.get (b.next + 2))) ctx)
      let bodyBound : bodyCtx.Bounded (b.next + 3) := by
        apply ((bound.mono (by have := a.grows; have := b.grows; omega)).cons
          (by exact Nat.le_refl _)).cons
        have := cell.readBound b.next
        omega
      let c ← lower body bodyCtx (b.next + 3) bodyBound
      pure (.loop cell a b c)
  | _, _, _, _, _, _ => none

end Verified.WGSL
