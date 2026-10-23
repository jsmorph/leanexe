import Verified.Wasi.EffectAnalysis

namespace Verified.Wasi

def EffectSig.callMoves (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i))
    (i : Fin signature.params.length) : Bool :=
  signature.mode i == .owned &&
    match (args i).varIndex? with
    | some k => (slots.getD k default).mode == .owned && !live k &&
        !(argsAny fun j => j != i && !(signature.params.get j).scalar && (args j).usesFast k)
    | none => false

/-- Scratch positions above the incoming context.  Every value result is owned.  Binds and
branches reserve their result words before child scratch.  Loops reserve count, index, and
state words, then share callback scratch. -/
def Command.width : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Nat
  | _, _, .unit => 0
  | _, _, .ret (type := type) value => max value.width (copyWidth type)
  | _, _, .bind (intermediate := intermediate) first next =>
    intermediate.width + max first.width next.width
  | _, result, .ite condition yes no =>
    max condition.width (result.width + max yes.width no.width)
  | _, _, .call (signature := signature) _ args =>
    argsMax fun i =>
      if signature.mode i = .owned then copyWidth (signature.params.get i) else (args i).width
  | _, _, .read capacity => capacity.width
  | _, _, .write _ _ => 0
  | _, _, .exit code => max code.width 1
  | _, _, .loop (type := type) count initial test step =>
    max count.width (max (1 + max initial.width (copyWidth type))
      (2 + type.width + max test.width step.width))

end Verified.Wasi
