import Verified.OwnedExpr
import Verified.FieldsAfter

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

def fieldCost {S : List Sig} {Γ : List Ty} {ps : List Ty} (funs : Funs S) (flags : Flags S)
    (bounds : Bounds S) (modes : List Mode) (paid : List Bool) (L : Nat → Nat → Bool)
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (env : Env Γ)
    (i : Fin ps.length) : Nat :=
  (args i).allocs funs flags bounds modes paid (L (i.val + 1)) env +
    coerceCost (ps.get i) ((args i).mode modes) .owned ((args i).denote funs env)

end Verified
