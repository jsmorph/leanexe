import Verified.ArrayFold

namespace Verified

def arrayIndexLeSize (xs : Array α) (i : UInt64) : Bool :=
  decide (i.toNat ≤ xs.size)

def arrayInsertIdx (xs : Array α) (i : UInt64) (value : α) : Array α :=
  if arrayIndexLeSize xs i then LeanExe.insertAt xs i value else #[]

theorem arrayInsertIdx_eq (xs : Array α) (i : UInt64) (value : α) :
    arrayInsertIdx xs i value = xs.insertIdx! i.toNat value := by
  by_cases hi : i.toNat ≤ xs.size
  · simp [arrayInsertIdx, arrayIndexLeSize, LeanExe.insertAt, Array.insertIdx!,
      Array.insertIdxIfInBounds, hi]
  · simp [arrayInsertIdx, arrayIndexLeSize, Array.insertIdx!,
      Array.insertIdxIfInBounds, hi, Nat.lt_of_not_ge hi]
    rfl

theorem Expr.insertIdx_denote (x : Var Γ (.array e)) (i : Var Γ .word)
    (value : Expr S Γ (.elem e)) (funs : Funs S) (env : Env Γ) :
    (Expr.insertIdx x i value).denote funs env =
      (env.get x).insertIdx! (env.get i).toNat (value.denote funs env) := by
  change arrayInsertIdx (env.get x) (env.get i) (value.denote funs env) = _
  exact arrayInsertIdx_eq _ _ _

theorem Expr.leSizeExpand_denote (x : Var Γ (.array e)) (i : Var Γ .word)
    (funs : Funs S) (env : Env Γ) (hSize : (env.get x).size < UInt64.size) :
    (Expr.leSizeExpand x i).denote funs env = (Expr.leSize x i).denote funs env := by
  simp only [Expr.leSizeExpand, Expr.denote, CmpOp.apply, UInt64.le_iff_toNat_le,
    UInt64.toNat_ofNat_of_lt' hSize]

theorem Expr.leSizeExpand_uses (x : Var Γ (.array e)) (i : Var Γ .word) (k : Nat) :
    (Expr.leSizeExpand (S := S) x i).uses k = (Expr.leSize (S := S) x i).uses k := rfl

theorem Expr.leSizeExpand_width (x : Var Γ (.array e)) (i : Var Γ .word) :
    (Expr.leSizeExpand (S := S) x i).width = (Expr.leSize (S := S) x i).width := rfl

theorem Expr.leSizeExpand_aborts (x : Var Γ (.array e)) (i : Var Γ .word) :
    (Expr.leSizeExpand (S := S) x i).aborts = (Expr.leSize (S := S) x i).aborts := rfl

theorem Expr.leSizeExpand_placeArgs (x : Var Γ (.array e)) (i : Var Γ .word) :
    (Expr.leSizeExpand (S := S) x i).placeArgs = (Expr.leSize (S := S) x i).placeArgs := rfl

theorem Expr.leSizeExpand_mode (x : Var Γ (.array e)) (i : Var Γ .word) (modes : List Mode) :
    (Expr.leSizeExpand (S := S) x i).mode modes = (Expr.leSize (S := S) x i).mode modes := rfl

theorem Expr.leSizeExpand_paid (x : Var Γ (.array e)) (i : Var Γ .word) (flags : Flags S)
    (modes : List Mode) (paid : List Bool) (live : Nat → Bool) :
    (Expr.leSizeExpand x i).paid flags modes paid live =
      (Expr.leSize x i).paid flags modes paid live := rfl

theorem Expr.leSizeExpand_allocs (x : Var Γ (.array e)) (i : Var Γ .word) (funs : Funs S)
    (flags : Flags S) (bounds : Bounds S) (modes : List Mode) (paid : List Bool)
    (live : Nat → Bool) (env : Env Γ) :
    (Expr.leSizeExpand x i).allocs funs flags bounds modes paid live env =
      (Expr.leSize x i).allocs funs flags bounds modes paid live env := by
  simp [Expr.leSizeExpand, Expr.allocs, Var.cost, Ty.copyCost]

theorem Expr.leSizeExpand_fits (x : Var Γ (.array e)) (i : Var Γ .word) (funs : Funs S)
    (fits : Fits S) (env : Env Γ) :
    (Expr.leSizeExpand x i).fits funs fits env = (Expr.leSize x i).fits funs fits env := rfl

theorem Expr.leSizeExpand_code (x : Var Γ (.array e)) (i : Var Γ .word) (h : Nat)
    (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    (Expr.leSizeExpand (S := S) x i).code h slots base live =
      (Expr.leSize (S := S) x i).code h slots base live := by
  simp [Expr.leSizeExpand, Expr.code, Expr.usesFast_eq, Expr.uses, CmpOp.instr]

#print axioms arrayInsertIdx_eq
#print axioms Expr.insertIdx_denote
#print axioms Expr.leSizeExpand_denote
#print axioms Expr.leSizeExpand_code

end Verified
