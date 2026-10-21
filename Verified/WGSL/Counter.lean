import Verified.WGSL.ParamLookup

namespace Verified.WGSL

def FitsCount (count : LeanExe.WGSL.Count) (args : List LeanExe.WGSL.Arg) (n : Nat) : Prop :=
  match count with
  | .size _ src => ∃ xs, args[src]? = some (.array xs) ∧ xs.size = n
  | .param j => args[j]? = some (.word (UInt64.ofNat n))

structure Counter (params : Params Γ) (e : Verified.Expr S Γ .word) where
  count : LeanExe.WGSL.Count
  value : ∀ funs env n, FitsCount count (params.args env) n → e.denote funs env = UInt64.ofNat n
  sizeBound : ∀ j, count.sizeLocal? = some j → j < Γ.length + 2

def Counter.param (params : Params Γ) (v : Var Γ .word) :
    Counter params (Verified.Expr.var (S := S) v) where
  count := .param v.index
  value := by
    intro funs env n h
    have ha := params.args_get env v
    cases hp : params.get v with
    | word =>
        simp only [hp, Param.arg] at ha
        change (params.args env)[v.index]? = some (.word (UInt64.ofNat n)) at h
        rw [ha] at h
        exact LeanExe.WGSL.Arg.word.inj (Option.some.inj h)
  sizeBound := by intro j hj; cases hj

def Counter.size (params : Params Γ) (v : Var Γ (.array e)) :
    Counter params (Verified.Expr.size (S := S) v) where
  count := .size (Γ.length + 1) v.index
  value := by
    intro funs env n h
    obtain ⟨xs, hxs, hSize⟩ := h
    have ha := params.args_get env v
    cases hp : params.get v with
    | words | bools | floats32 =>
        simp only [hp, Param.arg] at ha
        rw [ha] at hxs
        cases hxs
        have hs : (env.get v).size = n := by simpa only [Array.size_map] using hSize
        change (env.get v).size.toUInt64 = UInt64.ofNat n
        rw [hs]
  sizeBound := by intro j hj; cases hj; omega

def Counter.ofExpr (params : Params Γ) : (e : Verified.Expr S Γ .word) → Option (Counter params e)
  | .var v => some (.param params v)
  | .size v => some (.size params v)
  | _ => none

end Verified.WGSL
