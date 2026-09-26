import LeanExe.IR.Core

namespace LeanExe.IR

/-! Scalar semantics for the existing IR. Unsupported operators have no scalar
meaning. In particular this does not reuse the diagnostic partial evaluator,
which gives defaults to unsupported expressions and out-of-range local reads.
-/

def U64Op.evalScalar (op : U64Op) (a b : UInt64) : Option UInt64 :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  | .divU => some (a / b)
  | .modU => some (a % b)
  | .bitAnd => some (a &&& b)
  | .bitOr => some (a ||| b)
  | .bitXor => some (a ^^^ b)
  | .shiftLeft => some (a <<< b)
  | .shiftRight => some (a >>> b)
  | _ => none

/-- Finite locals; lookup and writes cannot silently create slots. -/
abbrev ScalarStore := List UInt64

def ScalarStore.write (s : ScalarStore) (index : Nat) (value : UInt64) :
    Option ScalarStore :=
  if index < s.length then some (s.set index value) else none

@[simp] theorem ScalarStore.write_length {s next : ScalarStore} {index : Nat}
    {value : UInt64} (h : s.write index value = some next) : next.length = s.length := by
  unfold write at h
  split at h
  · cases h
    simp
  · contradiction

theorem ScalarStore.read_write_same {s next : ScalarStore} {index : Nat}
    {value : UInt64} (h : s.write index value = some next) : next[index]? = some value := by
  unfold write at h
  split at h
  · cases h
    simp_all
  · contradiction

theorem ScalarStore.read_write_other {s next : ScalarStore} {index other : Nat}
    {value : UInt64} (h : s.write index value = some next) (hne : other ≠ index) :
    next[other]? = s[other]? := by
  unfold write at h
  split at h
  · cases h
    simp [hne.symm]
  · contradiction

mutual
  /-- Big-step scalar expression evaluation, including strict local binding.
  There is deliberately no rule for trap, heap operations, or floating point.
  Calls and iteration will require module-indexed extensions of this relation. -/
  inductive Expr.ScalarEval : Expr → ScalarStore → UInt64 → ScalarStore → Prop where
    | local (h : s[index]? = some value) : Expr.ScalarEval (.local index) s value s
    | const : Expr.ScalarEval (.u64 n) s (UInt64.ofNat n) s
    | bin (left : Expr.ScalarEval a s x s₁) (right : Expr.ScalarEval b s₁ y s₂)
        (op : operation.evalScalar x y = some value) :
        Expr.ScalarEval (.u64Bin operation a b) s value s₂
    | iteTrue (condition : Cond.ScalarEval c s true s₁)
        (branch : Expr.ScalarEval a s₁ value s₂) : Expr.ScalarEval (.ite c a b) s value s₂
    | iteFalse (condition : Cond.ScalarEval c s false s₁)
        (branch : Expr.ScalarEval b s₁ value s₂) : Expr.ScalarEval (.ite c a b) s value s₂
    | letE (value : Expr.ScalarEval a s x s₁) (write : s₁.write index x = some s₂)
        (body : Expr.ScalarEval b s₂ y s₃) : Expr.ScalarEval (.letE index a b) s y s₃

  inductive Cond.ScalarEval : Cond → ScalarStore → Bool → ScalarStore → Prop where
    | true : Cond.ScalarEval .true s true s
    | false : Cond.ScalarEval .false s false s
    | eq (left : Expr.ScalarEval a s x s₁) (right : Expr.ScalarEval b s₁ y s₂) :
        Cond.ScalarEval (.eqU64 a b) s (x == y) s₂
    | lt (left : Expr.ScalarEval a s x s₁) (right : Expr.ScalarEval b s₁ y s₂) :
        Cond.ScalarEval (.ltU64 a b) s (decide (x < y)) s₂
    | le (left : Expr.ScalarEval a s x s₁) (right : Expr.ScalarEval b s₁ y s₂) :
        Cond.ScalarEval (.leU64 a b) s (decide (x ≤ y)) s₂
    | not (condition : Cond.ScalarEval c s value s₁) : Cond.ScalarEval (.not c) s (!value) s₁
    | andTrue (left : Cond.ScalarEval a s true s₁) (right : Cond.ScalarEval b s₁ value s₂) :
        Cond.ScalarEval (.and a b) s value s₂
    | andFalse (left : Cond.ScalarEval a s false s₁) : Cond.ScalarEval (.and a b) s false s₁
    | orTrue (left : Cond.ScalarEval a s true s₁) : Cond.ScalarEval (.or a b) s true s₁
    | orFalse (left : Cond.ScalarEval a s false s₁) (right : Cond.ScalarEval b s₁ value s₂) :
        Cond.ScalarEval (.or a b) s value s₂
end

inductive Stmt.ScalarEval : Stmt → ScalarStore → ScalarStore → Prop where
  | skip : Stmt.ScalarEval .skip s s
  | assign (value : e.ScalarEval s v s₁) (write : s₁.write index v = some s₂) :
      Stmt.ScalarEval (.assign index e) s s₂
  | seq (first : Stmt.ScalarEval a s s₁) (second : Stmt.ScalarEval b s₁ s₂) :
      Stmt.ScalarEval (.seq a b) s s₂
  | iteTrue (condition : c.ScalarEval s true s₁) (branch : Stmt.ScalarEval a s₁ s₂) :
      Stmt.ScalarEval (.ite c a b) s s₂
  | iteFalse (condition : c.ScalarEval s false s₁) (branch : Stmt.ScalarEval b s₁ s₂) :
      Stmt.ScalarEval (.ite c a b) s s₂
  | whileFalse (condition : c.ScalarEval s false s₁) : Stmt.ScalarEval (.while c body) s s₁
  | whileTrue (condition : c.ScalarEval s true s₁) (step : Stmt.ScalarEval body s₁ s₂)
      (rest : Stmt.ScalarEval (.while c body) s₂ s₃) : Stmt.ScalarEval (.while c body) s s₃

/-- Call boundary for a scalar function with one result. Parameters occupy the
first slots; declared non-parameter locals start at zero, as in WebAssembly. -/
inductive Func.ScalarEval : Func → List UInt64 → UInt64 → Prop where
  | run (arity : args.length = func.params) (bounds : func.params ≤ func.locals)
      (body : func.body.ScalarEval
        (args ++ List.replicate (func.locals - func.params) 0) afterBody)
      (resultShape : func.results = [result])
      (resultValue : result.ScalarEval afterBody value afterResult) :
      Func.ScalarEval func args value

end LeanExe.IR
