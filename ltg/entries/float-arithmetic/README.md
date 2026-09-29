# Binary64 arithmetic

Use this entry when a hint has rule `float add`, `float sub`, `float mul`, or `float variable`.  The compiler translates Lean's `Float` operations to IR expressions of type `f64`, whose values are bit patterns: `Expr.getF` reads an `f64` local and `Expr.binF` applies `F64Op.apply`, which is Talos's `IEEE64.add`, `sub`, or `mul`, the meaning of WebAssembly's `f64.add`, `f64.sub`, and `f64.mul` in the deterministic profile.  A `Float` argument or result is an `f64` holding `Float.toBits`.

A proof evaluates the translated expression with `simp [Expr.eval, F64Op.apply, ...]`, which leaves an `IEEE64` expression over the arguments' bits, and rewrites the Lean side with `F64Bits.toBits_add`, `toBits_sub`, and `toBits_mul`.  Each states `(a ∘ b).toBits = IEEE64.∘ a.toBits b.toBits` for every pair of floats, NaN included, so the two sides meet without case analysis.  `Project.Axpy.axpy_implements` is the worked example; its proof is one `simp` call after `Func.implements`.

The theorems rest on `F64Add.add_eq`, `F64Sub.sub_eq`, and `F64Mul.mul_eq`, which compare Lean's `Float.Model` with `IEEE64` on all bit patterns, and on `F64Bits.ofBits_toBits`, which holds because every NaN in Lean's model is the canonical NaN.  Division, square root, comparisons, negation, absolute value, and conversions have no binary64 theorems yet.
