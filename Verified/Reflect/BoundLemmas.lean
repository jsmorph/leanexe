import Verified.BoundFacts

/-! The lemmas from which the reflector builds the equation between a function's allocation bound
and a Lean term: one lemma per source form and side condition.  Each states `Expr.allocs` of a
source expression from the bounds of its parts, with the modes and live sets of `Expr.allocs`, and
each side condition is an equation between a closed term and a constructor, which the kernel checks
by `rfl`.  The lemmas hold for every program, mode list, and live set, so the kernel checks each
once, when this file builds.

Each conclusion is built from the lemma's arguments without applying an argument or building a
lambda, and a binder's body enters through its equation at the value.  The type that the kernel
infers for an application of a lemma, which instantiates without beta reduction, is then the type
that `inferType` computes, so the reflector joins two equations where their terms are identical.
The kernel compares two closed `Nat` sums that differ by evaluating both, since it reduces the
operands of `Nat.add` to numerals before it compares arguments, and a sum can hold a loop's
cost. -/

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {funs : Funs S} {bounds : Bounds S} {modes : List Mode}
  {live : Nat → Bool} {env : Env Γ}

/-! Leaves and variables. -/

theorem word_bound (v : UInt64) :
    (Expr.word v : Expr S Γ .word).allocs funs bounds modes live env = 0 := rfl

theorem bool_bound (v : Bool) :
    (Expr.bool v : Expr S Γ .bool).allocs funs bounds modes live env = 0 := rfl

theorem float_bound (bits : UInt64) :
    (Expr.float bits : Expr S Γ .float).allocs funs bounds modes live env = 0 := rfl

theorem size_bound {e : Elem} (x : Var Γ (.array e)) :
    (Expr.size x : Expr S Γ .word).allocs funs bounds modes live env = 0 := rfl

theorem proj_bound {e e' : Elem} (x : Var Γ (.elem e)) (p : Path e e') :
    (Expr.proj x p : Expr S Γ (.elem e')).allocs funs bounds modes live env = 0 := rfl

theorem var_elem_bound {e : Elem} (x : Var Γ (.elem e)) :
    (Expr.var x : Expr S Γ (.elem e)).allocs funs bounds modes live env = 0 := by
  simp [Expr.allocs, Var.cost, Ty.copyCost]

theorem var_copy_bound {t : Ty} (x : Var Γ t) {C : Nat}
    (hm : modeAt modes x.index = .owned) (hl : live x.index = true)
    (hc : t.copyCost (env.get x) = C) :
    (Expr.var x : Expr S Γ t).allocs funs bounds modes live env = C := by
  simp [Expr.allocs, Var.cost, hm, hl, hc]

theorem var_borrowed_bound {t : Ty} (x : Var Γ t) (hm : modeAt modes x.index = .borrowed) :
    (Expr.var x : Expr S Γ t).allocs funs bounds modes live env = 0 := by
  simp [Expr.allocs, Var.cost, hm]

theorem var_dead_bound {t : Ty} (x : Var Γ t) (hl : live x.index = false) :
    (Expr.var x : Expr S Γ t).allocs funs bounds modes live env = 0 := by
  simp [Expr.allocs, Var.cost, hl]

/-! Copies and coercions. -/

theorem copyCost_pair {a b : Ty} {v : a.denote × b.denote} {A B : Nat}
    (ha : a.copyCost v.1 = A) (hb : b.copyCost v.2 = B) : (Ty.pair a b).copyCost v = A + B := by
  subst ha hb; rfl

theorem copyCost_array {e : Elem} {xs : Array e.denote} {n w : Nat}
    (hn : xs.size = n) (hw : e.width = w) : (Ty.array e).copyCost xs = blockCost (n * w) := by
  subst hn hw; rfl

theorem coerce_copy {t : Ty} {s m : Mode} {v : t.denote} {C : Nat}
    (hs : s = .borrowed) (hm : m = .owned) (hc : t.copyCost v = C) : coerceCost t s m v = C := by
  subst hs hm hc; rfl

theorem coerce_owned {t : Ty} {s m : Mode} {v : t.denote} (hs : s = .owned) :
    coerceCost t s m v = 0 := by
  subst hs; simp [coerceCost]

theorem coerce_borrowed {t : Ty} {s m : Mode} {v : t.denote} (hm : m = .borrowed) :
    coerceCost t s m v = 0 := by
  subst hm; simp [coerceCost]

theorem coerce_elem {e : Elem} {s m : Mode} {v : e.denote} :
    coerceCost (.elem e) s m v = 0 := by
  simp [coerceCost, Ty.copyCost]

/-! Operators. -/

theorem bin_bound (op : BinOp) {l r : Expr S Γ .word} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.bin op l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem cmp_bound (op : CmpOp) {l r : Expr S Γ .word} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.cmp op l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem fbin_bound (op : FBinOp) {l r : Expr S Γ .float} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.fbin op l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem fcmp_bound (op : FCmpOp) {l r : Expr S Γ .float} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.fcmp op l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem and_bound {l r : Expr S Γ .bool} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.and l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem or_bound {l r : Expr S Γ .bool} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.or l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem mk_bound {a b : Elem} {l : Expr S Γ (.elem a)} {r : Expr S Γ (.elem b)} {L R : Nat}
    (hl : l.allocs funs bounds modes (fun i => live i || r.uses i) env = L)
    (hr : r.allocs funs bounds modes live env = R) :
    (Expr.mk l r).allocs funs bounds modes live env = L + R := by
  subst hl hr; rfl

theorem not_bound {e : Expr S Γ .bool} {E : Nat} (h : e.allocs funs bounds modes live env = E) :
    (Expr.not e).allocs funs bounds modes live env = E := by
  subst h; rfl

theorem funary_bound (op : FUnOp) {e : Expr S Γ .float} {E : Nat}
    (h : e.allocs funs bounds modes live env = E) :
    (Expr.funary op e).allocs funs bounds modes live env = E := by
  subst h; rfl

theorem toFloat_bound (op : ToFloat) {e : Expr S Γ .word} {E : Nat}
    (h : e.allocs funs bounds modes live env = E) :
    (Expr.toFloat op e).allocs funs bounds modes live env = E := by
  subst h; rfl

theorem toWord_bound (op : ToWord) {e : Expr S Γ .float} {E : Nat}
    (h : e.allocs funs bounds modes live env = E) :
    (Expr.toWord op e).allocs funs bounds modes live env = E := by
  subst h; rfl

/-! `if`, one lemma per form of condition that the reflector produces. -/

theorem ite_bound {t : Ty} {c : Expr S Γ .bool} {a b : Expr S Γ t} {C : Bool} {A B : t.denote}
    {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hc : c.denote funs env = C) (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : c.allocs funs bounds modes (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite c a b).allocs funs bounds modes live env = CA + if C then AA else BA := by
  subst hM hc ha hb hca haa hba; rfl

/-- `ite_bound` for a condition `L < R` on words. -/
theorem ite_lt_bound {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.cmp .lt l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.cmp .lt l r) a b).allocs funs bounds modes live env =
      CA + if L < R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

/-- `ite_bound` for a condition `L ≤ R` on words. -/
theorem ite_le_bound {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.cmp .le l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.cmp .le l r) a b).allocs funs bounds modes live env =
      CA + if L ≤ R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

/-- `ite_bound` for a condition `L = R` on words. -/
theorem ite_eqP_bound {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.cmp .eq l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.cmp .eq l r) a b).allocs funs bounds modes live env =
      CA + if L = R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

/-- `ite_bound` for a condition `L ≠ R` on words. -/
theorem ite_ne_bound {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.cmp .ne l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.cmp .ne l r) a b).allocs funs bounds modes live env =
      CA + if L ≠ R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

/-- `ite_bound` for a condition `L < R` on floats. -/
theorem ite_flt_bound {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.fcmp .lt l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.fcmp .lt l r) a b).allocs funs bounds modes live env =
      CA + if L < R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, FCmpOp.apply]

/-- `ite_bound` for a condition `L ≤ R` on floats. -/
theorem ite_fle_bound {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {A B : t.denote} {M : Mode} {CA AA BA : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (hca : (Expr.fcmp .le l r).allocs funs bounds modes
      (fun i => live i || a.uses i || b.uses i) env = CA)
    (haa : a.allocs funs bounds modes live env + coerceCost t (a.mode modes) M A = AA)
    (hba : b.allocs funs bounds modes live env + coerceCost t (b.mode modes) M B = BA) :
    (Expr.ite (.fcmp .le l r) a b).allocs funs bounds modes live env =
      CA + if L ≤ R then AA else BA := by
  rw [ite_bound hM rfl ha hb hca haa hba]
  subst hl hr; simp [Expr.denote, FCmpOp.apply]

/-! `let`, pairs, and destructuring. -/

theorem letE_bound {s t : Ty} {v : Expr S Γ s} {b : Expr S (s :: Γ) t} {m : Mode}
    {V : s.denote} {VA BA : Nat}
    (hm : v.mode modes = m) (hv : v.denote funs env = V)
    (hva : v.allocs funs bounds modes (fun i => live i || b.uses (i + 1)) env = VA)
    (hba : b.allocs funs bounds (m :: modes) (shift 1 live) (.cons V env) = BA) :
    (Expr.letE v b).allocs funs bounds modes live env = VA + BA := by
  subst hm hv hva hba; rfl

/-- `letE_bound` for a value that means `φ X` for a Lean value `X` of another type. -/
theorem letE_flat_bound {s t : Ty} {α : Type} (φ : α → s.denote) (X : α)
    {v : Expr S Γ s} {b : Expr S (s :: Γ) t} {m : Mode} {VA BA : Nat}
    (hm : v.mode modes = m) (hv : v.denote funs env = φ X)
    (hva : v.allocs funs bounds modes (fun i => live i || b.uses (i + 1)) env = VA)
    (hba : b.allocs funs bounds (m :: modes) (shift 1 live) (.cons (φ X) env) = BA) :
    (Expr.letE v b).allocs funs bounds modes live env = VA + BA := by
  subst hm hva hba; rw [← hv]; rfl

theorem pair_bound {s t : Ty} {a : Expr S Γ s} {b : Expr S Γ t} {M : Mode}
    {A : s.denote} {B : t.denote} {AA KA BA KB : Nat}
    (hM : (a.mode modes).join (b.mode modes) = M)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B)
    (haa : a.allocs funs bounds modes (fun i => live i || b.uses i) env = AA)
    (hka : coerceCost s (a.mode modes) M A = KA)
    (hba : b.allocs funs bounds modes live env = BA)
    (hkb : coerceCost t (b.mode modes) M B = KB) :
    (Expr.pair a b).allocs funs bounds modes live env = AA + KA + BA + KB := by
  subst hM ha hb haa hka hba hkb; rfl

/-- The bound of a destructuring, with the body's at the components `A` and `B` of the pair's
value `E`: its projections, or the components themselves when the value is built in place. -/
theorem letPair_bound {s t u : Ty} {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u}
    {m : Mode} {E : s.denote × t.denote} {A : s.denote} {B : t.denote} {EA BA : Nat}
    (hm : e.mode modes = m) (he : e.denote funs env = E) (hA : E.1 = A) (hB : E.2 = B)
    (hea : e.allocs funs bounds modes (fun i => live i || body.uses (i + 2)) env = EA)
    (hba : body.allocs funs bounds (m :: m :: modes) (shift 2 live) (.cons B (.cons A env)) =
      BA) :
    (Expr.letPair e body).allocs funs bounds modes live env = EA + BA := by
  subst hm he hA hB hea hba; rfl

/-- `letPair_bound` for a pair whose components are the flattenings `φa P.1` and `φb P.2` of a
Lean pair `P`. -/
theorem letPair_flat_bound {s t u : Ty} {α β : Type} (φa : α → s.denote) (φb : β → t.denote)
    (P : α × β) {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u} {m : Mode}
    {A : α} {B : β} {EA BA : Nat}
    (hm : e.mode modes = m) (he : e.denote funs env = (φa P.1, φb P.2)) (hA : P.1 = A)
    (hB : P.2 = B)
    (hea : e.allocs funs bounds modes (fun i => live i || body.uses (i + 2)) env = EA)
    (hba : body.allocs funs bounds (m :: m :: modes) (shift 2 live)
      (.cons (φb B) (.cons (φa A) env)) = BA) :
    (Expr.letPair e body).allocs funs bounds modes live env = EA + BA := by
  subst hm hA hB hea hba; simp only [Expr.allocs, he]

/-! Calls. -/

/-- The bytes of a call's arguments: a scalar argument's allocations under `all`, the copy that
`ownedCode` makes of an argument at an owned parameter under `kept`, and nothing for an argument
at a borrowed parameter. -/
def ArgsCost (funs : Funs S) (bounds : Bounds S) (modes : List Mode) (all kept : Nat → Bool)
    (env : Env Γ) (md : Nat → Mode) : {ps : List Ty} → Args S Γ ps → Nat
  | [], .nil => 0
  | t :: _, .cons e rest =>
    (if t.scalar then e.allocs funs bounds modes all env
     else if md 0 = .owned then e.ownedCost modes kept env else 0) +
      ArgsCost funs bounds modes all kept env (fun i => md (i + 1)) rest

/-- `ArgsCost` is the sum that `Expr.allocs` takes over a call's arguments. -/
theorem argsSum_eq_argsCost {all kept : Nat → Bool} :
    ∀ {ps : List Ty} (md : Nat → Mode) (argList : Args S Γ ps),
    argsSum (fun i : Fin ps.length => if (ps.get i).scalar then
        (argList.get i).allocs funs bounds modes all env
      else if md i = .owned then (argList.get i).ownedCost modes kept env else 0) =
    ArgsCost funs bounds modes all kept env md argList
  | [], _, .nil => rfl
  | _ :: _, md, .cons _ rest => by
    simp only [argsSum, ArgsCost]
    congr 1
    exact argsSum_eq_argsCost (fun i => md (i + 1)) rest

theorem argsCost_nil {all kept : Nat → Bool} {md : Nat → Mode} :
    ArgsCost funs bounds modes all kept env md (.nil : Args S Γ []) = 0 := rfl

theorem argsCost_scalar {all kept : Nat → Bool} {md : Nat → Mode} {t : Ty} {ts : List Ty}
    {e : Expr S Γ t} {rest : Args S Γ ts} {E R : Nat}
    (ht : t.scalar = true) (he : e.allocs funs bounds modes all env = E)
    (hr : ArgsCost funs bounds modes all kept env (fun i => md (i + 1)) rest = R) :
    ArgsCost funs bounds modes all kept env md (.cons e rest) = E + R := by
  subst he hr; simp [ArgsCost, ht]

theorem argsCost_owned {all kept : Nat → Bool} {md : Nat → Mode} {t : Ty} {ts : List Ty}
    {e : Expr S Γ t} {rest : Args S Γ ts} {E R : Nat}
    (ht : t.scalar = false) (hm : md 0 = .owned) (he : e.ownedCost modes kept env = E)
    (hr : ArgsCost funs bounds modes all kept env (fun i => md (i + 1)) rest = R) :
    ArgsCost funs bounds modes all kept env md (.cons e rest) = E + R := by
  subst he hr; simp [ArgsCost, ht, hm]

theorem argsCost_borrowed {all kept : Nat → Bool} {md : Nat → Mode} {t : Ty} {ts : List Ty}
    {e : Expr S Γ t} {rest : Args S Γ ts} {R : Nat}
    (ht : t.scalar = false) (hm : md 0 = .borrowed)
    (hr : ArgsCost funs bounds modes all kept env (fun i => md (i + 1)) rest = R) :
    ArgsCost funs bounds modes all kept env md (.cons e rest) = R := by
  subst hr; simp [ArgsCost, ht, hm]

/-- The owned copy of a variable that the code moves: an owned variable that dies. -/
theorem varOwned_move {t : Ty} (x : Var Γ t) {v : t.denote}
    (hm : modeAt modes x.index = .owned) (hl : live x.index = false) :
    x.ownedCost modes live v = 0 := by
  simp [Var.ownedCost, Var.cost, coerceCost, hm, hl]

/-- The owned copy of an owned variable that stays live. -/
theorem varOwned_copyLive {t : Ty} (x : Var Γ t) {v : t.denote} {C : Nat}
    (hm : modeAt modes x.index = .owned) (hl : live x.index = true) (hc : t.copyCost v = C) :
    x.ownedCost modes live v = C := by
  simp [Var.ownedCost, Var.cost, coerceCost, hm, hl, hc]

/-- The owned copy of a borrowed variable. -/
theorem varOwned_copyBorrowed {t : Ty} (x : Var Γ t) {v : t.denote} {C : Nat}
    (hm : modeAt modes x.index = .borrowed) (hc : t.copyCost v = C) :
    x.ownedCost modes live v = C := by
  simp [Var.ownedCost, Var.cost, coerceCost, hm, hc]

/-- The owned copy of an argument, a variable, from its owned copy as a variable. -/
theorem ownedArg_var {t : Ty} (x : Var Γ t) {kept : Nat → Bool} {C : Nat}
    (h : x.ownedCost modes kept (env.get x) = C) :
    (Expr.var x : Expr S Γ t).ownedCost modes kept env = C :=
  h

theorem call_bound {g : Sig} (f : FVar S g) {argList : Args S Γ g.params}
    {all kept : Nat → Bool} {A : Env g.params} {AS R : Nat}
    (hall : all = fun i => live i || argsAny fun j => (argList.get j).uses i)
    (hkept : kept = fun i =>
      all i && !(argsAny fun j => callMovesAt modes live argList.get j && (argList.get j).uses i))
    (hargs : Env.ofFn (fun i => (argList.get i).denote funs env) = A)
    (hsum : ArgsCost funs bounds modes all kept env g.mode argList = AS)
    (hb : bounds.get f A = R) :
    (Expr.call f argList.get).allocs funs bounds modes live env = AS + R := by
  subst hall hkept hargs hsum hb
  rw [← argsSum_eq_argsCost]
  rfl

/-! Loops and builds. -/

/-- `loopCost` over the images of states under `φ`. -/
theorem loopCost_map {α β : Type} (φ : α → β) {CA : β → Nat} {C : β → Bool}
    {BA : UInt64 → β → Nat} {G : UInt64 → β → β} {F : UInt64 → α → α}
    (h : ∀ i s, G i (φ s) = φ (F i s)) :
    ∀ (n : Nat) (i : UInt64) (s : α), loopCost CA C BA G n i (φ s) =
      loopCost (fun s => CA (φ s)) (fun s => C (φ s)) (fun i s => BA i (φ s)) F n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
    simp only [loopCost, h, loopCost_map φ h n]

theorem loop_bound {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t}
    {N : UInt64} {I : t.denote} {C : t.denote → Bool} {F : UInt64 → t.denote → t.denote}
    {all : Nat → Bool} {M : Mode} {NA IA KA : Nat} {CA : t.denote → Nat}
    {BA : UInt64 → t.denote → Nat}
    (hall : all = fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
    (hM : (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)) = M)
    (hn : count.denote funs env = N) (hi : init.denote funs env = I)
    (hc : ∀ s, cond.denote funs (.cons s env) = C s)
    (hb : ∀ i s, body.denote funs (.cons s (.cons i env)) = F i s)
    (hna : count.allocs funs bounds modes (fun i => all i || init.uses i) env = NA)
    (hia : init.allocs funs bounds modes all env = IA)
    (hka : coerceCost t (init.mode modes) M I = KA)
    (hca : ∀ s, cond.allocs funs bounds (.borrowed :: modes)
      (fun j => j == 0 || shift 1 all j) (.cons s env) = CA s)
    (hba : ∀ i s, body.allocs funs bounds (M :: .borrowed :: modes) (shift 2 all)
        (.cons s (.cons i env)) + coerceCost t (body.mode (M :: .borrowed :: modes)) M (F i s) =
      BA i s) :
    (Expr.loop count init cond body).allocs funs bounds modes live env =
      NA + IA + KA + loopCost CA C BA F N.toNat 0 I := by
  subst hall hM hn hi hna hia hka
  obtain rfl : (fun s => cond.denote funs (.cons s env)) = C := funext hc
  obtain rfl : (fun i s => body.denote funs (.cons s (.cons i env))) = F :=
    funext fun i => funext (hb i)
  obtain rfl : (fun s => cond.allocs funs bounds (.borrowed :: modes)
      (fun j => j == 0 || shift 1 (fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) j)
      (.cons s env)) = CA := funext hca
  obtain rfl := funext fun i => funext (hba i)
  rfl

/-- `loop_bound` for a state that is the flattening `φ s` of a Lean state `s`. -/
theorem loop_flat_bound {t : Ty} {α : Type} (φ : α → t.denote) (I : α) (C : α → Bool)
    (F : UInt64 → α → α) {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {N : UInt64}
    {all : Nat → Bool} {M : Mode} {NA IA KA : Nat} {CA : α → Nat} {BA : UInt64 → α → Nat}
    (hall : all = fun i => live i || cond.uses (i + 1) || body.uses (i + 2))
    (hM : (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)) = M)
    (hn : count.denote funs env = N) (hi : init.denote funs env = φ I)
    (hc : ∀ s, cond.denote funs (.cons (φ s) env) = C s)
    (hb : ∀ i s, body.denote funs (.cons (φ s) (.cons i env)) = φ (F i s))
    (hna : count.allocs funs bounds modes (fun i => all i || init.uses i) env = NA)
    (hia : init.allocs funs bounds modes all env = IA)
    (hka : coerceCost t (init.mode modes) M (φ I) = KA)
    (hca : ∀ s, cond.allocs funs bounds (.borrowed :: modes)
      (fun j => j == 0 || shift 1 all j) (.cons (φ s) env) = CA s)
    (hba : ∀ i s, body.allocs funs bounds (M :: .borrowed :: modes) (shift 2 all)
        (.cons (φ s) (.cons i env)) +
          coerceCost t (body.mode (M :: .borrowed :: modes)) M (φ (F i s)) = BA i s) :
    (Expr.loop count init cond body).allocs funs bounds modes live env =
      NA + IA + KA + loopCost CA C BA F N.toNat 0 I := by
  subst hall hM hn hna hia hka
  show _ + _ + _ + loopCost _ _ _ (fun i s => body.denote funs (.cons s (.cons i env))) _ 0
    (init.denote funs env) = _
  rw [hi, loopCost_map φ hb]
  simp only [hc, hb, hca, hba]

theorem build_bound {e : Elem} {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) (.elem e)}
    {N : UInt64} {all : Nat → Bool} {w NA : Nat} {EA : Nat → Nat}
    (hall : all = fun i => live i || elem.uses (i + 1)) (hw : e.width = w)
    (hn : count.denote funs env = N)
    (hna : count.allocs funs bounds modes all env = NA)
    (hea : ∀ k : Nat, elem.allocs funs bounds (.borrowed :: modes) (shift 1 all)
      (.cons (UInt64.ofNat k) env) = EA k) :
    (Expr.build count elem).allocs funs bounds modes live env =
      NA + blockCost (N.toNat * w) + sumBelow EA N.toNat := by
  subst hall hw hn hna
  obtain rfl := funext hea
  rfl

/-! Array operations. -/

theorem get_bound {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word} {IA : Nat}
    (hi : i.allocs funs bounds modes (fun j => live j || j == x.index) env = IA) :
    (Expr.get x i).allocs funs bounds modes live env = IA := by
  subst hi; rfl

theorem set_bound {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word}
    {v : Expr S Γ (.elem e)} {IA VA XA : Nat}
    (hi : i.allocs funs bounds modes (fun j => live j || j == x.index || v.uses j) env = IA)
    (hv : v.allocs funs bounds modes (fun j => live j || j == x.index) env = VA)
    (hx : x.ownedCost modes live (env.get x) = XA) :
    (Expr.set x i v).allocs funs bounds modes live env = IA + VA + XA := by
  subst hi hv hx; rfl

theorem eraseAt_bound {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word} {IA XA : Nat}
    (hi : i.allocs funs bounds modes (fun j => live j || j == x.index) env = IA)
    (hx : x.ownedCost modes live (env.get x) = XA) :
    (Expr.eraseAt x i).allocs funs bounds modes live env = IA + XA := by
  subst hi hx; rfl

theorem push_bound {e : Elem} (x : Var Γ (.array e)) {v : Expr S Γ (.elem e)} {k VA XA : Nat}
    (hk : (wordCount e.width).toNat = k)
    (hv : v.allocs funs bounds modes (fun j => live j || j == x.index) env = VA)
    (hx : x.roomCost modes live (env.get x) k = XA) :
    (Expr.push x v).allocs funs bounds modes live env = VA + XA := by
  subst hk hv hx; rfl

theorem insertAt_bound {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word}
    {v : Expr S Γ (.elem e)} {k IA VA XA : Nat}
    (hk : (wordCount e.width).toNat = k)
    (hi : i.allocs funs bounds modes (fun j => live j || j == x.index || v.uses j) env = IA)
    (hv : v.allocs funs bounds modes (fun j => live j || j == x.index) env = VA)
    (hx : x.roomCost modes live (env.get x) k = XA) :
    (Expr.insertAt x i v).allocs funs bounds modes live env = IA + VA + XA := by
  subst hk hi hv hx; rfl

theorem append_bound {e : Elem} (x y : Var Γ (.array e)) {k XA : Nat}
    (hk : (env.get y).size * e.width = k)
    (hx : x.roomCost modes (fun j => live j || j == y.index) (env.get x) k = XA) :
    (Expr.append x y).allocs funs bounds modes live env = XA := by
  subst hk hx; rfl

/-- The room for an owned array that dies: a block of twice the bytes of its new length. -/
theorem room_grow {e : Elem} (x : Var Γ (.array e)) {xs : Array e.denote} {ext n w : Nat}
    (hm : modeAt modes x.index = .owned) (hl : live x.index = false)
    (hn : xs.size = n) (hw : e.width = w) :
    x.roomCost modes live xs ext = growCost (n * w + ext) := by
  subst hn hw; simp [Var.roomCost, growCost, hm, hl]

/-- The room for an owned array that stays live: a copy at the new length. -/
theorem room_copyLive {e : Elem} (x : Var Γ (.array e)) {xs : Array e.denote} {ext n w : Nat}
    (hm : modeAt modes x.index = .owned) (hl : live x.index = true)
    (hn : xs.size = n) (hw : e.width = w) :
    x.roomCost modes live xs ext = blockCost (n * w + ext) := by
  subst hn hw; simp [Var.roomCost, blockCost, hm, hl]

/-- The room for a borrowed array: a copy at the new length. -/
theorem room_copyBorrowed {e : Elem} (x : Var Γ (.array e)) {xs : Array e.denote}
    {ext n w : Nat} (hm : modeAt modes x.index = .borrowed) (hn : xs.size = n)
    (hw : e.width = w) :
    x.roomCost modes live xs ext = blockCost (n * w + ext) := by
  subst hn hw; simp [Var.roomCost, blockCost, hm]

/-! The function and the chain of a program's bounds. -/

theorem func_bound {func : Func S} {args : Env func.params} {ms : List Mode}
    {V : func.result.denote} {BA KA : Nat}
    (hms : entryModes func.params func.modes = ms)
    (hv : func.body.denote funs args = V)
    (hba : func.body.allocs funs bounds ms (fun _ => false) args = BA)
    (hk : coerceCost func.result (func.body.mode ms) .owned V = KA) :
    func.bound funs bounds args = BA + KA := by
  subst hms hv hba hk; rfl

/-- The entry of a function whose code takes no call depth, at any number of frames: its own
bound, with its callees at 0 frames. -/
theorem bounds_get_here (f : Func S) (rest : Prog S) (F : Env f.params → f.result.denote)
    (fs : Funs S) (k : Nat) (hd : f.depth = false) (env : Env f.params) :
    (Prog.boundsAt (.cons f rest) (.cons F fs) k).get .here env =
      f.bound fs (rest.boundsAt fs 0) env := by
  rw [Prog.boundsAt_cons_here, if_neg (by simp [hd])]

theorem bounds_get_there {g : Sig} (f : Func S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.boundsAt (.cons f rest) (.cons F fs) k).get (.there v) env =
      (rest.boundsAt fs k).get v env :=
  rfl

theorem bounds_get_thereRec {g : Sig} (f : RecFunc S) (rest : Prog S)
    (M : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.boundsAt (.consRec f rest) (.cons M fs) k).get (.there v) env =
      (rest.boundsAt fs k).get v env :=
  rfl

end Verified.Reflect
