import Verified.Source

/-! The lemmas from which the reflector builds the equation `denote (reflect f) = f` of a Lean
definition: one lemma per Lean form.  Each states the meaning of a source expression whose parts
have the given meanings, with the right-hand side in the form that Lean elaborates.  The forms
whose meaning is definitionally Lean's term need no lemma beyond `rfl`.  An `if` on a `Prop`
comparison is the exception: Lean elaborates `if a < b` with `UInt64`'s `Decidable` instance,
which is not definitionally the source's `if decide (a < b) = true`. -/

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {funs : Funs S} {env : Env Γ}

theorem bin_eq (op : BinOp) {l r : Expr S Γ .word} {L R : UInt64}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.bin op l r).denote funs env = op.apply L R := by
  subst hl hr; rfl

theorem cmp_eq (op : CmpOp) {l r : Expr S Γ .word} {L R : UInt64}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.cmp op l r).denote funs env = op.apply L R := by
  subst hl hr; rfl

theorem not_eq {e : Expr S Γ .bool} {E : Bool} (h : e.denote funs env = E) :
    (Expr.not e).denote funs env = !E := by
  subst h; rfl

theorem and_eq {l r : Expr S Γ .bool} {L R : Bool}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.and l r).denote funs env = (L && R) := by
  subst hl hr; rfl

theorem or_eq {l r : Expr S Γ .bool} {L R : Bool}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.or l r).denote funs env = (L || R) := by
  subst hl hr; rfl

theorem ite_eq {t : Ty} {c : Expr S Γ .bool} {a b : Expr S Γ t} {C : Bool} {A B : t.denote}
    (hc : c.denote funs env = C) (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite c a b).denote funs env = if C then A else B := by
  subst hc ha hb; rfl

theorem ite_lt_eq {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.cmp .lt l r) a b).denote funs env = if L < R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, CmpOp.apply]

theorem ite_le_eq {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.cmp .le l r) a b).denote funs env = if L ≤ R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, CmpOp.apply]

theorem ite_eqP_eq {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.cmp .eq l r) a b).denote funs env = if L = R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, CmpOp.apply]

theorem ite_ne_eq {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.cmp .ne l r) a b).denote funs env = if L ≠ R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, CmpOp.apply]

theorem letE_eq {s t : Ty} {v : Expr S Γ s} {b : Expr S (s :: Γ) t} {V : s.denote}
    {B : s.denote → t.denote} (hv : v.denote funs env = V)
    (hb : ∀ x, b.denote funs (.cons x env) = B x) :
    (Expr.letE v b).denote funs env = B V := by
  subst hv; exact hb _

theorem ofFn_nil_eq :
    Env.ofFn (fun i => ((Args.nil : Args S Γ []).get i).denote funs env) = Env.nil := rfl

theorem ofFn_cons_eq {t : Ty} {ts : List Ty} {e : Expr S Γ t} {rest : Args S Γ ts}
    {A : t.denote} {As : Env ts} (he : e.denote funs env = A)
    (hrest : Env.ofFn (fun i => (rest.get i).denote funs env) = As) :
    Env.ofFn (fun i => ((Args.cons e rest).get i).denote funs env) = Env.cons A As := by
  subst he hrest; rfl

/-- A call means its callee's value at its arguments' values. -/
theorem call_eq {g : Sig} (f : FVar S g)
    {args : (i : Fin g.params.length) → Expr S Γ (g.params.get i)} {A : Env g.params}
    {R : g.result.denote}
    (hargs : Env.ofFn (fun i => (args i).denote funs env) = A) (hf : funs.get f A = R) :
    (Expr.call f args).denote funs env = R := by
  subst hargs; exact hf

theorem pair_eq {s t : Ty} {a : Expr S Γ s} {b : Expr S Γ t} {A : s.denote} {B : t.denote}
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.pair a b).denote funs env = (A, B) := by
  subst ha hb; rfl

/-- A destructuring of a pair, which `Prod.fst`, `Prod.snd`, and `match` on a pair become. -/
theorem letPair_eq {s t u : Ty} {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u}
    {E : s.denote × t.denote} {B : s.denote → t.denote → u.denote}
    (he : e.denote funs env = E) (hb : ∀ a b, body.denote funs (.cons b (.cons a env)) = B a b) :
    (Expr.letPair e body).denote funs env = B E.1 E.2 := by
  subst he; exact hb _ _

/-- A loop means `LeanExe.loop` with the meanings of its count, its initial state, and its
body. -/
theorem loop_eq {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {body : Expr S (t :: .word :: Γ) t} {N : UInt64} {I : t.denote}
    {B : UInt64 → t.denote → t.denote} (hn : count.denote funs env = N)
    (hi : init.denote funs env = I)
    (hb : ∀ i acc, body.denote funs (.cons acc (.cons i env)) = B i acc) :
    (Expr.loop count init body).denote funs env = LeanExe.loop N I B := by
  subst hn hi
  obtain rfl : (fun i acc => body.denote funs (.cons acc (.cons i env))) = B :=
    funext fun i => funext (hb i)
  rfl

/-- The size of an array, as a word. -/
theorem size_eq {a : Expr S Γ .array} {A : Array UInt64} (ha : a.denote funs env = A) :
    (Expr.size a).denote funs env = A.size.toUInt64 := by
  subst ha; rfl

/-- A read of an array, 0 past its end. -/
theorem get_eq {a : Expr S Γ .array} {i : Expr S Γ .word} {A : Array UInt64} {I : UInt64}
    (ha : a.denote funs env = A) (hi : i.denote funs env = I) :
    (Expr.get a i).denote funs env = A[I.toNat]! := by
  subst ha hi; rfl

end Verified.Reflect
