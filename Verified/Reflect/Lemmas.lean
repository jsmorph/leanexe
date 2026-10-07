import Verified.Source
import LeanExe.ProofKit.F64Bits

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

theorem fbin_eq (op : FBinOp) {l r : Expr S Γ .float} {L R : Float}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.fbin op l r).denote funs env = op.apply L R := by
  subst hl hr; rfl

theorem funary_eq (op : FUnOp) {e : Expr S Γ .float} {E : Float} (h : e.denote funs env = E) :
    (Expr.funary op e).denote funs env = op.apply E := by
  subst h; rfl

theorem toFloat_eq (op : ToFloat) {e : Expr S Γ .word} {E : UInt64}
    (h : e.denote funs env = E) : (Expr.toFloat op e).denote funs env = op.apply E := by
  subst h; rfl

theorem toWord_eq (op : ToWord) {e : Expr S Γ .float} {E : Float}
    (h : e.denote funs env = E) : (Expr.toWord op e).denote funs env = op.apply E := by
  subst h; rfl

theorem fcmp_eq (op : FCmpOp) {l r : Expr S Γ .float} {L R : Float}
    (hl : l.denote funs env = L) (hr : r.denote funs env = R) :
    (Expr.fcmp op l r).denote funs env = op.apply L R := by
  subst hl hr; rfl

/-- A float literal, from bits that the kernel checks. -/
theorem float_eq {bits : UInt64} {x : Float} (h : x.toBits = bits) :
    (Expr.float bits : Expr S Γ .float).denote funs env = x := by
  show Float.ofBits bits = x
  rw [← h, LeanExe.ProofKit.F64Bits.ofBits_toBits]

theorem ite_flt_eq {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.fcmp .lt l r) a b).denote funs env = if L < R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, FCmpOp.apply]

theorem ite_fle_eq {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {A B : t.denote} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (ha : a.denote funs env = A) (hb : b.denote funs env = B) :
    (Expr.ite (.fcmp .le l r) a b).denote funs env = if L ≤ R then A else B := by
  subst hl hr ha hb; simp [Expr.denote, FCmpOp.apply]

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

/-- `LeanExe.build` with the meanings of its count and its element function. -/
theorem build_eq {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) .word} {N : UInt64}
    {F : UInt64 → UInt64} (hn : count.denote funs env = N)
    (hf : ∀ i, elem.denote funs (.cons i env) = F i) :
    (Expr.build count elem).denote funs env = LeanExe.build N F := by
  subst hn
  obtain rfl : (fun i => elem.denote funs (.cons i env)) = F := funext hf
  rfl

/-- An update of an array variable, which leaves it unchanged past its end. -/
theorem set_eq (x : Var Γ .array) {i v : Expr S Γ .word} {I V : UInt64}
    (hi : i.denote funs env = I) (hv : v.denote funs env = V) :
    (Expr.set x i v).denote funs env = (env.get x).set! I.toNat V := by
  subst hi hv; rfl

/-- An array variable with one more element. -/
theorem push_eq (x : Var Γ .array) {v : Expr S Γ .word} {V : UInt64}
    (hv : v.denote funs env = V) :
    (Expr.push x v).denote funs env = (env.get x).push V := by
  subst hv; rfl

/-- A read of an array variable, 0 past its end. -/
theorem get_eq (x : Var Γ .array) {i : Expr S Γ .word} {I : UInt64}
    (hi : i.denote funs env = I) : (Expr.get x i).denote funs env = (env.get x)[I.toNat]! := by
  subst hi; rfl

end Verified.Reflect
