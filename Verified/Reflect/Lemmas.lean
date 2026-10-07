import Verified.Source
import LeanExe.Dialect.RepeatWhile
import LeanExe.Pipeline.Implements
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

/-- A binding whose value means `φ X` for a Lean value `X` of another type, with the body's
meaning given at every `φ x`.  The reflector uses it for a value of a structure type, whose
source value is its flattening. -/
theorem letE_flat_eq {s t : Ty} {α : Type} (φ : α → s.denote) (X : α) {v : Expr S Γ s}
    {b : Expr S (s :: Γ) t} {B : α → t.denote} (hv : v.denote funs env = φ X)
    (hb : ∀ x, b.denote funs (.cons (φ x) env) = B x) :
    (Expr.letE v b).denote funs env = B X := by
  rw [Expr.denote, hv]; exact hb X

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

/-- A tuple of two elements. -/
theorem mk_eq {a b : Elem} {x : Expr S Γ (.elem a)} {y : Expr S Γ (.elem b)} {X : a.denote}
    {Y : b.denote} (hx : x.denote funs env = X) (hy : y.denote funs env = Y) :
    (Expr.mk x y).denote funs env = (X, Y) := by
  subst hx hy; rfl

/-- A destructuring of a pair, which `Prod.fst`, `Prod.snd`, and `match` on a pair become. -/
theorem letPair_eq {s t u : Ty} {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u}
    {E : s.denote × t.denote} {B : s.denote → t.denote → u.denote}
    (he : e.denote funs env = E) (hb : ∀ a b, body.denote funs (.cons b (.cons a env)) = B a b) :
    (Expr.letPair e body).denote funs env = B E.1 E.2 := by
  subst he; exact hb _ _

/-- A destructuring of a pair whose components are the flattenings `φa P.1` and `φb P.2` of a Lean
pair `P`. -/
theorem letPair_flat_eq {s t u : Ty} {α β : Type} (φa : α → s.denote) (φb : β → t.denote)
    (P : α × β) {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u} {B : α → β → u.denote}
    (he : e.denote funs env = (φa P.1, φb P.2))
    (hb : ∀ a b, body.denote funs (.cons (φb b) (.cons (φa a) env)) = B a b) :
    (Expr.letPair e body).denote funs env = B P.1 P.2 := by
  rw [Expr.denote, he]; exact hb _ _

/-- A loop whose state is the image of a state under `φ` gives the image of the loop of the
states. -/
theorem loop_map {α β : Type} (φ : α → β) (n : UInt64) (init : α) (F : UInt64 → α → α)
    (G : UInt64 → β → β) (h : ∀ i s, G i (φ s) = φ (F i s)) :
    LeanExe.loop n (φ init) G = φ (LeanExe.loop n init F) := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ k ih => simp only [Nat.fold_succ, ih, h]

/-- A loop whose condition is `true` means `LeanExe.loop` with the meanings of its count, its
initial state, and its body. -/
theorem loop_eq {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {body : Expr S (t :: .word :: Γ) t} {N : UInt64} {I : t.denote}
    {B : UInt64 → t.denote → t.denote} (hn : count.denote funs env = N)
    (hi : init.denote funs env = I)
    (hb : ∀ i acc, body.denote funs (.cons acc (.cons i env)) = B i acc) :
    (Expr.loop count init (.bool true) body).denote funs env = LeanExe.loop N I B := by
  subst hn hi
  obtain rfl : (fun i acc => body.denote funs (.cons acc (.cons i env))) = B :=
    funext fun i => funext (hb i)
  rfl

/-- A loop whose condition is `true` and whose state is a structure: the source state is the
flattening of the Lean state. -/
theorem loop_flat_eq {t : Ty} {α : Type} (φ : α → t.denote) (I : α) (F : UInt64 → α → α)
    {count : Expr S Γ .word} {init : Expr S Γ t} {body : Expr S (t :: .word :: Γ) t} {N : UInt64}
    (hn : count.denote funs env = N) (hi : init.denote funs env = φ I)
    (hb : ∀ i s, body.denote funs (.cons (φ s) (.cons i env)) = φ (F i s)) :
    (Expr.loop count init (.bool true) body).denote funs env = φ (LeanExe.loop N I F) := by
  subst hn
  show LeanExe.loop _ (init.denote funs env)
    (fun i acc => body.denote funs (.cons acc (.cons i env))) = _
  rw [hi]
  exact loop_map φ _ I F _ hb

/-- `LeanExe.repeatWhile` is the loop over its fuel whose function applies `step` to a state
that satisfies `cond` and keeps any other. -/
theorem repeatWhile_eq_loop {α : Type} (fuel : UInt64) (init : α) (cond : α → Bool)
    (step : α → α) :
    LeanExe.repeatWhile fuel init cond step =
      LeanExe.loop fuel init (fun _ s => bif cond s then step s else s) := by
  unfold LeanExe.repeatWhile LeanExe.loop
  suffices h : ∀ k s, LeanExe.repeatWhile.go cond step k s =
      (fun s => bif cond s then step s else s)^[k] s by
    rw [h]
    induction fuel.toNat with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.fold_succ]
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [Function.iterate_succ_apply]
    cases hc : cond s
    · simp only [LeanExe.repeatWhile.go, hc, Bool.cond_false]
      exact (Function.iterate_fixed (by simp [hc]) k).symm
    · simp [LeanExe.repeatWhile.go, hc, ih]

/-- A loop whose body ignores the index means `LeanExe.repeatWhile` with the meanings of its
count, its initial state, its condition, and its body. -/
theorem repeatWhile_eq {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {N : UInt64}
    {I : t.denote} (hn : count.denote funs env = N) (hi : init.denote funs env = I)
    (C : t.denote → Bool) (B : t.denote → t.denote)
    (hc : ∀ acc, cond.denote funs (.cons acc env) = C acc)
    (hb : ∀ i acc, body.denote funs (.cons acc (.cons i env)) = B acc) :
    (Expr.loop count init cond body).denote funs env = LeanExe.repeatWhile N I C B := by
  rw [repeatWhile_eq_loop]
  subst hn hi
  show LeanExe.loop _ _ (fun i acc => bif cond.denote funs (.cons acc env) then
    body.denote funs (.cons acc (.cons i env)) else acc) = _
  simp only [hc, hb]

/-- `repeatWhile_eq` for a state that is a structure. -/
theorem repeatWhile_flat_eq {t : Ty} {α : Type} (φ : α → t.denote) (I : α) (C : α → Bool)
    (B : α → α) {count : Expr S Γ .word} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} {N : UInt64}
    (hn : count.denote funs env = N) (hi : init.denote funs env = φ I)
    (hc : ∀ s, cond.denote funs (.cons (φ s) env) = C s)
    (hb : ∀ i s, body.denote funs (.cons (φ s) (.cons i env)) = φ (B s)) :
    (Expr.loop count init cond body).denote funs env = φ (LeanExe.repeatWhile N I C B) := by
  rw [repeatWhile_eq_loop]
  subst hn
  show LeanExe.loop _ (init.denote funs env) (fun i acc => bif cond.denote funs (.cons acc env)
    then body.denote funs (.cons acc (.cons i env)) else acc) = _
  rw [hi]
  exact loop_map φ _ I _ _ fun i s => by simp only [hc, hb]; cases C s <;> rfl

/-- `LeanExe.build` with the meanings of its count and its element function. -/
theorem build_eq {e : Elem} {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) (.elem e)}
    {N : UInt64} {F : UInt64 → e.denote} (hn : count.denote funs env = N)
    (hf : ∀ i, elem.denote funs (.cons i env) = F i) :
    (Expr.build count elem).denote funs env = LeanExe.build N F := by
  subst hn
  obtain rfl : (fun i => elem.denote funs (.cons i env)) = F := funext hf
  rfl

/-- An update of an array variable, which leaves it unchanged past its end. -/
theorem set_eq {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word} {v : Expr S Γ (.elem e)}
    {I : UInt64} {V : e.denote} (hi : i.denote funs env = I) (hv : v.denote funs env = V) :
    (Expr.set x i v).denote funs env = (env.get x).set! I.toNat V := by
  subst hi hv; rfl

/-- An array variable with one more element. -/
theorem push_eq {e : Elem} (x : Var Γ (.array e)) {v : Expr S Γ (.elem e)} {V : e.denote}
    (hv : v.denote funs env = V) :
    (Expr.push x v).denote funs env = (env.get x).push V := by
  subst hv; rfl

/-- A read of an array variable, the element type's default value past its end. -/
theorem get_eq {e : Elem} (x : Var Γ (.array e)) {i : Expr S Γ .word} {I : UInt64}
    (hi : i.denote funs env = I) : (Expr.get x i).denote funs env = (env.get x)[I.toNat]! := by
  subst hi; rfl

/-! The array operations on an array of structures, whose source value is the array of the
elements' flattenings. -/

theorem size_map_eq {e : Elem} {α : Type} (φ : α → e.denote) (x : Var Γ (.array e))
    (xs : Array α) (hx : env.get x = xs.map φ) :
    (Expr.size (S := S) x).denote funs env = xs.size.toUInt64 := by
  show (env.get x).size.toUInt64 = _
  rw [hx, Array.size_map]

/-- A read past the end gives the flattening of Lean's default structure, which must be the
element type's default value. -/
theorem get_map_eq {e : Elem} {α : Type} [Inhabited α] (φ : α → e.denote)
    (hd : φ default = default) (x : Var Γ (.array e)) (xs : Array α) {i : Expr S Γ .word}
    {I : UInt64} (hx : env.get x = xs.map φ) (hi : i.denote funs env = I) :
    (Expr.get x i).denote funs env = φ xs[I.toNat]! := by
  show (env.get x)[(i.denote funs env).toNat]! = _
  rw [hx, hi]
  by_cases h : I.toNat < xs.size
  · rw [getElem!_pos (xs.map φ) I.toNat (by simpa using h), getElem!_pos xs I.toNat h,
      Array.getElem_map]
  · rw [getElem!_neg (xs.map φ) I.toNat (by simpa using h), getElem!_neg xs I.toNat h, hd]

theorem set_map_eq {e : Elem} {α : Type} (φ : α → e.denote) (x : Var Γ (.array e))
    (xs : Array α) {i : Expr S Γ .word} {v : Expr S Γ (.elem e)} {I : UInt64} (V : α)
    (hx : env.get x = xs.map φ) (hi : i.denote funs env = I) (hv : v.denote funs env = φ V) :
    (Expr.set x i v).denote funs env = (xs.set! I.toNat V).map φ := by
  show (env.get x).set! (i.denote funs env).toNat (v.denote funs env) = _
  rw [hx, hi, hv, Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds,
    Array.map_setIfInBounds]

theorem push_map_eq {e : Elem} {α : Type} (φ : α → e.denote) (x : Var Γ (.array e))
    (xs : Array α) {v : Expr S Γ (.elem e)} (V : α) (hx : env.get x = xs.map φ)
    (hv : v.denote funs env = φ V) :
    (Expr.push x v).denote funs env = (xs.push V).map φ := by
  show (env.get x).push (v.denote funs env) = _
  rw [hx, hv, Array.map_push]

theorem append_map_eq {e : Elem} {α : Type} (φ : α → e.denote) (x y : Var Γ (.array e))
    (xs ys : Array α) (hx : env.get x = xs.map φ) (hy : env.get y = ys.map φ) :
    (Expr.append (S := S) x y).denote funs env = (xs ++ ys).map φ := by
  show env.get x ++ env.get y = _
  rw [hx, hy, Array.map_append]

theorem build_map_eq {e : Elem} {α : Type} (φ : α → e.denote) (F : UInt64 → α)
    {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) (.elem e)} {N : UInt64}
    (hn : count.denote funs env = N) (hf : ∀ i, elem.denote funs (.cons i env) = φ (F i)) :
    (Expr.build count elem).denote funs env = (LeanExe.build N F).map φ := by
  subst hn
  show LeanExe.build _ (fun i => elem.denote funs (.cons i env)) = _
  simp only [LeanExe.build, hf, Array.map_ofFn]
  rfl

/-- A function of a pair at the pair of its components is the function at the pair, by eta for
pairs on a variable. -/
theorem pair_eta {α β γ : Type} (B : α × β → γ) (v : α × β) : B (v.1, v.2) = B v := rfl

/-! An enumeration is the word of its `Flat` instance.  A comparison of enumerations is the
comparison of their words, given that the flattening is injective. -/

open LeanExe.Pipeline in
theorem flat_decide {E : Type} [Flat E UInt64] (h : Function.Injective (Flat.flat : E → UInt64))
    (a b : E) [Decidable (a = b)] : decide (a = b) = decide (Flat.flat a = Flat.flat b) :=
  decide_eq_decide.mpr h.eq_iff.symm

open LeanExe.Pipeline in
theorem flat_beq {E : Type} [Flat E UInt64] [BEq E] [LawfulBEq E]
    (h : Function.Injective (Flat.flat : E → UInt64)) (a b : E) :
    (a == b) = (Flat.flat a == Flat.flat b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h.eq_iff]

open LeanExe.Pipeline in
theorem flat_bne {E : Type} [Flat E UInt64] [BEq E] [LawfulBEq E]
    (h : Function.Injective (Flat.flat : E → UInt64)) (a b : E) :
    (a != b) = (Flat.flat a != Flat.flat b) := by
  rw [bne, bne, flat_beq h]

open LeanExe.Pipeline in
theorem flat_ite {E α : Type} [Flat E UInt64] (h : Function.Injective (Flat.flat : E → UInt64))
    (a b : E) [Decidable (a = b)] (x y : α) :
    (if a = b then x else y) = (if Flat.flat a = Flat.flat b then x else y) := by
  by_cases hab : a = b <;> simp [hab, h.eq_iff]

open LeanExe.Pipeline in
theorem flat_ite_ne {E α : Type} [Flat E UInt64]
    (h : Function.Injective (Flat.flat : E → UInt64)) (a b : E) [Decidable (a ≠ b)] (x y : α) :
    (if a ≠ b then x else y) = (if Flat.flat a ≠ Flat.flat b then x else y) := by
  by_cases hab : a = b <;> simp [hab, h.eq_iff]

/-- A statement about every environment of a nonempty context, from the statement about each
first value and each environment of the rest. -/
theorem env_forall_cons {t : Ty} {Γ' : List Ty} {P : Env (t :: Γ') → Prop}
    (h : ∀ v env, P (.cons v env)) : ∀ env, P env
  | .cons v env => h v env

theorem env_forall_nil {P : Env [] → Prop} (h : P .nil) : ∀ env, P env
  | .nil => h

/-- An array mapped by a function and then by a left inverse of it. -/
theorem map_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x)
    (xs : Array α) : (xs.map f).map g = xs := by
  rw [Array.map_map, show g ∘ f = id from funext h, Array.map_id]

end Verified.Reflect
