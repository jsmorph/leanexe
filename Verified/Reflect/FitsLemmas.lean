import Verified.Reflect.BoundLemmas

/-! The lemmas from which the reflector builds the equation between whether a function's calls find
their frames, `Expr.fits`, and a Lean term: one lemma per source form whose frames depend on
values, with the forms of conditions that `BoundLemmas` distinguishes.  The frames of a form
without such a dependence follow from `Expr.fits` by its definition.  As in `BoundLemmas`, each
conclusion is built from the lemma's arguments, and a binder's body enters through its equation at
the value. -/

namespace Verified.Reflect

variable {S : List Sig} {Γ : List Ty} {funs : Funs S} {fits : Fits S} {env : Env Γ}

/-! `if`, one lemma per form of condition. -/

theorem ite_fits {t : Ty} {c : Expr S Γ .bool} {a b : Expr S Γ t} {C CF AF BF : Bool}
    (hc : c.denote funs env = C) (hcf : c.fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite c a b).fits funs fits env = (CF && if C then AF else BF) := by
  subst hc hcf haf hbf; rfl

theorem ite_lt_fits {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.cmp .lt l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.cmp .lt l r) a b).fits funs fits env = (CF && if L < R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

theorem ite_le_fits {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.cmp .le l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.cmp .le l r) a b).fits funs fits env = (CF && if L ≤ R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

theorem ite_eqP_fits {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.cmp .eq l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.cmp .eq l r) a b).fits funs fits env = (CF && if L = R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

theorem ite_ne_fits {t : Ty} {l r : Expr S Γ .word} {a b : Expr S Γ t} {L R : UInt64}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.cmp .ne l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.cmp .ne l r) a b).fits funs fits env = (CF && if L ≠ R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, CmpOp.apply]

theorem ite_flt_fits {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.fcmp .lt l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.fcmp .lt l r) a b).fits funs fits env = (CF && if L < R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, FCmpOp.apply]

theorem ite_fle_fits {t : Ty} {l r : Expr S Γ .float} {a b : Expr S Γ t} {L R : Float}
    {CF AF BF : Bool} (hl : l.denote funs env = L) (hr : r.denote funs env = R)
    (hcf : (Expr.fcmp .le l r).fits funs fits env = CF)
    (haf : a.fits funs fits env = AF) (hbf : b.fits funs fits env = BF) :
    (Expr.ite (.fcmp .le l r) a b).fits funs fits env = (CF && if L ≤ R then AF else BF) := by
  rw [ite_fits rfl hcf haf hbf]
  subst hl hr; simp [Expr.denote, FCmpOp.apply]

/-! `let`, destructuring, and calls. -/

theorem letE_fits {s t : Ty} {v : Expr S Γ s} {b : Expr S (s :: Γ) t} {V : s.denote}
    {VF BF : Bool} (hv : v.denote funs env = V) (hvf : v.fits funs fits env = VF)
    (hbf : b.fits funs fits (.cons V env) = BF) :
    (Expr.letE v b).fits funs fits env = (VF && BF) := by
  subst hv hvf hbf; rfl

theorem letE_flat_fits {s t : Ty} {α : Type} (φ : α → s.denote) (X : α) {v : Expr S Γ s}
    {b : Expr S (s :: Γ) t} {VF BF : Bool} (hv : v.denote funs env = φ X)
    (hvf : v.fits funs fits env = VF) (hbf : b.fits funs fits (.cons (φ X) env) = BF) :
    (Expr.letE v b).fits funs fits env = (VF && BF) := by
  subst hvf hbf; rw [← hv]; rfl

theorem letPair_fits {s t u : Ty} {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u}
    {E : s.denote × t.denote} {A : s.denote} {B : t.denote} {EF BF : Bool}
    (he : e.denote funs env = E) (hA : E.1 = A) (hB : E.2 = B) (hef : e.fits funs fits env = EF)
    (hbf : body.fits funs fits (.cons B (.cons A env)) = BF) :
    (Expr.letPair e body).fits funs fits env = (EF && BF) := by
  subst he hA hB hef hbf; rfl

theorem letPair_flat_fits {s t u : Ty} {α β : Type} (φa : α → s.denote) (φb : β → t.denote)
    (P : α × β) {e : Expr S Γ (.pair s t)} {body : Expr S (t :: s :: Γ) u} {A : α} {B : β}
    {EF BF : Bool} (he : e.denote funs env = (φa P.1, φb P.2)) (hA : P.1 = A) (hB : P.2 = B)
    (hef : e.fits funs fits env = EF)
    (hbf : body.fits funs fits (.cons (φb B) (.cons (φa A) env)) = BF) :
    (Expr.letPair e body).fits funs fits env = (EF && BF) := by
  subst hA hB hef hbf; simp only [Expr.fits, he]

/-- The frames of a call's arguments. -/
def ArgsFits (funs : Funs S) (fits : Fits S) (env : Env Γ) : {ps : List Ty} → Args S Γ ps → Bool
  | [], .nil => true
  | _ :: _, .cons e rest => e.fits funs fits env && ArgsFits funs fits env rest

theorem argsAll_eq_argsFits : {ps : List Ty} → (argList : Args S Γ ps) →
    (argsAll fun i => (argList.get i).fits funs fits env) = ArgsFits funs fits env argList
  | [], .nil => rfl
  | _ :: _, .cons e rest => by
    simp only [argsAll, ArgsFits]
    exact congrArg (e.fits funs fits env && ·) (argsAll_eq_argsFits rest)

theorem argsFits_nil : ArgsFits funs fits env (.nil : Args S Γ []) = true := rfl

theorem argsFits_cons {t : Ty} {ts : List Ty} {e : Expr S Γ t} {rest : Args S Γ ts} {E R : Bool}
    (he : e.fits funs fits env = E) (hr : ArgsFits funs fits env rest = R) :
    ArgsFits funs fits env (.cons e rest) = (E && R) := by
  subst he hr; rfl

/-- A call of a function whose code takes the call depth: its arguments' frames, and the
callee's at the arguments. -/
theorem call_depth_fits {g : Sig} (f : FVar S g) {argList : Args S Γ g.params}
    {A : Env g.params} {AS R : Bool} (hd : g.depth = true)
    (hargs : Env.ofFn (fun i => (argList.get i).denote funs env) = A)
    (hsum : ArgsFits funs fits env argList = AS) (hf : fits.get f A = R) :
    (Expr.call f argList.get).fits funs fits env = (AS && R) := by
  subst hargs hsum hf
  rw [← argsAll_eq_argsFits]
  simp [Expr.fits, hd]

/-- A call of a function whose code takes no call depth: its arguments' frames. -/
theorem call_fits {g : Sig} (f : FVar S g) {argList : Args S Γ g.params} {AS : Bool}
    (hd : g.depth = false) (hsum : ArgsFits funs fits env argList = AS) :
    (Expr.call f argList.get).fits funs fits env = AS := by
  subst hsum
  rw [← argsAll_eq_argsFits]
  simp [Expr.fits, hd]

/-! Loops and builds. -/

/-- `loopFits` over the images of states under `φ`. -/
theorem loopFits_map {α β : Type} (φ : α → β) {CF : β → Bool} {C : β → Bool}
    {BF : UInt64 → β → Bool} {G : UInt64 → β → β} {F : UInt64 → α → α}
    (h : ∀ i s, G i (φ s) = φ (F i s)) :
    ∀ (n : Nat) (i : UInt64) (s : α), loopFits CF C BF G n i (φ s) =
      loopFits (fun s => CF (φ s)) (fun s => C (φ s)) (fun i s => BF i (φ s)) F n i s
  | 0, _, _ => rfl
  | n + 1, i, s => by
    simp only [loopFits, h, loopFits_map φ h n]

theorem loop_fits {t : Ty} {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t}
    {N : UInt64} {I : t.denote} {C : t.denote → Bool} {F : UInt64 → t.denote → t.denote}
    {NF IF : Bool} {CF : t.denote → Bool} {BF : UInt64 → t.denote → Bool}
    (hn : count.denote funs env = N) (hi : init.denote funs env = I)
    (hc : ∀ s, cond.denote funs (.cons s env) = C s)
    (hb : ∀ i s, body.denote funs (.cons s (.cons i env)) = F i s)
    (hnf : count.fits funs fits env = NF) (hif : init.fits funs fits env = IF)
    (hcf : ∀ s, cond.fits funs fits (.cons s env) = CF s)
    (hbf : ∀ i s, body.fits funs fits (.cons s (.cons i env)) = BF i s) :
    (Expr.loop count init cond body).fits funs fits env =
      (NF && IF && loopFits CF C BF F N.toNat 0 I) := by
  subst hn hi hnf hif
  obtain rfl : (fun s => cond.denote funs (.cons s env)) = C := funext hc
  obtain rfl : (fun i s => body.denote funs (.cons s (.cons i env))) = F :=
    funext fun i => funext (hb i)
  obtain rfl : (fun s => cond.fits funs fits (.cons s env)) = CF := funext hcf
  obtain rfl : (fun i s => body.fits funs fits (.cons s (.cons i env))) = BF :=
    funext fun i => funext (hbf i)
  rfl

theorem loop_flat_fits {t : Ty} {α : Type} (φ : α → t.denote) (I : α) (C : α → Bool)
    (F : UInt64 → α → α) {count : Expr S Γ .word} {init : Expr S Γ t}
    {cond : Expr S (t :: Γ) .bool} {body : Expr S (t :: .word :: Γ) t} {N : UInt64}
    {NF IF : Bool} {CF : α → Bool} {BF : UInt64 → α → Bool}
    (hn : count.denote funs env = N) (hi : init.denote funs env = φ I)
    (hc : ∀ s, cond.denote funs (.cons (φ s) env) = C s)
    (hb : ∀ i s, body.denote funs (.cons (φ s) (.cons i env)) = φ (F i s))
    (hnf : count.fits funs fits env = NF) (hif : init.fits funs fits env = IF)
    (hcf : ∀ s, cond.fits funs fits (.cons (φ s) env) = CF s)
    (hbf : ∀ i s, body.fits funs fits (.cons (φ s) (.cons i env)) = BF i s) :
    (Expr.loop count init cond body).fits funs fits env =
      (NF && IF && loopFits CF C BF F N.toNat 0 I) := by
  subst hn hnf hif
  show (_ && _ && loopFits _ _ _ (fun i s => body.denote funs (.cons s (.cons i env))) _ 0
    (init.denote funs env)) = _
  rw [hi, loopFits_map φ hb]
  simp only [hc, hcf, hbf]

theorem build_fits {e : Elem} {count : Expr S Γ .word} {elem : Expr S (.word :: Γ) (.elem e)}
    {N : UInt64} {NF : Bool} {EF : Nat → Bool}
    (hn : count.denote funs env = N) (hnf : count.fits funs fits env = NF)
    (hef : ∀ k : Nat, elem.fits funs fits (.cons (UInt64.ofNat k) env) = EF k) :
    (Expr.build count elem).fits funs fits env = (NF && allBelow EF N.toNat) := by
  subst hn hnf
  obtain rfl := funext hef
  rfl

/-! The frames of a function, and the chain of a program's frames. -/

theorem fits_get_there {g : Sig} (f : Func S) (rest : Prog S)
    (F : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.fitsAt (.cons f rest) (.cons F fs) k).get (.there v) env =
      (rest.fitsAt fs k).get v env :=
  rfl

theorem fits_get_thereRec {g : Sig} (f : RecFunc S) (rest : Prog S)
    (M : Env f.params → f.result.denote) (fs : Funs S) (k : Nat) (v : FVar S g)
    (env : Env g.params) :
    (Prog.fitsAt (.consRec f rest) (.cons M fs) k).get (.there v) env =
      (rest.fitsAt fs k).get v env :=
  rfl

/-- The frames of a function whose code takes the call depth, with `k` frames. -/
theorem fits_get_hereDepth (f : Func S) (rest : Prog S) (F : Env f.params → f.result.denote)
    (fs : Funs S) (k : Nat) (hd : f.depth = true) (env : Env f.params) :
    (Prog.fitsAt (.cons f rest) (.cons F fs) k).get .here env =
      f.fitsAt fs (rest.fitsAt fs) k env := by
  rw [Prog.fitsAt_cons_here, if_pos (by simp [hd])]

/-- The bound of a function whose code takes the call depth, with `k` frames. -/
theorem bounds_get_hereDepth (f : Func S) (rest : Prog S) (F : Env f.params → f.result.denote)
    (fs : Funs S) (k : Nat) (hd : f.depth = true) (env : Env f.params) :
    (Prog.boundsAt (.cons f rest) (.cons F fs) k).get .here env =
      f.boundAt fs (rest.boundsAt fs) k env := by
  rw [Prog.boundsAt_cons_here, if_pos (by simp [hd])]

end Verified.Reflect
