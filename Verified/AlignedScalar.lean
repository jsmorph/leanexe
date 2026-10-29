import Verified.AlignedSpecIn
import LeanExe.ProofKit.AlignedAtomic

/-!
The constructs whose values are scalars, under the flag: constants, the operations on words,
floats, and `Bool`s, the conversions, and the tuple of two elements.  Each is its original in
`ExprCorrect.lean` with `CodeSpecX strict` for `CodeSpec`, `seqX_spec` for `seq_spec`, and the
flagged rules for the trailing instructions.  Their values hold no pointers, so the continuation's
alignment is `HoldsA` of the variables live after the code, which the operands' specifications
give, and `Ty.AlignedVal.scalar`.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- A value without arrays has no regions. -/
theorem Ty.AlignedVal.scalar {mode : Mode} {store : Store Unit} {t : Ty} {ws : List Value}
    {v : t.denote} (h : t.scalar = true) : Ty.AlignedVal mode store t ws v := fun r hr => by
  rw [Ty.regions_scalar t h] at hr; exact nomatch hr

/-- A buffer at root 0 has no regions. -/
theorem Ty.AlignedVal.bytesNull {mode : Mode} {store : Store Unit} {l : UInt64}
    {v : LeanExe.Bytes} : Ty.AlignedVal mode store .bytes [.i64 0, .i64 l] v := by
  cases mode <;> simp [Ty.AlignedVal, Ty.regions, Ty.blocks, Ty.reads, Bytes.roots]

/-- The invariant for locals that agree below `base`. -/
theorem HoldsA.agree {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s s' : Locals}
    (h : Holds env slots live base heap store s) (hA : HoldsA env slots live heap store s)
    (hF : Frame base s s') : HoldsA env slots live heap store s' :=
  ⟨hA.1, fun t x hx ws hold hl => hA.2 t x hx ws ((h.hold_agree hF hx hl).mp hold) hl⟩

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value} {strict : Bool}

/-- A constant word. -/
theorem specX_word {Γ : List Ty} (value : UInt64) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.word (S := S) (Γ := Γ) value) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.usesFast_eq, Expr.denote, wpX_constI64_cons] using
    hNext heap store s [.i64 value] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .word rfl] at hb; exact nomatch hb)
      (fun hs => ⟨(hAl hs).live_mono (by intro i h; simp [h]), Ty.AlignedVal.scalar rfl⟩)
      (fun _ => Nat.le_add_right _ _)

theorem specX_treeNil {Γ : List Ty} (shape : TreeShape) (hn : shape.hasNull = true) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.treeNil (S := S) (Γ := Γ) shape hn) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  have hRep : (Ty.tree shape).Rep .owned heap store [.i64 0] (Tree.nil hn) :=
    ⟨0, rfl, rfl, List.Pairwise.nil⟩
  have hAfter : After env slots (fun i => live i || (Expr.treeNil shape hn).uses i) live base
      heap store s (.tree shape) .owned (.nil hn) heap store s [.i64 0] :=
    After.refl hAt hVars (by intro i hi; simp [hi]) hRep rfl
      (fun _ _ _ _ _ _ _ _ hb => nomatch hb)
  have hRun := hNext heap store s [.i64 0] hAfter
    (fun hs => ⟨(hAl hs).live_mono (by intro i hi; simp [hi]), fun r hr => nomatch hr⟩)
    (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote, wpX_constI64_cons] using hRun

theorem specX_bytesEmpty {Γ : List Ty} :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.bytesEmpty (S := S) (Γ := Γ)) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  have hRep : Ty.bytes.Rep .owned heap store [.i64 0, .i64 0] LeanExe.Bytes.empty :=
    ⟨0, 0, rfl, Bytes.Rep.empty heap store⟩
  have hAfter : After env slots (fun i => live i || Expr.bytesEmpty.uses i) live base
      heap store s .bytes .owned LeanExe.Bytes.empty heap store s [.i64 0, .i64 0] :=
    After.refl hAt hVars (by intro i hi; simp [hi]) hRep rfl
      (fun _ _ _ _ _ _ _ _ hb => nomatch hb)
  have hRun := hNext heap store s [.i64 0, .i64 0] hAfter
    (fun hs => ⟨(hAl hs).live_mono (by intro i hi; simp [hi]), Ty.AlignedVal.bytesNull⟩)
    (fun _ => Nat.le_add_right _ _)
  simpa [Expr.code, Expr.denote, wpX_constI64_cons] using hRun

/-- A constant `Bool`. -/
theorem specX_bool {Γ : List Ty} (value : Bool) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.bool (S := S) (Γ := Γ) value) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.usesFast_eq, Expr.denote, wpX_constI64_cons] using
    hNext heap store s [.i64 (boolWord value)] (After.refl hAt hVars (by intro i h; simp [h]) rfl
      (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .bool rfl] at hb; exact nomatch hb)
      (fun hs => ⟨(hAl hs).live_mono (by intro i h; simp [h]), Ty.AlignedVal.scalar rfl⟩)
      (fun _ => Nat.le_add_right _ _)

/-- A float constant, from its bit pattern. -/
theorem specX_float {Γ : List Ty} (bits : UInt64) :
    ∀ env slots paid live,
      CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
        (Expr.float (S := S) (Γ := Γ) bits) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  simpa [Expr.code, Expr.usesFast_eq, Expr.denote, F64Bits.toBits_ofBits] using
    hNext heap store s [.f64 (Float.ofBits bits).toBits] (After.refl hAt hVars
      (by intro i h; simp [h]) rfl (Mode.fresh_scalar rfl _ _) fun _ _ _ _ _ _ _ b hb => by
        rw [Ty.regions_scalar .float rfl] at hb; exact nomatch hb)
      (fun hs => ⟨(hAl hs).live_mono (by intro i h; simp [h]), Ty.AlignedVal.scalar rfl⟩)
      (fun _ => Nat.le_add_right _ _)

/-- A comparison of words. -/
theorem specX_cmp {Γ : List Ty} (op : CmpOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.cmp op left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op <;>
    simp only [CmpOp.instr, wpX_eqI64_cons, wpX_neI64_cons, wpX_ltUI64_cons,
      wpX_leUI64_cons, wpX_extendUI32_cons]
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env = right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env < right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  · by_cases hab : left.denote funs env ≤ right.denote funs env <;>
      simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv

/-- The negation of a `Bool`. -/
theorem specX_not {Γ : List Ty} {e : Expr S Γ .bool}
    (eSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.not e) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
  refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
      hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 hAl1 hTop => ?_
  have hNext1 := fun ws a => hNext heap1 store1 s1 ws a
    (fun hs => ⟨(hAl1 hs).1, Ty.AlignedVal.scalar rfl⟩) fun hf => top_part rfl le_rfl (hTop hf)
  have hR := a1.rep
  simp only [Ty.rep_bool] at hR
  subst hR
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wpX_eqzI64_cons, wpX_extendUI32_cons, boolWord_not]
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  simpa [Expr.denote] using
    hNext1 _ (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)

/-- The conjunction of `Bool`s. -/
theorem specX_and {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.and left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wpX_andI64_cons, boolWord_and]
  simpa [Expr.denote] using hNext2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)

/-- The disjunction of `Bool`s. -/
theorem specX_or {Γ : List Ty} {left right : Expr S Γ .bool}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.or left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  simp only [Ty.rep_bool] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    wpX_orI64_cons, boolWord_or]
  simpa [Expr.denote] using hNext2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)

/-- A tuple of two elements: the code of each, in order. -/
theorem specX_mk {Γ : List Ty} {a b : Elem} {first : Expr S Γ (.elem a)}
    {second : Expr S Γ (.elem b)}
    (firstSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv first env slots paid live)
    (secondSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv second env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.mk first second) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : first.width ≤ max first.width second.width := Nat.le_max_left ..
  have hR : second.width ≤ max first.width second.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec firstSpec secondSpec env slots paid live h base heap store s hh hpv hVars hAt
      hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  have hR1' : ws1 = a.values (first.denote funs env) := hR1
  have hR2' : ws2 = b.values (second.denote funs env) := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2
    (a.values (first.denote funs env) ++ b.values (second.denote funs env))
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simpa [List.reverse_append, List.append_assoc] using hv

/-- An operation on words; division and remainder save their operands to test the divisor. -/
theorem specX_bin {Γ : List Ty} (op : BinOp) {left right : Expr S Γ .word}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.bin op left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have hR : right.width ≤ max op.scratch (max left.width right.width) :=
    (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hS : op.scratch ≤ max op.scratch (max left.width right.width) := Nat.le_max_left ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun s' ws a (hA : strict = true → HoldsA env slots live heap2 store2 s') =>
    hNext heap2 store2 s' ws a (fun hs => ⟨hA hs, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  simp only [Ty.rep_word] at hR1 hR2
  subst hR1 hR2
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  cases op
  case div | rem =>
    have hW2 : base + 2 ≤ h := by
      have := hRoom
      simp only [Expr.width, BinOp.scratch] at this
      omega
    have hp2 : s2.params = s.params := hF.params
    have hh2 : s2.positions = h := hF.positions.trans hh
    simp only [BinOp.code, List.cons_append, List.nil_append]
    refine wpX_localSet_local (by rw [hp2]; omega)
      (Locals.lt_total (show base + 1 < ({ s2 with values := _ } : Locals).positions by
        rw [Locals.positions_values, hh2]; omega)) ?_
    refine wpX_localSet_local (vs := s.values)
      (s := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
        (.i64 (right.denote funs env)))
      (by show s2.params.length ≤ base; rw [hp2]; omega)
      (Locals.lt_total (by simp only [Locals.positions_setLocal, Locals.positions_values]; omega)) ?_
    let s2a := setLocal { s2 with values := .i64 (left.denote funs env) :: s.values } (base + 1)
      (.i64 (right.denote funs env))
    let s2b := setLocal { s2a with values := s.values } base (.i64 (left.denote funs env))
    show wpX strict m _ Q store2 s2b host
    have hLowA : ({ s2 with values := .i64 (left.denote funs env) :: s.values } :
        Locals).params.length ≤ base + 1 := by
      show s2.params.length ≤ base + 1; rw [hp2]; omega
    have hLowB : ({ s2a with values := s.values } : Locals).params.length ≤ base := by
      show s2.params.length ≤ base; rw [hp2]; omega
    have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) := by
      rw [Locals.get_setLocal_ne hLowB (by omega), Locals.get_values]
      exact Locals.get_setLocal_same hLowA
        (Locals.lt_total (by simp only [Locals.positions_values]; omega))
    have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) :=
      Locals.get_setLocal_same hLowB
        (Locals.lt_total (by simp only [s2a, Locals.positions_setLocal, Locals.positions_values]; omega))
    have hF2 : Frame base s2 s2b :=
      (Frame.setValues (s := s2) (vs := .i64 (left.denote funs env) :: s.values)
        (v := .i64 (right.denote funs env)) (by rw [hp2]; omega) (by omega) (by omega)).trans
        (Frame.setValues (s := s2a) (vs := s.values) (v := .i64 (left.denote funs env))
          (by show s2.params.length ≤ base; rw [hp2]; omega) le_rfl
          (by simp only [s2a, Locals.positions_setLocal, Locals.positions_values]; omega))
    have hFrame : Frame base s s2b := hF.trans hF2
    have hHolds : Holds env slots live base heap2 store2 s2b := hH.agree hF2
    have hHoldsA : strict = true → HoldsA env slots live heap2 store2 s2b := fun hs =>
      HoldsA.agree hH (hAl2 hs).1 hF2
    have hs2b : s2b.values = s.values := rfl
    simp only [wpX_localGet_cons, hRightSlot, wpX_eqzI64_cons]
    refine wpX_iff_cons rfl ?_
    by_cases hZero : right.denote funs env = 0
    · simp only [hZero, ite_true, ne_eq]
      simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl) hHoldsA
    · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
      simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
        hNext2 s2b _ (After.ofScalar rfl hStep' rfl hFrame hHolds rfl) hHoldsA
  all_goals
    simpa [BinOp.code, Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
      ← UInt64.shiftRight_eq_shiftRight_mod] using
      hNext2 s2 _ (After.ofScalar rfl hStep' rfl hF hH rfl) fun hs => (hAl2 hs).1

/-- An operation on floats. -/
theorem specX_fbin {Γ : List Ty} (op : FBinOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.fbin op left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 [.f64 ((Expr.fbin op left right).denote funs env).toBits]
    (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simpa [FBinOp.instr, Expr.denote, FBinOp.apply, f64Add, f64Sub, f64Mul, f64Div,
      F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div] using hv

/-- A comparison of floats. -/
theorem specX_fcmp {Γ : List Ty} (op : FCmpOp) {left right : Expr S Γ .float}
    (leftSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv left env slots paid live)
    (rightSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv right env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.fcmp op left right) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  have hWidth := hRoom
  simp only [Expr.width] at hWidth
  have hL : left.width ≤ max left.width right.width := Nat.le_max_left ..
  have hR : right.width ≤ max left.width right.width := Nat.le_max_right ..
  simp only [Expr.placeArgs, Bool.and_eq_true] at hPlace
  simp only [Expr.code, Expr.usesFast_eq, List.append_assoc]
  refine seqX_spec leftSpec rightSpec env slots paid live h base heap store s hh hpv
      hVars hAt hAl hSafe hCap hBase
    (by omega) (by omega) hPlace.1 hPlace.2 _ _
    hTrap (by flag_tac) (by flag_tac) (by flag_tac) (by flag_tac)
    fun heap2 store2 s2 ws1 ws2 hStep hF hH hR1 hR2 _ _ _ hTop hAl2 => ?_
  have hNext2 := fun ws a => hNext heap2 store2 s2 ws a
    (fun hs => ⟨(hAl2 hs).1, Ty.AlignedVal.scalar rfl⟩) (fitsOf hTop)
  have hR1' : ws1 = [.f64 (left.denote funs env).toBits] := hR1
  have hR2' : ws2 = [.f64 (right.denote funs env).toBits] := hR2
  subst hR1' hR2'
  have hStep' := hStep
  rw [fresh_scalar_append rfl rfl] at hStep'
  have hv := hNext2 _ (After.ofScalar rfl hStep' rfl hF hH rfl)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hv ⊢
  cases op <;>
    simp only [FCmpOp.instr, wpX_f64Lt_cons, wpX_f64Le_cons, wpX_f64Eq_cons, wpX_extendUI32_cons]
  · cases hc : IEEE64.lt (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_lt, f64Lt, boolWord] using hv
  · cases hc : IEEE64.le (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.decide_le, f64Le, boolWord] using hv
  · cases hc : IEEE64.eq (left.denote funs env).toBits (right.denote funs env).toBits <;>
      simpa [hc, Expr.denote, FCmpOp.apply, F64Bits.beq_eq, f64Eq, boolWord] using hv

/-- An operation on one float.  The negation subtracts from negative zero, pushed first. -/
theorem specX_funary {Γ : List Ty} (op : FUnOp) {e : Expr S Γ .float}
    (eSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.funary op e) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  simp only [Expr.code]
  cases op with
  | neg =>
    simp only [FUnOp.code, List.cons_append, List.append_assoc, wpX_f64Const_cons]
    refine eSpec env slots paid live h base heap store { s with values := .f64 0x8000000000000000 ::
      s.values } hh hpv (hVars.agree Frame.ofValues) hAt (fun hs => (hAl hs).values _)
      (hSafe.values _) hCap hBase hRoom hPlace _ _
      (by rw [dyingPot_values]; exact hTrap)
      fun heap1 store1 s1 ws a1 hAl1 hTop => ?_
    have hNext1 := fun ws a => hNext heap1 store1 s1 ws a
      (fun hs => ⟨(hAl1 hs).1, Ty.AlignedVal.scalar rfl⟩)
      fun hf => top_part rfl (dyingPot_values _ _ _).le (hTop hf)
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 [.f64 (-(e.denote funs env)).toBits]
      (After.ofValues (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl))
    simpa [Expr.denote, FUnOp.apply, f64Sub, F64Bits.toBits_neg] using hv
  | sqrt | abs =>
    simp only [FUnOp.code, List.append_assoc, List.cons_append, List.nil_append]
    refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
        hRoom hPlace _ _ hTrap
      fun heap1 store1 s1 ws a1 hAl1 hTop => ?_
    have hNext1 := fun ws a => hNext heap1 store1 s1 ws a
      (fun hs => ⟨(hAl1 hs).1, Ty.AlignedVal.scalar rfl⟩) fun hf => top_part rfl le_rfl (hTop hf)
    have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
    subst hR
    have hStep := a1.step
    rw [Mode.fresh_scalar rfl] at hStep
    have hv := hNext1 [.f64 ((Expr.funary _ e).denote funs env).toBits]
      (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
    simpa [Expr.denote, FUnOp.apply, f64Sqrt, f64Abs, F64Bits.toBits_sqrt, F64Bits.toBits_abs]
      using hv

/-- A conversion of a word to a float. -/
theorem specX_toFloat {Γ : List Ty} (op : ToFloat) {e : Expr S Γ .word}
    (eSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.toFloat op e) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
      hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 hAl1 hTop => ?_
  have hNext1 := fun ws a => hNext heap1 store1 s1 ws a
    (fun hs => ⟨(hAl1 hs).1, Ty.AlignedVal.scalar rfl⟩) fun hf => top_part rfl le_rfl (hTop hf)
  have hR : ws = [.i64 (e.denote funs env)] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 [.f64 ((Expr.toFloat op e).denote funs env).toBits]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToFloat.code, Expr.denote, ToFloat.apply, f64ConvertI64U, f64Add,
      F64Convert.toBits_toFloat, F64Bits.toBits_ofBits, add_negZero] using hv

/-- A conversion of a float to a word. -/
theorem specX_toWord {Γ : List Ty} (op : ToWord) {e : Expr S Γ .float}
    (eSpec : ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits
      host pv e env slots paid live) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.toWord op e) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase hRoom
      hPlace rest Q hTrap hNext
  simp only [Expr.code, List.append_assoc]
  refine eSpec env slots paid live h base heap store s hh hpv hVars hAt hAl hSafe hCap hBase
      hRoom hPlace _ _ hTrap
    fun heap1 store1 s1 ws a1 hAl1 hTop => ?_
  have hNext1 := fun ws a => hNext heap1 store1 s1 ws a
    (fun hs => ⟨(hAl1 hs).1, Ty.AlignedVal.scalar rfl⟩) fun hf => top_part rfl le_rfl (hTop hf)
  have hR : ws = [.f64 (e.denote funs env).toBits] := a1.rep
  subst hR
  have hStep := a1.step
  rw [Mode.fresh_scalar rfl] at hStep
  have hv := hNext1 [.i64 ((Expr.toWord op e).denote funs env)]
    (After.ofScalar rfl hStep rfl a1.frame a1.holds rfl)
  cases op <;>
    simpa [ToWord.instr, Expr.denote, ToWord.apply, i64TruncSatF64U, F64Convert.toUInt64_eq]
      using hv

end Cases

end Verified
