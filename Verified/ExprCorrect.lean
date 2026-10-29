import Verified.ExprSpec
import Verified.ArgsCorrect
import Verified.Bytes.Get
import Verified.LiteralCoverage
import Verified.LiteralCoverageFacts
import Verified.TreeNodeCode
import Verified.TreeMatchBody
import Verified.ListFoldCode
import Verified.Float32Facts
import LeanExe.ProofKit.F32Nearest
import Verified.TreeNodeBound
import Verified.FieldsAdvance
import Verified.TreeAssembleTyped
import Verified.OwnedExpr
import Verified.Bytes.StaticPrefix
import Verified.TreeDispatch
import Verified.ListFoldSource
import Verified.TailCorrect
import Verified.TreeMatchFacts
import Verified.TailBindPrefix
import Verified.TailAllocExpand
import Verified.TreeMatchPotential
import Verified.TailBind
import Verified.TailArgs
import Verified.ListFoldResource
import Verified.ListFoldBorrowed
import Verified.TailHeap
import Verified.Bytes.AfterWrite
import Verified.Bytes.BuildCode
import Verified.LocalFrame
import LeanExe.TalosCompat
import LeanExe.Pipeline.Aborts
import Verified.Bytes.StoreWord
import Verified.Bytes.Overlay
import Verified.Bytes.LiteralCode
import Verified.Bytes.LiteralFrame
import Verified.Bytes.Copy

/-! Correctness of expression code and ordinary function templates. -/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit}
  {pv : List Value}

/-- The regions of the first of two values in a row, which the second's code keeps. -/
theorem After.seq_regions {Γ : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {t u : Ty} {m1 m2 : Mode}
    {v1 : t.denote} {v2 : u.denote} {ws1 ws2 vs : List Value}
    (a1 : After env slots L0 L1 base heap store s t m1 v1 heap1 store1 s1 ws1)
    (a2 : After env slots L1 live base heap1 store1 { s1 with values := vs } u m2 v2 heap2
      store2 s2 ws2) :
    t.regions m1 store2 ws1 v1 = t.regions m1 store1 ws1 v1 := by
  have hKeep1 : ∀ c ∈ t.regions m1 store1 ws1 v1,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc w x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ w.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart w x hx (Or.inr hm) wx hwx hlx c hc b hb'
  exact (a1.rep.step a2.step hKeep1).2.1

/-- The bound of a pair from those of its components and their coercions: a paid pair's
potential is the sum of its components', each paid or 0. -/
theorem pair_top {T0 T1' T1 T2' T2 D1 D2 A1 C1 A2 C2 P1 P2 P1' P2' : Nat} {p1 p2 pp : Bool}
    (hF : T1' + (if p1 = true then P1' else 0) ≤ T0 + D1 + A1) (hC1 : T1 ≤ T1' + C1)
    (hS : T2' + (if p2 = true then P2' else 0) ≤ T1 + D2 + A2) (hC2 : T2 ≤ T2' + C2)
    (h1 : pp = true → (p1 = true ∧ P1 = P1') ∨ P1 = 0)
    (h2 : pp = true → (p2 = true ∧ P2 = P2') ∨ P2 = 0) :
    T2 + (if pp = true then P1 + P2 else 0) ≤ T0 + (D1 + D2) + (A1 + C1 + A2 + C2) := by
  cases pp with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega
  | true =>
    simp only [↓reduceIte]
    have e1 : P1 ≤ (if p1 = true then P1' else 0) := by
      rcases h1 rfl with ⟨hp1, rfl⟩ | h1
      · simp [hp1]
      · omega
    have e2 : P2 ≤ (if p2 = true then P2' else 0) := by
      rcases h2 rfl with ⟨hp2, rfl⟩ | h2
      · simp [hp2]
      · omega
    omega

/-- A paid loop state is held in owned mode. -/
theorem Expr.statePaid_mode {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} (h : Expr.statePaid flags modes paid live init cond body = true) :
    (init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes)) = .owned := by
  simp only [Expr.statePaid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- The body of a loop whose state is paid gives a value paid as `Expr.bodyPaid` states. -/
theorem Expr.statePaid_body {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} (h : Expr.statePaid flags modes paid live init cond body = true) :
    body.paidIn (Expr.statePaid flags modes paid live init cond body) flags
      (((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))) ::
        .borrowed :: modes) (Expr.statePaid flags modes paid live init cond body :: false :: paid)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) = true := by
  rw [h]
  simp only [Expr.statePaid, Bool.and_eq_true] at h
  simpa only [Expr.paidIn, ↓reduceIte] using h.2

/-- In a loop's body, no paid variable dies other than the state: the index is unpaid, and the outer
variables that the body uses stay live. -/
theorem loop_body_dies {live c b : Nat → Bool} {paid : List Bool} :
    ∀ i, (fun j => shift 2 (fun i => live i || c (i + 1) || b (i + 2)) j || b j) (i + 1) = true →
      (shift 2 fun i => live i || c (i + 1) || b (i + 2)) (i + 1) = false →
      paidAt (false :: paid) i = false
  | 0, _, _ => rfl
  | k + 1, h0, h1 => by
    have hk : ¬ k + 1 + 1 < 2 := by omega
    have hs : k + 1 + 1 - 2 = k := by omega
    have hb : b (k + 1 + 1) = b (k + 2) := rfl
    simp only [shift, hk, hs, ↓reduceIte, hb] at h0 h1
    revert h0 h1
    cases live k <;> cases c (k + 1) <;> cases b (k + 2) <;> simp

/-- The potential of a loop's first state: that of a paid initial value, which the coercion keeps,
or the credit. -/
theorem loop_entry_pot {ps ip : Bool} {P0 P1 C : Nat} (h1 : ps = true → ip = true → P1 = P0)
    (h2 : ps = true → ip = false → P1 ≤ C) :
    (if ps = true then P1 else 0) ≤
      (if ip = true then P0 else 0) + (if (ps && !ip) = true then C else 0) := by
  cases ps <;> cases ip <;> simp_all

/-- A pass of a loop: the body's bound with the state's potential among its dying variables, and
the coercion of its value, which keeps a paid value's potential. -/
theorem loop_body_pot {ps bp : Bool} {top6 top6' top2 D B Y K P6 P6' Pi : Nat}
    (hbp : ps = true → bp = true) (hsame : ps = true → P6' = P6)
    (hB : top6 + (if bp = true then P6 else 0) ≤ top2 + D + B + Y)
    (hD : D ≤ (if ps = true then Pi else 0)) (hK : top6' ≤ top6 + K) :
    top6' + (if ps = true then P6' else 0) ≤ top2 + (if ps = true then Pi else 0) + B + K + Y := by
  cases ps
  · simp only [Bool.false_eq_true, ↓reduceIte] at hD ⊢
    split at hB <;> omega
  · obtain rfl := hbp rfl
    rw [hsame rfl]
    simp only [↓reduceIte] at hB hD ⊢
    omega

/-- The body of a loop at the state's flag `ps`, which holds only when the state is paid, gives a
value paid as `Expr.bodyPaid` states. -/
theorem Expr.statePaid_body_of {Γ : List Ty} {t : Ty} {modes : List Mode} {paid : List Bool}
    {live : Nat → Bool} {init : Expr S Γ t} {cond : Expr S (t :: Γ) .bool}
    {body : Expr S (t :: .word :: Γ) t} {ps : Bool}
    (hpsS : ps = true → Expr.statePaid flags modes paid live init cond body = true)
    (h : ps = true) :
    body.paidIn ps flags (((init.mode modes).join (body.mode (.borrowed :: .borrowed :: modes))) ::
        .borrowed :: modes) (ps :: false :: paid)
      (shift 2 fun i => live i || cond.uses (i + 1) || body.uses (i + 2)) = true := by
  subst h
  have h2 := Expr.statePaid_body (hpsS rfl)
  rwa [hpsS rfl] at h2

/-- A request of at least 8 and at most `8 * k` bytes, within `2 ^ 32`, takes at most `8 * k`
bytes. -/
theorem allocSize_le_mul {bytes : UInt64} {k : Nat} (h8 : 8 ≤ bytes.toNat)
    (hb : bytes.toNat ≤ 4294967296) (h : bytes.toNat ≤ 8 * k) :
    (allocSize bytes).toNat ≤ 8 * k := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]; omega
  · rw [hRound]; omega

/-- `Var.roomCost` of an array that is copied: a copy at the new length. -/
theorem Var.roomCost_copy {Γ : List Ty} {e : Elem} (x : Var Γ (.array e)) {modes : List Mode}
    (paid : List Bool) {live : Nat → Bool} (xs : Array e.denote) (ext : Nat)
    (h : ¬(modeAt modes x.index = .owned ∧ live x.index = false)) :
    x.roomCost modes paid live xs ext = allocCost ((xs.size * e.width + ext + 1) * 8) := by
  simp only [Var.roomCost, ite_eq_right h]

/-- `Var.roomCost` of an owned array that dies: for a paid one, a header and four times the added
bytes, and for an unpaid one, a block of twice the new length's bytes and twice the added bytes. -/
theorem Var.roomCost_move {Γ : List Ty} {e : Elem} (x : Var Γ (.array e)) {modes : List Mode}
    (paid : List Bool) {live : Nat → Bool} (xs : Array e.denote) (ext : Nat)
    (h : modeAt modes x.index = .owned ∧ live x.index = false) :
    x.roomCost modes paid live xs ext =
      if paidAt paid x.index then allocCost (32 * ext)
      else allocCost (16 * (xs.size * e.width + ext + 1)) + 16 * ext := by
  simp only [Var.roomCost, ite_eq_left h]

/-! The arithmetic of a growth with the potential `4u ∸ 2c`, for an array of `n` words in a block
of capacity `c` that grows to `t` words.  A move requests `r`, twice the capacity or the new
length's bytes, which the allocator rounds to `A`, a multiple of 8. -/

theorem room_inplace_paid {n t c : Nat} (hnt : n ≤ t) :
    4 * (8 * (t + 1)) - 2 * c ≤ (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by omega

theorem room_inplace_unpaid {n t c : Nat} (hc : 8 * (n + 1) ≤ c) (hnt : n ≤ t) :
    4 * (8 * (t + 1)) - 2 * c ≤ 48 + 16 * (t + 1) + 16 * (t - n) := by omega

theorem room_alloc_paid {n t c r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A) (hAr7 : A ≤ r + 7)
    (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1))) :
    48 + A ≤ (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem room_alloc_unpaid {n t c r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A) (hAr7 : A ≤ r + 7)
    (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1))) :
    48 + A ≤ 48 + 16 * (t + 1) + 16 * (t - n) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

theorem room_move_paid {top top' n t c c' r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A)
    (hAr7 : A ≤ r + 7) (hc : 8 * (n + 1) ≤ c) (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1)))
    (hshape : (top' = top ∧ r ≤ c') ∨ (top' = top + 48 + A ∧ c' = A)) :
    top' + (4 * (8 * (t + 1)) - 2 * c') ≤
      top + (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases hshape with ⟨rfl, h'⟩ | ⟨rfl, rfl⟩ <;> omega

theorem room_move_unpaid {top top' n t c c' r A : Nat} (hA : A % 8 = 0) (hAr : r ≤ A)
    (hAr7 : A ≤ r + 7) (hc : 8 * (n + 1) ≤ c) (hroom : c < 8 * (t + 1))
    (hr : (r = 2 * c ∧ 8 * (t + 1) ≤ 2 * c) ∨ (r = 8 * (t + 1) ∧ 2 * c < 8 * (t + 1)))
    (hshape : (top' = top ∧ r ≤ c') ∨ (top' = top + 48 + A ∧ c' = A)) :
    top' + (4 * (8 * (t + 1)) - 2 * c') ≤ top + (48 + 16 * (t + 1) + 16 * (t - n)) := by
  rcases hr with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases hshape with ⟨rfl, h'⟩ | ⟨rfl, rfl⟩ <;> omega

/-- A block of more than `2 ^ 31` bytes below `top` leaves no room for either charge. -/
theorem room_huge {top n t c : Nat} (hroom : c < 8 * (t + 1)) (hnt : 8 * (n + 1) ≤ c)
    (hc : 4294967296 < 2 * c) (htop : c ≤ top) :
    4294901760 < top + (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) ∧
      4294901760 < top + (48 + 16 * (t + 1) + 16 * (t - n)) := by
  omega

/-- A new length of `2 ^ 29` words or more leaves no room for any charge. -/
theorem room_long {n t c : Nat} (ht : 536870912 ≤ t) (hnt : n ≤ t) (hc : c < 4294967296) :
    4294901760 < (4 * (8 * (n + 1)) - 2 * c) + (48 + 32 * (t - n)) ∧
      4294901760 < 48 + 16 * (t + 1) + 16 * (t - n) ∧ 4294901760 < 48 + (t + 1) * 8 := by
  omega

/-- The rounded byte count of an allocation is a multiple of 8 within 7 of the request. -/
theorem allocSize_round {bytes : UInt64} (h : bytes.toNat ≤ 4294967296) (h8 : 8 ≤ bytes.toNat) :
    (allocSize bytes).toNat % 8 = 0 ∧ bytes.toNat ≤ (allocSize bytes).toNat ∧
      (allocSize bytes).toNat ≤ bytes.toNat + 7 := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · rename_i hs
    rw [UInt64.lt_iff_toNat_lt, hRound] at hs
    simp only [UInt64.reduceToNat] at hs
    omega
  · rw [hRound]; omega

end Cases

/-- A run that may trap as `a` allows may trap as any `a'` that `a` implies. -/
theorem _root_.Wasm.Runs.of_imp {α : Type} {env : HostEnv α} {m : Module} {id : Nat}
    {initial : Store α} {args : List Value} {P : Store α → List Value → Prop} {a a' : Bool}
    (h : Runs a env m id initial args P) (himp : a = true → a' = true) :
    Runs a' env m id initial args P := by
  cases a
  · exact h.weaken
  · rw [himp rfl]; exact h

/-- The frames at the next depth: one fewer, below the limit. -/
theorem framesAt_succ {d : UInt64} (h : d < depthLimit) : framesAt d = framesAt (d + 1) + 1 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  simp only [depthLimit, UInt64.reduceToNat] at this
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  simp only [framesAt, depthLimit, UInt64.reduceToNat, hd1]; omega

theorem framesAt_eq_zero {d : UInt64} (h : ¬d < depthLimit) : framesAt d = 0 := by
  have := UInt64.not_lt.mp h
  have := UInt64.le_iff_toNat_le.mp this
  simp only [depthLimit, UInt64.reduceToNat] at this
  simp only [framesAt, depthLimit, UInt64.reduceToNat]; omega

end Verified
