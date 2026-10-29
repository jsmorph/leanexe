import Verified.AlignedArrayCopy
import Verified.ExprCorrect

/-!
The flag at the level of expressions.  `HoldsA` is the alignment invariant: the heap is aligned,
and every region of a live variable starts at a multiple of 8, the regions of an owned value
being its blocks, whose lengths are then multiples of 8 too.  A region of a borrowed array or
record starts at its pointer, and a block at its pointer minus 48, so the invariant covers every
pointer and the capacity of every owned block.  Stating it on regions makes it persist across a
step by the equality of regions that `Ty.Rep.step` already proves (`Ty.AlignedVal.step`).
`CodeSpecX strict` is `CodeSpec` with `wpX strict` for `wp`, `HoldsA` as a
premise under `strict = true`, and, for the continuation, `HoldsA` of the variables live after
the code and the alignment of the value it pushes.  `CodeSpecX.false_iff` states that at
`strict = false` it is `CodeSpec`.

`specX_size` ports `spec_size`, the length of an array, whose code loads the length word at the
array's address and then releases the array when it is owned and dies there.  The release is the
boundary of this port: `ReadReleaseX` is the flagged statement of `read_release`, which
`readReleaseX_false` proves at `strict = false` from `read_release`, and whose proof at
`strict = true` would port the release of every type.
-/

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-- Every region of a value starts at a multiple of 8, and when the value is owned, its regions,
which are its blocks, have lengths that are multiples of 8. -/
def Ty.AlignedVal (mode : Mode) (store : Store Unit) (t : Ty) (ws : List Value)
    (v : t.denote) : Prop :=
  ∀ r ∈ t.regions mode store ws v, r.1 % 8 = 0 ∧ (mode = .owned → r.2 % 8 = 0)

/-- The invariant persists across a step that keeps the value's regions. -/
theorem Ty.AlignedVal.step {mode : Mode} {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh) {t : Ty} {ws : List Value} {v : t.denote}
    (hRep : t.Rep mode heap store ws v) (hKeep : ∀ r ∈ t.regions mode store ws v, keep r)
    (h : Ty.AlignedVal mode store t ws v) : Ty.AlignedVal mode store' t ws v := by
  obtain ⟨-, hSame, -⟩ := hRep.step hStep hKeep
  intro r hr
  rw [hSame] at hr
  exact h r hr

/-- The address of an array, from the invariant, in either mode. -/
theorem Ty.AlignedVal.array {mode : Mode} {heap : Heap} {store : Store Unit} {e : Elem}
    {ptr : UInt64} {xs : Array e.denote} (hRep : mode.array heap store ptr (e.words xs))
    (h : Ty.AlignedVal mode store (.array e) [.i64 ptr] xs) : ptr.toNat % 8 = 0 := by
  cases mode
  · exact (h (ptr.toNat, 8 * ((e.words xs).size + 1)) (by simp [Ty.regions, Ty.reads])).1
  · have hBase := (show heap.Owned store ptr (e.words xs) from hRep).base
    have := (h (block store ptr) (by simp [Ty.regions, Ty.blocks])).1
    simp only [block] at this
    omega

/-- The alignment invariant: the heap is aligned, and so is every variable live in `live`. -/
def HoldsA {Γ : List Ty} (env : Env Γ) (slots : List Slot) (live : Nat → Bool) (heap : Heap)
    (store : Store Unit) (s : Locals) : Prop :=
  heap.Aligned ∧ ∀ (t : Ty) (x : Var Γ t), live x.index = true →
    ∀ ws, LocalsHold s (slots.getD x.index default).loc t.types ws → ws.length = t.width →
      Ty.AlignedVal (slots.getD x.index default).mode store t ws (env.get x)

/-- `CodeSpec` under the flag. -/
def CodeSpecX (strict : Bool) {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module)
    (funs : Funs S) (flags : Flags S) (bounds : Bounds S) (fits : Fits S) (host : HostEnv Unit)
    (pv : List Value) (e : Expr S Γ t) (env : Env Γ) (slots : List Slot) (paid : List Bool)
    (live : Nat → Bool) (pool : Bytes.LiteralPool) : Prop :=
  ∀ (h base : Nat) (heap : Heap) (store : Store Unit) (s : Locals), s.positions = h → s.params = pv →
    Holds env slots (fun i => live i || e.uses i) base heap store s → heap.At store →
    (strict = true → HoldsA env slots (fun i => live i || e.uses i) heap store s) →
    pool.Safe env slots (fun i => live i || e.uses i) heap store s →
    store.memoryCap m 0 ≤ 65535 → s.params.length ≤ base → base + e.width ≤ h →
    e.placeArgs = true →
    ∀ (rest : Program) (Q : Assertion Unit),
    TrapOK (trapFlag m e slots heap store
      (dyingPot store s env slots paid (fun i => live i || e.uses i) live +
        e.allocs funs flags bounds (slots.map Slot.mode) paid live env) (e.fits funs fits env)) Q →
    (∀ heap' store' s' ws,
      After env slots (fun i => live i || e.uses i) live base heap store s t
        (e.mode (slots.map Slot.mode)) (e.denote funs env) heap' store' s' ws →
      (strict = true → HoldsA env slots live heap' store' s' ∧
        Ty.AlignedVal (e.mode (slots.map Slot.mode)) store' t ws (e.denote funs env)) →
      (e.fits funs fits env = true →
        heap'.top.toNat +
            (if e.paid flags (slots.map Slot.mode) paid live then t.pot store' ws (e.denote funs env)
              else 0) ≤
          heap.top.toNat + dyingPot store s env slots paid (fun i => live i || e.uses i) live +
            e.allocs funs flags bounds (slots.map Slot.mode) paid live env) →
      wpX strict m rest Q store' { s' with values := ws.reverse ++ s.values } host) →
    wpX strict m (e.code (pool := pool) h slots base live ++ rest) Q store s host

/-- At `strict = false`, `CodeSpecX` is `CodeSpec`. -/
theorem CodeSpecX.false_iff {S : List Sig} {Γ : List Ty} {t : Ty} {m : Module} {funs : Funs S}
    {flags : Flags S} {bounds : Bounds S} {fits : Fits S} {host : HostEnv Unit} {pv : List Value}
    {e : Expr S Γ t} {env : Env Γ} {slots : List Slot} {paid : List Bool} {live : Nat → Bool} :
    CodeSpecX false m funs flags bounds fits host pv e env slots paid live pool ↔
      CodeSpec m funs flags bounds fits host pv e env slots paid live pool := by
  constructor
  · intro hX h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hX h base heap store s hh hpv hVars hAt nofun hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA _ hb => hNext heap' store' s' ws hA hb
  · intro hC h base heap store s hh hpv hVars hAt _ hSafe hCap hBase hRoom hPlace rest Q hTrap hNext
    exact hC h base heap store s hh hpv hVars hAt hSafe hCap hBase hRoom hPlace rest Q hTrap
      fun heap' store' s' ws hA hb => hNext heap' store' s' ws hA nofun hb

theorem wpX_divCode {strict : Bool} {m : Module} {st : Store Unit} {env' : HostEnv Unit}
    {s : Locals} {vs : List Value} {rest : Program} {Q : Assertion Unit} {k : Nat} (hk : 0 < k)
    (x : UInt64) :
    wpX strict m (divCode k ++ rest) Q st { s with values := .i64 x :: vs } env' ↔
      wpX strict m rest Q st { s with values := .i64 (x / wordCount k) :: vs } env' := by
  cases strict
  · exact wp_divCode hk x
  · unfold divCode
    split
    · next hk1 => subst hk1; simp [wordCount]
    · simp [wpA_cons_wp, AlignedOne, wordCount_ne_zero hk]

section

variable {m : Module} {host : HostEnv Unit}

/-- `read_release` under the flag: the release of a variable that dies at a read keeps the
invariant of the variables that stay live. -/
def ReadReleaseX (strict : Bool) (m : Module) (host : HostEnv Unit) : Prop :=
  ∀ {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {vals : List Value} {rest : Program}
    {Q : Assertion Unit} {t : Ty} (x : Var Γ t),
    Holds env slots (fun k => live k || k == x.index) base heap store s → heap.At store →
    (strict = true → HoldsA env slots (fun k => live k || k == x.index) heap store s) →
    (∀ heap' store', Evolves env slots (fun k => live k || k == x.index) live base heap
      store s heap' store' s → heap'.top = heap.top →
      (strict = true → HoldsA env slots live heap' store' s) →
      wpX strict m rest Q store' { s with values := vals } host) →
    wpX strict m ((if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
        releaseCode t (slots.getD x.index default).loc else []) ++ rest) Q store
      { s with values := vals } host

theorem readReleaseX_false (hm : Runtime m) : ReadReleaseX false m host :=
  fun x hVars hAt _ hNext => read_release hm x hVars hAt fun heap' store' ev hTop =>
    hNext heap' store' ev hTop nofun

end

section Cases

variable {S : List Sig} {m : Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
  {fits : Fits S} {host : HostEnv Unit} {pv : List Value}

/-- `spec_size` under the flag: the length word is loaded at the array's address, which `HoldsA`
makes a multiple of 8, and the value pushed is a word, which holds no pointer. -/
theorem specX_size {strict : Bool} (_hm : Runtime m) (hRel : ReadReleaseX strict m host)
    {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots paid live, CodeSpecX strict (pool := pool) m funs flags bounds fits host pv
      (Expr.size (S := S) x) env slots paid live := by
  intro env slots paid live h base heap store s hh hpv hVars hAt hAl _ _ _ _ _ rest Q _ hNext
  obtain ⟨-, ws, hold, hRep⟩ := hVars.1 _ x (by simp [Expr.uses])
  obtain ⟨ptr, rfl, hB⟩ := hRep
  have hPtrAl : strict = true → ptr.toNat % 8 = 0 := fun hs =>
    Ty.AlignedVal.array hB ((hAl hs).2 _ x (by simp [Expr.uses]) [.i64 ptr] hold rfl)
  have hA := hB.borrow.values
  have hLength := hA.lengthBound
  have hPtr : s.get (slots.getD x.index default).loc = some (.i64 ptr) := by
    exact LocalsHold.word hold
  have hnk : (env.get x).size * e.width < 536870912 := by
    have := hA.1; rw [Elem.words_size] at this; omega
  simp only [Expr.code, Var.sizeCode, List.append_assoc, List.cons_append,
    List.nil_append]
  simp only [wpX_localGet_cons, hPtr, wpX_wrapI64_cons, wpX_load64_cons, wrap_toUInt32,
    UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by omega), hA.lengthRead, Elem.words_size, wpX_divCode e.width_pos,
    words_div e.width_pos hnk]
  refine ⟨fun hs => UInt64.toUInt32_mod8 (hPtrAl hs), ?_⟩
  refine hRel x hVars hAt hAl fun heap' store' ev hTop hAl' => ?_
  exact hNext heap' store' s [.i64 (env.get x).size.toUInt64]
    (After.ofScalar rfl ev.step rfl ev.frame ev.holds rfl)
    (fun hs => ⟨hAl' hs, fun r hr => by rw [Ty.regions_scalar _ rfl] at hr; exact nomatch hr⟩)
    fun _ => top_unpaid_le rfl (by rw [hTop]; omega)

/-- At `strict = false` the port gives `spec_size`'s statement. -/
theorem spec_size_of_flag (hm : Runtime m) {Γ' : List Ty} {e : Elem} (x : Var Γ' (.array e)) :
    ∀ env slots paid live, CodeSpec (pool := pool) m funs flags bounds fits host pv
      (Expr.size (S := S) x) env slots paid live :=
  fun env slots paid live => CodeSpecX.false_iff.mp
    (specX_size (strict := false) hm (readReleaseX_false hm) x env slots paid live)

end Cases

end Verified
