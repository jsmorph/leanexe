import LeanExe.A64.Proof.ImageLayout
import LeanExe.A64.Proof.Program

/-!
The bytes of an image that `genImage` writes are the same at two addresses of the RAM GiB that
differ by a multiple of 4096.  The generator encodes a branch by the difference between its target
and its own address, `ADRP` by the difference between their pages, and `ADD` by the target's
offset in its page.  A shift by `d` under which every address that the generator forms moves by
the same number `δ`, as `Moves d δ` states, keeps those differences, and a `δ` that is a multiple
of 4096 keeps the page differences and the offsets in a page, so the generator emits the same
instructions.  Two images in the RAM GiB give such a `δ`, the difference of their addresses, also
when `image + d` lies below `image` because the sum wraps around 2^64.  The generator's error
messages name addresses, so the theorems carry a successful result from one address to the other.
-/

namespace LeanExe.A64

open Wasm

/-! ## Moved addresses -/

/-- The shift by `d` moves `x` by `δ`: the number of `x + d` is that of `x` plus `δ`. -/
def Moves (d : UInt64) (δ : Int) (x : UInt64) : Prop := ((x + d).toNat : Int) = x.toNat + δ

/-- The shift by `d` moves by `δ` the addresses `after a j` for `j` up to `n`. -/
def MovesFrom (d : UInt64) (δ : Int) (a : UInt64) (n : Nat) : Prop :=
  ∀ j ≤ n, Moves d δ (after a j)

theorem after_shift (a d : UInt64) (n : Nat) : after (a + d) n = after a n + d := by
  simp only [after]
  ac_rfl

theorem MovesFrom.base {d : UInt64} {δ : Int} {a : UInt64} {n : Nat} (h : MovesFrom d δ a n) :
    Moves d δ a := by
  have := h 0 (Nat.zero_le n)
  rwa [after_zero] at this

theorem MovesFrom.le {d : UInt64} {δ : Int} {a : UInt64} {n k : Nat} (h : MovesFrom d δ a n)
    (hk : k ≤ n) : MovesFrom d δ a k := fun j hj => h j (by omega)

theorem MovesFrom.drop {d : UInt64} {δ : Int} {a : UInt64} {n m : Nat} (h : MovesFrom d δ a n)
    (hm : m ≤ n) : MovesFrom d δ (after a m) (n - m) := fun j hj => by
  rw [after_after]
  exact h _ (by omega)

/-- When `x + n` and `x + d + n`, as numbers, lie below 2^64, the shift by `d` moves every address
from `x` to `x + n` by the same number. -/
theorem moves_of_range {x d y : UInt64} {n : Nat} (h1 : x.toNat + n < 2 ^ 64)
    (h2 : (x + d).toNat + n < 2 ^ 64) (hy1 : x.toNat ≤ y.toNat) (hy2 : y.toNat ≤ x.toNat + n) :
    Moves d ((x + d).toNat - x.toNat) y := by
  unfold Moves
  have e1 := UInt64.toNat_add y d
  have e2 := UInt64.toNat_add x d
  have hd := d.toNat_lt
  simp only [Nat.reducePow] at e1 e2 hd h1 h2 ⊢
  omega

theorem toNat_after {a : UInt64} {n : Nat} (h : a.toNat + 4 * n < 2 ^ 64) :
    (after a n).toNat = a.toNat + 4 * n := by
  have h4 : (4 : UInt64).toNat = 4 := rfl
  rw [after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', h4]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- When `a + 4 * n` and `a + d + 4 * n`, as numbers, lie below 2^64, the shift by `d` moves the
addresses of the words from `a` by the same number. -/
theorem movesFrom_of {a d : UInt64} {n : Nat} (h1 : a.toNat + 4 * n < 2 ^ 64)
    (h2 : (a + d).toNat + 4 * n < 2 ^ 64) : MovesFrom d ((a + d).toNat - a.toNat) a n :=
  fun j hj => moves_of_range h1 h2 (by rw [toNat_after (by omega)]; omega)
    (by rw [toNat_after (by omega)]; omega)

/-! ## Branch fields and addresses -/

/-- A branch field depends on its address and its target through their difference alone, so a
shift that moves both by the same number keeps it. -/
theorem branchField_shift {bits : Nat} {d : UInt64} {δ : Int} {here target : UInt64} {f : Nat}
    (hh : Moves d δ here) (ht : Moves d δ target) (h : branchField bits here target = .ok f) :
    branchField bits (here + d) (target + d) = .ok f := by
  have e : Int.ofNat (target + d).toNat - Int.ofNat (here + d).toNat =
      Int.ofNat target.toNat - Int.ofNat here.toNat := by
    unfold Moves at hh ht
    simp only [Int.ofNat_eq_natCast]
    omega
  unfold branchField at h ⊢
  dsimp only at h ⊢
  rw [e]
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hc
    rw [ite_eq_right hc]
    exact h

theorem bField_shift {d : UInt64} {δ : Int} {here target : UInt64} {f : Fin 67108864}
    (hh : Moves d δ here) (ht : Moves d δ target) (h : bField here target = .ok f) :
    bField (here + d) (target + d) = .ok f := by
  unfold bField at h ⊢
  cases hb : branchField 26 here target with
  | error e => simp [hb, bind, Except.bind] at h
  | ok n => rw [branchField_shift hh ht hb, ← hb]; exact h

theorem cbField_shift {d : UInt64} {δ : Int} {here target : UInt64} {f : Fin 524288}
    (hh : Moves d δ here) (ht : Moves d δ target) (h : cbField here target = .ok f) :
    cbField (here + d) (target + d) = .ok f := by
  unfold cbField at h ⊢
  cases hb : branchField 19 here target with
  | error e => simp [hb, bind, Except.bind] at h
  | ok n => rw [branchField_shift hh ht hb, ← hb]; exact h

/-- `ADRP` and `ADD` depend on the difference between the page of their address and that of the
target and on the target's offset in its page, and a shift that moves both addresses by a multiple
of 4096 keeps both. -/
theorem addrOf_shift {r : Fin 32} {d : UInt64} {δ : Int} {here target : UInt64}
    {is : List Instr} (hδ : δ % 4096 = 0) (hh : Moves d δ here) (ht : Moves d δ target)
    (h : addrOf r here target = .ok is) : addrOf r (here + d) (target + d) = .ok is := by
  have e : Int.ofNat ((target + d).toNat / 4096) - Int.ofNat ((here + d).toNat / 4096) =
      Int.ofNat (target.toNat / 4096) - Int.ofNat (here.toNat / 4096) := by
    unfold Moves at hh ht
    simp only [Int.ofNat_eq_natCast]
    omega
  have o : (target + d).toNat % 4096 = target.toNat % 4096 := by
    unfold Moves at ht
    omega
  unfold addrOf at h ⊢
  dsimp only at h ⊢
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i hc
    split
    · rename_i hc'
      rw [e] at hc'
      exact absurd hc' hc
    · simp only [e, o]
      exact h

/-! ## Shifted environments -/

/-- The construct `t` with its target shifted by `d`. -/
def Ctl.shift (d : UInt64) (t : Ctl) : Ctl := { t with target := t.target + d }

/-- The table `T` with each entry shifted by `d`. -/
def shiftTable (d : UInt64) (T : Table) : Table := fun j => (T j).map fun c => (c.1 + d, c.2)

/-- The trap stubs of `S` shifted by `d`. -/
def Shared.shift (d : UInt64) (S : Shared) : Shared :=
  { S with
    trapUnreachable := S.trapUnreachable + d, trapBounds := S.trapBounds + d,
    trapDiv := S.trapDiv + d, trapStack := S.trapStack + d }

/-- The trap stubs and the table of the calls of `E` shifted by `d`. -/
def Env.shift (d : UInt64) (E : Env) : Env :=
  { E with toShared := E.toShared.shift d, callee := shiftTable d E.callee }

/-- The shift by `d` moves by `δ` the trap stubs of `S` and the entries of `T`. -/
def SharedMoves (d : UInt64) (δ : Int) (S : Shared) (T : Table) : Prop :=
  Moves d δ S.trapUnreachable ∧ Moves d δ S.trapBounds ∧ Moves d δ S.trapDiv ∧
    Moves d δ S.trapStack ∧ ∀ j c, T j = some c → Moves d δ c.1

theorem Ctl.shift_eq (d : UInt64) (t : Ctl) :
    (t.shift d).target = t.target + d ∧ (t.shift d).types = t.types ∧
      (t.shift d).base = t.base ∧ (t.shift d).arity = t.arity :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem Ctl.shift_mk (d tg : UInt64) (ts : List ValueType) (b : Nat) :
    Ctl.shift d ⟨tg, ts, b⟩ = ⟨tg + d, ts, b⟩ := rfl

theorem Shared.shift_eq (d : UInt64) (S : Shared) :
    (S.shift d).trapUnreachable = S.trapUnreachable + d ∧
      (S.shift d).trapBounds = S.trapBounds + d ∧ (S.shift d).trapDiv = S.trapDiv + d ∧
      (S.shift d).trapStack = S.trapStack + d ∧ (S.shift d).cap = S.cap ∧
      (S.shift d).globalTypes = S.globalTypes :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Env.shift_eq (d : UInt64) (E : Env) :
    (E.shift d).localTypes = E.localTypes ∧ (E.shift d).locals = E.locals ∧
      (E.shift d).globalTypes = E.globalTypes ∧ (E.shift d).cap = E.cap ∧
      (E.shift d).trapUnreachable = E.trapUnreachable + d ∧
      (E.shift d).trapBounds = E.trapBounds + d ∧ (E.shift d).trapDiv = E.trapDiv + d ∧
      (E.shift d).callee = shiftTable d E.callee :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem shiftTable_apply (d : UInt64) (T : Table) (j : Nat) :
    shiftTable d T j = (T j).map fun c => (c.1 + d, c.2) := rfl

theorem curBase_shift (d : UInt64) (ctl : List Ctl) :
    curBase (ctl.map (Ctl.shift d)) = curBase ctl := by
  cases ctl <;> rfl

theorem arity_shift (d : UInt64) (ctl : List Ctl) :
    (ctl.map (Ctl.shift d)).map (·.arity) = ctl.map (·.arity) := by
  rw [List.map_map]
  rfl

theorem sigOf_shift (d : UInt64) (T : Table) : sigOf (shiftTable d T) = sigOf T := by
  funext j
  simp only [sigOf, shiftTable, Option.map_map]
  rfl

theorem branchTo_shift {d : UInt64} {δ : Int} {t : Ctl} {σ : List ValueType} {a : UInt64}
    {is : List Instr} (hg : branchTo t σ a = .ok is) (ht : Moves d δ t.target)
    (ha : Moves d δ (after a t.arity)) : branchTo (t.shift d) σ (a + d) = .ok is := by
  obtain ⟨-, -, -, -, f, hf, -⟩ := gen_branchTo hg
  rw [← hg]
  simp only [branchTo, Ctl.shift_eq, after_shift, hf, bField_shift ha ht hf]

/-! ## Instructions -/

/-- The generated code of an instruction at `a + d`, with the environment and the constructs
shifted by `d`, is that at `a`, given the same for each instruction list smaller than the
instruction. -/
theorem genInstr_shift_of {E : Env} {d : UInt64} {δ : Int}
    (hE : SharedMoves d δ E.toShared E.callee) {ctl : List Ctl} {σ : List ValueType}
    {a : UInt64} {inst : Instruction} {is : List Instr} {fin : Option (List ValueType)}
    (ih : ∀ (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (p : List Instruction)
      (is : List Instr) (fin : Option (List ValueType)), sizeOf p < sizeOf inst →
      genList E ctl σ a p = .ok (is, fin) → (∀ t ∈ ctl, Moves d δ t.target) →
      MovesFrom d δ a is.length →
      genList (E.shift d) (ctl.map (Ctl.shift d)) σ (a + d) p = .ok (is, fin))
    (hg : genInstr E ctl σ a inst = .ok (is, fin)) (hctl : ∀ t ∈ ctl, Moves d δ t.target)
    (ha : MovesFrom d δ a is.length) :
    genInstr (E.shift d) (ctl.map (Ctl.shift d)) σ (a + d) inst = .ok (is, fin) := by
  obtain ⟨hU, hB, hD, -, hT⟩ := hE
  have h0 := ha.base
  rw [← hg]
  cases inst with
  | unreachable =>
      obtain ⟨f, hf, -, -⟩ := gen_unreachable hg
      simp only [genInstr, Env.shift_eq, hf, bField_shift h0 hU hf]
  | remUI64 =>
      obtain ⟨-, -, f, hf, -, -⟩ := gen_divrem (.inl ⟨rfl, rfl⟩) hg
      simp only [genInstr, Env.shift_eq, curBase_shift, hf, cbField_shift h0 hD hf]
  | divUI64 =>
      obtain ⟨-, -, f, hf, -, -⟩ := gen_divrem (.inr ⟨rfl, rfl⟩) hg
      simp only [genInstr, Env.shift_eq, curBase_shift, hf, cbField_shift h0 hD hf]
  | memoryGrow =>
      obtain ⟨hc, gf, gd, -, -, -, hf, hd, his, -⟩ := gen_memoryGrow hg
      have hl : is.length = 16 := by rw [his]; rfl
      simp only [genInstr, Env.shift_eq, curBase_shift, after_shift, hf, hd,
        cbField_shift (ha 5 (by omega)) (ha 12 (by omega)) hf,
        bField_shift (ha 11 (by omega)) (ha 16 (by omega)) hd]
  | load64 off =>
      obtain ⟨ho, g, -, -, -, hf, his, -⟩ := gen_load64 hg
      have hl : is.length = 6 := by rw [his]; rfl
      simp only [genInstr, Env.shift_eq, curBase_shift, after_shift, hf,
        cbField_shift (ha 3 (by omega)) hB hf]
  | store64 off =>
      obtain ⟨ho, g, -, -, -, -, hf, his, -⟩ := gen_store64 hg
      have hl : is.length = 6 := by rw [his]; rfl
      simp only [genInstr, Env.shift_eq, curBase_shift, after_shift, hf,
        cbField_shift (ha 3 (by omega)) hB hf]
  | br n =>
      obtain ⟨t, ht, hb, -⟩ := gen_br hg
      have hb' := branchTo_shift hb (hctl t (List.mem_of_getElem? ht))
        (ha _ (by rw [branchTo_length hb]; omega))
      simp only [genInstr, List.getElem?_map, ht, Option.map_some, hb, hb']
  | ret =>
      obtain ⟨t, ht, hb, -⟩ := gen_ret hg
      have hb' := branchTo_shift hb (hctl t (List.mem_of_getLast? ht))
        (ha _ (by rw [branchTo_length hb]; omega))
      simp only [genInstr, List.getLast?_map, ht, Option.map_some, hb, hb']
  | br_if n =>
      obtain ⟨-, -, -, t, ht, ⟨h0', f, hf, -⟩ | ⟨h0', f, bs, hf, hb, his⟩⟩ := gen_br_if hg
      · simp only [genInstr, curBase_shift, List.getElem?_map, ht, Option.map_some, Ctl.shift_eq,
          ite_eq_left h0', hf, cbField_shift h0 (hctl t (List.mem_of_getElem? ht)) hf]
      · have hl : is.length = bs.length + 1 := by rw [his]; rfl
        have hbl := branchTo_length hb
        have hb' := branchTo_shift hb (hctl t (List.mem_of_getElem? ht))
          ((ha.drop (m := 1) (by omega)) t.arity (by omega))
        simp only [genInstr, curBase_shift, List.getElem?_map, ht, Option.map_some, Ctl.shift_eq,
          after_shift, ite_eq_right h0', hf, cbField_shift h0 (ha _ (by omega)) hf, hb, hb']
  | block pa ra body pts rts =>
      obtain ⟨-, -, hrl, -, fb, hl, -⟩ := gen_block hg
      have hn := (genList_size _ _ _ body is fb hl).1
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl] at hn
      have hl' := ih _ σ a body is fb (by simp; omega) hl
        (List.forall_mem_cons.mpr ⟨ha _ (by omega), hctl⟩) ha
      simp only [List.map_cons, Ctl.shift_mk] at hl'
      simp only [genInstr, Env.shift_eq, sigOf_shift, arity_shift, after_shift, hl, hl']
  | loop pa ra body pts rts =>
      obtain ⟨-, -, -, -, fb, hl, -⟩ := gen_loop hg
      have hl' := ih _ σ a body is fb (by simp; omega) hl (List.forall_mem_cons.mpr ⟨h0, hctl⟩) ha
      simp only [List.map_cons, Ctl.shift_mk] at hl'
      simp only [genInstr, hl, hl']
  | iff pa ra thn els pts rts =>
      obtain ⟨-, -, hrl, -, -, -, ti, ta, ei, ea, f, g, ht, he, -, -, hf, hb, his⟩ := gen_iff hg
      have hst := (genList_size _ _ _ thn ti ta ht).1
      have hse := (genList_size _ _ _ els ei ea he).1
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl, List.length_tail]
        at hst hse
      rw [← hst, ← hse] at ht he hb
      rw [← hst] at hf
      have hl : is.length = 1 + ti.length + 1 + ei.length := by
        rw [his]; simp only [List.length_cons, List.length_append]; omega
      have hx := ha.drop (m := 1 + ti.length) (by omega)
      have hy := hx.drop (m := 1) (by omega)
      have hin : Moves d δ (after (after (after a (1 + ti.length)) 1) ei.length) :=
        hy _ (by omega)
      have ht' := ih _ _ _ thn ti ta (by simp; omega) ht (List.forall_mem_cons.mpr ⟨hin, hctl⟩)
        ((ha.drop (m := 1) (by omega)).le (by omega))
      have he' := ih _ _ _ els ei ea (by simp; omega) he (List.forall_mem_cons.mpr ⟨hin, hctl⟩)
        (hy.le (by omega))
      simp only [List.map_cons, Ctl.shift_mk] at ht' he'
      simp only [genInstr, Env.shift_eq, curBase_shift, sigOf_shift, arity_shift, ← hst, ← hse,
        after_shift, ht, he, hf, hb, ht', he', cbField_shift h0 hy.base hf,
        bField_shift hx.base hin hb]
  | call k =>
      obtain ⟨target, ps, rs, hk, -, -, h, p, r, rfl, rfl, rfl, -, -, -, -, spills, moves, res,
        reloads, g, his, hsl, -, hml, -, hrl, -, hrel, -, hb⟩ := gen_call hg
      have hl : is.length = σ.length - ps.length + ps.length + 1 + rs.length +
          (σ.length - ps.length) := by
        rw [his]
        simp only [List.length_append, List.length_cons, List.length_nil, hsl, hml, hrl, hrel]
      have hb' := bField_shift (ha _ (by omega)) (hT k _ hk : Moves d δ target) hb
      simp only [genInstr, Env.shift_eq, shiftTable_apply, hk, Option.map_some, curBase_shift,
        after_shift, hb, hb']
  | _ => simp only [genInstr, genCmp, genBin, curBase_shift, Env.shift_eq]

mutual

/-- The generated code of an instruction at `a + d`, with the environment and the constructs
shifted by `d`, is that at `a`, when the shift moves by the same number every address that the
generator forms. -/
theorem genInstr_shift {E : Env} {d : UInt64} {δ : Int}
    (hE : SharedMoves d δ E.toShared E.callee) : (ctl : List Ctl) → (σ : List ValueType) →
    (a : UInt64) → (inst : Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    genInstr E ctl σ a inst = .ok (is, fin) → (∀ t ∈ ctl, Moves d δ t.target) →
    MovesFrom d δ a is.length →
    genInstr (E.shift d) (ctl.map (Ctl.shift d)) σ (a + d) inst = .ok (is, fin)
  | _, _, _, _, _, _, hg, hctl, ha =>
      genInstr_shift_of hE
        (fun ctl σ a p is fin _ hl hc hm => genList_shift hE ctl σ a p is fin hl hc hm) hg hctl ha
termination_by _ _ _ inst _ _ _ _ _ => sizeOf inst
decreasing_by all_goals omega

/-- The generated code of an instruction list at `a + d`, with the environment and the
constructs shifted by `d`, is that at `a`. -/
theorem genList_shift {E : Env} {d : UInt64} {δ : Int}
    (hE : SharedMoves d δ E.toShared E.callee) : (ctl : List Ctl) → (σ : List ValueType) →
    (a : UInt64) → (p : List Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    genList E ctl σ a p = .ok (is, fin) → (∀ t ∈ ctl, Moves d δ t.target) →
    MovesFrom d δ a is.length →
    genList (E.shift d) (ctl.map (Ctl.shift d)) σ (a + d) p = .ok (is, fin)
  | ctl, σ, a, [], is, fin, hg, _, _ => by
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      simp [genList, pure, Except.pure]
  | ctl, σ, a, i :: rest, is, fin, hg, hctl, ha => by
      obtain ⟨c1, f1, h1, ⟨rfl, rfl, rfl⟩ | ⟨σ', c2, rfl, h2, rfl⟩⟩ := gen_cons hg
      · have h1' := genInstr_shift hE ctl σ a i _ none h1 hctl ha
        simp [genList, h1', bind, Except.bind, pure, Except.pure]
      · have h1' := genInstr_shift hE ctl σ a i c1 (some σ') h1 hctl
          (ha.le (by simp only [List.length_append]; omega))
        have h2' := genList_shift hE ctl σ' (after a c1.length) rest c2 fin h2 hctl
          ((ha.drop (by simp only [List.length_append]; omega)).le
            (by simp only [List.length_append]; omega))
        simp [genList, h1', after_shift, h2', bind, Except.bind, pure, Except.pure]
termination_by _ _ _ p _ _ _ _ _ => sizeOf p
decreasing_by all_goals (try simp_wf); all_goals omega

end

/-! ## Functions and programs -/

theorem genFunction_shift {callee : Table} {S : Shared} {entry d : UInt64} {δ : Int}
    {f : Function} {is : List Instr} (hS : SharedMoves d δ S callee)
    (hg : genFunction callee S entry f = .ok is) (ha : MovesFrom d δ entry is.length) :
    genFunction (shiftTable d callee) (S.shift d) (entry + d) f = .ok is := by
  obtain ⟨-, -, -, hf, hn, stores, body, fin, g, hsl, -, hl, -, hcb, his⟩ := gen_function hg
  have hbl := (genList_size _ _ _ f.body body fin hl).1
  simp only [List.map_cons, List.map_nil, List.length_nil, Ctl.arity_mk, List.length_reverse]
    at hbl
  have hlen : is.length = 5 + (f.params.length + f.locals.length) + body.length + 3 := by
    rw [his]
    simp only [List.length_append, List.length_cons, List.length_nil, hsl]
  have hx := ha.drop (m := 5 + (f.params.length + f.locals.length)) (by omega)
  have hl' := genList_shift hS _ _ _ _ _ _ hl
    (List.forall_mem_cons.mpr ⟨hx _ (by omega), fun _ h => absurd h List.not_mem_nil⟩)
    (hx.le (by omega))
  simp only [List.map_cons, List.map_nil, Ctl.shift_mk] at hl'
  have hl'' : genList
      { toShared := S.shift d, localTypes := f.params ++ f.locals, callee := shiftTable d callee }
      _ _ _ _ = _ := hl'
  rw [← hg]
  simp only [genFunction, Shared.shift_eq, sigOf_shift, after_shift, hl, hl'', hcb,
    cbField_shift (ha 2 (by omega)) hS.2.2.2.1 hcb]

theorem genFunctions_shift {callee : Table} {S : Shared} {d : UInt64} {δ : Int}
    (hS : SharedMoves d δ S callee) :
    ∀ {a : UInt64} {fs : List (Nat × Function)} {is : List Instr},
      genFunctions callee S a fs = .ok is → MovesFrom d δ a is.length →
      genFunctions (shiftTable d callee) (S.shift d) (a + d) fs = .ok is
  | _, [], _, hg, _ => hg
  | a, (j, f) :: rest, is, hg, ha => by
      simp only [genFunctions, bind, Except.bind] at hg
      cases h1 : genFunction callee S a f with
      | error e => simp [h1] at hg
      | ok is1 =>
          cases h2 : genFunctions callee S (after a is1.length) rest with
          | error e => simp [h1, h2] at hg
          | ok is2 =>
              simp [h1, h2, pure, Except.pure] at hg
              subst hg
              have h1' := genFunction_shift hS h1 (ha.le (by simp))
              have h2' := genFunctions_shift hS h2 ((ha.drop (by simp)).le (by simp))
              simp [genFunctions, h1', after_shift, h2', bind, Except.bind, pure, Except.pure]

theorem entriesFrom_shift (sig : Nat → Option (Nat × Nat)) (d : UInt64) :
    ∀ (a : UInt64) (fs : List (Nat × Function)),
      entriesFrom sig (a + d) fs = (entriesFrom sig a fs).map fun x => (x.1, x.2.1 + d, x.2.2)
  | _, [] => rfl
  | a, (j, f) :: rest => by
      simp only [entriesFrom, after_shift, entriesFrom_shift sig d _ rest, List.map_cons]

theorem endOf_shift (sig : Nat → Option (Nat × Nat)) (d : UInt64) :
    ∀ (a : UInt64) (fs : List (Nat × Function)), endOf sig (a + d) fs = endOf sig a fs + d
  | _, [] => rfl
  | a, (j, f) :: rest => by simp only [endOf, after_shift, endOf_shift sig d _ rest]

theorem entryIn_shift (sig : Nat → Option (Nat × Nat)) (a d : UInt64)
    (fs : List (Nat × Function)) (j : Nat) :
    entryIn sig (a + d) fs j = (entryIn sig a fs j).map fun c => (c.1 + d, c.2) := by
  simp only [entryIn, entriesFrom_shift, List.find?_map, Option.map_map]
  rfl

theorem tableOf_shift (targets : List Nat) (a d : UInt64) (fs : List (Nat × Function)) :
    tableOf targets (a + d) fs = shiftTable d (tableOf targets a fs) := by
  funext j
  by_cases h : j ∈ targets <;> simp [tableOf, shiftTable, entryIn_shift, h]

/-- The entries of the functions of `fs`, laid out from `a`, lie within their code. -/
theorem entriesFrom_at (sig : Nat → Option (Nat × Nat)) :
    ∀ (a : UInt64) (fs : List (Nat × Function)), ∀ x ∈ entriesFrom sig a fs,
      ∃ k ≤ (fs.map fun y => functionSize sig y.2).sum, x.2.1 = after a k
  | _, [] => by simp [entriesFrom]
  | a, (j, f) :: rest => by
      intro x hx
      simp only [entriesFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨0, Nat.zero_le _, (after_zero a).symm⟩
      · obtain ⟨k, hk, e⟩ := entriesFrom_at sig _ rest x hx
        exact ⟨functionSize sig f + k, by simp only [List.map_cons, List.sum_cons]; omega,
          by rw [e, after_after]⟩

theorem entryIn_moves {sig : Nat → Option (Nat × Nat)} {a d : UInt64} {δ : Int}
    {fs : List (Nat × Function)}
    (ha : MovesFrom d δ a (fs.map fun y => functionSize sig y.2).sum) {j : Nat}
    {c : UInt64 × List ValueType × List ValueType} (h : entryIn sig a fs j = some c) :
    Moves d δ c.1 := by
  obtain ⟨k, hk, e⟩ := entriesFrom_at sig a fs _ (entryIn_mem h)
  have e' : c.1 = after a k := e
  rw [e']
  exact ha k hk

theorem tableOf_some {targets : List Nat} {a : UInt64} {fs : List (Nat × Function)} {j : Nat}
    {c : UInt64 × List ValueType × List ValueType} (h : tableOf targets a fs j = some c) :
    entryIn (sigIn targets fs) a fs j = some c := by
  unfold tableOf at h
  split at h
  · exact h
  · cases h

theorem genOut_shift {a d : UInt64} {δ : Int} {o : Output} {out : List Instr}
    (hg : genOut a o = .ok out) (ha : MovesFrom d δ a (outSize o)) :
    genOut (a + d) o = .ok out := by
  cases o with
  | word => exact hg
  | array =>
      obtain ⟨cz, back, h1, h2, -⟩ := gen_out_array hg
      rw [← hg]
      simp only [genOut, after_shift, h1, h2,
        cbField_shift (ha 18 (by decide)) (ha 39 (by decide)) h1,
        bField_shift (ha 38 (by decide)) (ha 18 (by decide)) h2]

theorem genMain_shift {a entry uart room d : UInt64} {δ : Int} {args : List UInt64}
    {o : Output} {is : List Instr} (hg : genMain a entry args uart room o = .ok is)
    (ha : MovesFrom d δ a is.length) (he : Moves d δ entry) :
    genMain (a + d) (entry + d) args uart room o = .ok is := by
  obtain ⟨-, g, out, hb, ho, -⟩ := gen_main hg
  have hl := genMain_length hg
  unfold mainSize at hl
  have ho' := genOut_shift ho ((ha.drop (m := 13 + 4 * args.length) (by omega)).le (by omega))
  rw [← hg]
  simp only [genMain, after_shift, hb, bField_shift (ha _ (by omega)) he hb, ho, ho']

/-- The program that `genProgram` places at `base + d` is the one at `base`, when
`base + 4 * p.length` and `base + d + 4 * p.length`, as numbers, lie below 2^64. -/
theorem genProgram_shift {m : Module} {k : Nat} {args : List UInt64} {uart base room : UInt64}
    {cap : Nat} {o : Output} {p : List Instr} {d : UInt64}
    (hg : genProgram m k args uart base room cap o = .ok p)
    (h1 : base.toNat + 4 * p.length < 2 ^ 64) (h2 : (base + d).toNat + 4 * p.length < 2 ^ 64) :
    genProgram m k args uart (base + d) room cap o = .ok p := by
  have ha := movesFrom_of h1 h2
  generalize ((base + d).toNat - base.toNat : Int) = δ at ha
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hok, hgt, hgl, hfs, hfirst,
    hT, hen, hps, hmn, hfn, hp, hb1, hb2, hb3, hb4⟩ := gen_program hg
  have hml := genMain_length hmn
  obtain ⟨hfl, hend⟩ := genFunctions_length (sigOf_tableOf _ _ _) hfn
  have hpl : p.length = mainSize args.length o + fns.length + 20 := by
    rw [hp]
    simp only [List.length_append, List.length_cons, List.length_nil, movImm_length, hml]
  have hF : MovesFrom d δ first (p.length - (1 + mainSize args.length o)) := by
    rw [hfirst, after_after]
    exact ha.drop (by omega)
  have hX : MovesFrom d δ T 19 := by
    rw [hT, hend]
    exact (hF.drop (by omega)).le (by omega)
  have hE : ∀ {j c}, entryIn (sigIn (callTargets m k) fs) first fs j = some c → Moves d δ c.1 :=
    fun h => entryIn_moves (hF.le (by omega)) h
  have hS : SharedMoves d δ ⟨T, after T 5, after T 10, after T 15, cap, gts⟩
      (tableOf (callTargets m k) first fs) :=
    ⟨hX.base, hX 5 (by omega), hX 10 (by omega), hX 15 (by omega),
      fun _ _ h => hE (tableOf_some h)⟩
  have hen' : entryIn (sigIn (callTargets m k) fs) (first + d) fs k = some (e + d, pk, rk) := by
    rw [entryIn_shift, hen]
    rfl
  have hmn' := genMain_shift hmn ((ha.drop (m := 1) (by omega)).le (by omega))
    (hE hen : Moves d δ e)
  have hfn' : genFunctions (shiftTable d (tableOf (callTargets m k) first fs))
      ⟨T + d, after T 5 + d, after T 10 + d, after T 15 + d, cap, gts⟩ (first + d) fs =
      .ok fns := genFunctions_shift hS hfn (hF.le (by omega))
  have h0 := ha.base
  have hb1' := bField_shift (hX 4 (by omega)) h0 hb1
  have hb2' := bField_shift ((hX.drop (m := 5) (by omega)) 4 (by omega)) h0 hb2
  have hb3' := bField_shift ((hX.drop (m := 10) (by omega)) 4 (by omega)) h0 hb3
  have hb4' := bField_shift ((hX.drop (m := 15) (by omega)) 4 (by omega)) h0 hb4
  rw [← hg]
  simp only [genProgram, hok, hgt, hgl, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
    hfs, bind, Except.bind, pure, Except.pure, after_shift, ← hfirst, endOf_shift, ← hT,
    tableOf_shift, hen, hen', hps, hmn, hmn', hfn, hfn', hb1, hb2, hb3, hb4, hb1', hb2', hb3',
    hb4']

/-! ## Images -/

/-- The layout `L` with its addresses shifted by `d`. -/
def Layout.shift (d : UInt64) (L : Layout) : Layout :=
  { L with
    image := L.image + d, base := L.base + d, vectors := L.vectors + d, table := L.table + d,
    area := L.area + d, clear := L.clear + d, areaEnd := L.areaEnd + d,
    stackTop := L.stackTop + d }

theorem Layout.shift_eq (d : UInt64) (L : Layout) :
    (L.shift d).image = L.image + d ∧ (L.shift d).base = L.base + d ∧
      (L.shift d).vectors = L.vectors + d ∧ (L.shift d).table = L.table + d ∧
      (L.shift d).area = L.area + d ∧ (L.shift d).clear = L.clear + d ∧
      (L.shift d).areaEnd = L.areaEnd + d ∧ (L.shift d).stackTop = L.stackTop + d ∧
      (L.shift d).fileSize = L.fileSize ∧ (L.shift d).size = L.size :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem add_right_comm' (x y d : UInt64) : x + d + y = x + y + d := by ac_rfl

/-- The layout of an image at `image + d` is that at `image` with each address shifted by `d`
and the same sizes. -/
theorem layoutOf_shift (image d : UInt64) (n : Nat) (m : Module) (cap : Nat) (room : UInt64) :
    layoutOf (image + d) n m cap room = (layoutOf image n m cap room).shift d := by
  simp only [layoutOf, Layout.shift, add_right_comm' image d]

theorem after_add_comm (x d c : UInt64) (k : Nat) : after (x + d + c) k = after (x + c) k + d := by
  simp only [after]
  ac_rfl

theorem add_sub_add (x y d : UInt64) : x + d - (y + d) = x - y := by
  rw [UInt64.sub_eq_iff_eq_add, ← UInt64.add_assoc, UInt64.sub_add_cancel]

/-- The startup of the image at `image + d` is that at `image`, when `d` is a multiple of 4096,
neither image passes 2^64, and the area holds its prefix. -/
theorem startupCode_shift {image d : UInt64} {n : Nat} {m : Module} {cap : Nat}
    {room : UInt64} {is : List Instr} (hd : d.toNat % 4096 = 0)
    (hpre : areaPrefix m ≤ areaSize cap)
    (h1 : image.toNat + (layoutOf image n m cap room).size < 2 ^ 64)
    (h2 : (image + d).toNat + (layoutOf image n m cap room).size < 2 ^ 64)
    (hs : startupCode (layoutOf image n m cap room) = .ok is) :
    startupCode (layoutOf (image + d) n m cap room) = .ok is := by
  obtain ⟨toHalt, skip, vec, tab, clr, fin, stk, ar, call, back, c0, c1, c2, c3, c4, c5, c6, c7,
    c8, c9, -⟩ := startupCode_ok hs
  obtain ⟨hI, hB, hV, hTb, hA, hC, hE, hS, hsz⟩ := layoutOf_fields image n m cap room
  simp only [hI, hB, hV, hTb, hA, hC, hE, hS] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have hv := vecOff_ge n
  have hao := areaOff_ge n
  have htab : tabOff n = vecOff n + 2048 := rfl
  have h67 : startupLength = 67 := rfl
  have hδ : ((image + d).toNat - image.toNat : Int) % 4096 = 0 := by
    have := UInt64.toNat_add image d
    have := image.toNat_lt
    simp only [Nat.reducePow] at *
    omega
  have hofs : ∀ X, X ≤ (layoutOf image n m cap room).size →
      (image + UInt64.ofNat X).toNat = image.toNat + X := fun X hX => by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hF : ∀ X, X ≤ (layoutOf image n m cap room).size →
      Moves d ((image + d).toNat - image.toNat) (image + UInt64.ofNat X) := fun X hX =>
    moves_of_range h1 h2 (by rw [hofs X hX]; omega) (by rw [hofs X hX]; omega)
  have h64 : (image + 64).toNat = image.toNat + 64 := by
    have := UInt64.toNat_add image 64
    simp only [UInt64.reduceToNat, Nat.reducePow] at this h1 ⊢
    omega
  have hW : ∀ k ≤ 66, Moves d ((image + d).toNat - image.toNat) (after (image + 64) k) :=
    fun k hk => moves_of_range h1 h2
      (by rw [toNat_after (by rw [h64]; omega), h64]; omega)
      (by rw [toNat_after (by rw [h64]; omega), h64]; omega)
  have hB1 : Moves d ((image + d).toNat - image.toNat)
      (after (image + UInt64.ofNat (64 + 4 * startupLength)) 1) :=
    moves_of_range h1 h2
      (by rw [toNat_after (by rw [hofs _ (by omega)]; omega), hofs _ (by omega)]; omega)
      (by rw [toNat_after (by rw [hofs _ (by omega)]; omega), hofs _ (by omega)]; omega)
  rw [layoutOf_shift, ← hs]
  simp only [startupCode, Layout.shift_eq, hI, hB, hV, hTb, hA, hC, hE, hS,
    after_add_comm image d 64, after_shift (image + UInt64.ofNat (64 + 4 * startupLength)) d 1,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    cbField_shift (hW 3 (by omega)) (hW 66 (by omega)) c0,
    cbField_shift (hW 29 (by omega)) (hW 31 (by omega)) c1,
    addrOf_shift hδ (hW 4 (by omega)) (hF _ (by omega)) c2,
    addrOf_shift hδ (hW 23 (by omega)) (hF _ (by omega)) c3,
    addrOf_shift hδ (hW 40 (by omega)) (hF _ (by omega)) c4,
    addrOf_shift hδ (hW 42 (by omega)) (hF _ (by omega)) c5,
    addrOf_shift hδ (hW 49 (by omega)) (hF _ (by omega)) c6,
    addrOf_shift hδ (hW 52 (by omega)) (hF _ (by omega)) c7,
    bField_shift (hW 54 (by omega)) hB1 c8, bField_shift (hF _ (by omega)) (hW 55 (by omega)) c9]

/-- The image that `genImage` writes at `image + d` has the bytes of the image at `image` and its
layout shifted by `d`, when `d` is a multiple of 4096 and the image at `image + d` also lies in the
RAM GiB.  The sum `image + d` may wrap around 2^64, which places the second image below the
first. -/
theorem genImage_shift {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image d : UInt64} {bytes : List UInt8} {L : Layout}
    (hg : genImage m k args room cap o image = .ok (bytes, L)) (hd : d.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ (image + d).toNat) (hhi : (image + d).toNat + L.size ≤ 0x80000000) :
    genImage m k args room cap o (image + d) = .ok (bytes, L.shift d) := by
  obtain ⟨prog, start, hp, rfl, -, hhi0, hpre, hs, rfl⟩ := gen_image hg
  have hsz := (layoutOf_fields image prog.length m cap room).2.2.2.2.2.2.2.2
  have hv := vecOff_ge prog.length
  have hao := areaOff_ge prog.length
  unfold tabOff at hao
  have h67 : startupLength = 67 := rfl
  have e1 : (image + UInt64.ofNat (64 + 4 * startupLength)).toNat = image.toNat + 332 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (image + d + UInt64.ofNat (64 + 4 * startupLength)).toNat =
      (image + d).toNat + 332 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hp' := genProgram_shift hp (by rw [e1]; omega) (by rw [← add_right_comm', e2]; omega)
  rw [← add_right_comm'] at hp'
  have hs' := startupCode_shift hd hpre (by omega) (by omega) hs
  rw [layoutOf_shift] at hs'
  have hr : 0x40000000 ≤ (image + d).toNat ∧
      (image + d).toNat + (layoutOf image prog.length m cap room).size ≤ 0x80000000 ∧
      areaPrefix m ≤ areaSize cap := ⟨hlo, hhi, hpre⟩
  unfold genImage
  rw [hp']
  simp only [bind, Except.bind, layoutOf_shift, Layout.shift_eq, hr, and_self, ite_true, hs',
    pure, Except.pure, add_sub_add]

/-- The kernel's check of the image at `image` holds for the image at `image + d`, when `d` is a
multiple of 4096 and the image at `image + d` lies in the RAM GiB. -/
theorem bytesOk_shift {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image d : UInt64} {n len : Nat}
    (hk : bytesOk (genImage m k args room cap o image) n len = true) (hd : d.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ (image + d).toNat)
    (hhi : ∀ bytes L, genImage m k args room cap o image = .ok (bytes, L) →
      (image + d).toNat + L.size ≤ 0x80000000) :
    bytesOk (genImage m k args room cap o (image + d)) n len = true := by
  obtain ⟨bytes, L, hg, -, -⟩ := of_bytesOk hk
  rw [genImage_shift hg hd hlo (hhi bytes L hg)]
  rw [hg] at hk
  exact hk

end LeanExe.A64
