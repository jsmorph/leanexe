import Project.ClobQuote.Spec
import Project.ClobCancel.Program
import Project.Common
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# The id-scan loop of the `cancel` export

`func3` scans the order array once for the first element whose id equals the
argument.  The scan records zero when no element matches and records the
first matching index plus one otherwise.  The lemma uses the literal
block-loop program with a generic continuation and preserves the five loaded
element fields at the found exit.

The list-level bridge is `List.findIdx?` over the element predicate.
-/

namespace Project.ClobCancel.Spec

open Wasm Project.Common Project.ClobQuote.Step Project.ClobQuote.Spec Project.ClobCancel

set_option maxHeartbeats 64000000

/-- The first index whose order id equals `cid`. -/
def idIdx (os : List OrderL) (cid : UInt64) : Option Nat :=
  os.findIdx? (fun o => o.oid == cid)

theorem idIdx_of_first (os : List OrderL) (cid : UInt64) (k : Nat)
    (hk : k < os.length)
    (hclean : ∀ j, j < k → (os[j]!.oid == cid) = false)
    (hhit : (os[k]!.oid == cid) = true) :
    idIdx os cid = some k := by
  unfold idIdx
  induction os generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero =>
          have h := hhit
          rw [getBang_eq hk, List.getElem_cons_zero] at h
          simp [List.findIdx?_cons, h]
      | succ n =>
          have hk' : n < xs.length := by simpa using hk
          have hx : (x.oid == cid) = false := by
            have h := hclean 0 (Nat.succ_pos n)
            rwa [getBang_eq (by simp : (0 : Nat) < (x :: xs).length),
              List.getElem_cons_zero] at h
          have hclean' : ∀ j, j < n → (xs[j]!.oid == cid) = false := by
            intro j hj
            have hb : j + 1 < (x :: xs).length := by
              simp
              omega
            have h := hclean (j + 1) (by omega)
            rw [getBang_eq hb, List.getElem_cons_succ] at h
            rwa [getBang_eq (by omega : j < xs.length)]
          have hhit' : (xs[n]!.oid == cid) = true := by
            have h := hhit
            rw [getBang_eq hk, List.getElem_cons_succ] at h
            rwa [getBang_eq hk']
          simp [List.findIdx?_cons, hx]
          exact ih n hk' hclean' hhit'

theorem idIdx_none_of_clean (os : List OrderL) (cid : UInt64)
    (hclean : ∀ j, j < os.length → (os[j]!.oid == cid) = false) :
    idIdx os cid = none := by
  unfold idIdx
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have h := hclean j hj
  rwa [getBang_eq hj] at h

/-- The scan frame is `func3`'s: two parameters and twenty-nine locals,
with the pointer copy at 15, the length at 16, the index at 17, the encoded
result at 18, and the element fields at 2 through 6. -/
theorem scanIndex_spec {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program}
    {ptr cid : UInt64} (os : List OrderL)
    {e2 e3 e4 e5 e6 g7 g8 g9 g10 g11 g12 g13 g14 g19 g20 g21 g22 g23 g24
     g25 g26 g27 g28 g29 g30 : UInt64}
    (hlen : os.length < 4294967296)
    (hIn : OrdersAt st ptr os)
    (hNone : idIdx os cid = none →
      ∀ f2 f3 f4 f5 f6 : UInt64,
        wp «module» rest Q st
          ({ params := [.i64 ptr, .i64 cid],
             locals := [.i64 f2, .i64 f3, .i64 f4, .i64 f5, .i64 f6,
             .i64 g7, .i64 g8, .i64 g9, .i64 g10, .i64 g11, .i64 g12,
             .i64 g13, .i64 g14, .i64 ptr, .i64 (UInt64.ofNat os.length),
             .i64 (UInt64.ofNat os.length), .i64 0, .i64 g19, .i64 g20,
             .i64 g21, .i64 g22, .i64 g23, .i64 g24, .i64 g25, .i64 g26,
             .i64 g27, .i64 g28, .i64 g29, .i64 g30],
             values := [] } : Locals)
          env)
    (hSome : ∀ i : Nat, idIdx os cid = some i →
      ∀ f2 f3 f4 f5 f6 : UInt64,
        wp «module» rest Q st
          ({ params := [.i64 ptr, .i64 cid],
             locals := [.i64 f2, .i64 f3, .i64 f4, .i64 f5, .i64 f6,
             .i64 g7, .i64 g8, .i64 g9, .i64 g10, .i64 g11, .i64 g12,
             .i64 g13, .i64 g14, .i64 ptr, .i64 (UInt64.ofNat os.length),
             .i64 (UInt64.ofNat i), .i64 (UInt64.ofNat i + 1), .i64 g19,
             .i64 g20, .i64 g21, .i64 g22, .i64 g23, .i64 g24, .i64 g25,
             .i64 g26, .i64 g27, .i64 g28, .i64 g29, .i64 g30],
             values := [] } : Locals)
          env) :
    wp «module»
      (  .block 0 0 [
    .loop 0 0 [
      .localGet 17,
      .localGet 16,
      .geUI64,
      .br_if 1,
      .localGet 15,
      .localGet 17,
      .constI64 (5 : UInt64),
      .mulI64,
      .constI64 (1 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 2,
      .localGet 15,
      .localGet 17,
      .constI64 (5 : UInt64),
      .mulI64,
      .constI64 (2 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 3,
      .localGet 15,
      .localGet 17,
      .constI64 (5 : UInt64),
      .mulI64,
      .constI64 (3 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 4,
      .localGet 15,
      .localGet 17,
      .constI64 (5 : UInt64),
      .mulI64,
      .constI64 (4 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 5,
      .localGet 15,
      .localGet 17,
      .constI64 (5 : UInt64),
      .mulI64,
      .constI64 (5 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 6,
      .localGet 2,
      .localGet 1,
      .eqI64,
      .iff 0 1 [
        .constI64 (1 : UInt64)
      ] [
        .constI64 (0 : UInt64)
      ],
      .constI64 (0 : UInt64),
      .neI64,
      .iff 0 0 [
        .localGet 17,
        .constI64 (1 : UInt64),
        .addI64,
        .localSet 18,
        .br 2
      ] [],
      .localGet 17,
      .constI64 (1 : UInt64),
      .addI64,
      .localSet 17,
      .br 0
    ]
  ] :: rest)
      Q st
      ({ params := [.i64 ptr, .i64 cid],
         locals := [.i64 e2, .i64 e3, .i64 e4, .i64 e5, .i64 e6,
         .i64 g7, .i64 g8, .i64 g9, .i64 g10, .i64 g11, .i64 g12,
         .i64 g13, .i64 g14, .i64 ptr, .i64 (UInt64.ofNat os.length),
         .i64 0, .i64 0, .i64 g19, .i64 g20, .i64 g21, .i64 g22, .i64 g23,
         .i64 g24, .i64 g25, .i64 g26, .i64 g27, .i64 g28, .i64 g29,
         .i64 g30],
         values := [] } : Locals)
      env := by
  obtain ⟨-, hElems⟩ := hIn
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s =>
      st' = st ∧
      ∃ k : Nat, k ≤ os.length ∧
      (∀ j : Nat, j < k → (os[j]!.oid == cid) = false) ∧
      ∃ f2 f3 f4 f5 f6 : UInt64,
        s = ({ params := [.i64 ptr, .i64 cid],
               locals := [.i64 f2, .i64 f3, .i64 f4, .i64 f5, .i64 f6,
               .i64 g7, .i64 g8, .i64 g9, .i64 g10, .i64 g11, .i64 g12,
               .i64 g13, .i64 g14, .i64 ptr, .i64 (UInt64.ofNat os.length),
               .i64 (UInt64.ofNat k), .i64 0, .i64 g19, .i64 g20, .i64 g21,
               .i64 g22, .i64 g23, .i64 g24, .i64 g25, .i64 g26, .i64 g27,
               .i64 g28, .i64 g29, .i64 g30],
               values := [] } : Locals))
    (μ := fun _ s =>
      match s.locals with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
        _ :: _ :: .i64 idx :: _ => os.length - idx.toNat
      | _ => 0)
  · exact ⟨rfl, 0, Nat.zero_le _, by omega, e2, e3, e4, e5, e6, rfl⟩
  · rintro st2 s2 ⟨rfl, k, hk, hclean, f2, f3, f4, f5, f6, rfl⟩
    have hkU : (UInt64.ofNat k).toNat = k :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    wp_run
    try simp
    by_cases hkend : k = os.length
    · have hge : UInt64.ofNat k ≥ UInt64.ofNat os.length := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
        omega
      rw [if_pos hge]
      try wp_run
      try simp
      subst hkend
      exact hNone (idIdx_none_of_clean os cid hclean) _ _ _ _ _
    · have hklt : k < os.length := Nat.lt_of_le_of_ne hk hkend
      have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat os.length) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
        omega
      rw [if_neg hnge]
      wp_run
      try simp
      obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩,
        ⟨hr5, hb5⟩⟩ := hElems k hklt
      rw [if_neg (Nat.not_lt.mpr hb1), if_neg (Nat.not_lt.mpr hb2),
        if_neg (Nat.not_lt.mpr hb3), if_neg (Nat.not_lt.mpr hb4),
        if_neg (Nat.not_lt.mpr hb5)]
      rw [hr1, hr2, hr3, hr4, hr5]
      by_cases hm : (os[k]!.oid == cid) = true
      · refine wp_iff_cons rfl ?_
        rw [if_pos (by simpa using hm)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        try simp
        exact hSome k (idIdx_of_first os cid k hklt hclean hm) _ _ _ _ _
      · have hm' : (os[k]!.oid == cid) = false := by
          simpa using hm
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa using hm')]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        try simp
        have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
        rw [hkadd]
        refine ⟨⟨k + 1, by omega, ?_, rfl⟩, by omega⟩
        intro j hj
        by_cases hjk : j < k
        · simpa using hclean j hjk
        · have hjeq : j = k := by omega
          subst hjeq
          simpa using hm'

end Project.ClobCancel.Spec
