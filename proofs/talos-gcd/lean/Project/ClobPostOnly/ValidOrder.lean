import Project.ClobPostOnly.Model
import Project.ClobPostOnly.SearchHelpers
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Order-validity helpers used by `postOnly`

The validity check combines four scalar conditions with an identifier scan.
The scan theorem ranges over every order array represented by `OrdersAt` and
preserves the store.  The combined theorem states the exact `validOrderL`
result while retaining the generated short-circuit order.
-/

namespace Project.ClobPostOnly.ValidOrder

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Model Project.ClobPostOnly.SearchHelpers

set_option maxHeartbeats 64000000

private theorem hasIdL_of_index (os : List OrderL) (id : UInt64) (k : Nat)
    (hk : k < os.length) (hhit : (os[k]!.oid == id) = true) :
    hasIdL os id := by
  refine ⟨os[k]!, ?_, by simpa using hhit⟩
  rw [getBang_eq hk]
  exact List.getElem_mem hk

private theorem not_hasIdL_of_clean (os : List OrderL) (id : UInt64)
    (hclean : ∀ j, j < os.length → (os[j]!.oid == id) = false) :
    ¬hasIdL os id := by
  rintro ⟨order, hmem, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
  have h := hclean j hj
  rw [getBang_eq hj] at h
  simp at h

theorem func2_spec (env : HostEnv Unit) (st : Store Unit) (side : UInt64) :
    TerminatesWith (m := «module») (id := 2) (initial := st) (env := env)
      [.i64 side]
      (fun st' vs => vs = [.i64 (boolWord (validSideL side))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func2 _ st
      { params := [.i64 side], locals := [.i64 0], values := [] } env
    unfold func2
    wp_run
    by_cases hz : side = 0
    · po_step
      po_step
      po_step
      simp [validSideL, hz, boolWord, func2Def]
    · po_step
      by_cases ho : side = 1
      · po_step
        po_step
        po_step
        simp [validSideL, ho, boolWord, func2Def]
      · po_step
        po_step
        po_step
        simp [validSideL, ho, boolWord, func2Def]
        exact hz

/-- The generated array scan returns whether an order identifier occurs. -/
theorem func5_spec (env : HostEnv Unit) (st : Store Unit) (ptr id : UInt64)
    (os : List OrderL) (hlen : os.length < 4294967296)
    (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 5) (initial := st) (env := env)
      [.i64 id, .i64 ptr, .i64 0]
      (fun st' vs => vs = [.i64 (boolWord (hasIdL os id))] ∧ st' = st) := by
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  apply TerminatesWith.of_wp_entry_for (f := func5Def)
  · simp [«module»]
  · change wp «module» func5 _ st
      { params := [.i64 0, .i64 ptr, .i64 id],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func5
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    apply wp_block_cons
    apply wp_loop_cons
      (Inv := fun st' s =>
        st' = st ∧
        ∃ k : Nat, k ≤ os.length ∧
        (∀ j : Nat, j < k → (os[j]!.oid == id) = false) ∧
        ∃ f3 f4 f5 f6 f7 f8 g16 g17 g18 g19 g20 : UInt64,
          s = ({ params := [.i64 0, .i64 ptr, .i64 id],
                 locals := [.i64 f3, .i64 f4, .i64 f5, .i64 f6, .i64 f7,
                   .i64 f8, .i64 ptr, .i64 (UInt64.ofNat os.length),
                   .i64 (UInt64.ofNat k), .i64 (UInt64.ofNat os.length),
                   .i64 (UInt64.ofNat os.length), .i64 0, .i64 ptr,
                   .i64 g16, .i64 g17, .i64 g18, .i64 g19, .i64 g20],
                 values := [] } : Locals))
      (μ := fun _ s =>
        match s.locals with
        | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: .i64 idx :: _ =>
            os.length - idx.toNat
        | _ => 0)
    · exact ⟨rfl, 0, Nat.zero_le _, by omega, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, rfl⟩
    · rintro st2 s2 ⟨rfl, k, hk, hclean, f3, f4, f5, f6, f7, f8,
        g16, g17, g18, g19, g20, rfl⟩
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
        subst k
        have hnot := not_hasIdL_of_clean os id hclean
        simp [boolWord, hnot, func5Def]
      · have hklt : k < os.length := Nat.lt_of_le_of_ne hk hkend
        have hnge : ¬UInt64.ofNat k ≥ UInt64.ofNat os.length := by
          rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
          omega
        rw [if_neg hnge]
        wp_run
        obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩,
          ⟨hr5, hb5⟩⟩ := hElems k hklt
        refine ⟨hb1, hb2, hb3, hb4, hb5, ?_⟩
        rw [hr1, hr2, hr3, hr4, hr5]
        by_cases hm : (os[k]!.oid == id) = true
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simpa using hm)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run
          have hhas := hasIdL_of_index os id k hklt hm
          simp [boolWord, hhas, func5Def]
        · have hm' : (os[k]!.oid == id) = false := by
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
            subst j
            simpa using hm'

/-- The generated helper returns the exact source order-validity result. -/
theorem func6_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (order : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 6) (initial := st) (env := env)
      [.i64 order.oqty, .i64 order.oprice, .i64 order.oside,
       .i64 order.otrader, .i64 order.oid, .i64 ptr, .i64 0]
      (fun st' vs =>
        vs = [.i64 (boolWord (validOrderL os order))] ∧ st' = st) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) ?_ ?_
  · simp [«module»]
  · change wp «module» func6 _ st
      { params := [.i64 0, .i64 ptr, .i64 order.oid,
          .i64 order.otrader, .i64 order.oside, .i64 order.oprice,
          .i64 order.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func6
    wp_run
    by_cases hid : order.oid = 0
    · po_step
      po_step
      po_step
      po_step
      po_step
      po_step
      simp [validOrderL, hid, boolWord, func6Def]
    · po_step
      po_step
      by_cases htrader : order.otrader = 0
      · po_step
        po_step
        po_step
        po_step
        po_step
        simp [validOrderL, hid, htrader, boolWord, func6Def]
      · po_step
        po_step
        refine wp_call_tw (func2_spec env st order.oside) ?_
        rintro st1 vs ⟨rfl, rfl⟩
        by_cases hside : validSideL order.oside
        · by_cases hqty : order.oqty = 0
          · have hinvalid : ¬validOrderL os order := by
              simp [validOrderL, hqty]
            simp only [boolWord, if_pos hside, if_neg hinvalid]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            po_step
            po_step
            po_step
            simp [func6Def]
          · by_cases hhas : hasIdL os order.oid
            · have hinvalid : ¬validOrderL os order := by
                simp [validOrderL, hhas]
              simp only [boolWord, if_pos hside, if_neg hinvalid]
              wp_run
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              po_step
              po_step
              refine wp_call_tw
                (func5_spec env st1 ptr order.oid os hlen hInput) ?_
              rintro st2 vs ⟨rfl, rfl⟩
              simp only [boolWord, if_pos hhas]
              wp_run
              po_step
              simp [func6Def]
            · have hvalid : validOrderL os order := by
                exact ⟨hid, htrader, hside, hqty, hhas⟩
              simp only [boolWord, if_pos hside, if_pos hvalid]
              wp_run
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              wp_run
              po_step
              po_step
              refine wp_call_tw
                (func5_spec env st1 ptr order.oid os hlen hInput) ?_
              rintro st2 vs ⟨rfl, rfl⟩
              simp only [boolWord, if_neg hhas]
              wp_run
              po_step
              simp [func6Def]
        · have hinvalid : ¬validOrderL os order := by
            simp [validOrderL, hside]
          simp only [boolWord, if_neg hinvalid, if_neg hside]
          wp_run
          po_step
          po_step
          po_step
          simp [func6Def]

end Project.ClobPostOnly.ValidOrder
