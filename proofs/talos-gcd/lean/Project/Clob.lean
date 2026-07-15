import Project.Common

/-!
# Shared CLOB model

The CLOB artifacts read one order as five consecutive `UInt64` words.  This
module states that source-independent layout once for quote, cancel, and the
remaining kernel proofs.  It also states the common fixed-width array header
used by artifacts that allocate CLOB values.
-/

namespace Project.Clob

open Wasm

structure OrderL where
  oid : UInt64
  otrader : UInt64
  oside : UInt64
  oprice : UInt64
  oqty : UInt64
  deriving Inhabited

def OrderL.word (order : OrderL) (field : Nat) : UInt64 :=
  match field with
  | 0 => order.oid
  | 1 => order.otrader
  | 2 => order.oside
  | 3 => order.oprice
  | 4 => order.oqty
  | _ => 0

def orderWord (st : Store Unit) (ptr : UInt64) (word : Nat) : UInt64 :=
  st.mem.read64
    (UInt32.ofNat ((ptr.toNat + (word + 1) * 8) % 4294967296))

def OrdersAt (st : Store Unit) (ptr : UInt64) (os : List OrderL) : Prop :=
  (st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) =
      UInt64.ofNat os.length ∧
    ptr.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536) ∧
  ∀ j : Nat, j < os.length →
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 5 + 1) * 8) % 4294967296)) =
          os[j]!.oid ∧
      (ptr.toNat + (j * 5 + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) ∧
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 5 + 2) * 8) % 4294967296)) =
          os[j]!.otrader ∧
      (ptr.toNat + (j * 5 + 2) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) ∧
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 5 + 3) * 8) % 4294967296)) =
          os[j]!.oside ∧
      (ptr.toNat + (j * 5 + 3) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) ∧
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 5 + 4) * 8) % 4294967296)) =
          os[j]!.oprice ∧
      (ptr.toNat + (j * 5 + 4) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) ∧
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 5 + 5) * 8) % 4294967296)) =
          os[j]!.oqty ∧
      (ptr.toNat + (j * 5 + 5) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536)

theorem OrdersAt.orderWord_eq {st : Store Unit} {ptr : UInt64}
    {os : List OrderL} (hOrders : OrdersAt st ptr os) (j field : Nat)
    (hj : j < os.length) (hfield : field < 5) :
    orderWord st ptr (j * 5 + field) = os[j]!.word field := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOrders.2 j hj
  unfold orderWord
  rw [show j * 5 + field + 1 = j * 5 + (field + 1) by omega]
  interval_cases field
  · simpa [OrderL.word] using h1.1
  · simpa [OrderL.word] using h2.1
  · simpa [OrderL.word] using h3.1
  · simpa [OrderL.word] using h4.1
  · simpa [OrderL.word] using h5.1

theorem OrdersAt.ofFlatWords {st : Store Unit} {ptr : UInt64}
    {os : List OrderL}
    (hLength : st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) =
      UInt64.ofNat os.length)
    (hLengthBound : ptr.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536)
    (hWord : ∀ (j : Nat), j < os.length → ∀ field : Nat, field < 5 →
      orderWord st ptr (j * 5 + field) = os[j]!.word field)
    (hBound : ∀ (j : Nat), j < os.length → ∀ field : Nat, field < 5 →
      (ptr.toNat + (j * 5 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) :
    OrdersAt st ptr os := by
  refine ⟨⟨hLength, hLengthBound⟩, ?_⟩
  intro j hj
  have hRead (field : Nat) (hfield : field < 5) :
      st.mem.read64
          (UInt32.ofNat
            ((ptr.toNat + (j * 5 + (field + 1)) * 8) % 4294967296)) =
        os[j]!.word field := by
    have h := hWord j hj field hfield
    unfold orderWord at h
    rw [show j * 5 + field + 1 = j * 5 + (field + 1) by omega] at h
    exact h
  have hFieldBound (field : Nat) (hfield : field < 5) :
      (ptr.toNat + (j * 5 + (field + 1)) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
    have h := hBound j hj field hfield
    rw [show j * 5 + field + 1 = j * 5 + (field + 1) by omega] at h
    exact h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [OrderL.word] using hRead 0 (by omega)
  · simpa using hFieldBound 0 (by omega)
  · simpa [OrderL.word] using hRead 1 (by omega)
  · simpa using hFieldBound 1 (by omega)
  · simpa [OrderL.word] using hRead 2 (by omega)
  · simpa using hFieldBound 2 (by omega)
  · simpa [OrderL.word] using hRead 3 (by omega)
  · simpa using hFieldBound 3 (by omega)
  · simpa [OrderL.word] using hRead 4 (by omega)
  · simpa using hFieldBound 4 (by omega)

def fixedArrayBytes (n stride : Nat) : Nat :=
  8 + n * stride * 8

def fixedArrayBytesU (n stride : Nat) : UInt64 :=
  8 + UInt64.ofNat n * UInt64.ofNat stride * 8

def FreshFixedArrayAt (st : Store Unit) (ptr capacity stride : UInt64) : Prop :=
  st.mem.read64 ((ptr - 48).toUInt32) = 5501223100278326855 ∧
  st.mem.read64 ((ptr - 40).toUInt32) = 1 ∧
  st.mem.read64 ((ptr - 32).toUInt32) = capacity ∧
  st.mem.read64 ((ptr - 24).toUInt32) = 2 ∧
  st.mem.read64 ((ptr - 16).toUInt32) = stride ∧
  st.mem.read64 ((ptr - 8).toUInt32) = 0

theorem FreshFixedArrayAt.write64_data {st : Store Unit}
    {ptr capacity stride : UInt64} {ad : UInt32} {value : UInt64}
    (hFresh : FreshFixedArrayAt st ptr capacity stride)
    (hHeader : 48 ≤ ptr.toNat) (hData : ptr.toNat ≤ ad.toNat) :
    FreshFixedArrayAt { st with mem := st.mem.write64 ad value }
      ptr capacity stride := by
  have hAd32 : ad.toNat < 4294967296 := ad.toNat_lt_size
  have hPtr32 : ptr.toNat < 4294967296 := hData.trans_lt hAd32
  have hDisjoint (offset : UInt64) (hOffset : offset.toNat ≤ ptr.toNat)
      (hOffset8 : 8 ≤ offset.toNat) :
      ((ptr - offset).toUInt32).toNat + 8 ≤ ad.toNat := by
    rw [Project.Common.toUInt32_toNat,
      Project.Common.toNat_sub_le ptr offset hOffset,
      Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨h48, h40, h32, h24, h16, h8⟩ := hFresh
  unfold FreshFixedArrayAt
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 48 (by change 48 ≤ ptr.toNat; omega) (by decide)))]
    exact h48
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 40 (by change 40 ≤ ptr.toNat; omega) (by decide)))]
    exact h40
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 32 (by change 32 ≤ ptr.toNat; omega) (by decide)))]
    exact h32
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 24 (by change 24 ≤ ptr.toNat; omega) (by decide)))]
    exact h24
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 16 (by change 16 ≤ ptr.toNat; omega) (by decide)))]
    exact h16
  · rw [Project.Common.read64_write64_ne _ _ _ _
      (Or.inl (hDisjoint 8 (by change 8 ≤ ptr.toNat; omega) (by decide)))]
    exact h8

theorem OrdersAt.frame {st st' : Store Unit} {ptr g0 : UInt64}
    {os : List OrderL}
    (hInput32 : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hBelow : ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat)
    (hPages : st'.mem.pages = st.mem.pages)
    (hBytes : ∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a)
    (hInput : OrdersAt st ptr os) :
    OrdersAt st' ptr os := by
  obtain ⟨⟨hHead, hHeadBound⟩, hElems⟩ := hInput
  have hHeadRead : st'.mem.read64
      (UInt32.ofNat (ptr.toNat % 4294967296)) =
      st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) := by
    apply Project.Common.read64_congr
    intro i hi
    rw [Project.Common.toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (by omega)]
    exact hBytes _ (by omega)
  refine ⟨⟨hHeadRead.trans hHead, ?_⟩, ?_⟩
  · rwa [hPages]
  · intro j hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hElems j hj
    have hRead (field : Nat) (hfield : field ≤ 5) :
        st'.mem.read64
            (UInt32.ofNat
              ((ptr.toNat + (j * 5 + field) * 8) % 4294967296)) =
          st.mem.read64
            (UInt32.ofNat
              ((ptr.toNat + (j * 5 + field) * 8) % 4294967296)) := by
      apply Project.Common.read64_congr
      intro i hi
      rw [Project.Common.toUInt32_ofNat_mod_toNat,
        Nat.mod_eq_of_lt (by omega)]
      exact hBytes _ (by omega)
    refine ⟨?_, ?_⟩
    · refine ⟨(hRead 1 (by omega)).trans h1.1, ?_⟩
      rw [hPages]
      exact h1.2
    · refine ⟨?_, ?_⟩
      · refine ⟨(hRead 2 (by omega)).trans h2.1, ?_⟩
        rw [hPages]
        exact h2.2
      · refine ⟨?_, ?_⟩
        · refine ⟨(hRead 3 (by omega)).trans h3.1, ?_⟩
          rw [hPages]
          exact h3.2
        · refine ⟨?_, ?_⟩
          · refine ⟨(hRead 4 (by omega)).trans h4.1, ?_⟩
            rw [hPages]
            exact h4.2
          · refine ⟨(hRead 5 (by omega)).trans h5.1, ?_⟩
            rw [hPages]
            exact h5.2

end Project.Clob
