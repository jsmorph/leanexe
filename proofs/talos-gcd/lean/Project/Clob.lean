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
