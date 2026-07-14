import Project.Common

/-!
# Shared CLOB model

The CLOB artifacts read one order as five consecutive `UInt64` words.  This
module states that source-independent layout once for quote, cancel, and the
remaining kernel proofs.
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

end Project.Clob
