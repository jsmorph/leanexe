import Project.ClobLimit.HeapAppendFacts

namespace Project.ClobLimit.HeapAppendCopy
open Wasm Project.Common Project.Clob Project.ProofKit
  Project.ClobMatchFuel.Allocation
open Project.ProofKit.FixedArrayCopy Project.ClobLimit.HeapAppendFacts

private theorem cellRead_eq (st : Store Unit) (ptr : UInt64) (cell cells : Nat)
    (hFit : ptr.toNat + 8 * (cells + 1) ≤ 4294967296) (hCell : cell < cells) :
    cellRead st ptr cell = orderWord st ptr cell := by
  unfold cellRead orderWord
  congr 1
  apply UInt32.toNat.inj
  rw [cellAddress_toNat hFit hCell, toUInt32_ofNat_mod_toNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The common prefix-copy loop supplies the order-specific append facts. -/
theorem spec
    (sourceLocal targetLocal prefixLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (source target capacity : UInt64) (os : List OrderL)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 source))
    (hTargetLocal : frame.get targetLocal = some (.i64 target))
    (hPrefixLocal : frame.get prefixLocal = some (.i64 (UInt64.ofNat (os.length * 5))))
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget48 : 48 ≤ target.toNat)
    (hTarget32 : target.toNat + ((os.length + 1) * 5 + 1) * 8 < 4294967296)
    (hSourceFit : source.toNat + (os.length * 5 + 1) * 8 ≤ initial.mem.pages * 65536)
    (hTargetFit : target.toNat + ((os.length + 1) * 5 + 1) * 8 ≤ initial.mem.pages * 65536)
    (hDisjoint : source.toNat + (os.length * 5 + 1) * 8 ≤ target.toNat ∨
      target.toNat + ((os.length + 1) * 5 + 1) * 8 ≤ source.toNat)
    (hFresh : FreshOrderArrayAt initial target capacity)
    (hLength : initial.mem.read64 target.toUInt32 = UInt64.ofNat (os.length + 1))
    (hOrders : OrdersAt initial source os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final, CopyState initial final target source capacity os (os.length * 5) →
      wp module_ rest Q final (counterFrame frame counterLocal (os.length * 5) hCounter) env) :
    wp module_ (prefixProgram sourceLocal targetLocal prefixLocal counterLocal ++ rest)
      Q initial frame env := by
  apply prefixProgram_framed_spec sourceLocal targetLocal prefixLocal counterLocal
    module_ env initial frame source target (os.length * 5) ((os.length + 1) * 5)
    (os.length * 5) hCounter hCounterSource hCounterTarget hCounterPrefix hValues
    hSourceLocal hTargetLocal hPrefixLocal (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  intro final hPages hHeader _ hCopied hWrites
  apply hDone final
  refine {
    pages := hPages
    globals := by rw [hWrites.1]
    fresh := FreshFixedArrayAt.frame (base := target) (by omega) hTarget48
      (by omega) (fun a ha => hWrites.2.2 a (Or.inl (by omega))) hFresh
    length := hHeader.trans hLength
    sourceInitial := hOrders
    copied := ?_
    outside := ?_ }
  · intro address hOutside
    exact hWrites.2.2 address (by omega)
  · intro cell hCell
    rw [← cellRead_eq final target cell ((os.length + 1) * 5) (by omega) (by omega),
      ← cellRead_eq initial source cell (os.length * 5) (by omega) hCell]
    exact hCopied cell hCell

#print axioms spec
end Project.ClobLimit.HeapAppendCopy
