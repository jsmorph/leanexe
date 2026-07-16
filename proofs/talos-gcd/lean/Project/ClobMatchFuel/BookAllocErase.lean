import Project.ClobMatchFuel.BookAlloc
import Project.ClobMatchFuel.AllocatorFrame
import Project.ClobMatchFuel.BookEraseSuffix

/-!
# Full-fill book allocation and erasure

This module first composes the two generated copy loops that erase a matched
order.  The allocator composition then supplies either a reused free node or a
new heap object to that common copy theorem.
-/

namespace Project.ClobMatchFuel.BookAllocErase

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def bookCopiesProg : Wasm.Program :=
  BookErasePrefix.erasePrefixProg ++ BookEraseSuffix.eraseSuffixProg

set_option Elab.async false in
theorem bookCopiesProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity
      newLength : UInt64)
    (os : List OrderL) (i targetWords prefixWords suffixWords : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat prefixWords)))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat suffixWords)))
    (hLengthLocal : base.locals[62]? = some (.i64 newLength))
    (hPrefixU : (UInt64.ofNat prefixWords).toNat = prefixWords)
    (hSuffixU : (UInt64.ofNat suffixWords).toNat = suffixWords)
    (hPrefix64 : prefixWords < UInt64.size)
    (hSuffix64 : suffixWords < UInt64.size)
    (hi : i < os.length)
    (hPrefixWords : prefixWords = i * 5)
    (hSuffixWords : suffixWords = (os.length - 1 - i) * 5)
    (hTargetWords : targetWords = (os.length - 1) * 5)
    (hNewLength : newLength = UInt64.ofNat (os.length - 1))
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (targetWords + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat + (targetWords + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint (flatWordsRegion target targetWords)
      (flatWordsRegion source (os.length * 5)))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hFresh : FreshOrderArrayAt st0 target arrayCapacity)
    (hOrders : OrdersAt st0 source os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st2,
      BookEraseSuffix.eraseSuffixInv st0 base need previous current capacity
          next target source g2 arrayCapacity newLength os targetWords
          prefixWords suffixWords st2
          (BookErasePrefix.eraseCopyFrame base need previous current capacity
            next target suffixWords) →
        OrdersAt st2 target (os.eraseIdx i) →
        wp «module» rest Q st2
          (BookEraseSuffix.eraseResultFrame base need previous current capacity
            next target suffixWords) env) :
    wp «module» (bookCopiesProg ++ rest) Q st0
      (BookAllocSearch.bookAllocSearchFrame base need previous current capacity
        next target) env := by
  unfold bookCopiesProg
  rw [List.append_assoc]
  apply BookErasePrefix.erasePrefixProg_spec env st0 base need previous current
    capacity next target source g2 arrayCapacity newLength os targetWords
    prefixWords hParams hLocals hValues hSourceLocal hPrefixLocal hLengthLocal
    hPrefixU hPrefix64 (by rw [hPrefixWords, hTargetWords]; omega)
    (by rw [hPrefixWords]; omega) hTarget48 hSource32 hTarget32 hTargetFit
    hsep hg2 hFresh hOrders Q (BookEraseSuffix.eraseSuffixProg ++ rest)
  intro st1 hPrefixInv hPrefix
  obtain ⟨_, _, _, hPages, hGlobals, hFresh1, hLength, hOrders1,
    hOutside, _⟩ := hPrefixInv
  apply BookEraseSuffix.eraseSuffixProg_spec env st0 st1 base need previous
    current capacity next target source g2 arrayCapacity newLength os i
    targetWords prefixWords suffixWords hParams hLocals hSourceLocal
    hPrefixLocal hSuffixLocal hPrefixU hSuffixU hSuffix64 hi hPrefixWords
    hSuffixWords hTargetWords hNewLength hTarget48 hSource32 hTarget32
    hTargetFit hsep hPages hGlobals hFresh1 hLength hOrders hOrders1
    hOutside hPrefix Q rest
  intro st2 hSuffixInv hTargetOrders
  exact hDone st2 hSuffixInv hTargetOrders

end Project.ClobMatchFuel.BookAllocErase
