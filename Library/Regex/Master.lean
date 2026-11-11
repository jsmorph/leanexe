import Library.Regex.Bytes
import Verified.Master

namespace Library.Regex

/-- The export `matchWith`, called on a pattern array `pat`, a word count `pn` with
`3 * pn < 2 ^ 64`, an input array `msg`, and a byte count `n`, returns `Spec.answer` of the first
`pn` words of `pat` and the first `n` bytes of `msg`: 2 when the words do not decode as a regular
expression in postfix form, 3 when the expression has more than 63 sets of bytes, and otherwise 1
or 0 for whether the bytes are in the expression's language. -/
theorem matchWith_master :
    Verified.Master compiled.module compiled.tables "matchWith" compiled.matchWith.bound
      (fun x : Array UInt64 × UInt64 × Array UInt64 × UInt64 => 3 * x.2.1.toNat < 2 ^ 64)
      (fun x (y : UInt64) => y = Spec.answer ((List.range x.2.1.toNat).map fun j => x.1[j]!)
        ((List.range x.2.2.2.toNat).map (Library.Bytes.byteAt x.2.2.1))) :=
  .of_trapFree (.ofA compiled.matchWith.trapFree) nofun matchWith_export
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hpn => Proof.matchWith_eq x.1 x.2.2.1 x.2.1 x.2.2.2 hpn

#print axioms matchWith_master

end Library.Regex
