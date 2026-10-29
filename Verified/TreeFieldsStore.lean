import Verified.TreeFieldsCode
import Verified.TreeFieldsMemory
import Verified.LocalFrame
import Verified.WordCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

/-- The locals of the positions `srcs`, of the types `tys`, hold the values whose words are
`words`, and each value's word is the word it was made from. -/
def SourcesHold (s : Locals) (h : Nat) : List Nat → List ValueType → List UInt64 → Prop
  | [], _, [] => True
  | src :: srcs, tys, word :: words =>
    s.get (slotIndex h src (tys.headD .i64)) = some (typedValue (tys.headD .i64) word) ∧
      Value.word (typedValue (tys.headD .i64) word) = word ∧ SourcesHold s h srcs tys.tail words
  | _, _, _ => False

theorem SourcesHold.length {s : Locals} {h : Nat} :
    ∀ {srcs : List Nat} {tys : List ValueType} {words : List UInt64},
      SourcesHold s h srcs tys words → words.length = srcs.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, hold => congrArg (· + 1) (SourcesHold.length hold.2.2)

end Verified
