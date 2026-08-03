import Project.Artifact.Binary.Translate
import Project.AppendBang.Program
import Project.AssocList.Program
import Project.BoxFree.Program
import Project.ClobCancel.Program
import Project.ClobDepth.Program
import Project.ClobFindBest.Program
import Project.ClobLimit.Program
import Project.ClobMarket.Program
import Project.ClobMatchFuel.Program
import Project.ClobPostOnly.Program
import Project.ClobQuote.Program
import Project.FoldSum.Program
import Project.Gcd.Program
import Project.LebU32.Program
import Project.OrderBook.Program
import Project.PairFree.Program
import Project.PushSize.Program
import Project.PushTwice.Program
import Project.SharedPair.Program
import Project.Validate.Program

open Wasm.Binary

private def cases : List (String × Wasm.Module) :=
  [("append_bang", Project.AppendBang.«module»),
   ("assoc_list", Project.AssocList.«module»),
   ("box_free", Project.BoxFree.«module»),
   ("clob_cancel", Project.ClobCancel.«module»),
   ("clob_depth", Project.ClobDepth.«module»),
   ("clob_find_best", Project.ClobFindBest.«module»),
   ("clob_limit", Project.ClobLimit.«module»),
   ("clob_market", Project.ClobMarket.«module»),
   ("clob_match_fuel", Project.ClobMatchFuel.«module»),
   ("clob_post_only", Project.ClobPostOnly.«module»),
   ("clob_quote", Project.ClobQuote.«module»),
   ("fold_sum", Project.FoldSum.«module»),
   ("gcd", Project.Gcd.«module»),
   ("leb_u32", Project.LebU32.«module»),
   ("order_book", Project.OrderBook.«module»),
   ("pair_free", Project.PairFree.«module»),
   ("push_size", Project.PushSize.«module»),
   ("push_twice", Project.PushTwice.«module»),
   ("shared_pair", Project.SharedPair.«module»),
   ("validate", Project.Validate.«module»)]

private def compareCase (root : String) (entry : String × Wasm.Module) : IO Bool := do
  let path := root ++ "/" ++ entry.1 ++ "/program.wasm"
  let bytes ← IO.FS.readBinFile path
  match decode bytes with
  | .error error =>
      IO.eprintln s!"{path}:{error.offset}: decode: {repr error.kind}"
      pure false
  | .ok raw =>
      match validate raw with
      | .error error =>
          IO.eprintln s!"{path}: validation: {repr error}"
          pure false
      | .ok validated =>
          let translated := validated.toTalos
          let cached := entry.2
          let functionsEqual : Bool := reprStr translated.funcs == reprStr cached.funcs
          let typesEqual : Bool := decide (translated.types = cached.types)
          let exportsEqual : Bool := decide (translated.exports = cached.exports)
          let memoryEqual : Bool := reprStr translated.memory == reprStr cached.memory
          let globalsEqual : Bool := reprStr translated.globals == reprStr cached.globals
          let equal := functionsEqual && typesEqual && exportsEqual && memoryEqual && globalsEqual
          if equal then
            IO.println s!"matched {entry.1}"
          else
            IO.eprintln s!"{entry.1}: funcs={functionsEqual}, types={typesEqual}, exports={exportsEqual}, memory={memoryEqual}, globals={globalsEqual}"
          pure equal

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "proofs/talos/.generated"
  let results ← cases.mapM (compareCase root)
  pure (if results.all id then 0 else 1)
