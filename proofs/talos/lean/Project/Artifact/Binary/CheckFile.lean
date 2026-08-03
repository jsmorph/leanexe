import Project.Gcd.ArtifactBytes
import Project.AssocList.ArtifactBytes
import Project.OrderBook.ArtifactBytes
import Project.Validate.ArtifactBytes
import Project.AppendBang.ArtifactBytes
import Project.PushSize.ArtifactBytes
import Project.PushTwice.ArtifactBytes
import Project.SharedPair.ArtifactBytes
import Project.PairFree.ArtifactBytes
import Project.BoxFree.ArtifactBytes
import Project.FoldSum.ArtifactBytes
import Project.LebU32.ArtifactBytes
import Project.ClobQuote.ArtifactBytes
import Project.ClobCancel.ArtifactBytes
import Project.ClobFindBest.ArtifactBytes
import Project.ClobPostOnly.ArtifactBytes
import Project.ClobMatchFuel.ArtifactBytes
import Project.ClobLimit.ArtifactBytes
import Project.ClobMarket.ArtifactBytes
import Project.ClobDepth.ArtifactBytes

private def artifactBytes : String → Option ByteArray
  | "gcd" => some Project.Gcd.Artifact.artifactBytes
  | "assoc_list" => some Project.AssocList.Artifact.artifactBytes
  | "order_book" => some Project.OrderBook.Artifact.artifactBytes
  | "validate" => some Project.Validate.Artifact.artifactBytes
  | "append_bang" => some Project.AppendBang.Artifact.artifactBytes
  | "push_size" => some Project.PushSize.Artifact.artifactBytes
  | "push_twice" => some Project.PushTwice.Artifact.artifactBytes
  | "shared_pair" => some Project.SharedPair.Artifact.artifactBytes
  | "pair_free" => some Project.PairFree.Artifact.artifactBytes
  | "box_free" => some Project.BoxFree.Artifact.artifactBytes
  | "fold_sum" => some Project.FoldSum.Artifact.artifactBytes
  | "leb_u32" => some Project.LebU32.Artifact.artifactBytes
  | "clob_quote" => some Project.ClobQuote.Artifact.artifactBytes
  | "clob_cancel" => some Project.ClobCancel.Artifact.artifactBytes
  | "clob_find_best" => some Project.ClobFindBest.Artifact.artifactBytes
  | "clob_post_only" => some Project.ClobPostOnly.Artifact.artifactBytes
  | "clob_match_fuel" => some Project.ClobMatchFuel.Artifact.artifactBytes
  | "clob_limit" => some Project.ClobLimit.Artifact.artifactBytes
  | "clob_market" => some Project.ClobMarket.Artifact.artifactBytes
  | "clob_depth" => some Project.ClobDepth.Artifact.artifactBytes
  | _ => none

def main (args : List String) : IO UInt32 := do
  let rec check : List String → IO UInt32
  | [] => pure 0
  | caseName :: path :: rest => do
      let some expected := artifactBytes caseName
        | IO.eprintln s!"unregistered artifact case: {caseName}"
          return 2
      let found ← IO.FS.readBinFile path
      if found == expected then
        IO.println s!"embedded bytes matched {caseName}: {found.size} bytes"
        check rest
      else
        IO.eprintln s!"embedded bytes differ for {caseName}: {path}"
        pure 1
  | _ => do
      IO.eprintln "usage: CheckFile (<case> <program.wasm>)+"
      pure 2
  check args
