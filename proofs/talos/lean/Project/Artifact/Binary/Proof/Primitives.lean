import Project.Artifact.Binary.Primitives
import Project.Artifact.Binary.Proof.Leb

namespace Wasm.Binary.Proof

open Parser

def ByteVectorEncoding (bytes : List UInt8) (values : List UInt8) : Prop :=
  ∃ lengthBytes,
    Grammar.U32 lengthBytes values.length ∧
    bytes = lengthBytes ++ values

theorem vectorLoop_sound
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    (hparser : Sound parser relation) (count : Nat) :
    Sound (Internal.vectorLoop parser count)
      (fun bytes values =>
        Grammar.Items relation bytes values ∧ values.length = count) := by
  induction count with
  | zero =>
      intro start values finish hstart hrun
      unfold Internal.vectorLoop at hrun
      change Except.ok ([], start) = Except.ok (values, finish) at hrun
      cases hrun
      exact ⟨[], Cursor.consumed_refl start hstart, Grammar.Items.nil, rfl⟩
  | succ count ih =>
      intro start values finish hstart hrun
      unfold Internal.vectorLoop at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsedHead headPair hheadRun
        rcases headPair with ⟨head, middle⟩
        split at hrun
        · contradiction
        · rename_i parsedTail tailPair htailRun
          rcases tailPair with ⟨tail, tailFinish⟩
          cases hrun
          rcases hparser start head middle hstart hheadRun with
            ⟨headBytes, hheadConsumed, hheadRelation⟩
          rcases ih middle tail tailFinish
              (hheadConsumed.finish_wellFormed hstart) htailRun with
            ⟨tailBytes, htailConsumed, htailRelation, htailLength⟩
          exact ⟨headBytes ++ tailBytes, hheadConsumed.trans htailConsumed,
            Grammar.Items.cons headBytes tailBytes head tail hheadRelation
              htailRelation, by simp [htailLength]⟩

theorem vector_sound
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    (hparser : Sound parser relation) :
    Sound (vector parser) (Grammar.Vector relation) := by
  intro start values finish hstart hrun
  unfold vector at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedLength lengthPair hlengthRun
    rcases lengthPair with ⟨length, middle⟩
    dsimp only at hrun
    split at hrun
    · rename_i lengthFits
      rcases Leb.Proof.u32_sound start length middle hstart hlengthRun with
        ⟨lengthBytes, hlengthConsumed, hlengthEncoding⟩
      rcases vectorLoop_sound hparser length.toNat middle values finish
          (hlengthConsumed.finish_wellFormed hstart) hrun with
        ⟨bodyBytes, hbodyConsumed, hbodyEncoding, hvalueLength⟩
      refine ⟨lengthBytes ++ bodyBytes,
        hlengthConsumed.trans hbodyConsumed, ?_⟩
      apply Grammar.Vector.intro lengthBytes bodyBytes values
      · rw [hvalueLength]
        exact hlengthEncoding
      · exact hbodyEncoding
    · contradiction

theorem byteVector_sound :
    Sound byteVector ByteVectorEncoding := by
  intro start values finish hstart hrun
  unfold byteVector at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedLength lengthPair hlengthRun
    rcases lengthPair with ⟨length, middle⟩
    rcases Leb.Proof.u32_sound start length middle hstart hlengthRun with
      ⟨lengthBytes, hlengthConsumed, hlengthEncoding⟩
    rcases readBytes_sound length.toNat middle values finish
        (hlengthConsumed.finish_wellFormed hstart) hrun with
      ⟨bodyBytes, hbodyConsumed, hbodyValues, hbodyLength⟩
    rw [hbodyValues] at hbodyConsumed hbodyLength
    refine ⟨lengthBytes ++ values, hlengthConsumed.trans hbodyConsumed,
      lengthBytes, ?_, rfl⟩
    rw [hbodyLength]
    exact hlengthEncoding

theorem name_sound :
    Sound name Grammar.Name := by
  intro start value finish hstart hrun
  unfold name at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedBytes bytesPair hbytesRun
    rcases bytesPair with ⟨bytes, middle⟩
    cases htext : String.fromUTF8? bytes.toByteArray with
    | none =>
      rw [htext] at hrun
      contradiction
    | some text =>
      rw [htext] at hrun
      cases hrun
      rcases byteVector_sound start bytes middle hstart hbytesRun with
        ⟨allBytes, hconsumed, lengthBytes, hlengthEncoding, hallBytes⟩
      rw [hallBytes] at hconsumed
      exact ⟨lengthBytes ++ bytes, hconsumed,
        Grammar.Name.intro lengthBytes bytes text hlengthEncoding htext⟩

theorem sized_sound
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    (hparser : Sound parser relation) :
    Sound (sized parser) (Grammar.Sized relation) := by
  intro start value finish hstart hrun
  unfold sized at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedSize sizePair hsizeRun
    rcases sizePair with ⟨size, middle⟩
    rcases Leb.Proof.u32_sound start size middle hstart hsizeRun with
      ⟨sizeBytes, hsizeConsumed, hsizeEncoding⟩
    rcases bounded_sound size.toNat hparser middle value finish
        (hsizeConsumed.finish_wellFormed hstart) hrun with
      ⟨bodyBytes, hbodyConsumed, hbodyEncoding, hbodyLength⟩
    refine ⟨sizeBytes ++ bodyBytes, hsizeConsumed.trans hbodyConsumed,
      Grammar.Sized.intro sizeBytes bodyBytes value ?_ hbodyEncoding⟩
    rw [hbodyLength]
    exact hsizeEncoding

end Wasm.Binary.Proof
