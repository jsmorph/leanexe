import Init.Data.ByteArray.Lemmas
import Init.Omega
import Project.Artifact.Binary.Cursor

namespace Wasm.Binary

namespace Cursor

def WellFormed (cursor : Cursor) : Prop :=
  cursor.pos ≤ cursor.limit ∧ cursor.limit ≤ cursor.bytes.size

def Consumed (start finish : Cursor) (bytes : List UInt8) : Prop :=
  finish.bytes = start.bytes ∧
  finish.limit = start.limit ∧
  start.pos ≤ finish.pos ∧
  finish.pos ≤ start.limit ∧
  bytes = (start.bytes.extract start.pos finish.pos).data.toList

theorem start_wellFormed (bytes : ByteArray) : (start bytes).WellFormed := by
  simp [start, WellFormed]

theorem consumed_refl (cursor : Cursor) (h : cursor.WellFormed) :
    Consumed cursor cursor [] := by
  refine ⟨rfl, rfl, Nat.le_refl _, h.1, ?_⟩
  simp

theorem Consumed.finish_wellFormed
    {start finish : Cursor} {bytes : List UInt8}
    (hstart : start.WellFormed) (h : Consumed start finish bytes) :
    finish.WellFormed := by
  rcases h with ⟨hbytes, hlimit, _, hpos, _⟩
  simp only [WellFormed]
  constructor
  · simpa [hlimit] using hpos
  · simpa [hbytes, hlimit] using hstart.2

theorem Consumed.length
    {start finish : Cursor} {bytes : List UInt8}
    (hstart : start.WellFormed) (h : Consumed start finish bytes) :
    bytes.length = finish.pos - start.pos := by
  rcases hstart with ⟨hstartLimit, hlimitSize⟩
  rcases h with ⟨_, _, hpos, hfinish, rfl⟩
  simp only [Array.length_toList, ByteArray.size_data, ByteArray.size_extract]
  omega

theorem Consumed.eq_of_nil
    {start finish : Cursor}
    (hstart : start.WellFormed) (h : Consumed start finish []) :
    finish = start := by
  rcases h with ⟨hbytes, hlimit, hpos, hfinish, hconsumed⟩
  have hlength := Consumed.length hstart
    ⟨hbytes, hlimit, hpos, hfinish, hconsumed⟩
  simp at hlength
  have hposition : finish.pos = start.pos := by omega
  cases start
  cases finish
  simp_all

theorem Consumed.trans
    {start middle finish : Cursor} {first second : List UInt8}
    (h₁ : Consumed start middle first)
    (h₂ : Consumed middle finish second) :
    Consumed start finish (first ++ second) := by
  rcases h₁ with ⟨hmbytes, hmlimit, hsm, hmlim, hfirst⟩
  rcases h₂ with ⟨hfbytes, hflimit, hmf, hflim, hsecond⟩
  refine ⟨hfbytes.trans hmbytes, hflimit.trans hmlimit, Nat.le_trans hsm hmf, ?_, ?_⟩
  · simpa [hmlimit] using hflim
  · rw [hfirst, hsecond]
    rw [hmbytes]
    rw [← ByteArray.toList_data_append]
    rw [← ByteArray.extract_eq_extract_append_extract middle.pos hsm hmf]

end Cursor

namespace Parser

def Sound (parser : Parser α) (relation : List UInt8 → α → Prop) : Prop :=
  ∀ start value finish,
    start.WellFormed →
    parser start = .ok (value, finish) →
    ∃ bytes, start.Consumed finish bytes ∧ relation bytes value

def Sequence
    (first : List UInt8 → α → Prop)
    (next : α → List UInt8 → β → Prop)
    (bytes : List UInt8) (result : β) : Prop :=
  ∃ firstBytes secondBytes intermediate,
    bytes = firstBytes ++ secondBytes ∧
    first firstBytes intermediate ∧
    next intermediate secondBytes result

theorem sound_pure (value : α) :
    Sound (pure value) (fun bytes result => bytes = [] ∧ result = value) := by
  intro start result finish hstart hrun
  change Except.ok (value, start) = Except.ok (result, finish) at hrun
  cases hrun
  exact ⟨[], Cursor.consumed_refl start hstart, rfl, rfl⟩

theorem sound_bind
    {parser : Parser α} {next : α → Parser β}
    {firstRelation : List UInt8 → α → Prop}
    {nextRelation : α → List UInt8 → β → Prop}
    (hparser : Sound parser firstRelation)
    (hnext : ∀ value, Sound (next value) (nextRelation value)) :
    Sound (parser >>= next) (Sequence firstRelation nextRelation) := by
  intro start result finish hstart hrun
  dsimp [Bind.bind, Monad.toBind, instMonad] at hrun
  cases hmiddle : parser start with
  | error error =>
      rw [hmiddle] at hrun
      contradiction
  | ok pair =>
    rcases pair with ⟨value, middle⟩
    rw [hmiddle] at hrun
    rcases hparser start value middle hstart hmiddle with
      ⟨firstBytes, hfirstCursor, hfirstRelation⟩
    have hmiddleWellFormed := hfirstCursor.finish_wellFormed hstart
    rcases hnext value middle result finish hmiddleWellFormed hrun with
      ⟨secondBytes, hsecondCursor, hsecondRelation⟩
    exact ⟨firstBytes ++ secondBytes, hfirstCursor.trans hsecondCursor,
      firstBytes, secondBytes, value, rfl, hfirstRelation, hsecondRelation⟩

theorem readByte_sound :
    Sound readByte (fun bytes value => bytes = [value]) := by
  intro start value finish hstart hrun
  rcases hstart with ⟨hposLimit, hlimitSize⟩
  by_cases hposLimitStrict : start.pos < start.limit
  · have hposSize : start.pos < start.bytes.data.size := by
      simpa using Nat.lt_of_lt_of_le hposLimitStrict hlimitSize
    unfold readByte at hrun
    rw [if_pos hposLimitStrict, Array.getElem?_eq_getElem hposSize] at hrun
    change Except.ok
      (start.bytes.data[start.pos], { start with pos := start.pos + 1 }) =
        Except.ok (value, finish) at hrun
    cases hrun
    refine ⟨[start.bytes.data[start.pos]], ?_, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · show start.pos ≤ start.pos + 1
      omega
    · show start.pos + 1 ≤ start.limit
      omega
    rw [ByteArray.extract_add_one (by omega)]
    simp [ByteArray.getElem_eq_getElem_data]
    rfl
  · unfold readByte at hrun
    rw [if_neg hposLimitStrict] at hrun
    contradiction

theorem peekByte_sound :
    Sound peekByte (fun bytes _ => bytes = []) := by
  intro start value finish hstart hrun
  rcases hstart with ⟨hposLimit, hlimitSize⟩
  by_cases hposLimitStrict : start.pos < start.limit
  · have hposSize : start.pos < start.bytes.data.size := by
      simpa using Nat.lt_of_lt_of_le hposLimitStrict hlimitSize
    unfold peekByte at hrun
    rw [if_pos hposLimitStrict, Array.getElem?_eq_getElem hposSize] at hrun
    change Except.ok (start.bytes.data[start.pos], start) =
      Except.ok (value, finish) at hrun
    cases hrun
    exact ⟨[], Cursor.consumed_refl start ⟨hposLimit, hlimitSize⟩, rfl⟩
  · unfold peekByte at hrun
    rw [if_neg hposLimitStrict] at hrun
    contradiction

theorem peekByte_readByte_eq
    {start middle finish : Cursor} {peeked read : UInt8}
    (hstart : start.WellFormed)
    (hpeek : peekByte start = .ok (peeked, middle))
    (hread : readByte middle = .ok (read, finish)) :
    middle = start ∧ read = peeked := by
  rcases peekByte_sound start peeked middle hstart hpeek with
    ⟨bytes, hconsumed, hbytes⟩
  rw [hbytes] at hconsumed
  have hmiddle := hconsumed.eq_of_nil hstart
  subst middle
  refine ⟨rfl, ?_⟩
  by_cases hposition : start.pos < start.limit
  · unfold peekByte at hpeek
    unfold readByte at hread
    rw [if_pos hposition] at hpeek hread
    cases hvalue : start.bytes.data[start.pos]? with
    | none =>
        rw [hvalue] at hpeek
        contradiction
    | some value =>
        rw [hvalue] at hpeek hread
        cases hpeek
        cases hread
        rfl
  · unfold peekByte at hpeek
    rw [if_neg hposition] at hpeek
    contradiction

theorem readBytes_sound (count : Nat) :
    Sound (readBytes count)
      (fun bytes values => bytes = values ∧ bytes.length = count) := by
  intro start values finish hstart hrun
  rcases hstart with ⟨hposLimit, hlimitSize⟩
  unfold readBytes at hrun
  split at hrun
  · rename_i hfits
    simp at hfits
    cases hrun
    let stop := start.pos + count
    let bytes := (start.bytes.extract start.pos stop).data.toList
    refine ⟨bytes, ?_, rfl, ?_⟩
    · refine ⟨rfl, rfl, ?_, ?_, rfl⟩
      · simp
      · simp [Cursor.remaining] at hfits ⊢
        omega
    · simp only [bytes, Array.length_toList, ByteArray.size_data,
        ByteArray.size_extract]
      simp [Cursor.remaining] at hfits
      omega
  · contradiction

theorem expectByte_sound (expected : UInt8) :
    Sound (expectByte expected) (fun bytes _ => bytes = [expected]) := by
  intro start value finish hstart hrun
  unfold expectByte at hrun
  dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsedOffset offsetPair hoffsetRun
    rcases offsetPair with ⟨offset, afterOffset⟩
    have hoffset : afterOffset = start := by
      unfold position at hoffsetRun
      cases hoffsetRun
      rfl
    subst afterOffset
    split at hrun
    · contradiction
    · rename_i parsedByte bytePair hbyteRun
      rcases bytePair with ⟨byte, afterByte⟩
      split at hrun
      · rename_i hequal
        cases hrun
        rcases readByte_sound start byte afterByte
            hstart hbyteRun with
          ⟨bytes, hconsumed, hbytes⟩
        simp at hequal
        rw [hbytes, hequal] at hconsumed
        exact ⟨[expected], hconsumed, rfl⟩
      · contradiction

theorem expectBytes_sound (expected : List UInt8) :
    Sound (expectBytes expected) (fun bytes _ => bytes = expected) := by
  induction expected with
  | nil =>
      intro start value finish hstart hrun
      unfold expectBytes at hrun
      change Except.ok ((), start) = Except.ok (value, finish) at hrun
      cases hrun
      exact ⟨[], Cursor.consumed_refl start hstart, rfl⟩
  | cons byte rest ih =>
      intro start value finish hstart hrun
      unfold expectBytes at hrun
      dsimp [Bind.bind, Monad.toBind, Parser.instMonad, Except.bind] at hrun
      split at hrun
      · contradiction
      · rename_i parsedHead headPair hheadRun
        rcases headPair with ⟨headValue, middle⟩
        rcases expectByte_sound byte start headValue middle hstart hheadRun with
          ⟨headBytes, hheadConsumed, hheadBytes⟩
        rcases ih middle value finish
            (hheadConsumed.finish_wellFormed hstart) hrun with
          ⟨tailBytes, htailConsumed, htailBytes⟩
        rw [hheadBytes] at hheadConsumed
        rw [htailBytes] at htailConsumed
        exact ⟨byte :: rest, hheadConsumed.trans htailConsumed, rfl⟩

theorem bounded_sound
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    (size : Nat) (hparser : Sound parser relation) :
    Sound (bounded size parser)
      (fun bytes value => relation bytes value ∧ bytes.length = size) := by
  intro start value finish hstart hrun
  rcases hstart with ⟨hposLimit, hlimitSize⟩
  unfold bounded at hrun
  split at hrun
  · rename_i hfits
    simp at hfits
    let stop := start.pos + size
    let inner : Cursor := { start with limit := stop }
    let outer : Cursor := { start with pos := stop }
    have hinnerWellFormed : inner.WellFormed := by
      constructor
      · simp [inner, stop]
      · simp [inner, stop]
        exact hfits.2
    dsimp only at hrun
    split at hrun
    · contradiction
    · rename_i innerFinish hinnerRun
      split at hrun
      · rename_i hfinishPos
        cases hrun
        rcases hparser inner value innerFinish hinnerWellFormed hinnerRun with
          ⟨bytes, hinnerConsumed, hrelation⟩
        rcases hinnerConsumed with
          ⟨hfinishBytes, hfinishLimit, hstartPos, hlimitPos, hbytes⟩
        refine ⟨bytes, ?_, hrelation, ?_⟩
        · refine ⟨rfl, rfl, ?_, ?_, ?_⟩
          · show start.pos ≤ start.pos + size
            omega
          · simp [Cursor.remaining] at hfits ⊢
            omega
          · rw [hbytes]
            change (start.bytes.extract start.pos innerFinish.pos).data.toList =
              (start.bytes.extract start.pos (start.pos + size)).data.toList
            rw [hfinishPos]
        · have hlength := Cursor.Consumed.length hinnerWellFormed
            ⟨hfinishBytes, hfinishLimit, hstartPos, hlimitPos, hbytes⟩
          change bytes.length = innerFinish.pos - start.pos at hlength
          rw [hfinishPos] at hlength
          omega
      · contradiction
  · contradiction

theorem runAll_sound
    {parser : Parser α} {relation : List UInt8 → α → Prop}
    (hparser : Sound parser relation)
    {input : ByteArray} {value : α}
    (hrun : runAll parser input = .ok value) :
    relation input.data.toList value := by
  unfold runAll run at hrun
  dsimp [Bind.bind, Monad.toBind, Except.bind] at hrun
  split at hrun
  · contradiction
  · rename_i parsed pair hparse
    rcases pair with ⟨parsedValue, cursor⟩
    split at hrun
    · rename_i hcomplete
      cases hrun
      rcases hparser (Cursor.start input) parsedValue cursor
          (Cursor.start_wellFormed input) hparse with
        ⟨bytes, hconsumed, hrelation⟩
      rcases hconsumed with
        ⟨hcursorBytes, hcursorLimit, hstartPos, hlimitPos, hbytes⟩
      have hbytesInput : bytes = input.data.toList := by
        rw [hbytes]
        simp [Cursor.start] at hcursorLimit hcomplete ⊢
        rw [hcomplete, hcursorLimit]
        have hsize : input.size = input.data.toList.length := by simp
        rw [hsize, List.take_length]
      rwa [hbytesInput] at hrelation
    · contradiction

end Parser

end Wasm.Binary
