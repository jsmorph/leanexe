import Project.Artifact.Binary.CodeParts

namespace Wasm.Binary
open Parser

theorem sectionLoop_eq_step
    {fuel lastRank rank : Nat} {rawId : UInt8} {id : SectionId}
    {start payload next finish : Cursor} {before parsed result : RawModule}
    (hremaining : start.remaining ≠ 0)
    (hid : readByte start = .ok (rawId, payload))
    (hinfo : sectionInfo rawId = .ok (id, rank))
    (habsent : id ∉ before.sections)
    (horder : lastRank < rank)
    (hparse : parseSection id before payload = .ok (parsed, next))
    (hnext : sectionLoop fuel rank { parsed with sections := parsed.sections ++ [id] } next =
      .ok (result, finish)) :
    sectionLoop (fuel + 1) lastRank before start = .ok (result, finish) := by
  rw [sectionLoop]
  simp [remainingBytes, Bind.bind, Except.bind, hremaining, sectionStep,
    hid, hinfo, habsent, Nat.not_le_of_lt horder, hparse, hnext]

theorem decode_eq_of_parts {bytes : ByteArray} {versionStart sectionsStart finish : Cursor}
    {result : RawModule}
    (hmagic : expectBytes [0, 97, 115, 109] (Cursor.start bytes) = .ok ((), versionStart))
    (hversion : expectBytes [1, 0, 0, 0] versionStart = .ok ((), sectionsStart))
    (hsections : sectionLoop sectionsStart.remaining 0 default sectionsStart = .ok (result, finish))
    (hfinish : finish.pos = finish.limit) :
    decode bytes = .ok result := by
  simp [decode, runAll, run, moduleParser, Bind.bind, Pure.pure, Except.bind, Except.pure,
    hmagic, hversion, remainingBytes, hsections, hfinish]

#print axioms sectionLoop_eq_step
#print axioms decode_eq_of_parts

end Wasm.Binary
