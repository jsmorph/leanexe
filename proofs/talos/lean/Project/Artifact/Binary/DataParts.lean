import Project.Artifact.Binary.Proof.Cursor
import Project.Artifact.Binary.Decode

namespace Wasm.Binary
open Parser

theorem readBytes_eq_of_consumed {start finish : Cursor} {values : List UInt8}
    (hwf : start.WellFormed) (h : start.Consumed finish values) :
    readBytes values.length start = .ok (values, finish) := by
  have hlen := h.length hwf
  rcases h with ⟨hbytes, hlimit, hpos, hfinish, hvalues⟩
  have hstop : start.pos + values.length = finish.pos := by omega
  have hfits : values.length ≤ start.remaining ∧
      start.pos + values.length ≤ start.bytes.size := by
    have hsize := hwf.2
    simp only [Cursor.remaining]
    omega
  simp only [readBytes, Bool.and_eq_true, decide_eq_true_eq, hfits, hstop]
  rw [← hvalues]
  congr 2
  cases start
  cases finish
  simp_all

theorem readBytes_eq_append {start middle finish : Cursor} {first second : List UInt8}
    {n k : Nat} (hwf : start.WellFormed)
    (hfirst : readBytes n start = .ok (first, middle))
    (hsecond : readBytes k middle = .ok (second, finish)) :
    readBytes (n + k) start = .ok (first ++ second, finish) := by
  rcases Parser.readBytes_sound n start first middle hwf hfirst with
    ⟨_, hc1, rfl, hn⟩
  rcases Parser.readBytes_sound k middle second finish (hc1.finish_wellFormed hwf) hsecond with
    ⟨_, hc2, rfl, hk⟩
  simpa only [List.length_append, hn, hk] using
    readBytes_eq_of_consumed hwf (hc1.trans hc2)

theorem dataSegment_eq_of_parts {start afterMode afterOffset payload finish : Cursor}
    {offset : ConstExpr} {count : UInt32} {bytes : List UInt8}
    (hmode : Leb.u32 start = .ok (0, afterMode))
    (hoffset : constExpr afterMode = .ok (offset, afterOffset))
    (hcount : Leb.u32 afterOffset = .ok (count, payload))
    (hbytes : readBytes count.toNat payload = .ok (bytes, finish)) :
    dataSegment start = .ok ({ offset, bytes }, finish) := by
  simp [dataSegment, byteVector, Bind.bind, Pure.pure, Except.bind,
    hmode, hoffset, hcount, hbytes]

theorem readBytes_eq_split {start middle finish : Cursor} {bytes : List UInt8}
    {offset n k : Nat} (hwf : start.WellFormed)
    (hfirst : readBytes n start = .ok ((bytes.drop offset).take n, middle))
    (hsecond : readBytes k middle = .ok (bytes.drop (offset + n), finish)) :
    readBytes (n + k) start = .ok (bytes.drop offset, finish) := by
  rw [← List.drop_drop] at hsecond
  simpa only [List.take_append_drop] using readBytes_eq_append hwf hfirst hsecond

theorem readBytes_eq_of_vectorLoop (count : Nat) {start finish : Cursor}
    {bytes : List UInt8} (hwf : start.WellFormed)
    (h : Internal.vectorLoop readByte count start = .ok (bytes, finish)) :
    readBytes count start = .ok (bytes, finish) := by
  induction count generalizing start finish bytes with
  | zero =>
    cases h
    simpa using readBytes_eq_of_consumed hwf (Cursor.consumed_refl start hwf)
  | succ n ih =>
    simp only [Internal.vectorLoop, Bind.bind, Except.bind, Pure.pure] at h
    cases hb : readByte start with
    | error e => simp [hb] at h
    | ok pair =>
      rcases pair with ⟨byte, middle⟩
      simp only [hb] at h
      cases hr : Internal.vectorLoop readByte n middle with
      | error e => simp [hr] at h
      | ok pair =>
        rcases pair with ⟨rest, stop⟩
        simp only [hr] at h
        cases h
        rcases Parser.readByte_sound start byte middle hwf hb with ⟨_, hc, rfl⟩
        have hfirst := readBytes_eq_of_consumed hwf hc
        have hrest := ih (hc.finish_wellFormed hwf) hr
        simpa only [List.length_singleton, List.singleton_append, Nat.add_comm] using
          readBytes_eq_append hwf hfirst hrest

#print axioms readBytes_eq_append
#print axioms dataSegment_eq_of_parts
#print axioms readBytes_eq_of_vectorLoop
end Wasm.Binary
