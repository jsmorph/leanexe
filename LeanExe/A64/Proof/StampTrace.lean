import LeanExe.A64.Stamp
import LeanExe.A64.Linux
import LeanExe.Linux.Trace
import LeanExe.Area

/-!
The events of a run of the stamp program, the vocabulary of its theorem.  `ReadLoop` describes the
reads of a loop that reads a descriptor into a buffer until a read returns 0, and `WriteLoop` the
writes of a loop that writes a buffer to a descriptor until no byte remains, each read or write at
the address and count that the ones before it leave.  `StampEvents` follows the stamp program's
calls in order: each stage names its event with the arguments that the program fixes, and either
ends the run with its status or continues.  Lemmas compute `readData` and `writeData` of the
events of other calls and of appended traces.  `StampOpened` and `StampInput` name the events of
the stages that succeed, and a lemma for each end of `StampEvents` builds it from the events of
the stages before that end.
-/

namespace LeanExe.A64

open LeanExe.Linux (readCall writeCall closeCall openatCall clockGettimeCall getrandomCall
  readData writeData)

/-- The reads `rs` of a loop that reads descriptor `d` into the `c` bytes from `a`: each a `read`
of `d` at the address and count that the reads before it leave; each read but the last returns a
count from 1 to below its own, and the last one's count and result satisfy `last`. -/
def ReadLoop (d : UInt64) (last : Nat → UInt64 → Prop) :
    UInt64 → Nat → List LeanExe.Linux.Event → Prop
  | _, _, [] => False
  | a, c, e :: rs => e.call = readCall ∧ e.args = [d, a, UInt64.ofNat c] ∧
      ((rs = [] ∧ last c e.ret) ∨
        (0 < e.ret.toNat ∧ e.ret.toNat < c ∧ ReadLoop d last (a + e.ret) (c - e.ret.toNat) rs))

/-- The writes `ws` of a loop that writes the `c` bytes from `a` to descriptor `fd` while bytes
remain: each a `write` of `fd` of a positive count at the address and count that the writes
before it leave.  When `fails` is false, each returns a count from 1 to its own and the last
leaves no byte; when it is true, each but the last does so, and the last returns 0 or more than
its count. -/
def WriteLoop (fd : UInt64) (fails : Bool) : UInt64 → Nat → List LeanExe.Linux.Event → Prop
  | _, c, [] => fails = false ∧ c = 0
  | a, c, e :: ws => 0 < c ∧ e.call = writeCall ∧ e.args = [fd, a, UInt64.ofNat c] ∧
      ((fails = true ∧ ws = [] ∧ (e.ret = 0 ∨ c < e.ret.toNat)) ∨
        (0 < e.ret.toNat ∧ e.ret.toNat ≤ c ∧ WriteLoop fd fails (a + e.ret) (c - e.ret.toNat) ws))

/-- The events `tr` of a run of the stamp program from `main` with SP at `sp`, the limit `inMax`
of the input file, and the paths `pin` and `pout`, that returned when `s` is `none` and reached the
exit word with status `x` when `s` is `some x`.  The address `B` is existential, with the block
of `inMax + 33` bytes from `B` below `main`'s frame of `stampFrame pin pout` bytes, where the
program places the allocator's block; the input path lies 32 bytes above the frame's base and the output path
`32 + 8 * (pathWords pin).length` bytes above it.  In order: `clock_gettime` of the realtime clock
into the 16 bytes at `B`, which ends the run with status 72 unless it returns 0; `getrandom` of 16
bytes at `B + 16` without flags (73 unless 16); `openat` of the input path, read-only and closed
on `exec` (67 unless the result `d` lies below 2^31); the reads of `d` from `B + 32` of
`inMax + 1` bytes, which end with a result above its count (68), with a result that fills the
block (64), or with a result of 0; `close` of `d` (69 unless 0); the function on the clock's 16
bytes, the random bytes, and the bytes read, whose statuses `Tr` gives; `openat` of the output
path, write-only, created, truncated, and closed on `exec`, with mode 0644 (70 unless the result
`e` lies below 2^31); the writes to `e` of the function's result `Out` of those bytes from an
existential address `R`, where the program places the result, which end with a result of 0 or above its count (74, after
writing a prefix of the result) or after the whole result; and `close` of `e` (71 unless 0), after
which the run returns. -/
def StampEvents (sp inMax : UInt64) (pin pout : List UInt8)
    (Out : List UInt8 → List UInt8) (Tr : List UInt8 → UInt64 → Prop) (s : Option UInt64)
    (tr : List LeanExe.Linux.Event) : Prop :=
  ∃ B ec, B.toNat + inMax.toNat + 33 ≤ sp.toNat - stampFrame pin pout ∧
    ec.call = clockGettimeCall ∧ ec.args = [0, B] ∧
    ((s = some 72 ∧ tr = [ec] ∧ ec.ret ≠ 0) ∨ ec.ret = 0 ∧
    ∃ er, er.call = getrandomCall ∧ er.args = [B + 16, 16, 0] ∧
    ((s = some 73 ∧ tr = [ec, er] ∧ er.ret ≠ 16) ∨ er.ret = 16 ∧
    ∃ eo, eo.call = openatCall ∧
      eo.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) + 32, stampInFlags, 0] ∧
      eo.inputs = [pin ++ [0]] ∧
    ((s = some 67 ∧ tr = [ec, er, eo] ∧ 2 ^ 31 ≤ eo.ret.toNat) ∨ eo.ret.toNat < 2 ^ 31 ∧
    ∃ rs, (s = some 68 ∧ tr = [ec, er, eo] ++ rs ∧
        ReadLoop eo.ret (fun c r => c < r.toNat) (B + 32) (inMax.toNat + 1) rs) ∨
      (s = some 64 ∧ tr = [ec, er, eo] ++ rs ∧
        ReadLoop eo.ret (fun c r => 0 < c ∧ r.toNat = c) (B + 32) (inMax.toNat + 1) rs ∧
        (readData eo.ret tr).length = inMax.toNat + 1) ∨
      (ReadLoop eo.ret (fun c r => 0 < c ∧ r = 0) (B + 32) (inMax.toNat + 1) rs ∧
        (readData eo.ret tr).length ≤ inMax.toNat ∧
    ∃ ecl, ecl.call = closeCall ∧ ecl.args = [eo.ret] ∧
    ((s = some 69 ∧ tr = [ec, er, eo] ++ rs ++ [ecl] ∧ ecl.ret ≠ 0) ∨ ecl.ret = 0 ∧
    ((∃ x, s = some x ∧ tr = [ec, er, eo] ++ rs ++ [ecl] ∧
        Tr (ec.output ++ er.output ++ readData eo.ret tr) x) ∨
    ∃ eo2, eo2.call = openatCall ∧
      eo2.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) +
        UInt64.ofNat (32 + 8 * (pathWords pin).length), stampOutFlags, 420] ∧
      eo2.inputs = [pout ++ [0]] ∧
    ((s = some 70 ∧ tr = [ec, er, eo] ++ rs ++ [ecl, eo2] ∧ 2 ^ 31 ≤ eo2.ret.toNat) ∨
      eo2.ret.toNat < 2 ^ 31 ∧
    ∃ R ws,
    ((s = some 74 ∧ tr = [ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ∧
        WriteLoop eo2.ret true R (Out (ec.output ++ er.output ++ readData eo.ret tr)).length ws ∧
        writeData eo2.ret tr <+: Out (ec.output ++ er.output ++ readData eo.ret tr)) ∨
      (WriteLoop eo2.ret false R (Out (ec.output ++ er.output ++ readData eo.ret tr)).length ws ∧
        writeData eo2.ret tr = Out (ec.output ++ er.output ++ readData eo.ret tr) ∧
    ∃ ecl2, ecl2.call = closeCall ∧ ecl2.args = [eo2.ret] ∧
      tr = [ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ++ [ecl2] ∧
      ((s = some 71 ∧ ecl2.ret ≠ 0) ∨ (s = none ∧ ecl2.ret = 0)))))))))))

/-! ## The bytes of traces -/

theorem readData_append (d : UInt64) (a b : List LeanExe.Linux.Event) :
    readData d (a ++ b) = readData d a ++ readData d b := List.flatMap_append

theorem writeData_append (d : UInt64) (a b : List LeanExe.Linux.Event) :
    writeData d (a ++ b) = writeData d a ++ writeData d b := List.flatMap_append

theorem readData_single (d : UInt64) (e : LeanExe.Linux.Event) :
    readData d [e] = e.readBytes d := by simp [readData]

theorem writeData_single (d : UInt64) (e : LeanExe.Linux.Event) :
    writeData d [e] = e.writeBytes d := by simp [writeData]

/-- An event of a call other than `read` returns no bytes of a read. -/
theorem readBytes_other {d : UInt64} {e : LeanExe.Linux.Event} (h : e.call ≠ readCall) :
    e.readBytes d = [] := by
  unfold LeanExe.Linux.Event.readBytes
  rw [ite_eq_right (fun h' => h h'.1)]

/-- An event of a call other than `write` takes no bytes of a write. -/
theorem writeBytes_other {d : UInt64} {e : LeanExe.Linux.Event} (h : e.call ≠ writeCall) :
    e.writeBytes d = [] := by
  unfold LeanExe.Linux.Event.writeBytes
  rw [ite_eq_right (fun h' => h h'.1)]

/-- The events of `sysEvents` after a call's event. -/
theorem sysEvents_snoc (tr : List Event) (e : LeanExe.Linux.Event) :
    sysEvents (tr ++ [.sys e]) = sysEvents tr ++ [e] := by
  simp [sysEvents]

theorem sysEvents_nil : sysEvents [] = [] := rfl

/-- The reads of a loop return no bytes of a write. -/
theorem writeData_readLoop {fd d : UInt64} {last : Nat → UInt64 → Prop} :
    ∀ {a : UInt64} {c : Nat} {rs : List LeanExe.Linux.Event}, ReadLoop d last a c rs →
      writeData fd rs = []
  | _, _, [], h => h.elim
  | a, c, e :: rs, h => by
    obtain ⟨hc, -, h'⟩ := h
    have he : e.writeBytes fd = [] := writeBytes_other (by rw [hc]; decide)
    rcases h' with ⟨rfl, -⟩ | ⟨-, -, h'⟩
    · simp [writeData, he]
    · rw [show e :: rs = [e] ++ rs from rfl, writeData_append, writeData_single, he,
        writeData_readLoop h']
      rfl

/-- The writes of a loop return no bytes of a read. -/
theorem readData_writeLoop {fd d : UInt64} {fails : Bool} :
    ∀ {a : UInt64} {c : Nat} {ws : List LeanExe.Linux.Event}, WriteLoop fd fails a c ws →
      readData d ws = []
  | _, _, [], _ => rfl
  | a, c, e :: ws, h => by
    obtain ⟨-, hc, -, h'⟩ := h
    have he : e.readBytes d = [] := readBytes_other (by rw [hc]; decide)
    rcases h' with ⟨-, rfl, -⟩ | ⟨-, -, h'⟩
    · simp [readData, he]
    · rw [show e :: ws = [e] ++ ws from rfl, readData_append, readData_single, he,
        readData_writeLoop h']
      rfl

/-! ## The stages of `StampEvents` -/

/-- The first three events of a run of the stamp program that opened its input file. -/
def StampOpened (sp inMax : UInt64) (pin pout : List UInt8)
    (B : UInt64) (ec er eo : LeanExe.Linux.Event) : Prop :=
  B.toNat + inMax.toNat + 33 ≤ sp.toNat - stampFrame pin pout ∧
  ec.call = clockGettimeCall ∧ ec.args = [0, B] ∧ ec.ret = 0 ∧
  er.call = getrandomCall ∧ er.args = [B + 16, 16, 0] ∧ er.ret = 16 ∧
  eo.call = openatCall ∧
  eo.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) + 32, stampInFlags, 0] ∧
  eo.inputs = [pin ++ [0]] ∧ eo.ret.toNat < 2 ^ 31

/-- The events of a run of the stamp program that read its input file to its end and closed it. -/
def StampInput (sp inMax : UInt64) (pin pout : List UInt8)
    (B : UInt64) (ec er eo : LeanExe.Linux.Event) (rs : List LeanExe.Linux.Event)
    (ecl : LeanExe.Linux.Event) : Prop :=
  StampOpened sp inMax pin pout B ec er eo ∧
  ReadLoop eo.ret (fun c r => 0 < c ∧ r = 0) (B + 32) (inMax.toNat + 1) rs ∧
  ecl.call = closeCall ∧ ecl.args = [eo.ret] ∧ ecl.ret = 0

theorem readData_cons_other {d : UInt64} {e : LeanExe.Linux.Event} (h : e.call ≠ readCall)
    (tr : List LeanExe.Linux.Event) : readData d (e :: tr) = readData d tr := by
  rw [show e :: tr = [e] ++ tr from rfl, readData_append, readData_single, readBytes_other h]
  rfl

theorem writeData_cons_other {d : UInt64} {e : LeanExe.Linux.Event} (h : e.call ≠ writeCall)
    (tr : List LeanExe.Linux.Event) : writeData d (e :: tr) = writeData d tr := by
  rw [show e :: tr = [e] ++ tr from rfl, writeData_append, writeData_single, writeBytes_other h]
  rfl

section Stages

variable {sp inMax : UInt64} {pin pout : List UInt8}
  {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop} {B : UInt64}
  {ec er eo ecl eo2 ecl2 : LeanExe.Linux.Event} {rs ws : List LeanExe.Linux.Event}

theorem StampEvents.clock (hB : B.toNat + inMax.toNat + 33 ≤ sp.toNat - stampFrame pin pout)
    (hc1 : ec.call = clockGettimeCall) (hc2 : ec.args = [0, B]) (h : ec.ret ≠ 0) :
    StampEvents sp inMax pin pout Out Tr (some 72) [ec] :=
  ⟨B, ec, hB, hc1, hc2, .inl ⟨rfl, rfl, h⟩⟩

theorem StampEvents.random (hB : B.toNat + inMax.toNat + 33 ≤ sp.toNat - stampFrame pin pout)
    (hc1 : ec.call = clockGettimeCall) (hc2 : ec.args = [0, B]) (hc0 : ec.ret = 0)
    (hr1 : er.call = getrandomCall) (hr2 : er.args = [B + 16, 16, 0]) (h : er.ret ≠ 16) :
    StampEvents sp inMax pin pout Out Tr (some 73) [ec, er] :=
  ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inl ⟨rfl, rfl, h⟩⟩⟩

theorem StampEvents.openIn (hB : B.toNat + inMax.toNat + 33 ≤ sp.toNat - stampFrame pin pout)
    (hc1 : ec.call = clockGettimeCall) (hc2 : ec.args = [0, B]) (hc0 : ec.ret = 0)
    (hr1 : er.call = getrandomCall) (hr2 : er.args = [B + 16, 16, 0]) (hr0 : er.ret = 16)
    (ho1 : eo.call = openatCall)
    (ho2 : eo.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) + 32, stampInFlags, 0])
    (ho3 : eo.inputs = [pin ++ [0]]) (h : 2 ^ 31 ≤ eo.ret.toNat) :
    StampEvents sp inMax pin pout Out Tr (some 67) [ec, er, eo] :=
  ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1, ho2, ho3,
    .inl ⟨rfl, rfl, h⟩⟩⟩⟩

theorem StampEvents.read68 (h : StampOpened sp inMax pin pout B ec er eo)
    (hr : ReadLoop eo.ret (fun c r => c < r.toNat) (B + 32) (inMax.toNat + 1) rs) :
    StampEvents sp inMax pin pout Out Tr (some 68) ([ec, er, eo] ++ rs) := by
  obtain ⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1, ho2, ho3, ho0⟩ := h
  exact ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1, ho2, ho3,
    .inr ⟨ho0, rs, .inl ⟨rfl, rfl, hr⟩⟩⟩⟩⟩

/-- The bytes that the reads of a trace returned: those of the read loop. -/
theorem readData_stamp (h : StampOpened sp inMax pin pout B ec er eo)
    (tr : List LeanExe.Linux.Event) :
    readData eo.ret ([ec, er, eo] ++ tr) = readData eo.ret tr := by
  obtain ⟨-, hc1, -, -, hr1, -, -, ho1, -, -, -⟩ := h
  simp only [List.cons_append, List.nil_append]
  rw [readData_cons_other (by rw [hc1]; decide), readData_cons_other (by rw [hr1]; decide),
    readData_cons_other (by rw [ho1]; decide)]

theorem StampEvents.read64 (h : StampOpened sp inMax pin pout B ec er eo)
    (hr : ReadLoop eo.ret (fun c r => 0 < c ∧ r.toNat = c) (B + 32) (inMax.toNat + 1) rs)
    (hl : (readData eo.ret rs).length = inMax.toNat + 1) :
    StampEvents sp inMax pin pout Out Tr (some 64) ([ec, er, eo] ++ rs) := by
  have hd := readData_stamp h rs
  obtain ⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1, ho2, ho3, ho0⟩ := h
  exact ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1, ho2, ho3,
    .inr ⟨ho0, rs, .inr (.inl ⟨rfl, rfl, hr, by rw [hd]; exact hl⟩)⟩⟩⟩⟩

theorem StampEvents.close69 (h : StampOpened sp inMax pin pout B ec er eo)
    (hr : ReadLoop eo.ret (fun c r => 0 < c ∧ r = 0) (B + 32) (inMax.toNat + 1) rs)
    (hl : (readData eo.ret rs).length ≤ inMax.toNat) (hl1 : ecl.call = closeCall)
    (hl2 : ecl.args = [eo.ret]) (hne : ecl.ret ≠ 0) :
    StampEvents sp inMax pin pout Out Tr (some 69) ([ec, er, eo] ++ rs ++ [ecl]) := by
  have hd : readData eo.ret ([ec, er, eo] ++ rs ++ [ecl]) = readData eo.ret rs := by
    rw [List.append_assoc, readData_stamp h, readData_append, readData_single,
      readBytes_other (by rw [hl1]; decide), List.append_nil]
  obtain ⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1, ho2, ho3, ho0⟩ := h
  refine ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1, ho2, ho3,
    .inr ⟨ho0, rs, .inr (.inr ⟨hr, ?_, ecl, hl1, hl2, .inl ⟨rfl, rfl, hne⟩⟩)⟩⟩⟩⟩
  rw [hd]
  exact hl

/-- The bytes that the reads of a trace that continues past the input's `close` returned: those
of the read loop. -/
theorem readData_input (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (tr : List LeanExe.Linux.Event) (htr : readData eo.ret tr = []) :
    readData eo.ret ([ec, er, eo] ++ rs ++ [ecl] ++ tr) = readData eo.ret rs := by
  obtain ⟨ho, -, hl1, -, -⟩ := h
  rw [List.append_assoc, List.append_assoc, readData_stamp ho, readData_append,
    readData_append, readData_single, readBytes_other (by rw [hl1]; decide), htr]
  simp

theorem StampEvents.function {x : UInt64}
    (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (hl : (readData eo.ret rs).length ≤ inMax.toNat)
    (ht : Tr (ec.output ++ er.output ++ readData eo.ret rs) x) :
    StampEvents sp inMax pin pout Out Tr (some x) ([ec, er, eo] ++ rs ++ [ecl]) := by
  have hd := readData_input h [] rfl
  rw [List.append_nil] at hd
  obtain ⟨⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1, ho2, ho3, ho0⟩, hr, hl1, hl2, hl0⟩ := h
  refine ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1, ho2, ho3,
    .inr ⟨ho0, rs, .inr (.inr ⟨hr, by rw [hd]; exact hl, ecl, hl1, hl2,
      .inr ⟨hl0, .inl ⟨x, rfl, rfl, by rw [hd]; exact ht⟩⟩⟩)⟩⟩⟩⟩

theorem StampEvents.openOut (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (hl : (readData eo.ret rs).length ≤ inMax.toNat) (ho1 : eo2.call = openatCall)
    (ho2 : eo2.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) +
      UInt64.ofNat (32 + 8 * (pathWords pin).length), stampOutFlags, 420])
    (ho3 : eo2.inputs = [pout ++ [0]]) (hge : 2 ^ 31 ≤ eo2.ret.toNat) :
    StampEvents sp inMax pin pout Out Tr (some 70)
      ([ec, er, eo] ++ rs ++ [ecl, eo2]) := by
  have hd : readData eo.ret ([ec, er, eo] ++ rs ++ [ecl, eo2]) = readData eo.ret rs := by
    rw [← readData_input h [eo2] (by
      rw [readData_single, readBytes_other (by rw [ho1]; decide)])]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1', ho2', ho3', ho0⟩, hr, hl1, hl2, hl0⟩ := h
  refine ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1', ho2', ho3',
    .inr ⟨ho0, rs, .inr (.inr ⟨hr, ?_, ecl, hl1, hl2,
      .inr ⟨hl0, .inr ⟨eo2, ho1, ho2, ho3, .inl ⟨rfl, ?_, hge⟩⟩⟩⟩)⟩⟩⟩⟩
  · rw [hd]
    exact hl
  · simp

/-- The writes of the output and the bytes of a trace that continues past the output's `openat`:
the reads are those of the read loop and the writes those of the write loop. -/
theorem data_output (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (ho1 : eo2.call = openatCall) {fails : Bool} {R : UInt64} {c : Nat}
    (hw : WriteLoop eo2.ret fails R c ws) (tl : List LeanExe.Linux.Event)
    (htl : readData eo.ret tl = [] ∧ writeData eo2.ret tl = []) :
    readData eo.ret ([ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ++ tl) = readData eo.ret rs ∧
      writeData eo2.ret ([ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ++ tl) =
        writeData eo2.ret ws := by
  have hr := readData_input h (eo2 :: (ws ++ tl)) (by
    rw [readData_cons_other (by rw [ho1]; decide), readData_append, readData_writeLoop hw,
      htl.1]
    rfl)
  obtain ⟨⟨-, hc1, -, -, hr1, -, -, ho1', -, -, -⟩, hrl, hl1, -, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [writeData_cons_other (by rw [hc1]; decide), writeData_cons_other (by rw [hr1]; decide),
      writeData_cons_other (by rw [ho1']; decide), writeData_append, writeData_readLoop hrl,
      writeData_cons_other (by rw [hl1]; decide), writeData_cons_other (by rw [ho1]; decide),
      writeData_append, htl.2]
    simp

theorem StampEvents.write74 (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (hl : (readData eo.ret rs).length ≤ inMax.toNat) (ho1 : eo2.call = openatCall)
    (ho2 : eo2.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) +
      UInt64.ofNat (32 + 8 * (pathWords pin).length), stampOutFlags, 420])
    (ho3 : eo2.inputs = [pout ++ [0]]) (ho0 : eo2.ret.toNat < 2 ^ 31) {R : UInt64}
    (hw : WriteLoop eo2.ret true R (Out (ec.output ++ er.output ++ readData eo.ret rs)).length ws)
    (hpre : writeData eo2.ret ws <+: Out (ec.output ++ er.output ++ readData eo.ret rs)) :
    StampEvents sp inMax pin pout Out Tr (some 74)
      ([ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws) := by
  obtain ⟨hd, hwd⟩ := data_output h ho1 hw [] ⟨rfl, rfl⟩
  rw [List.append_nil] at hd hwd
  have hd' := readData_input h [] rfl
  rw [List.append_nil] at hd'
  obtain ⟨⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1', ho2', ho3', ho0'⟩, hr, hl1, hl2, hl0⟩ := h
  refine ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1', ho2', ho3',
    .inr ⟨ho0', rs, .inr (.inr ⟨hr, ?_, ecl, hl1, hl2,
      .inr ⟨hl0, .inr ⟨eo2, ho1, ho2, ho3, .inr ⟨ho0, R, ws,
        .inl ⟨rfl, by simp, ?_, ?_⟩⟩⟩⟩⟩)⟩⟩⟩⟩
  · rw [hd]; exact hl
  · rw [hd]; exact hw
  · rw [hd, hwd]; exact hpre

theorem StampEvents.close71 {s : Option UInt64}
    (h : StampInput sp inMax pin pout B ec er eo rs ecl)
    (hl : (readData eo.ret rs).length ≤ inMax.toNat) (ho1 : eo2.call = openatCall)
    (ho2 : eo2.args = [atFdcwd, sp - UInt64.ofNat (stampFrame pin pout) +
      UInt64.ofNat (32 + 8 * (pathWords pin).length), stampOutFlags, 420])
    (ho3 : eo2.inputs = [pout ++ [0]]) (ho0 : eo2.ret.toNat < 2 ^ 31) {R : UInt64}
    (hw : WriteLoop eo2.ret false R (Out (ec.output ++ er.output ++ readData eo.ret rs)).length ws)
    (hout : writeData eo2.ret ws = Out (ec.output ++ er.output ++ readData eo.ret rs))
    (hc1' : ecl2.call = closeCall) (hc2' : ecl2.args = [eo2.ret])
    (hend : (s = some 71 ∧ ecl2.ret ≠ 0) ∨ (s = none ∧ ecl2.ret = 0)) :
    StampEvents sp inMax pin pout Out Tr s
      ([ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ++ [ecl2]) := by
  obtain ⟨hd, hwd⟩ := data_output h ho1 hw [ecl2] ⟨by
    rw [readData_single, readBytes_other (by rw [hc1']; decide)], by
    rw [writeData_single, writeBytes_other (by rw [hc1']; decide)]⟩
  have hd' := readData_input h [] rfl
  rw [List.append_nil] at hd'
  obtain ⟨⟨hB, hc1, hc2, hc0, hr1, hr2, hr0, ho1', ho2', ho3', ho0'⟩, hr, hl1, hl2, hl0⟩ := h
  refine ⟨B, ec, hB, hc1, hc2, .inr ⟨hc0, er, hr1, hr2, .inr ⟨hr0, eo, ho1', ho2', ho3',
    .inr ⟨ho0', rs, .inr (.inr ⟨hr, ?_, ecl, hl1, hl2,
      .inr ⟨hl0, .inr ⟨eo2, ho1, ho2, ho3, .inr ⟨ho0, R, ws,
        .inr ⟨?_, ?_, ecl2, hc1', hc2', rfl, hend⟩⟩⟩⟩⟩)⟩⟩⟩⟩
  · rw [hd]; exact hl
  · rw [hd]; exact hw
  · rw [hd, hwd]; exact hout

end Stages

end LeanExe.A64
