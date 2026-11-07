import LeanExe.Requests.Windows

/-!
Records of words over a UART, through the program with requests.  `frameTick` is a step that
reads records of `kin` words, runs a record machine on each, and writes the machine's record of
`kout` words, each word as 8 bytes, most significant first.  It reads the status register before
each access to the receive or transmit register, reads a byte only when the receiver holds one,
and writes one only when the transmitter has room.  `frame_prefix` states, for every sequence `σ`
of the values that the reads return and every trace type with its `Bus`, that the bytes that the
first `n` windows write to the transmit register begin the bytes of the machine's outputs for the
records that the bytes read from the receive register in those windows encode.  A step that the
verified compiler compiles holds the records in structures with a `Flat` instance, and a theorem
that relates it to `frameTick` carries `frame_prefix` to its program through `reqTrace_map`.
-/

namespace LeanExe.Requests

open LeanExe.Native (readReq writeReq)

/-! ## The framing -/

/-- The registers of a UART among the registers that requests name: the indices of the receive register, from which bytes
are read, the transmit register, to which bytes are written, and the status register; the status
bit `rxFull`, which is set while the receiver holds a byte; and the status bits `txMask`, which
equal `txRoom` while the transmitter can take a byte.  The CMSDK UART has one data register for
both directions and a bit that is set while the transmitter is full, and an STM32 USART has two
data registers and a bit that is set while the transmitter is empty. -/
structure Uart where
  rx : UInt64
  tx : UInt64
  status : UInt64
  rxFull : UInt64
  txMask : UInt64
  txRoom : UInt64

/-- The state of the framing.  The phase names the last request: 0 a read of the status before a
byte is read, 1 a read of the receive register, 2 a read of the status before a byte is written,
and 3 a write of the transmit register.  `nbyte` and `nword` count the bytes of the current word and
the words of the current record that are done, `acc` is the word being received, `inb` the input
record of `kin` words, into which each word shifts at the end, `outb` the output record of `kout`
words, whose first word shifts out a byte at a time, and `m` the record machine's state. -/
structure Framing (M : Type) where
  phase : UInt64
  nbyte : UInt64
  nword : UInt64
  acc : UInt64
  inb : List UInt64
  outb : List UInt64
  m : M

variable {M α : Type}

/-- One window of the framing, from the state `f` and the value `v` that the last request read,
for records of `kin` words in and `kout` words out and the record machine `mach`. -/
def frameTick (u : Uart) (kin kout : Nat) (mach : M → List UInt64 → M × List UInt64)
    (f : Framing M) (v : UInt64) : Framing M × UInt64 :=
  if f.phase == 0 then
    if v &&& u.rxFull != 0 then ({ f with phase := 1 }, readReq u.rx)
    else (f, readReq u.status)
  else if f.phase == 1 then
    if f.nbyte < 7 then
      ({ f with phase := 0, nbyte := f.nbyte + 1, acc := f.acc * 256 + (v &&& 255) },
        readReq u.status)
    else if f.nword < UInt64.ofNat (kin - 1) then
      ({ f with
          phase := 0, nbyte := 0, nword := f.nword + 1, acc := 0,
          inb := f.inb.tail ++ [f.acc * 256 + (v &&& 255)] }, readReq u.status)
    else
      ({ phase := 2, nbyte := 0, nword := 0, acc := 0,
          inb := f.inb.tail ++ [f.acc * 256 + (v &&& 255)],
          outb := (mach f.m (f.inb.tail ++ [f.acc * 256 + (v &&& 255)])).2,
          m := (mach f.m (f.inb.tail ++ [f.acc * 256 + (v &&& 255)])).1 }, readReq u.status)
  else if f.phase == 2 then
    if v &&& u.txMask == u.txRoom then
      ({ f with phase := 3 }, writeReq u.tx (f.outb.headD 0 >>> 56))
    else (f, readReq u.status)
  else if f.nbyte < 7 then
    ({ f with phase := 2, nbyte := f.nbyte + 1, outb := (f.outb.headD 0 <<< 8) :: f.outb.tail },
      readReq u.status)
  else if f.nword < UInt64.ofNat (kout - 1) then
    ({ f with phase := 2, nbyte := 0, nword := f.nword + 1, outb := f.outb.tail ++ [0] },
      readReq u.status)
  else
    ({ f with phase := 0, nbyte := 0, nword := 0, outb := f.outb.tail ++ [0] }, readReq u.status)

/-- The initial state of the framing, with the machine's state `m0`. -/
def frame0 (kin kout : Nat) (m0 : M) : Framing M :=
  ⟨0, 0, 0, 0, List.replicate kin 0, List.replicate kout 0, m0⟩

/-! ## Records and their bytes -/

/-- The state of the decoder of bytes into records: the complete records, the words of the
current record, the current word, and the number of its bytes. -/
structure Decoded where
  recs : List (List UInt64)
  words : List UInt64
  acc : UInt64
  nbyte : Nat

/-- The decoder's state after the byte `b`: words of 8 bytes, most significant first, and
records of `kin` words. -/
def decodeByte (kin : Nat) (d : Decoded) (b : UInt64) : Decoded :=
  if d.nbyte < 7 then { d with acc := d.acc * 256 + b, nbyte := d.nbyte + 1 }
  else if d.words.length + 1 < kin then
    { d with words := d.words ++ [d.acc * 256 + b], acc := 0, nbyte := 0 }
  else ⟨d.recs ++ [d.words ++ [d.acc * 256 + b]], [], 0, 0⟩

/-- The decoder's state after the bytes `bs`. -/
def decode (kin : Nat) (bs : List UInt64) : Decoded := bs.foldl (decodeByte kin) ⟨[], [], 0, 0⟩

/-- The `k` bytes of the word `w` from its most significant on. -/
def wordBytes (w : UInt64) : Nat → List UInt64
  | 0 => []
  | k + 1 => (w >>> 56) :: wordBytes (w <<< 8) k

/-- The bytes of a record: 8 for each word. -/
def recordBytes (ws : List UInt64) : List UInt64 := ws.flatMap fun w => wordBytes w 8

/-- The record machine's state and outputs after the records `recs`, from the state `m0`. -/
def machRun (mach : M → List UInt64 → M × List UInt64) (m0 : M) (recs : List (List UInt64)) :
    M × List (List UInt64) :=
  recs.foldl (fun p r => ((mach p.1 r).1, p.2 ++ [(mach p.1 r).2])) (m0, [])

/-- The bytes of the record machine's outputs for the records `recs`. -/
def outBytes (mach : M → List UInt64 → M × List UInt64) (m0 : M) (recs : List (List UInt64)) :
    List UInt64 :=
  (machRun mach m0 recs).2.flatMap recordBytes

/-- The byte that an access reads from the receive register: the low byte of the value read. -/
def dataInByte (B : Bus α) (u : Uart) (e : α) : Option UInt64 :=
  (B.readOf u.rx e).map fun v => UInt64.ofNat v.toNat &&& 255

/-- The value that an access writes to the transmit register. -/
def dataOutByte (B : Bus α) (u : Uart) (e : α) : Option UInt64 :=
  (B.writeOf u.tx e).map fun v => UInt64.ofNat v.toNat

/-- The bytes that the trace reads from the receive register. -/
def dataIn (B : Bus α) (u : Uart) (tr : List α) : List UInt64 := tr.filterMap (dataInByte B u)

/-- The values that the trace writes to the transmit register. -/
def dataOut (B : Bus α) (u : Uart) (tr : List α) : List UInt64 := tr.filterMap (dataOutByte B u)

theorem decode_append (kin : Nat) (bs : List UInt64) (b : UInt64) :
    decode kin (bs ++ [b]) = decodeByte kin (decode kin bs) b := by
  simp [decode, List.foldl_append]

theorem machRun_append (mach : M → List UInt64 → M × List UInt64) (m0 : M)
    (recs : List (List UInt64)) (r : List UInt64) :
    machRun mach m0 (recs ++ [r]) = ((mach (machRun mach m0 recs).1 r).1,
      (machRun mach m0 recs).2 ++ [(mach (machRun mach m0 recs).1 r).2]) := by
  simp [machRun, List.foldl_append]

theorem outBytes_append (mach : M → List UInt64 → M × List UInt64) (m0 : M)
    (recs : List (List UInt64)) (r : List UInt64) :
    outBytes mach m0 (recs ++ [r]) =
      outBytes mach m0 recs ++ recordBytes (mach (machRun mach m0 recs).1 r).2 := by
  simp [outBytes, machRun_append, List.flatMap_append]

/-! ## The invariant of the framing -/

/-- While a record is received, the framing's state `f` holds the decoder's state `d`, and the
bytes written, `out`, are those of the outputs for the records of `d`. -/
structure Recv (kin kout : Nat) (mach : M → List UInt64 → M × List UInt64) (m0 : M)
    (f : Framing M) (d : Decoded) (out : List UInt64) : Prop where
  m : f.m = (machRun mach m0 d.recs).1
  out : out = outBytes mach m0 d.recs
  nbyte : f.nbyte.toNat = d.nbyte
  nbyte_le : d.nbyte ≤ 7
  acc : f.acc = d.acc
  nword : f.nword.toNat = d.words.length
  nword_lt : d.words.length < kin
  inb_len : f.inb.length = kin
  inb : f.inb.drop (kin - d.words.length) = d.words
  outb_len : f.outb.length = kout

/-- While an output record is sent, the decoder's state `d` lies at the end of a record, and the
bytes written, `out`, followed by the bytes `rest` that remain, are those of the outputs for the
records of `d`. -/
structure Send (kin kout : Nat) (mach : M → List UInt64 → M × List UInt64) (m0 : M)
    (f : Framing M) (d : Decoded) (out rest : List UInt64) : Prop where
  m : f.m = (machRun mach m0 d.recs).1
  out : out ++ rest = outBytes mach m0 d.recs
  words : d.words = []
  dacc : d.acc = 0
  dnbyte : d.nbyte = 0
  acc : f.acc = 0
  nbyte_le : f.nbyte.toNat ≤ 7
  nword_lt : f.nword.toNat < kout
  inb_len : f.inb.length = kin
  outb_len : f.outb.length = kout

/-- The bytes that remain of the output record in phase 2. -/
def rest2 (kout : Nat) (f : Framing M) : List UInt64 :=
  wordBytes (f.outb.headD 0) (8 - f.nbyte.toNat) ++
    recordBytes (f.outb.tail.take (kout - 1 - f.nword.toNat))

/-- The bytes that remain of the output record in phase 3, after the byte just written. -/
def rest3 (kout : Nat) (f : Framing M) : List UInt64 :=
  wordBytes (f.outb.headD 0 <<< 8) (7 - f.nbyte.toNat) ++
    recordBytes (f.outb.tail.take (kout - 1 - f.nword.toNat))

/-- The invariant of the framing's state `f`, the last value `v`, and the bytes read and written
so far. -/
def FrameInv (kin kout : Nat) (mach : M → List UInt64 → M × List UInt64) (m0 : M)
    (f : Framing M) (v : UInt64) (inp out : List UInt64) : Prop :=
  (f.phase = 0 ∧ Recv kin kout mach m0 f (decode kin inp) out) ∨
  (f.phase = 1 ∧ ∃ inp0, inp = inp0 ++ [v &&& 255] ∧
    Recv kin kout mach m0 f (decode kin inp0) out) ∨
  (f.phase = 2 ∧ Send kin kout mach m0 f (decode kin inp) out (rest2 kout f)) ∨
  (f.phase = 3 ∧ Send kin kout mach m0 f (decode kin inp) out (rest3 kout f))

/-! ## The prefix theorem -/

section

variable (B : Bus α) (u : Uart) (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
  (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status)

include hrx hs hrs in
theorem dataIn_status (x : UInt32) : dataIn B u [B.read u.status x] = [] := by
  simp [dataIn, dataInByte, B.readOf_read_ne u.rx u.status x hrx hs hrs]

theorem dataOut_read (r : UInt64) (x : UInt32) : dataOut B u [B.read r x] = [] := by
  simp [dataOut, dataOutByte, B.writeOf_read]

theorem dataIn_data (x : UInt32) :
    dataIn B u [B.read u.rx x] = [UInt64.ofNat x.toNat &&& 255] := by
  simp [dataIn, dataInByte, B.readOf_read]

theorem dataIn_write (r : UInt64) (x : UInt32) : dataIn B u [B.write r x] = [] := by
  simp [dataIn, dataInByte, B.readOf_write]

include htx in
theorem dataOut_write {b : UInt64} (hb : b.toNat < 256) :
    dataOut B u [B.write u.tx (UInt32.ofNat ((writeReq u.tx b).toNat % 2 ^ 32))] = [b] := by
  have hv : UInt64.ofNat (UInt32.ofNat ((writeReq u.tx b).toNat % 2 ^ 32)).toNat = b := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat', UInt32.toNat_ofNat', writeReq_toNat b htx]
    omega
  have he : dataOutByte B u (B.write u.tx (UInt32.ofNat ((writeReq u.tx b).toNat % 2 ^ 32))) =
      some b := by
    unfold dataOutByte
    rw [B.writeOf_write]
    exact congrArg some hv
  simp only [dataOut, List.filterMap_cons, he, List.filterMap_nil]

theorem top_byte (w : UInt64) : (w >>> 56).toNat < 256 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := UInt64.toNat_lt w
  show w.toNat / 2 ^ 56 < 256
  omega

end

theorem recordBytes_cons (w : UInt64) (ws : List UInt64) :
    recordBytes (w :: ws) = wordBytes w 8 ++ recordBytes ws := by
  simp [recordBytes]

theorem decodeByte_nbyte_le (kin : Nat) {d : Decoded} (b : UInt64) (h : d.nbyte ≤ 7) :
    (decodeByte kin d b).nbyte ≤ 7 := by
  unfold decodeByte
  split
  · simp only
    omega
  · split <;> simp

theorem decode_nbyte_le (kin : Nat) (bs : List UInt64) : (decode kin bs).nbyte ≤ 7 := by
  suffices h : ∀ d : Decoded, d.nbyte ≤ 7 → (bs.foldl (decodeByte kin) d).nbyte ≤ 7 from
    h ⟨[], [], 0, 0⟩ (Nat.zero_le _)
  induction bs with
  | nil => exact fun _ h => h
  | cons b bs ih => exact fun d h => ih _ (decodeByte_nbyte_le kin b h)

theorem recv_phase {kin kout : Nat} {mach : M → List UInt64 → M × List UInt64} {m0 : M}
    {f : Framing M} {d : Decoded} {out : List UInt64} (h : Recv kin kout mach m0 f d out)
    (p : UInt64) : Recv kin kout mach m0 { f with phase := p } d out :=
  ⟨h.m, h.out, h.nbyte, h.nbyte_le, h.acc, h.nword, h.nword_lt, h.inb_len, h.inb, h.outb_len⟩

theorem send_phase {kin kout : Nat} {mach : M → List UInt64 → M × List UInt64} {m0 : M}
    {f : Framing M} {d : Decoded} {out rest : List UInt64}
    (h : Send kin kout mach m0 f d out rest) (p : UInt64) (rest' : List UInt64)
    (hr : out ++ rest' = out ++ rest) : Send kin kout mach m0 { f with phase := p } d out rest' :=
  ⟨h.m, hr.trans h.out, h.words, h.dacc, h.dnbyte, h.acc, h.nbyte_le, h.nword_lt, h.inb_len,
    h.outb_len⟩

theorem toNat_succ_of_lt {x : UInt64} {n : Nat} (h : x.toNat < n) (hn : n ≤ 4294967296) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

theorem drop_tail_append {β : Type} (l : List β) (x : β) {j : Nat} (hj : 1 ≤ j)
    (hl : j ≤ l.length) : (l.tail ++ [x]).drop (j - 1) = l.drop j ++ [x] := by
  rw [List.drop_append_of_le_length (by rw [List.length_tail]; omega), List.drop_tail,
    Nat.sub_add_cancel hj]

theorem rest_full {o : List UInt64} {kout : Nat} (h : o.length = kout) (hk : 0 < kout) :
    wordBytes (o.headD 0) 8 ++ recordBytes (o.tail.take (kout - 1)) = recordBytes o := by
  cases o with
  | nil => simp at h; omega
  | cons w t =>
      simp only [List.length_cons] at h
      rw [List.headD_cons, List.tail_cons, List.take_of_length_le (by omega), recordBytes_cons]

theorem rest_shift (t : List UInt64) (j : Nat) (hj : j + 1 ≤ t.length) :
    wordBytes ((t ++ [0]).headD 0) 8 ++ recordBytes ((t ++ [0]).tail.take j) =
      recordBytes (t.take (j + 1)) := by
  cases t with
  | nil => simp at hj
  | cons w t =>
      simp only [List.length_cons] at hj
      rw [List.cons_append, List.headD_cons, List.tail_cons,
        List.take_append_of_le_length (by omega), List.take_succ_cons, recordBytes_cons]

theorem decodeByte_recs (kin : Nat) (d : Decoded) (b : UInt64) :
    ∃ rs, (decodeByte kin d b).recs = d.recs ++ rs := by
  unfold decodeByte
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[], by simp⟩
    · exact ⟨_, rfl⟩

theorem outBytes_prefix (mach : M → List UInt64 → M × List UInt64) (m0 : M) :
    ∀ (rs recs : List (List UInt64)), outBytes mach m0 recs <+: outBytes mach m0 (recs ++ rs)
  | [], recs => by simp
  | r :: rs, recs => by
      have := outBytes_prefix mach m0 rs (recs ++ [r])
      rw [List.append_assoc, List.singleton_append] at this
      exact (by rw [outBytes_append]; exact List.prefix_append _ _ : outBytes mach m0 recs <+:
        outBytes mach m0 (recs ++ [r])).trans this

theorem dataIn_append (B : Bus α) (u : Uart) (a b : List α) :
    dataIn B u (a ++ b) = dataIn B u a ++ dataIn B u b :=
  List.filterMap_append

theorem dataOut_append (B : Bus α) (u : Uart) (a b : List α) :
    dataOut B u (a ++ b) = dataOut B u a ++ dataOut B u b :=
  List.filterMap_append

section

variable {B : Bus α} {u : Uart} {kin kout : Nat} {mach : M → List UInt64 → M × List UInt64}
  {m0 : M}

/-- The invariant after the window from the state `f`, the last value `v`, and `k` reads. -/
def FrameNext (B : Bus α) (u : Uart) (kin kout : Nat) (mach : M → List UInt64 → M × List UInt64)
    (m0 : M) (σ : Nat → UInt32) (f : Framing M) (v : UInt64) (k : Nat) (inp out : List UInt64) :
    Prop :=
  FrameInv kin kout mach m0 (reqNext (frameTick u kin kout mach) σ ⟨f, v, k⟩).state
    (reqNext (frameTick u kin kout mach) σ ⟨f, v, k⟩).last
    (inp ++ dataIn B u [reqEvent B (frameTick u kin kout mach) σ ⟨f, v, k⟩])
    (out ++ dataOut B u [reqEvent B (frameTick u kin kout mach) σ ⟨f, v, k⟩])

variable (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
  (hrs : u.rx ≠ u.status) (hkin : 0 < kin) (hkin' : kin < 4294967296) (hkout : 0 < kout)
  (hkout' : kout < 4294967296) (hmach : ∀ m r, r.length = kin → (mach m r).2.length = kout)
  (σ : Nat → UInt32) (f : Framing M) (v : UInt64) (k : Nat) {inp out : List UInt64}

include hrx hs hrs in
/-- After a window whose request reads the status, the invariant needs only the new state. -/
theorem frameNext_status {g : Framing M}
    (htick : frameTick u kin kout mach f v = (g, readReq u.status))
    (h : ∀ x, FrameInv kin kout mach m0 g x inp out) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_readReq hs)
  unfold FrameNext
  rw [h1, h2, h3, reqReg_readReq hs, dataIn_status B u hrx hs hrs, dataOut_read B u, List.append_nil,
    List.append_nil]
  exact h _

include hrx hs hrs in
theorem frameNext_phase0 (hp : f.phase = 0) (hr : Recv kin kout mach m0 f (decode kin inp) out) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  by_cases hx : (v &&& u.rxFull != 0) = true
  · have htick : frameTick u kin kout mach f v = ({ f with phase := 1 }, readReq u.rx) := by
      rw [frameTick, ite_eq_left (by rw [hp]; decide), ite_eq_left hx]
    obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_readReq hrx)
    unfold FrameNext
    rw [h1, h2, h3, reqReg_readReq hrx, dataIn_data B u, dataOut_read B u, List.append_nil]
    exact Or.inr (Or.inl ⟨rfl, inp, rfl, recv_phase hr 1⟩)
  · exact frameNext_status hrx hs hrs σ f v k
      (by rw [frameTick, ite_eq_left (by rw [hp]; decide), ite_eq_right hx])
      (fun _ => Or.inl ⟨hp, hr⟩)

include hrx hs hrs in
theorem frameNext_byte {inp0 : List UInt64} (hp : f.phase = 1) (hin : inp = inp0 ++ [v &&& 255])
    (hr : Recv kin kout mach m0 f (decode kin inp0) out) (hb : f.nbyte < 7) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : f.nbyte.toNat < 7 := UInt64.lt_iff_toNat_lt.mp hb
  have hd0 := hr.nbyte
  refine frameNext_status hrx hs hrs σ f v k (g := { f with
    phase := 0, nbyte := f.nbyte + 1, acc := f.acc * 256 + (v &&& 255) })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; decide),
      ite_eq_left hb])
    (fun _ => Or.inl ⟨rfl, ?_⟩)
  rw [hin, decode_append, decodeByte, ite_eq_left (by omega)]
  exact ⟨hr.m, hr.out, by
      rw [toNat_succ_of_lt h7 (by decide)]
      show f.nbyte.toNat + 1 = (decode kin inp0).nbyte + 1
      omega,
    by show (decode kin inp0).nbyte + 1 ≤ 7; omega, by rw [hr.acc], hr.nword, hr.nword_lt,
    hr.inb_len, hr.inb, hr.outb_len⟩

include hrx hs hrs hkin' in
theorem frameNext_word {inp0 : List UInt64} (hp : f.phase = 1) (hin : inp = inp0 ++ [v &&& 255])
    (hr : Recv kin kout mach m0 f (decode kin inp0) out) (hb : ¬f.nbyte < 7)
    (hw : f.nword < UInt64.ofNat (kin - 1)) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : ¬f.nbyte.toNat < 7 := fun h => hb (UInt64.lt_iff_toNat_lt.mpr h)
  have hkm : (UInt64.ofNat (kin - 1)).toNat = kin - 1 := by
    rw [UInt64.toNat_ofNat']
    omega
  have hw' : f.nword.toNat < kin - 1 := hkm ▸ UInt64.lt_iff_toNat_lt.mp hw
  have hd0 := hr.nbyte
  have hdl := hr.nbyte_le
  have hwn := hr.nword
  refine frameNext_status hrx hs hrs σ f v k (g := { f with
    phase := 0, nbyte := 0, nword := f.nword + 1, acc := 0,
    inb := f.inb.tail ++ [f.acc * 256 + (v &&& 255)] })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; decide),
      ite_eq_right hb,
      ite_eq_left hw]) (fun _ => Or.inl ⟨rfl, ?_⟩)
  rw [hin, decode_append, decodeByte, ite_eq_right (by omega), ite_eq_left (by omega)]
  refine ⟨hr.m, hr.out, rfl, by show 0 ≤ 7; omega, rfl, ?_, ?_, ?_, ?_, hr.outb_len⟩
  · show (f.nword + 1).toNat = ((decode kin inp0).words ++ [_]).length
    rw [toNat_succ_of_lt hw' (by omega), List.length_append, List.length_singleton]
    omega
  · show ((decode kin inp0).words ++ [_]).length < kin
    rw [List.length_append, List.length_singleton]
    omega
  · show (f.inb.tail ++ [_]).length = kin
    rw [List.length_append, List.length_tail, hr.inb_len, List.length_singleton]
    omega
  · show (f.inb.tail ++ [f.acc * 256 + (v &&& 255)]).drop
      (kin - ((decode kin inp0).words ++ [_]).length) = _
    rw [List.length_append, List.length_singleton, hr.acc,
      show kin - ((decode kin inp0).words.length + 1) =
        kin - (decode kin inp0).words.length - 1 by omega,
      drop_tail_append _ _ (by omega) (by rw [hr.inb_len]; omega), hr.inb]

include hrx hs hrs hkin' hkout hmach in
theorem frameNext_record {inp0 : List UInt64} (hp : f.phase = 1)
    (hin : inp = inp0 ++ [v &&& 255]) (hr : Recv kin kout mach m0 f (decode kin inp0) out)
    (hb : ¬f.nbyte < 7) (hw : ¬f.nword < UInt64.ofNat (kin - 1)) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : ¬f.nbyte.toNat < 7 := fun h => hb (UInt64.lt_iff_toNat_lt.mpr h)
  have hkm : (UInt64.ofNat (kin - 1)).toNat = kin - 1 := by
    rw [UInt64.toNat_ofNat']
    omega
  have hw' : ¬f.nword.toNat < kin - 1 :=
    fun h => hw (UInt64.lt_iff_toNat_lt.mpr (by rw [hkm]; exact h))
  have hd0 := hr.nbyte
  have hdl := hr.nbyte_le
  have hwn := hr.nword
  have hwl := hr.nword_lt
  have htail : f.inb.tail = (decode kin inp0).words := by
    rw [← List.drop_one, ← hr.inb]
    congr 1
    omega
  have hlen : (f.inb.tail ++ [f.acc * 256 + (v &&& 255)]).length = kin := by
    rw [List.length_append, List.length_tail, hr.inb_len, List.length_singleton]
    omega
  have hrec : f.inb.tail ++ [f.acc * 256 + (v &&& 255)] =
      (decode kin inp0).words ++ [(decode kin inp0).acc * 256 + (v &&& 255)] := by
    rw [htail, hr.acc]
  refine frameNext_status hrx hs hrs σ f v k (g := {
    phase := 2, nbyte := 0, nword := 0, acc := 0,
    inb := f.inb.tail ++ [f.acc * 256 + (v &&& 255)],
    outb := (mach f.m (f.inb.tail ++ [f.acc * 256 + (v &&& 255)])).2,
    m := (mach f.m (f.inb.tail ++ [f.acc * 256 + (v &&& 255)])).1 })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_left (by rw [hp]; decide),
      ite_eq_right hb,
      ite_eq_right hw]) (fun _ => Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
  rw [hin, decode_append, decodeByte, ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, by show (0 : UInt64).toNat ≤ 7; decide, hkout, hlen,
    hmach _ _ hlen⟩
  · show (mach f.m _).1 = _
    rw [machRun_append, hr.m, hrec]
  · show out ++ rest2 kout _ = _
    rw [outBytes_append, ← hr.out, ← hr.m, ← hrec]
    congr 1
    exact rest_full (hmach _ _ hlen) hkout

include hrx htx hs hrs in
theorem frameNext_phase2 (hp : f.phase = 2)
    (hsd : Send kin kout mach m0 f (decode kin inp) out (rest2 kout f)) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  by_cases hx : (v &&& u.txMask == u.txRoom) = true
  · have htick : frameTick u kin kout mach f v =
        ({ f with phase := 3 }, writeReq u.tx (f.outb.headD 0 >>> 56)) := by
      rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
        ite_eq_left (by rw [hp]; decide), ite_eq_left hx]
    obtain ⟨h1, h2, h3⟩ :=
      next_write (B := B) (σ := σ) (r := ⟨f, v, k⟩) htick (reqWrite_writeReq _ htx)
    unfold FrameNext
    rw [h1, h2, h3, reqReg_writeReq _ htx, dataIn_write B u, dataOut_write B u htx (top_byte _),
      List.append_nil]
    refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
    have hrest : rest2 kout f = (f.outb.headD 0 >>> 56) :: rest3 kout f := by
      unfold rest2 rest3
      rw [show 8 - f.nbyte.toNat = 7 - f.nbyte.toNat + 1 by have := hsd.nbyte_le; omega]
      rfl
    refine ⟨hsd.m, ?_, hsd.words, hsd.dacc, hsd.dnbyte, hsd.acc, hsd.nbyte_le, hsd.nword_lt,
      hsd.inb_len, hsd.outb_len⟩
    show (out ++ [f.outb.headD 0 >>> 56]) ++ rest3 kout f = _
    rw [List.append_assoc, List.singleton_append, ← hrest]
    exact hsd.out
  · exact frameNext_status hrx hs hrs σ f v k
      (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
        ite_eq_left (by rw [hp]; decide), ite_eq_right hx])
      (fun _ => Or.inr (Or.inr (Or.inl ⟨hp, hsd⟩)))

include hrx hs hrs hkout in
theorem frameNext_sent (hp : f.phase = 3)
    (hsd : Send kin kout mach m0 f (decode kin inp) out (rest3 kout f)) (hb : f.nbyte < 7) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : f.nbyte.toNat < 7 := UInt64.lt_iff_toNat_lt.mp hb
  have hnb : (f.nbyte + 1).toNat = f.nbyte.toNat + 1 := toNat_succ_of_lt h7 (by decide)
  have htl : f.outb.tail.length = kout - 1 := by rw [List.length_tail, hsd.outb_len]
  refine frameNext_status hrx hs hrs σ f v k (g := { f with
    phase := 2, nbyte := f.nbyte + 1, outb := (f.outb.headD 0 <<< 8) :: f.outb.tail })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
      ite_eq_right (by rw [hp]; decide), ite_eq_left hb])
    (fun _ => Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
  have hrest : rest2 kout { f with
      phase := 2, nbyte := f.nbyte + 1, outb := (f.outb.headD 0 <<< 8) :: f.outb.tail } =
      rest3 kout f := by
    unfold rest2 rest3
    simp only [List.headD_cons, List.tail_cons, hnb]
    rw [show 8 - (f.nbyte.toNat + 1) = 7 - f.nbyte.toNat by omega]
  refine ⟨hsd.m, by rw [hrest]; exact hsd.out, hsd.words, hsd.dacc, hsd.dnbyte, hsd.acc,
    by show (f.nbyte + 1).toNat ≤ 7; omega, hsd.nword_lt, hsd.inb_len, ?_⟩
  show ((f.outb.headD 0 <<< 8) :: f.outb.tail).length = kout
  rw [List.length_cons, htl]
  omega

include hrx hs hrs hkout' in
theorem frameNext_sentWord (hp : f.phase = 3)
    (hsd : Send kin kout mach m0 f (decode kin inp) out (rest3 kout f)) (hb : ¬f.nbyte < 7)
    (hw : f.nword < UInt64.ofNat (kout - 1)) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : ¬f.nbyte.toNat < 7 := fun h => hb (UInt64.lt_iff_toNat_lt.mpr h)
  have hle := hsd.nbyte_le
  have h7' : f.nbyte.toNat = 7 := by omega
  have hkm : (UInt64.ofNat (kout - 1)).toNat = kout - 1 := by
    rw [UInt64.toNat_ofNat']
    omega
  have hw' : f.nword.toNat < kout - 1 := hkm ▸ UInt64.lt_iff_toNat_lt.mp hw
  have hnw : (f.nword + 1).toNat = f.nword.toNat + 1 := toNat_succ_of_lt hw' (by omega)
  have htl : f.outb.tail.length = kout - 1 := by rw [List.length_tail, hsd.outb_len]
  have hout := hsd.out
  unfold rest3 at hout
  rw [h7', show 7 - 7 = 0 from rfl, wordBytes, List.nil_append] at hout
  refine frameNext_status hrx hs hrs σ f v k (g := { f with
    phase := 2, nbyte := 0, nword := f.nword + 1, outb := f.outb.tail ++ [0] })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
      ite_eq_right (by rw [hp]; decide), ite_eq_right hb, ite_eq_left hw])
    (fun _ => Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))
  have hrest : rest2 kout { f with
      phase := 2, nbyte := 0, nword := f.nword + 1, outb := f.outb.tail ++ [0] } =
      recordBytes (f.outb.tail.take (kout - 1 - f.nword.toNat)) := by
    have h := rest_shift f.outb.tail (kout - 1 - (f.nword.toNat + 1)) (by rw [htl]; omega)
    rw [show kout - 1 - (f.nword.toNat + 1) + 1 = kout - 1 - f.nword.toNat by omega] at h
    rw [← h, ← hnw]
    rfl
  refine ⟨hsd.m, by rw [hrest]; exact hout, hsd.words, hsd.dacc, hsd.dnbyte, hsd.acc,
    by show (0 : UInt64).toNat ≤ 7; decide, by show (f.nword + 1).toNat < kout; omega,
    hsd.inb_len, ?_⟩
  show (f.outb.tail ++ [0]).length = kout
  rw [List.length_append, htl, List.length_singleton]
  omega

include hrx hs hrs hkin hkout' in
theorem frameNext_sentRecord (hp : f.phase = 3)
    (hsd : Send kin kout mach m0 f (decode kin inp) out (rest3 kout f)) (hb : ¬f.nbyte < 7)
    (hw : ¬f.nword < UInt64.ofNat (kout - 1)) :
    FrameNext B u kin kout mach m0 σ f v k inp out := by
  have h7 : ¬f.nbyte.toNat < 7 := fun h => hb (UInt64.lt_iff_toNat_lt.mpr h)
  have hle := hsd.nbyte_le
  have h7' : f.nbyte.toNat = 7 := by omega
  have hkm : (UInt64.ofNat (kout - 1)).toNat = kout - 1 := by
    rw [UInt64.toNat_ofNat']
    omega
  have hw' : ¬f.nword.toNat < kout - 1 :=
    fun h => hw (UInt64.lt_iff_toNat_lt.mpr (by rw [hkm]; exact h))
  have hnwl := hsd.nword_lt
  have htl : f.outb.tail.length = kout - 1 := by rw [List.length_tail, hsd.outb_len]
  have hout := hsd.out
  unfold rest3 at hout
  rw [h7', show 7 - 7 = 0 from rfl, wordBytes, List.nil_append,
    show kout - 1 - f.nword.toNat = 0 by omega, List.take_zero, recordBytes, List.flatMap_nil,
    List.append_nil] at hout
  refine frameNext_status hrx hs hrs σ f v k (g := { f with
    phase := 0, nbyte := 0, nword := 0, outb := f.outb.tail ++ [0] })
    (by rw [frameTick, ite_eq_right (by rw [hp]; decide), ite_eq_right (by rw [hp]; decide),
      ite_eq_right (by rw [hp]; decide), ite_eq_right hb, ite_eq_right hw])
    (fun _ => Or.inl ⟨rfl, ?_⟩)
  have hwd := hsd.words
  refine ⟨hsd.m, hout, by rw [hsd.dnbyte]; rfl, by rw [hsd.dnbyte]; omega,
    hsd.acc.trans hsd.dacc.symm, by rw [hwd]; rfl, by rw [hwd]; exact hkin, hsd.inb_len,
    by rw [hwd]; exact List.drop_eq_nil_of_le (by rw [hsd.inb_len, List.length_nil]; omega),
    ?_⟩
  show (f.outb.tail ++ [0]).length = kout
  rw [List.length_append, htl, List.length_singleton]
  omega

include hrx htx hs hrs hkin hkin' hkout hkout' hmach in
/-- One window keeps the invariant of the framing. -/
theorem frameInv_next (r : ReqState (Framing M))
    (h : FrameInv kin kout mach m0 r.state r.last inp out) :
    FrameInv kin kout mach m0 (reqNext (frameTick u kin kout mach) σ r).state
      (reqNext (frameTick u kin kout mach) σ r).last
      (inp ++ dataIn B u [reqEvent B (frameTick u kin kout mach) σ r])
      (out ++ dataOut B u [reqEvent B (frameTick u kin kout mach) σ r]) := by
  obtain ⟨f, v, k⟩ := r
  change FrameInv kin kout mach m0 f v inp out at h
  change FrameNext B u kin kout mach m0 σ f v k inp out
  rcases h with ⟨hp, hr⟩ | ⟨hp, inp0, hin, hr⟩ | ⟨hp, hsd⟩ | ⟨hp, hsd⟩
  · exact frameNext_phase0 hrx hs hrs σ f v k hp hr
  · by_cases hb : f.nbyte < 7
    · exact frameNext_byte hrx hs hrs σ f v k hp hin hr hb
    · by_cases hw : f.nword < UInt64.ofNat (kin - 1)
      · exact frameNext_word hrx hs hrs hkin' σ f v k hp hin hr hb hw
      · exact frameNext_record hrx hs hrs hkin' hkout hmach σ f v k hp hin hr hb hw
  · exact frameNext_phase2 hrx htx hs hrs σ f v k hp hsd
  · by_cases hb : f.nbyte < 7
    · exact frameNext_sent hrx hs hrs hkout σ f v k hp hsd hb
    · by_cases hw : f.nword < UInt64.ofNat (kout - 1)
      · exact frameNext_sentWord hrx hs hrs hkout' σ f v k hp hsd hb hw
      · exact frameNext_sentRecord hrx hs hrs hkin hkout' σ f v k hp hsd hb hw

end

section

variable {B : Bus α} {u : Uart} {kin kout : Nat} {mach : M → List UInt64 → M × List UInt64}
  {m0 : M}

/-- The invariant of the framing holds before every window. -/
theorem frameInv_run (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) (hkin : 0 < kin)
    (hkin' : kin < 4294967296) (hkout : 0 < kout) (hkout' : kout < 4294967296)
    (hmach : ∀ m r, r.length = kin → (mach m r).2.length = kout) (σ : Nat → UInt32) : ∀ n,
    FrameInv kin kout mach m0 (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ n).state
      (reqRun (frameTick u kin kout mach) (frame0 kin kout m0) σ n).last
      (dataIn B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ) n))
      (dataOut B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ) n))
  | 0 => Or.inl ⟨rfl, rfl, rfl, rfl, by show 0 ≤ 7; omega, rfl, rfl, hkin,
      List.length_replicate, List.drop_eq_nil_of_le (by simp [frame0, reqRun, windows, dataIn,
        decode]),
      List.length_replicate⟩
  | n + 1 => by
      rw [windows, dataIn_append, dataOut_append]
      exact frameInv_next hrx htx hs hrs hkin hkin' hkout hkout' hmach σ _
        (frameInv_run hrx htx hs hrs hkin hkin' hkout hkout' hmach σ n)

/-- The bytes that the first `n` windows of the framing write to the transmit register begin the
bytes of the record machine's outputs for the records that the bytes read from the receive
register in those windows encode, for every sequence `σ` of the values read. -/
theorem frame_prefix (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536)
    (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status) (hkin : 0 < kin)
    (hkin' : kin < 4294967296) (hkout : 0 < kout) (hkout' : kout < 4294967296)
    (hmach : ∀ m r, r.length = kin → (mach m r).2.length = kout) (σ : Nat → UInt32) (n : Nat) :
    dataOut B u (windows (reqTrace B (frameTick u kin kout mach) (frame0 kin kout m0) σ) n) <+:
      outBytes mach m0 (decode kin
        (dataIn B u (windows (reqTrace B (frameTick u kin kout mach)
          (frame0 kin kout m0) σ) n))).recs := by
  rcases frameInv_run (B := B) (m0 := m0) hrx htx hs hrs hkin hkin' hkout hkout' hmach σ n with
    ⟨-, hr⟩ | ⟨-, inp0, hin, hr⟩ | ⟨-, hsd⟩ | ⟨-, hsd⟩
  · rw [hr.out]
    exact ⟨[], List.append_nil _⟩
  · rw [hin, decode_append, hr.out]
    obtain ⟨rs, hrs⟩ := decodeByte_recs kin (decode kin inp0) _
    rw [hrs]
    exact outBytes_prefix mach m0 rs _
  · exact ⟨_, hsd.out⟩
  · exact ⟨_, hsd.out⟩

end

end LeanExe.Requests
