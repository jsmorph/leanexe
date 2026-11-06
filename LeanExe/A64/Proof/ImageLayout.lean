import LeanExe.A64.BootImage
import LeanExe.A64.Proof.StartupCode
import LeanExe.A64.Proof.Area
import LeanExe.A64.Proof.Machine

/-!
Where the bytes of an image that `genImage` gives lie.  `gen_image` unpacks the generator, and
the lemmas after it turn a memory that holds the image's bytes from `image` into a memory that
holds each part at its address: the header's two instructions, the startup and the program from
byte 64, the translation table at `L.table`, and the area's bytes at `L.area`.
`codeAt_fetchFrom_at` gives the code map of a region whose words are an image's instructions.
-/

namespace LeanExe.A64

open Wasm

/-- The byte offset of the vector table in an image whose program has `n` instructions. -/
def vecOff (n : Nat) : Nat := roundUp (64 + 4 * (startupLength + 1) + 4 * n) 2048

/-- The byte offset of the translation table. -/
def tabOff (n : Nat) : Nat := vecOff n + 2048

/-- The byte offset of the area. -/
def areaOff (n : Nat) : Nat := roundUp (tabOff n + 32) 4096

theorem roundUp_ge (n a : Nat) (ha : 0 < a) : n ≤ roundUp n a := by
  unfold roundUp
  have h1 := Nat.div_add_mod (n + a - 1) a
  have h2 := Nat.mod_lt (n + a - 1) ha
  rw [Nat.mul_comm]
  omega

theorem roundUp_dvd (n a : Nat) : a ∣ roundUp n a := Nat.dvd_mul_left a _

theorem layoutOf_fields (image : UInt64) (n : Nat) (m : Module) (cap : Nat) (room : UInt64) :
    (layoutOf image n m cap room).image = image ∧
    (layoutOf image n m cap room).base = image + UInt64.ofNat (64 + 4 * startupLength) ∧
    (layoutOf image n m cap room).vectors = image + UInt64.ofNat (vecOff n) ∧
    (layoutOf image n m cap room).table = image + UInt64.ofNat (tabOff n) ∧
    (layoutOf image n m cap room).area = image + UInt64.ofNat (areaOff n) ∧
    (layoutOf image n m cap room).clear = image + UInt64.ofNat (areaOff n + areaPrefix m) ∧
    (layoutOf image n m cap room).areaEnd = image + UInt64.ofNat (areaOff n + areaSize cap) ∧
    (layoutOf image n m cap room).stackTop =
      image + UInt64.ofNat (areaOff n + areaSize cap + room.toNat + 16) ∧
    (layoutOf image n m cap room).size = areaOff n + areaSize cap + room.toNat + 16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem imageHeader_length (size : Nat) : (imageHeader size).length = 64 := by
  simp [imageHeader, bytes64, wordBytes]

theorem vectorBytes_length : vectorBytes.length = 2048 := by decide +kernel

theorem tableBytes_length : tableBytes.length = 32 := by decide +kernel

theorem startupCode_length {L : Layout} {is : List Instr} (h : startupCode L = .ok is) :
    is.length = startupLength + 1 := by
  obtain ⟨_, _, vec, tab, clr, fin, stk, ar, _, _, _, _, h2, h3, h4, h5, h6, h7, _, _, his⟩ :=
    startupCode_ok h
  rw [his]
  simp only [List.length_append, List.length_cons, List.length_nil, addrOf_length h2,
    addrOf_length h3, addrOf_length h4, addrOf_length h5, addrOf_length h6, addrOf_length h7,
    movImm, clearLoop, startupLength]

/-- `genImage` unpacked: the program, the layout, the range of the image, the startup, and the
bytes. -/
theorem gen_image {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image : UInt64} {bytes : List UInt8} {L : Layout}
    (hg : genImage m k args room cap o image = .ok (bytes, L)) :
    ∃ prog start, genProgram m k args uartAddr (image + UInt64.ofNat (64 + 4 * startupLength))
        room cap o = .ok prog ∧
      L = layoutOf image prog.length m cap room ∧
      0x40000000 ≤ image.toNat ∧ image.toNat + L.size ≤ 0x80000000 ∧
      startupCode L = .ok start ∧
      bytes = imageHeader L.size ++ imageBytes (start ++ prog) ++
        List.replicate ((L.vectors - image).toNat - 64 - (imageBytes (start ++ prog)).length) 0 ++
        vectorBytes ++ tableBytes ++ List.replicate ((L.area - L.table).toNat - 32) 0 ++
        areaPrefixBytes m := by
  unfold genImage at hg
  cases hp : genProgram m k args uartAddr (image + UInt64.ofNat (64 + 4 * startupLength)) room cap
    o with
  | error e => rw [hp] at hg; cases hg
  | ok prog => ?_
  rw [hp] at hg
  by_cases hr : 0x40000000 ≤ image.toNat ∧
      image.toNat + (layoutOf image prog.length m cap room).size ≤ 0x80000000
  · simp only [bind, Except.bind, hr] at hg
    cases hs : startupCode (layoutOf image prog.length m cap room) with
    | error e => rw [hs] at hg; cases hg
    | ok start =>
        rw [hs] at hg
        simp only [pure, Except.pure] at hg
        injection hg with hg1
        injection hg1 with hb hL
        subst hL
        exact ⟨prog, start, rfl, rfl, hr.1, hr.2, hs, hb.symm⟩
  · simp only [bind, Except.bind, hr, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at hg
    cases hg

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem vecOff_ge (n : Nat) : 64 + 4 * (startupLength + 1) + 4 * n ≤ vecOff n :=
  roundUp_ge _ _ (by decide)

theorem areaOff_ge (n : Nat) : tabOff n + 32 ≤ areaOff n := roundUp_ge _ _ (by decide)

theorem getElem?_append_offset {α : Type} (l1 l2 : List α) (n j : Nat) (h : l1.length = n) :
    (l1 ++ l2)[n + j]? = l2[j]? := by
  subst h
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

theorem sub_offsets {a : UInt64} {x y : Nat} (hy : y ≤ x) (hx : a.toNat + x < 2 ^ 64) :
    (a + UInt64.ofNat x - (a + UInt64.ofNat y)).toNat = x - y := by
  have h1 : (a + UInt64.ofNat x).toNat = a.toNat + x := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt hx
  have h2 : (a + UInt64.ofNat y).toNat = a.toNat + y := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1, h2]; omega), h1, h2]
  omega

theorem imageHeader_eq (size : Nat) :
    ∃ rest, imageHeader size = imageBytes [.spsel1, .b 15] ++ rest :=
  ⟨bytes64 0 ++ bytes64 (UInt64.ofNat size) ++ bytes64 2 ++ bytes64 0 ++ bytes64 0 ++ bytes64 0 ++
    wordBytes 0x644D5241 ++ wordBytes 0, by
    simp only [imageHeader, imageBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]⟩

/-- The parts of an image's bytes at their offsets: the header's two instructions, the startup
and the program from byte 64, the table at `tabOff`, and the area's prefix at `areaOff`. -/
theorem image_parts {m : Module} {cap : Nat} {room image : UInt64} {prog start : List Instr}
    {L : Layout} {bytes : List UInt8} (hL : L = layoutOf image prog.length m cap room)
    (hs : startupCode L = .ok start) (hr : image.toNat + L.size ≤ 0x80000000)
    (hb : bytes = imageHeader L.size ++ imageBytes (start ++ prog) ++
      List.replicate ((L.vectors - image).toNat - 64 - (imageBytes (start ++ prog)).length) 0 ++
      vectorBytes ++ tableBytes ++ List.replicate ((L.area - L.table).toNat - 32) 0 ++
      areaPrefixBytes m) :
    bytes.length = areaOff prog.length + areaPrefix m ∧
    (∀ j < 8, bytes[j]? = (imageBytes [.spsel1, .b 15])[j]?) ∧
    (∀ j < (imageBytes (start ++ prog)).length,
      bytes[64 + j]? = (imageBytes (start ++ prog))[j]?) ∧
    (∀ j < 32, bytes[tabOff prog.length + j]? = tableBytes[j]?) ∧
    (∀ j < areaPrefix m, bytes[areaOff prog.length + j]? = (areaPrefixBytes m)[j]?) := by
  subst hL
  have hsz := (layoutOf_fields image prog.length m cap room).2.2.2.2.2.2.2.2
  rw [hsz] at hr
  have hv := vecOff_ge prog.length
  have ha := areaOff_ge prog.length
  have hcl : (imageBytes (start ++ prog)).length = 4 * (startupLength + 1) + 4 * prog.length := by
    rw [length_imageBytes, List.length_append, startupCode_length hs]
    omega
  have hvec : ((layoutOf image prog.length m cap room).vectors - image).toNat =
      vecOff prog.length := by
    show (image + UInt64.ofNat (vecOff prog.length) - image).toNat = _
    rw [UInt64.add_comm, UInt64.add_sub_cancel, toNat_ofNat_lt (by unfold tabOff at ha; omega)]
  have hat : ((layoutOf image prog.length m cap room).area -
      (layoutOf image prog.length m cap room).table).toNat =
      areaOff prog.length - tabOff prog.length :=
    sub_offsets (x := areaOff prog.length) (y := tabOff prog.length) (by omega) (by omega)
  rw [hvec, hat, hcl] at hb
  have hH := imageHeader_length (layoutOf image prog.length m cap room).size
  have hV := vectorBytes_length
  have hT := tableBytes_length
  have hA := areaPrefixBytes_length m
  obtain ⟨rest, hrest⟩ := imageHeader_eq (layoutOf image prog.length m cap room).size
  have h8 : (imageBytes [Instr.spsel1, .b 15]).length = 8 := rfl
  subst hb
  simp only [List.append_assoc]
  generalize hC : imageBytes (start ++ prog) = C at *
  generalize hP1 : List.replicate (vecOff prog.length - 64 - (4 * (startupLength + 1) +
    4 * prog.length)) (0 : UInt8) = P1
  generalize hP2 : List.replicate (areaOff prog.length - tabOff prog.length - 32) (0 : UInt8) = P2
  have hP1l :
      P1.length = vecOff prog.length - 64 - (4 * (startupLength + 1) + 4 * prog.length) := by
    rw [← hP1, List.length_replicate]
  have hP2l : P2.length = areaOff prog.length - tabOff prog.length - 32 := by
    rw [← hP2, List.length_replicate]
  have e1 : 64 + C.length + P1.length = vecOff prog.length := by rw [hcl, hP1l]; omega
  have e2 : 64 + C.length + P1.length + 2048 = tabOff prog.length := by unfold tabOff; omega
  have e3 : tabOff prog.length + 32 + P2.length = areaOff prog.length := by rw [hP2l]; omega
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [List.length_append, hH, hV, hT, hA]
    omega
  · rw [hrest, List.append_assoc, List.getElem?_append_left (by omega)]
  · rw [getElem?_append_offset _ _ 64 j hH, List.getElem?_append_left (by omega)]
  · rw [show tabOff prog.length + j = 64 + (C.length + (P1.length + (2048 + j))) by omega,
      getElem?_append_offset _ _ 64 _ hH, getElem?_append_offset _ _ _ _ rfl,
      getElem?_append_offset _ _ _ _ rfl, getElem?_append_offset _ _ 2048 j hV,
      List.getElem?_append_left (by omega)]
  · rw [show areaOff prog.length + j = 64 + (C.length + (P1.length + (2048 +
        (32 + (P2.length + j))))) by omega,
      getElem?_append_offset _ _ 64 _ hH, getElem?_append_offset _ _ _ _ rfl,
      getElem?_append_offset _ _ _ _ rfl, getElem?_append_offset _ _ 2048 _ hV,
      getElem?_append_offset _ _ 32 _ hT, getElem?_append_offset _ _ _ j rfl]

end LeanExe.A64
