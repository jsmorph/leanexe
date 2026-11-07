import LeanExe.A64.Proof.ImageRun
import LeanExe.A64.Proof.StartupOff
import LeanExe.A64.Proof.StartupTail
import LeanExe.A64.Proof.Shift

/-!
The run of an image from the boot state to `main`.  `image_main` takes a memory that holds the
bytes of a file that the kernel found to be an image at `image` and a boot state at the image's
first word with the MMU off, and gives a run of the boot model, with the code map of the image's
code and the image's protected bytes, to `main` in a ready state that satisfies every premise of
a program's theorem: SP at the stack's top, a multiple of 16, the stack's room and the area in the
platform's Normal memory, X17 at the area, the area's bytes those of the module's initial store,
and the program's bytes at `main`.  The program's code map is part of the image's.
-/

namespace LeanExe.A64

open Wasm

theorem toNat_add_ofNat {a : UInt64} {x : Nat} (h : a.toNat + x < 2 ^ 64) :
    (a + UInt64.ofNat x).toNat = a.toNat + x := by
  rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
  exact Nat.mod_eq_of_lt h

theorem add_ofNat_sub_toNat (a : UInt64) {x : Nat} (h : x < 2 ^ 64) :
    (a + UInt64.ofNat x - a).toNat = x := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel, toNat_ofNat_lt h]

theorem ofNat_add_add (a : UInt64) (x y : Nat) :
    a + UInt64.ofNat x + UInt64.ofNat y = a + UInt64.ofNat (x + y) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

/-- A byte at offset `x` of an image in the RAM GiB, at or past the end of its translation table,
is writable Normal memory under a boot state whose effective registers are the covered
configuration with the table at `TTBR0_EL1`. -/
theorem platform_normal_at {h : Hw} {b : Boot} (hcov : b.eff.covered h = true)
    (htab : ∀ j (hj : j < 32), b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    {image : UInt64} {n x : Nat} (hlo : 0x40000000 ≤ image.toNat)
    (hx : image.toNat + x < 0x80000000) (hge : tabOff n + 32 ≤ x) :
    (b.platform h (protectedBytes image n)).normal (image + UInt64.ofNat x) = true := by
  have ht := toNat_add_ofNat (a := image) (x := x) (by omega)
  apply platform_normal hcov htab
  · rw [UInt64.le_iff_toNat_le, ht]
    exact Nat.le_trans (by decide) (Nat.le_add_right_of_le hlo)
  · rw [UInt64.lt_iff_toNat_lt, ht]
    exact Nat.lt_of_lt_of_le hx (by decide)
  · simp only [protectedBytes, add_ofNat_sub_toNat image (show x < 2 ^ 64 by omega)]
    exact decide_eq_false (by omega)

theorem sub_offsets_toNat (image : UInt64) {x c : Nat} (hx : image.toNat + x < 2 ^ 64)
    (hc : image.toNat + c < 2 ^ 64) :
    (image + UInt64.ofNat x - (image + UInt64.ofNat c)).toNat = (2 ^ 64 + x - c) % 2 ^ 64 := by
  rw [UInt64.toNat_sub, toNat_add_ofNat hx, toNat_add_ofNat hc]
  omega

/-- The run from an image's first word to `main`, with every premise of a program's theorem. -/
theorem image_main {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image : UInt64} {n len : Nat} (h : Hw) {b : Boot}
    (hk : bytesOk (genImage m k args room cap o image) n len = true)
    (himg : image.toNat % 4096 = 0) (hroom : room.toNat % 16 = 0)
    (hm : ∀ j < len, b.core.mem (image + UInt64.ofNat j) = byteAt n j)
    (hpc : b.core.pc = image) (hoff : b.mmuOff) :
    ∃ prog start L, genProgram m k args uartAddr (image + UInt64.ofNat (64 + 4 * startupLength))
        room cap o = .ok prog ∧ L = layoutOf image prog.length m cap room ∧
      startupCode L = .ok start ∧
      CodeAt (fetchFrom b.core.mem image (codeWords prog.length)) (image + 64) start ∧
      ∃ b1, BootReach h (protectedBytes image prog.length)
          (fetchFrom b.core.mem image (codeWords prog.length)) b b1 ∧
        Ready h (protectedBytes image prog.length)
          (fetchFrom b.core.mem image (codeWords prog.length)) b1 ∧
        b1.core.pc = after L.base 1 ∧ b1.core.x 30 = after (image + 64) 55 ∧
        b1.core.x 17 = L.area ∧ b1.core.sp % 16 = 0 ∧ b1.core.sp.toNat ≤ 2 ^ 63 ∧
        (∀ j < room.toNat + 16, (b1.platform h (protectedBytes image prog.length)).normal
          (b1.core.sp - 16 - room + UInt64.ofNat j) = true) ∧
        (∀ j < areaSize cap,
          b1.core.mem (L.area + UInt64.ofNat j) = areaByte m.initialStore j) ∧
        (∀ j < areaSize cap, (b1.platform h (protectedBytes image prog.length)).normal
          (L.area + UInt64.ofNat j) = true) ∧
        L.area.toNat + areaSize cap + room.toNat + 16 ≤ b1.core.sp.toNat ∧
        (∀ j (hj : j < (imageBytes prog).length),
          b1.core.mem (after L.base 1 + UInt64.ofNat j) = (imageBytes prog)[j]) ∧
        (∀ a w, fetchFrom b1.core.mem (after L.base 1) prog.length a = some w →
          fetchFrom b.core.mem image (codeWords prog.length) a = some w) ∧
        b1.core.out = b.core.out ∧ b1.uartDone = true := by
  obtain ⟨L, prog, start, hp, hL, hlo, hhi, hpre, hs, hhead, hcode, htab, harea, hprog⟩ :=
    image_loaded hk hm
  have hcs := (CodeAt.append (code := fetchFrom b.core.mem image (codeWords prog.length))).mp hcode
  rw [← image_add_64] at hcs
  obtain ⟨cstart, -⟩ := hcs
  subst hL
  obtain ⟨-, hbase, -, htabf, harf, hclf, hendf, htopf, hsize⟩ :=
    layoutOf_fields image prog.length m cap room
  have hv := vecOff_ge prog.length
  have ha := areaOff_ge prog.length
  have hhi' := hhi
  rw [hsize] at hhi'
  have hpd : 8 ∣ areaPrefix m := roundUp_dvd _ _
  have had : 4096 ∣ areaOff prog.length := roundUp_dvd _ _
  have hcw : 4 * codeWords prog.length = tabOff prog.length := tabOff_dvd _
  unfold tabOff at hcw ha
  have hsz : areaSize cap = 4096 + cap * 65536 := rfl
  -- the MMU-off part
  obtain ⟨b0, r0, p0, sp0, sync0, tlb0, cov0, ttb0, mem0, -, out0, ud0⟩ :=
    boot_startupOff (h := h) (R := protectedBytes image prog.length)
      (code := fetchFrom b.core.mem image (codeWords prog.length))
      (fun a w hw => Nat.lt_trans (fetchFrom_ram hw hlo (by omega)).2.1 (by decide)) himg hlo hhi
      hs hhead cstart hpc hoff htab
  have htab0 : ∀ j (hj : j < 32), b0.core.mem (b0.eff.ttbr0 + UInt64.ofNat j) = tableBytes[j] :=
    fun j hj => by rw [ttb0, mem0]; exact htab j hj
  have hr0 : Ready h (protectedBytes image prog.length)
      (fetchFrom b.core.mem image (codeWords prog.length)) b0 := by
    refine ⟨sp0, sync0, cov0, tlb0, htab0, fun j hj => ?_, fun a w hw => ?_⟩
    · rw [ttb0, htabf, ofNat_add_add]
      simp only [protectedBytes, add_ofNat_sub_toNat image (show tabOff prog.length + j < 2 ^ 64
        by unfold tabOff; omega)]
      exact decide_eq_true (by omega)
    · obtain ⟨h1, h2, -⟩ := fetchFrom_ram hw hlo (by omega)
      exact ⟨true, classify_normal cov0 htab0 (UInt64.le_iff_toNat_le.mpr (by
        exact Nat.le_trans (by decide) h1)) (UInt64.lt_iff_toNat_lt.mpr (by
        exact Nat.lt_of_lt_of_le h2 (by decide)))⟩
  -- the tail
  have hpre' : 4096 + dataEnd m ≤ areaPrefix m := by unfold areaPrefix roundUp; omega
  have hcl : (layoutOf image prog.length m cap room).clear.toNat ≤
      (layoutOf image prog.length m cap room).areaEnd.toNat := by
    rw [hclf, hendf, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    omega
  have h8 : ((layoutOf image prog.length m cap room).areaEnd.toNat -
      (layoutOf image prog.length m cap room).clear.toNat) % 8 = 0 := by
    rw [hclf, hendf, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)]
    omega
  have hnorm : ∀ j < (layoutOf image prog.length m cap room).areaEnd.toNat -
      (layoutOf image prog.length m cap room).clear.toNat,
      (b0.platform h (protectedBytes image prog.length)).normal
        ((layoutOf image prog.length m cap room).clear + UInt64.ofNat j) = true := by
    intro j hj
    rw [hclf, hendf, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at hj
    rw [hclf, ofNat_add_add]
    exact platform_normal_at cov0 htab0 hlo (by omega) (by unfold tabOff; omega)
  obtain ⟨s1, r1, p1, x30, x17, sp1, out1, hz, hk1⟩ :=
    run_startup_tail (b0.platform h (protectedBytes image prog.length)) hs cstart p0 hcl h8 hnorm
  have hu0 := classify_uart cov0 htab0
  have rb := bootReach_of_reach sp0 sync0 cov0 tlb0 hu0 hr0.prot hr0.exe r1
  have hr1 := hr0.reach r1 (b0.uartDone && s1.out == b0.core.out)
  have hkept : ∀ x, x < areaOff prog.length + areaPrefix m →
      s1.mem (image + UInt64.ofNat x) = b.core.mem (image + UInt64.ofNat x) := by
    intro x hx
    rw [hk1 _ ?_, mem0]
    rw [hclf, hendf, sub_offsets_toNat image (by omega) (by omega),
      sub_offsets_toNat image (by omega) (by omega)]
    omega
  have hmain : after (image + UInt64.ofNat (64 + 4 * startupLength)) 1 =
      image + UInt64.ofNat (64 + 4 * (startupLength + 1)) := by
    rw [after, UInt64.add_assoc]
    congr 1
  have htop : (image + UInt64.ofNat (areaOff prog.length + areaSize cap + room.toNat + 16)).toNat
      = image.toNat + (areaOff prog.length + areaSize cap + room.toNat + 16) :=
    toNat_add_ofNat (by omega)
  refine ⟨prog, start, layoutOf image prog.length m cap room, hp, rfl, hs, cstart, _,
    r0.trans rb, hr1, p1, x30, x17, ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_,
    fun j hj => ?_, fun a w hw => ?_, ?_, ?_⟩
  · show s1.sp % 16 = 0
    apply UInt64.toNat_inj.mp
    rw [sp1, htopf, UInt64.toNat_mod, htop]
    show _ % 16 = 0
    omega
  · show s1.sp.toNat ≤ _
    rw [sp1, htopf, htop]
    omega
  · show (({ b0 with core := s1, uartDone := _ } : Boot).platform h _).normal
      (s1.sp - 16 - room + UInt64.ofNat j) = true
    have he : s1.sp - 16 - room + UInt64.ofNat j =
        image + UInt64.ofNat (areaOff prog.length + areaSize cap + j) := by
      apply UInt64.toNat_inj.mp
      rw [sp1, htopf]
      have hr := room.toNat_lt
      have hi := image.toNat_lt
      simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat,
        Nat.reducePow] at *
      omega
    rw [he]
    exact platform_normal_at hr1.cov hr1.tab hlo (by omega) (by unfold tabOff; omega)
  · show s1.mem ((layoutOf image prog.length m cap room).area + UInt64.ofNat j) = _
    rw [harf, ofNat_add_add]
    by_cases hj' : areaPrefix m ≤ j
    · rw [hz _ ?_, areaByte_tail m j hj']
      rw [hclf, hendf, sub_offsets_toNat image (by omega) (by omega),
        sub_offsets_toNat image (by omega) (by omega)]
      omega
    · rw [hkept _ (by omega), ← ofNat_add_add, ← harf]
      exact harea j (by omega)
  · show (({ b0 with core := s1, uartDone := _ } : Boot).platform h _).normal _ = true
    rw [harf, ofNat_add_add]
    exact platform_normal_at hr1.cov hr1.tab hlo (by omega) (by unfold tabOff; omega)
  · show (layoutOf image prog.length m cap room).area.toNat + _ + _ + _ ≤ s1.sp.toNat
    rw [harf, sp1, htopf, htop, toNat_add_ofNat (by omega)]
    omega
  · show s1.mem (after (layoutOf image prog.length m cap room).base 1 + UInt64.ofNat j) = _
    rw [hbase, hmain, ofNat_add_add]
    rw [length_imageBytes] at hj
    rw [hkept _ (by omega)]
    exact hprog j (by rw [length_imageBytes]; omega)
  · refine fetchFrom_sub (o := 16 + (startupLength + 1)) ?_ ?_ ?_ ?_ hw
    · rw [hbase, hmain]
      congr 1
    · unfold codeWords tabOff at *
      omega
    · omega
    · intro j hj
      rw [hbase, hmain, ofNat_add_add, hkept _ (by omega)]
  · show s1.out = b.core.out
    rw [out1, out0]
  · show (b0.uartDone && s1.out == b0.core.out) = true
    rw [ud0, out1]
    simp

/-- The number of the program's instructions in the image of `genImage` at `image`. -/
def imageProgLength (m : Module) (k : Nat) (args : List UInt64) (room : UInt64) (cap : Nat)
    (o : Output) (image : UInt64) : Nat :=
  match genProgram m k args uartAddr (image + UInt64.ofNat (64 + 4 * startupLength)) room cap o with
  | .ok p => p.length
  | .error _ => 0

/-- The form of the program theorems: for every platform `P`, exit word `base`, and area `area`,
from `main` with the program's premises, the program either returns to X30 with X0 = 0 after
writing `out`, or reaches the exit word with a status that satisfies `T` and writes nothing. -/
def ProgramRuns (m : Module) (k : Nat) (args : List UInt64) (room : UInt64) (cap : Nat)
    (o : Output) (out : List UInt8) (T : UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (base area : UInt64) {is : List Instr},
    genProgram m k args P.uart base room cap o = .ok is → ∀ (ms : State),
    (∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j]) →
    ms.pc = after base 1 → ms.sp % 16 = 0 → 4096 ≤ room.toNat → ms.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true) →
    ms.x 17 = area →
    (∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat →
    (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
      ms'.x 0 = 0 ∧ ms'.out = ms.out ++ out) ∨
    ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
      T (ms'.x 0) ∧ ms'.out = ms.out

/-- The run of an image from its first word to `HVC #0`, given the program's theorem in the form
`ProgramRuns`.  The image's run writes `out` and the byte 0, or the status's byte alone, and
reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF` and every store to the UART complete.  The
code map is that of the image's first words up to its translation table, and the protected bytes
are those below the table's end. -/
theorem image_run {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image : UInt64} {n len : Nat} (h : Hw) {b : Boot}
    (hk : bytesOk (genImage m k args room cap o image) n len = true)
    (himg : image.toNat % 4096 = 0) (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat)
    (hm : ∀ j < len, b.core.mem (image + UInt64.ofNat j) = byteAt n j)
    (hpc : b.core.pc = image) (hoff : b.mmuOff) {out : List UInt8} {T : UInt64 → Prop}
    (hprog : ProgramRuns m k args room cap o out T) :
    ∃ b', BootReach h (protectedBytes image (imageProgLength m k args room cap o image))
        (fetchFrom b.core.mem image (codeWords (imageProgLength m k args room cap o image)))
        b b' ∧
      fetchFrom b.core.mem image (codeWords (imageProgLength m k args room cap o image))
        b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++ out ++ [0] ∨
        ∃ c, T c ∧ b'.core.out = b.core.out ++ [c.toUInt8]) := by
  obtain ⟨prog, start, L, hp, hL, hs, cstart, b1, r1, hr1, p1, x30, x17, hal, htop, hstack,
    harea, hamap, habove, himage, hmono, hout1, hud1⟩ := image_main h hk himg hroom hm hpc hoff
  have hN : imageProgLength m k args room cap o image = prog.length := by
    simp only [imageProgLength, hp]
  rw [hN]
  subst hL
  have hbase := layout_base image prog.length m cap room
  have hpr := hprog (b1.platform h (protectedBytes image prog.length)) _ _ hp b1.core himage p1
    hal hroom' htop hstack x17 harea hamap habove
  obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_main (T := T) hs cstart hbase hmono hr1 (by
    rcases hpr with ⟨ms, hr, hpc', hx, ho⟩ | ⟨ms, hr, hpc', ht, ho⟩
    · exact .inl ⟨ms, hr, by rw [hpc', x30]; rfl, hx, ho⟩
    · exact .inr ⟨ms, hr, hpc', ht, ho⟩)
  refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
  rw [hout1] at ho'
  exact ho'

/-- The bytes of memory that the image of `genImage` at `image` uses from its start: the size in
its header, which covers the area and the stack. -/
def imageSize (m : Module) (k : Nat) (args : List UInt64) (room : UInt64) (cap : Nat)
    (o : Output) (image : UInt64) : Nat :=
  match genImage m k args room cap o image with
  | .ok (_, L) => L.size
  | .error _ => 0

/-- The image at `image + d` has as many program instructions as the image at `image`, under the
premises of `genImage_shift`. -/
theorem imageProgLength_shift {m : Module} {k : Nat} {args : List UInt64} {room : UInt64}
    {cap : Nat} {o : Output} {image d : UInt64} {bytes : List UInt8} {L : Layout}
    (hg : genImage m k args room cap o image = .ok (bytes, L))
    (hlo : 0x40000000 ≤ (image + d).toNat) (hhi : (image + d).toNat + L.size ≤ 0x80000000) :
    imageProgLength m k args room cap o (image + d) =
      imageProgLength m k args room cap o image := by
  obtain ⟨prog, start, hp, rfl, -, hhi0, -, -, -⟩ := gen_image hg
  have hsz := (layoutOf_fields image prog.length m cap room).2.2.2.2.2.2.2.2
  have hv := vecOff_ge prog.length
  have hao := areaOff_ge prog.length
  unfold tabOff at hao
  have h67 : startupLength = 67 := rfl
  have e1 : (image + UInt64.ofNat (64 + 4 * startupLength)).toNat = image.toNat + 332 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (image + d + UInt64.ofNat (64 + 4 * startupLength)).toNat =
      (image + d).toNat + 332 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hp' := genProgram_shift hp (by rw [e1]; omega) (by rw [← add_right_comm', e2]; omega)
  rw [← add_right_comm'] at hp'
  simp only [imageProgLength, hp, hp']

/-- `image_run` at every base `B` that is a multiple of 4096 and whose image lies in the RAM GiB,
given the kernel's check of the image at one base `image`: the image's bytes are the same at both
bases, and so are its program's instructions. -/
theorem image_run_at {m : Module} {k : Nat} {args : List UInt64} {room : UInt64} {cap : Nat}
    {o : Output} {image : UInt64} {n len : Nat} (h : Hw) {B : UInt64} {b : Boot}
    (hk : bytesOk (genImage m k args room cap o image) n len = true)
    (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat) (himg : image.toNat % 4096 = 0)
    (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + imageSize m k args room cap o image ≤ 0x80000000)
    (hm : ∀ j < len, b.core.mem (B + UInt64.ofNat j) = byteAt n j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) {out : List UInt8} {T : UInt64 → Prop}
    (hprog : ProgramRuns m k args room cap o out T) :
    ∃ b', BootReach h (protectedBytes B (imageProgLength m k args room cap o image))
        (fetchFrom b.core.mem B (codeWords (imageProgLength m k args room cap o image))) b b' ∧
      fetchFrom b.core.mem B (codeWords (imageProgLength m k args room cap o image))
        b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++ out ++ [0] ∨
        ∃ c, T c ∧ b'.core.out = b.core.out ++ [c.toUInt8]) := by
  obtain ⟨bytes, L, hg, -, -⟩ := of_bytesOk hk
  have hBd : image + (B - image) = B := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
  have hd : (B - image).toNat % 4096 = 0 := by
    have := image.toNat_lt
    have := B.toNat_lt
    rw [UInt64.toNat_sub]
    omega
  have hsize : imageSize m k args room cap o image = L.size := by simp only [imageSize, hg]
  have hhi' : (image + (B - image)).toNat + L.size ≤ 0x80000000 := by rw [hBd, ← hsize]; exact hhi
  have hlo' : 0x40000000 ≤ (image + (B - image)).toNat := by rw [hBd]; exact hlo
  have hk' := bytesOk_shift hk hd hlo' (fun bytes' L' hg' => by
    rw [hg] at hg'
    cases hg'
    exact hhi')
  have hN := imageProgLength_shift hg hlo' hhi'
  rw [hBd] at hk' hN
  rw [← hN]
  exact image_run h hk' hB hroom hroom' hm hpc hoff hprog

end LeanExe.A64
