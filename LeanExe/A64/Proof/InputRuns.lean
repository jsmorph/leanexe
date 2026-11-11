import LeanExe.A64.Proof.Input

/-!
The theorems of the programs and images that read their arguments from the UART.
`InputRuns` is the counterpart of `ProgramRuns` for a program of `genInProgram`: from `main`, with
the receiver at its first read and no poll done, when the receiver delivers the bytes of words
`ws` without an error flag, the program writes `Out ws` and returns 0, or reaches the exit word
with a status that `T ws` allows; and when a byte among those it reads carries an error flag after
bytes without one, it reaches the exit word with status 65 and writes nothing.  `input_runs` gives
`InputRuns` from the compiler's theorem of the function that the program calls, and
`image_input_run` joins it to the startup, as `image_run` joins `ProgramRuns`.
-/

namespace LeanExe.A64

open Wasm LeanExe.Pipeline

/-- The form of the theorems of programs of `genInProgram`, which read `n` words from the UART: for
every platform `P`, exit word `base`, and area `area`, from `main` with the premises of
`ProgramRuns` and the receiver at its first read with no poll done, when the receiver delivers the
bytes of words `ws` without an error flag, the program writes `Out ws` and returns 0 or reaches the
exit word with a status that `T ws` allows and writes nothing, and when byte `j` of the first
`8 * n` carries an error flag and no byte before it does, the program reaches the exit word with
status 65 and writes nothing. -/
def InputRuns (m : Module) (k n : Nat) (room : UInt64) (cap : Nat) (o : Output)
    (Out : List UInt64 → List UInt8) (T : List UInt64 → UInt64 → Prop) : Prop :=
  ∀ (P : Platform) (base area : UInt64) {is : List Instr},
    genInProgram m k n P.uart base room cap o = .ok is → ∀ (ms : State),
    (∀ j (hj : j < (imageBytes is).length),
      ms.mem (after base 1 + UInt64.ofNat j) = (imageBytes is)[j]) →
    ms.pc = after base 1 → ms.sp % 16 = 0 → 4096 ≤ room.toNat → ms.sp.toNat ≤ 2 ^ 63 →
    (∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true) →
    ms.x 17 = area →
    (∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j) →
    (∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true) →
    area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat →
    ms.io.rxNext = 0 → ms.io.rxPolls = 0 →
    (∀ ws : List UInt64, ws.length = n → P.rx.Delivers (ws.flatMap bytesOf) →
      (∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = ms.x 30 ∧
        ms'.x 0 = 0 ∧ ms'.out = ms.out ++ Out ws) ∨
      ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
        T ws (ms'.x 0) ∧ ms'.out = ms.out) ∧
    (∀ j < 8 * n, (∀ i < j, ¬ P.rx.Flagged i) → P.rx.Flagged j →
      ∃ ms', Reach P (fetchFrom ms.mem (after base 1) is.length) ms ms' ∧ ms'.pc = base ∧
        ms'.x 0 = 65 ∧ ms'.out = ms.out)

theorem genInProgram_length {m : Module} {k n : Nat} {uart base room : UInt64} {cap : Nat}
    {o : Output} {is : List Instr} (hg : genInProgram m k n uart base room cap o = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = inMainSize n o +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 :=
  genProgramWith_length hg (fun e main hmg => by
    obtain ⟨-, reads, exit, hr, -, hs⟩ := gen_inMain hmg
    rw [hs.length]
    simp only [inMainSize, List.length_append, movImm_length, List.length_cons, List.length_nil,
      readWords_length n 0 hr]
    omega) hfs

/-- A receiver that delivers the bytes of words `ws` gives each word's bytes to the reads. -/
theorem delivers_rxSum {rx : Rx} {ws : List UInt64} (hd : rx.Delivers (ws.flatMap bytesOf))
    {i : Nat} (hi : i < ws.length) : rxSum rx (8 * i) 8 = ws[i].toNat := by
  rw [rxSum_digits 8 fun t ht => (delivers_words hd hi ht).1]
  exact Nat.mod_eq_of_lt ws[i].toNat_lt

/-- `InputRuns` from the compiler's theorem `h` that function `k` of `m` computes `f`, for the
argument `dec ws` that the words `ws` give, whose values, of the parameters' types `ts`, have
`ws` as their words.  The program writes `enc (f (dec ws))` and returns 0, or reaches the exit
word with the status 1 of `unreachable` when `aborts` holds, or with the status 4 of an overflow of
the stack when function `k` calls others and `room` lies below `stackBound m k`.  `entryOkWith`
holds the facts about the module that `genInProgram` leaves unchecked. -/
theorem input_runs {α β : Type} [Scalar α] [Represent β] {aborts : Bool} {m : Module}
    {k n : Nat} {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} {room : UInt64} {cap : Nat}
    {o : Output} {enc : β → List UInt8}
    (h : ImplementsA aborts m k f Pre Post) (dec : List UInt64 → α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : ∀ ws : List UInt64, ws.length = n → initialPages m ≤ cap →
      Pre (dec ws) heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (ts : List ValueType := List.replicate n .i64)
    (hargs : ∀ ws : List UInt64, ws.length = n → argValues ts ws = Scalar.values (dec ws))
    (hok : entryOkWith (inMainSize n o) m k ts n = true := by decide +kernel) :
    InputRuns m k n room cap o (fun ws => enc (f (dec ws))) fun _ c =>
      (aborts = true ∧ c = 1) ∨ (callTargets m k ≠ [] ∧ room.toNat < stackBound m k ∧ c = 4) := by
  intro P base area is hg ms himage hpc hal hroom htop hstack h17 harea hamap habove hrx hpo
  obtain ⟨-, fs, -, -, -, -, -, -, -, -, -, -, -, hao, -, -, hfs, -⟩ := gen_programWith hg
  have hcap := cap_lt_of_areaOk hao
  unfold entryOkWith at hok
  rw [hfs] at hok
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨himp, hpar⟩, hlen⟩, hsize⟩ := hok
  have hn : 4 * is.length < 2 ^ 64 := by
    rw [genInProgram_length hg hfs]
    exact hsize
  obtain ⟨g, hk, hp⟩ : ∃ g, m.funcs[k]? = some g ∧ g.params = ts := by
    cases hk : m.funcs[k]? with
    | none => rw [hk] at hpar; cases hpar
    | some g => rw [hk] at hpar; exact ⟨g, rfl, Option.some.inj hpar⟩
  have hsim := fun F => inProgram_sim P _ hg (codeAt_fetchFrom hn himage) himp hk
    (by rw [hp, hlen]) F ms hpc hal hroom htop hstack h17 harea hamap habove hrx hpo
  refine ⟨fun ws hws hd => ?_, fun j hj hpre' hfj => ?_⟩
  · have hclean : ∀ t < 8 * n, ¬ P.rx.Flagged t := fun t ht => by
      have := (delivers_words hd (i := t / 8) (t := t % 8) (by omega) (Nat.mod_lt _ (by decide))).2
      rwa [Nat.div_add_mod] at this
    rcases outcome_runs h (dec ws) hheap (hpre ws hws (pages_le_of_areaOk hao)) (by omega) hout
        (hargs ws hws) (fun F => by
          rcases hsim F with ⟨ms', -, -, ⟨-, t, ht, hft⟩, -⟩ | ⟨ws', ⟨hl', hv', -⟩, hs⟩
          · exact absurd hft (hclean t ht)
          · have hw : ws' = ws := List.ext_getElem (by rw [hl', hws]) fun i h1 h2 =>
              UInt64.toNat_inj.mp (by rw [hv' i h1, delivers_rxSum hd h2])
            rw [hw, hp] at hs
            exact hs) with hr | ⟨ms', hr, hpc', hc, ho⟩
    · exact .inl hr
    · exact .inr ⟨ms', hr, hpc', hc.imp id fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, ho⟩
  · rcases hsim 0 with ⟨ms', hr, hpc', ⟨hx, -⟩, ho⟩ | ⟨ws', ⟨-, -, hcl⟩, -⟩
    · exact ⟨ms', hr, hpc', hx, ho⟩
    · exact absurd hfj (hcl j hj)

/-- `input_runs` for a theorem without the trap at `unreachable` and a stack whose bound is at
most 4096 bytes, which `InputRuns` requires of the room, or at most `room`: no status. -/
theorem input_runs_bounded {α β : Type} [Scalar α] [Represent β] {m : Module} {k n : Nat}
    {f : α → β} {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop} {room : UInt64} {cap : Nat}
    {o : Output} {enc : β → List UInt8}
    (h : ImplementsA false m k f Pre Post) (dec : List UInt64 → α) {heap : Heap}
    (hheap : heap.At (m.initialStore : Store Unit))
    (hpre : ∀ ws : List UInt64, ws.length = n → initialPages m ≤ cap →
      Pre (dec ws) heap (initStore m cap))
    (hout : ∀ heap st vs y, Represent.owned heap st vs y → Writes o st vs (enc y))
    (hbound : stackBound m k ≤ 4096 ∨ stackBound m k ≤ room.toNat)
    (ts : List ValueType := List.replicate n .i64)
    (hargs : ∀ ws : List UInt64, ws.length = n → argValues ts ws = Scalar.values (dec ws))
    (hok : entryOkWith (inMainSize n o) m k ts n = true := by decide +kernel) :
    InputRuns m k n room cap o (fun ws => enc (f (dec ws))) fun _ _ => False := by
  intro P base area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove hrx hpo
  obtain ⟨h1, h2⟩ := input_runs h dec hheap hpre hout ts hargs hok P base area hg ms himage hpc
    hal hroom htop hstack h17 harea hamap habove hrx hpo
  refine ⟨fun ws hws hd => ?_, h2⟩
  rcases h1 ws hws hd with hr | ⟨_, -, -, ⟨hf, -⟩ | ⟨-, hlt, -⟩, -⟩
  · exact .inl hr
  · cases hf
  · omega

/-- The number of the program's instructions in the image of `genInImage` at `image`. -/
def imageInProgLength (m : Module) (k n : Nat) (room : UInt64) (cap : Nat) (o : Output)
    (image : UInt64) : Nat :=
  match genInProgram m k n uartAddr (image + UInt64.ofNat (64 + 4 * startupLength)) room cap o with
  | .ok p => p.length
  | .error _ => 0

/-- The run of an image of `genInImage` from its first word to `HVC #0`, given the program's
theorem in the form `InputRuns`, with the receiver of `h` at its first read and no poll done.
When the receiver delivers the bytes of words `ws` without an error flag, the image's run writes
`Out ws` and the byte 0, or the byte of a status that `T ws` allows.  When byte `j` of the first
`8 * n` carries an error flag and no byte before it does, the run writes the byte 65 alone.  Each
run reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF` and every store to the UART complete.
The code map is that of the image's first words up to its translation table, and the protected
bytes are those below the table's end. -/
theorem image_input_run {m : Module} {k n : Nat} {room : UInt64} {cap : Nat} {o : Output}
    {image : UInt64} {nb len : Nat} (h : Hw) {b : Boot}
    (hk : bytesOk (genInImage m k n room cap o image) nb len = true)
    (himg : image.toNat % 4096 = 0) (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat)
    (hm : ∀ j < len, b.core.mem (image + UInt64.ofNat j) = byteAt nb j)
    (hpc : b.core.pc = image) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0)
    {Out : List UInt64 → List UInt8} {T : List UInt64 → UInt64 → Prop}
    (hprog : InputRuns m k n room cap o Out T) :
    (∀ ws : List UInt64, ws.length = n → h.rx.Delivers (ws.flatMap bytesOf) →
      ∃ b', BootReach h (protectedBytes image (imageInProgLength m k n room cap o image))
          (fetchFrom b.core.mem image (codeWords (imageInProgLength m k n room cap o image)))
          b b' ∧
        fetchFrom b.core.mem image (codeWords (imageInProgLength m k n room cap o image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
        (b'.core.out = b.core.out ++ Out ws ++ [0] ∨
          ∃ c, T ws c ∧ b'.core.out = b.core.out ++ [c.toUInt8])) ∧
    (∀ j < 8 * n, (∀ i < j, ¬ h.rx.Flagged i) → h.rx.Flagged j →
      ∃ b', BootReach h (protectedBytes image (imageInProgLength m k n room cap o image))
          (fetchFrom b.core.mem image (codeWords (imageInProgLength m k n room cap o image)))
          b b' ∧
        fetchFrom b.core.mem image (codeWords (imageInProgLength m k n room cap o image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65]) := by
  obtain ⟨prog, start, L, hp, hL, hs, cstart, b1, r1, hr1, p1, x30, x17, hal, htop, hstack,
    harea, hamap, habove, himage, hmono, hout1, hud1⟩ :=
    image_main (gp := fun base => genInProgram m k n uartAddr base room cap o) h hk himg hroom hm
      hpc hoff
  have hN : imageInProgLength m k n room cap o image = prog.length := by
    simp only [imageInProgLength, hp]
  rw [hN]
  subst hL
  have hbase := layout_base image prog.length m cap room
  have hpr := hprog (b1.platform h (protectedBytes image prog.length)) _ _ hp b1.core himage p1
    hal hroom' htop hstack x17 harea hamap habove (by rw [hout1]; exact hio.1)
    (by rw [hout1]; exact hio.2)
  refine ⟨fun ws hws hd => ?_, fun j hj hpre hf => ?_⟩
  · obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_main (T := T ws) hs cstart hbase hmono hr1
      (by
        rcases hpr.1 ws hws hd with ⟨ms, hr, hpc', hx, ho⟩ | ⟨ms, hr, hpc', ht, ho⟩
        · exact .inl ⟨ms, hr, by rw [hpc', x30]; rfl, hx, ho⟩
        · exact .inr ⟨ms, hr, hpc', ht, ho⟩)
    refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
    rw [hout1] at ho'
    exact ho'
  · obtain ⟨ms, hr, hpc', hx, ho⟩ := hpr.2 j hj hpre hf
    obtain ⟨b', r2, hc', hx', hu', ho'⟩ := boot_after_exit hs cstart hbase hmono hr1 hr hpc'
    refine ⟨b', r1.trans r2, hc', hx', hu', ?_⟩
    show b'.core.io.out = b.core.io.out ++ [65]
    rw [ho', show ms.io.out = b.core.io.out from ho.trans (congrArg Io.out hout1), hx]
    rfl

end LeanExe.A64
