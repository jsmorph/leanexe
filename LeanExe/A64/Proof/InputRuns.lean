import LeanExe.A64.Proof.Input

/-!
The theorems of the programs and images that read their arguments from the UART.
`InputRuns` is the counterpart of `ProgramRuns` for a program of `genInProgram`: from `main`, with
the receiver at its first read and no poll done, when the receiver delivers the bytes of words
`ws` without an error flag, the program writes `Out ws` and returns 0, or reaches the exit word
with a status that `T ws` allows; and when a byte among those it reads carries an error flag after
bytes without one, it reaches the exit word with status 65 and writes nothing.  `input_runs` gives
`InputRuns` from the compiler's theorem of the function that the program calls, and
`image_input_run` joins it to the startup, as `image_run` joins `ProgramRuns`.  `genInProgram`
places the same program at every base (`genInProgram_shift`), so `image_input_run_at` states the
run of an image at every base that is a multiple of 4096 from the kernel's check of the image at
one base.
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

/-! ## The programs and images at every base -/

theorem readByte_shift {a err d : UInt64} {δ : Int} {r : Fin 32} {b : Nat} {is : List Instr}
    (hg : readByte a err r b = .ok is) (ha : MovesFrom d δ a 10) (he : Moves d δ err) :
    readByte (a + d) (err + d) r b = .ok is := by
  unfold readByte at hg ⊢
  cases hb1 : cbField (after a 3) (after a 1) with
  | error e => simp [hb1, bind, Except.bind] at hg
  | ok back =>
  cases hb2 : cbField (after a 6) err with
  | error e => simp [hb1, hb2, bind, Except.bind] at hg
  | ok fail =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  simp only [after_shift, cbField_shift (ha 3 (by omega)) (ha 1 (by omega)) hb1,
    cbField_shift (ha 6 (by omega)) he hb2, bind, Except.bind, pure, Except.pure]

theorem readBytes_shift {err d : UInt64} {δ : Int} {r : Fin 32} (he : Moves d δ err) :
    ∀ c b {a : UInt64} {is : List Instr}, readBytes err r a b c = .ok is →
      MovesFrom d δ a (10 * c) → readBytes (err + d) r (a + d) b c = .ok is
  | 0, b, a, is, hg, _ => hg
  | c + 1, b, a, is, hg, ha => by
      simp only [readBytes] at hg ⊢
      cases h1 : readByte a err r b with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok first =>
      cases h2 : readBytes err r (after a 10) (b + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure] at hg
      have h1' := readByte_shift h1 (ha.le (by omega)) he
      have h2' := readBytes_shift he c (b + 1) h2
        ((ha.drop (m := 10) (by omega)).le (by omega))
      simp only [after_shift, h1', h2', bind, Except.bind, pure, Except.pure]
      exact hg

theorem readWords_shift {err d : UInt64} {δ : Int} (he : Moves d δ err) :
    ∀ c i {a : UInt64} {is : List Instr}, readWords err a i c = .ok is →
      MovesFrom d δ a (81 * c) → readWords (err + d) (a + d) i c = .ok is
  | 0, i, a, is, hg, _ => hg
  | c + 1, i, a, is, hg, ha => by
      simp only [readWords] at hg ⊢
      cases h1 : readBytes err ⟨i % 32, Nat.mod_lt _ (by decide)⟩ (after a 1) 0 8 with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok bytes =>
      cases h2 : readWords err (after a 81) (i + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure] at hg
      have h1' := readBytes_shift he 8 0 h1 ((ha.drop (m := 1) (by omega)).le (by omega))
      have h2' := readWords_shift he c (i + 1) h2 ((ha.drop (m := 81) (by omega)).le (by omega))
      simp only [after_shift, h1', h2', bind, Except.bind, pure, Except.pure]
      exact hg

theorem genInMain_length {a e uart room base : UInt64} {n : Nat} {o : Output}
    {main : List Instr} (hg : genInMain a e n uart room base o = .ok main) :
    main.length = inMainSize n o := by
  obtain ⟨-, reads, exit, hr, -, hs⟩ := gen_inMain hg
  rw [hs.length]
  simp only [inMainSize, List.length_append, movImm_length, List.length_cons, List.length_nil,
    readWords_length n 0 hr]
  omega

/-- The entry routine of `genInMain` at `a + d`, with its function's entry and its exit word
shifted by `d`, is the one at `a`, when the shift moves its addresses, the entry, and the exit
word by the same number. -/
theorem genInMain_shift {a e uart room base d : UInt64} {δ : Int} {n : Nat} {o : Output}
    {main : List Instr} (hg : genInMain a e n uart room base o = .ok main)
    (ha : MovesFrom d δ a main.length) (he : Moves d δ e) (hb : Moves d δ base) :
    genInMain (a + d) (e + d) n uart room (base + d) o = .ok main := by
  have hl := genInMain_length hg
  unfold inMainSize at hl
  rw [hl] at ha
  unfold genInMain at hg ⊢
  by_cases hc : n > 8
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases hr : readWords (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) (after a 15) 0 n with
  | error err => simp [hc, hr, bind, Except.bind] at hg
  | ok reads =>
  cases hbl : bField (after a (8 + (7 + 81 * n))) e with
  | error err => simp [hc, hr, hbl, bind, Except.bind] at hg
  | ok g =>
  cases hgo : genOut (after a (13 + (7 + 81 * n))) o with
  | error err => simp [hc, hr, hbl, hgo, bind, Except.bind] at hg
  | ok out =>
  cases hx : bField (after (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) 4) base with
  | error err => simp [hc, hr, hbl, hgo, hx, bind, Except.bind] at hg
  | ok exit =>
  have hr' := readWords_shift (ha _ (by omega)) n 0 hr
    ((ha.drop (m := 15) (by omega)).le (by omega))
  have hbl' := bField_shift (ha _ (by omega)) he hbl
  have hgo' := genOut_shift hgo ((ha.drop (m := 13 + (7 + 81 * n)) (by omega)).le (by omega))
  have hx' := bField_shift (by rw [after_after]; exact ha _ (by omega)) hb hx
  rw [← hg]
  simp only [hc, ite_false, after_shift, hr, hr', hbl, hbl', hgo, hgo', hx, hx', bind,
    Except.bind, pure, Except.pure]

/-- `genInProgram` places the same program at every base where it lies below 2^64. -/
theorem genInProgram_shift {m : Module} {k n : Nat} {uart base room : UInt64} {cap : Nat}
    {o : Output} {p : List Instr} {d : UInt64}
    (hg : genInProgram m k n uart base room cap o = .ok p)
    (h1 : base.toNat + 4 * p.length < 2 ^ 64) (h2 : (base + d).toNat + 4 * p.length < 2 ^ 64) :
    genInProgram m k n uart (base + d) room cap o = .ok p :=
  genProgramWith_shift hg (fun _ _ hmg => genInMain_length hmg)
    (fun _ _ _ hmg ha he _ => by
      rw [after_shift]
      exact genInMain_shift hmg (by
        rw [genInMain_length hmg]
        exact (ha.drop (m := 1) (by omega)).le (by omega)) he ha.base) h1 h2

theorem genInProgram_shiftsBy (m : Module) (k n : Nat) (room : UInt64) (cap : Nat) (o : Output)
    (d : UInt64) : ShiftsBy (fun base => genInProgram m k n uartAddr base room cap o) d :=
  fun _ _ hp h1 h2 => genInProgram_shift hp h1 h2

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

/-- The bytes of memory that the image of `genInImage` at `image` uses from its start: the size in
its header, which covers the area and the stack. -/
def imageInSize (m : Module) (k n : Nat) (room : UInt64) (cap : Nat) (o : Output)
    (image : UInt64) : Nat :=
  match genInImage m k n room cap o image with
  | .ok (_, L) => L.size
  | .error _ => 0

/-- The image of `genInImage` at `image + d` has as many program instructions as the image at
`image`, under the premises of `genImageWith_shift`. -/
theorem imageInProgLength_shift {m : Module} {k n : Nat} {room : UInt64} {cap : Nat}
    {o : Output} {image d : UInt64} {bytes : List UInt8} {L : Layout}
    (hg : genInImage m k n room cap o image = .ok (bytes, L))
    (hlo : 0x40000000 ≤ (image + d).toNat) (hhi : (image + d).toNat + L.size ≤ 0x80000000) :
    imageInProgLength m k n room cap o (image + d) = imageInProgLength m k n room cap o image := by
  obtain ⟨prog, start, hp, rfl, -, hhi0, -, -, -⟩ := gen_imageWith hg
  have hsz := (layoutOf_fields image prog.length m cap room).2.2.2.2.2.2.2.2
  have hv := vecOff_ge prog.length
  have hao := areaOff_ge prog.length
  unfold tabOff at hao
  have h70 : startupLength = 70 := rfl
  have e1 : (image + UInt64.ofNat (64 + 4 * startupLength)).toNat = image.toNat + 344 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (image + d + UInt64.ofNat (64 + 4 * startupLength)).toNat =
      (image + d).toNat + 344 := by
    rw [UInt64.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hp' := genInProgram_shift hp (by rw [e1]; omega) (by rw [← add_right_comm', e2]; omega)
  rw [← add_right_comm'] at hp'
  simp only [imageInProgLength, hp, hp']

/-- `image_input_run` at every base `B` that is a multiple of 4096 and whose image lies in the RAM
GiB, given the kernel's check of the image at one base `image`: the image's bytes are the same at
both bases, and so are its program's instructions. -/
theorem image_input_run_at {m : Module} {k n : Nat} {room : UInt64} {cap : Nat} {o : Output}
    {image : UInt64} {nb len : Nat} (h : Hw) {B : UInt64} {b : Boot}
    (hk : bytesOk (genInImage m k n room cap o image) nb len = true)
    (hroom : room.toNat % 16 = 0) (hroom' : 4096 ≤ room.toNat) (himg : image.toNat % 4096 = 0)
    (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + imageInSize m k n room cap o image ≤ 0x80000000)
    (hm : ∀ j < len, b.core.mem (B + UInt64.ofNat j) = byteAt nb j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0)
    {Out : List UInt64 → List UInt8} {T : List UInt64 → UInt64 → Prop}
    (hprog : InputRuns m k n room cap o Out T) :
    (∀ ws : List UInt64, ws.length = n → h.rx.Delivers (ws.flatMap bytesOf) →
      ∃ b', BootReach h (protectedBytes B (imageInProgLength m k n room cap o image))
          (fetchFrom b.core.mem B (codeWords (imageInProgLength m k n room cap o image))) b b' ∧
        fetchFrom b.core.mem B (codeWords (imageInProgLength m k n room cap o image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
        (b'.core.out = b.core.out ++ Out ws ++ [0] ∨
          ∃ c, T ws c ∧ b'.core.out = b.core.out ++ [c.toUInt8])) ∧
    (∀ j < 8 * n, (∀ i < j, ¬ h.rx.Flagged i) → h.rx.Flagged j →
      ∃ b', BootReach h (protectedBytes B (imageInProgLength m k n room cap o image))
          (fetchFrom b.core.mem B (codeWords (imageInProgLength m k n room cap o image))) b b' ∧
        fetchFrom b.core.mem B (codeWords (imageInProgLength m k n room cap o image))
          b'.core.pc = some (encode .hvc0) ∧
        b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65]) := by
  obtain ⟨bytes, L, hg, -, -⟩ := of_bytesOk hk
  have hBd : image + (B - image) = B := by rw [UInt64.add_comm, UInt64.sub_add_cancel]
  have hd : (B - image).toNat % 4096 = 0 := by
    have := image.toNat_lt
    have := B.toNat_lt
    rw [UInt64.toNat_sub]
    omega
  have hsize : imageInSize m k n room cap o image = L.size := by simp only [imageInSize, hg]
  have hhi' : (image + (B - image)).toNat + L.size ≤ 0x80000000 := by
    rw [hBd, ← hsize]; exact hhi
  have hlo' : 0x40000000 ≤ (image + (B - image)).toNat := by rw [hBd]; exact hlo
  have hk' := bytesOkWith_shift (genInProgram_shiftsBy m k n room cap o _) hk hd hlo'
    (fun bytes' L' hg' => by
      cases hg.symm.trans hg'
      exact hhi')
  have hN := imageInProgLength_shift hg hlo' hhi'
  rw [hBd] at hk' hN
  rw [← hN]
  exact image_input_run h hk' hB hroom hroom' hm hpc hoff hio hprog

end LeanExe.A64
