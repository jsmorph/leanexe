import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.WasiStrings

/-!
The runs of the stubs of `LeanExe/A64/WasiStrings.lean` in the program's model.  `StrAt P mem p s`
states that the string `s` with its terminating zero lies at `p`, and `VectorAt P mem v strs` that
the vector at `v` holds the addresses of the strings `strs` and then 0, every byte in Normal memory
of `P` from `2^32` up and below `2^63`, where Linux places the initial stack.  A write below `2^32`
keeps both (`StrAt.frame`, `VectorAt.frame`).

`run_lenLoop` follows the loop that walks a string to its zero byte, `run_copyLoop` the loop that
copies it with its zero byte, and `run_scanLoop`, `run_pointerPass`, and `run_copyPass` the loops
over a vector, each by induction on the strings that remain.  `run_scanPiece`, `run_sizesStub`, and
`run_stringsStub` give the runs of the scan piece and of the two stubs from their entries: the
sizes stub reaches the trap stub, returns errno 61 with the memory unchanged, or returns 0 with the
count and the size stored at the guest's pointers in X0 and X1; the strings stub reaches the trap
stub or returns 0 with the strings' addresses written into the array at X0 and then the strings
into the buffer at X1.
-/

namespace LeanExe.A64

open Wasm

/-! ## Strings and vectors -/

/-- The string `str` with its terminating zero lies at `p` of the memory `mem`: each of its bytes
in Normal memory of `P`, from `2^32` up and below `2^63`, the bytes of `str`, none of them 0, and
then 0. -/
def StrAt (P : Platform) (mem : UInt64 → UInt8) : UInt64 → List UInt8 → Prop
  | p, [] => 2 ^ 32 ≤ p.toNat ∧ p.toNat < 2 ^ 63 ∧ P.normal p = true ∧ mem p = 0
  | p, c :: cs => 2 ^ 32 ≤ p.toNat ∧ p.toNat < 2 ^ 63 ∧ P.normal p = true ∧ mem p = c ∧ c ≠ 0 ∧
      StrAt P mem (p + 1) cs

/-- The eight bytes from `w` lie in Normal memory of `P`, from `2^32` up and below `2^63`. -/
def WordAt (P : Platform) (w : UInt64) : Prop :=
  2 ^ 32 ≤ w.toNat ∧ w.toNat + 8 ≤ 2 ^ 63 ∧ ∀ k < 8, P.normal (w + UInt64.ofNat k) = true

/-- The vector at `v` of the memory `mem` holds the addresses of the strings `strs` in order and
then 0, each address a word that `WordAt` admits. -/
def VectorAt (P : Platform) (mem : UInt64 → UInt8) : UInt64 → List (List UInt8) → Prop
  | v, [] => WordAt P v ∧ load64 mem v = 0
  | v, s :: rest => WordAt P v ∧ load64 mem v ≠ 0 ∧ StrAt P mem (load64 mem v) s ∧
      VectorAt P mem (v + 8) rest

/-- The bytes that `strs` take with a terminating zero each. -/
def vectorSize (strs : List (List UInt8)) : Nat := (strs.map fun s => s.length + 1).sum

/-- The four bytes of the low 32 bits of `x`, the lowest first, as `store32` stores them. -/
def word32Bytes (x : UInt64) : List UInt8 :=
  [x.toUInt8, (x >>> UInt64.ofNat 8).toUInt8, (x >>> UInt64.ofNat 16).toUInt8,
    (x >>> UInt64.ofNat 24).toUInt8]

/-- The addresses of copies of `strs` laid out one after another from `b`, each with its zero
byte, as the four bytes of each address's low 32 bits. -/
def pointerBytes : UInt64 → List (List UInt8) → List UInt8
  | _, [] => []
  | b, s :: rest => word32Bytes b ++ pointerBytes (b + UInt64.ofNat (s.length + 1)) rest

/-- The address of the vector `v` for the initial SP `sp` and the initial stack in `mem`: `sp + 8`
for the arguments, and `sp + 8 · argc + 16` for the environment, with `argc` the word at `sp`. -/
def vectorAddr (mem : UInt64 → UInt8) (sp : UInt64) : StringVector → UInt64
  | .args => sp + 8
  | .environ => sp + load64 mem sp * 8 + 16

@[simp] theorem vectorSize_nil : vectorSize [] = 0 := rfl

theorem vectorSize_cons (s : List UInt8) (rest : List (List UInt8)) :
    vectorSize (s :: rest) = s.length + 1 + vectorSize rest := by
  simp [vectorSize]

theorem length_le_vectorSize (strs : List (List UInt8)) : strs.length ≤ vectorSize strs := by
  induction strs with
  | nil => simp
  | cons s rest ih => rw [vectorSize_cons, List.length_cons]; omega

@[simp] theorem word32Bytes_length (x : UInt64) : (word32Bytes x).length = 4 := rfl

theorem pointerBytes_length : ∀ (b : UInt64) (strs : List (List UInt8)),
    (pointerBytes b strs).length = 4 * strs.length
  | _, [] => rfl
  | b, s :: rest => by
    rw [pointerBytes, List.length_append, word32Bytes_length, pointerBytes_length, List.length_cons]
    omega

theorem flatMap_zero_length (strs : List (List UInt8)) :
    (strs.flatMap (· ++ [0])).length = vectorSize strs := by
  induction strs with
  | nil => rfl
  | cons s rest ih =>
    rw [List.flatMap_cons, List.length_append, ih, vectorSize_cons, List.length_append]
    rfl

theorem writeList_append (m : UInt64 → UInt8) :
    ∀ (a : UInt64) (l1 l2 : List UInt8),
      writeList m a (l1 ++ l2) = writeList (writeList m a l1) (a + UInt64.ofNat l1.length) l2
  | a, [], l2 => by simp [writeList]
  | a, b :: l1, l2 => by
    rw [List.cons_append, writeList, writeList, writeList_append (store8 m a b) (a + 1) l1 l2,
      List.length_cons, LeanExe.Linux.succ_ofNat]

/-- A write of `bs` from `a` below a bound keeps every byte at or above it. -/
theorem writeList_low {m : UInt64 → UInt8} {a : UInt64} {bs : List UInt8} {c : UInt64} {lim : Nat}
    (ha : a.toNat + bs.length ≤ lim) (hc : lim ≤ c.toNat) : writeList m a bs c = m c :=
  writeList_other m bs a c (by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega)

theorem toNat_add_one {p : UInt64} (h : p.toNat + 1 < 2 ^ 64) : (p + 1).toNat = p.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem StrAt.frame {P : Platform} {mem mem' : UInt64 → UInt8}
    (h : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → mem' a = mem a) :
    ∀ {p : UInt64} {s : List UInt8}, StrAt P mem p s → StrAt P mem' p s
  | p, [], ⟨lo, hi, hn, hz⟩ => ⟨lo, hi, hn, by rw [h p lo]; exact hz⟩
  | p, c :: cs, ⟨lo, hi, hn, hc, h0, rest⟩ =>
    ⟨lo, hi, hn, by rw [h p lo]; exact hc, h0, StrAt.frame h rest⟩

theorem StrAt.bound {P : Platform} {mem : UInt64 → UInt8} :
    ∀ {p : UInt64} {s : List UInt8}, StrAt P mem p s → p.toNat + s.length < 2 ^ 63
  | p, [], ⟨_, hi, _⟩ => by simpa using hi
  | p, c :: cs, ⟨lo, hi, _, _, _, rest⟩ => by
    have := rest.bound
    rw [toNat_add_one (by omega)] at this
    simp only [List.length_cons]
    omega

theorem StrAt.low {P : Platform} {mem : UInt64 → UInt8} {p : UInt64} {s : List UInt8}
    (h : StrAt P mem p s) : 2 ^ 32 ≤ p.toNat := by
  cases s <;> exact h.1

theorem WordAt.byte {P : Platform} {w : UInt64} (h : WordAt P w) {k : Nat} (hk : k < 8) :
    (w + UInt64.ofNat k).toNat = w.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by have := h.2.1; omega)]

theorem WordAt.load {P : Platform} {mem mem' : UInt64 → UInt8} {w : UInt64} (hw : WordAt P w)
    (h : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → mem' a = mem a) : load64 mem' w = load64 mem w :=
  load64_congr fun k hk => h _ (by rw [hw.byte hk]; have := hw.1; omega)

theorem VectorAt.word {P : Platform} {mem : UInt64 → UInt8} {v : UInt64}
    {strs : List (List UInt8)} (h : VectorAt P mem v strs) : WordAt P v := by
  cases strs <;> exact h.1

theorem VectorAt.frame {P : Platform} {mem mem' : UInt64 → UInt8}
    (h : ∀ a : UInt64, 2 ^ 32 ≤ a.toNat → mem' a = mem a) :
    ∀ {v : UInt64} {strs : List (List UInt8)}, VectorAt P mem v strs → VectorAt P mem' v strs
  | v, [], ⟨hw, hz⟩ => ⟨hw, by rw [hw.load h]; exact hz⟩
  | v, s :: rest, ⟨hw, hz, hs, hr⟩ =>
    ⟨hw, by rw [hw.load h]; exact hz, by rw [hw.load h]; exact StrAt.frame h hs,
      VectorAt.frame h hr⟩

/-- The bytes `s ++ [0]` that `readList` reads from `p`, in Normal memory, from `2^32` up and below
`2^63`, with no 0 in `s`, are a string that `StrAt` admits. -/
theorem strAt_of_readList {P : Platform} {mem : UInt64 → UInt8} :
    ∀ (s : List UInt8) (p : UInt64), readList mem p (s.length + 1) = s ++ [0] → 0 ∉ s →
      2 ^ 32 ≤ p.toNat → p.toNat + s.length < 2 ^ 63 →
      (∀ j ≤ s.length, P.normal (p + UInt64.ofNat j) = true) → StrAt P mem p s
  | [], p, hr, _, hlo, hhi, hn => by
    simp only [List.length_nil, readList, List.nil_append, List.cons.injEq,
      and_true] at hr
    exact ⟨hlo, by simpa using hhi, by simpa [add_ofNat_zero] using hn 0 (by simp), hr⟩
  | c :: cs, p, hr, h0, hlo, hhi, hn => by
    simp only [List.length_cons, readList, List.cons_append, List.cons.injEq] at hr hhi
    have hp1 : (p + 1).toNat = p.toNat + 1 := toNat_add_one (by omega)
    refine ⟨hlo, by omega, by simpa [add_ofNat_zero] using hn 0 (by simp), hr.1,
      fun e => h0 (by rw [← e]; exact List.mem_cons_self), strAt_of_readList cs (p + 1) hr.2
        (fun h => h0 (List.mem_cons_of_mem _ h)) (by omega) (by rw [hp1]; omega)
        (fun j hj => by
          rw [LeanExe.Linux.succ_ofNat]
          exact hn (j + 1) (by simp only [List.length_cons]; omega))⟩

/-- A vector whose word `j + i` above `sp` holds the address of the string `strs[i]`, with every
word and string from `sp` up and below `top`, and a 0 after the strings' addresses, is one that
`VectorAt` admits from its word `j`, on a platform that maps the bytes from `sp` to `top` as
Normal memory. -/
theorem vectorAt_of {P : Platform} {mem : UInt64 → UInt8} {sp top : UInt64}
    (hsp : 2 ^ 32 ≤ sp.toNat) (htop : top.toNat < 2 ^ 63)
    (hP : ∀ a : UInt64, sp.toNat ≤ a.toNat → a.toNat < top.toNat → P.normal a = true) :
    ∀ (strs : List (List UInt8)) (j : Nat), sp.toNat + 8 * (j + strs.length + 1) ≤ top.toNat →
      (∀ i (h : i < strs.length),
        sp.toNat ≤ (load64 mem (sp + UInt64.ofNat (8 * (j + i)))).toNat ∧
        (load64 mem (sp + UInt64.ofNat (8 * (j + i)))).toNat + strs[i].length + 1 ≤
          top.toNat ∧ 0 ∉ strs[i] ∧
        readList mem (load64 mem (sp + UInt64.ofNat (8 * (j + i)))) (strs[i].length + 1) =
          strs[i] ++ [0]) →
      load64 mem (sp + UInt64.ofNat (8 * (j + strs.length))) = 0 →
      VectorAt P mem (sp + UInt64.ofNat (8 * j)) strs := by
  have word : ∀ j : Nat, sp.toNat + 8 * (j + 1) ≤ top.toNat →
      WordAt P (sp + UInt64.ofNat (8 * j)) ∧
        (sp + UInt64.ofNat (8 * j)).toNat = sp.toNat + 8 * j := by
    intro j hj
    have e : (sp + UInt64.ofNat (8 * j)).toNat = sp.toNat + 8 * j := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    refine ⟨⟨by omega, by omega, fun k hk => hP _ ?_ ?_⟩, e⟩ <;>
    · rw [UInt64.toNat_add, e, UInt64.toNat_ofNat']
      omega
  intro strs
  induction strs with
  | nil =>
    intro j hb _ hz
    exact ⟨(word j (by simpa using hb)).1, by simpa using hz⟩
  | cons s rest ih =>
    intro j hb hs hz
    simp only [List.length_cons] at hb
    obtain ⟨hw, he⟩ := word j (by omega)
    obtain ⟨plo, phi, p0, pr⟩ := hs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at plo phi p0 pr
    refine ⟨hw, fun e => by rw [e] at plo; simp at plo; omega,
      strAt_of_readList s _ pr p0 (by omega) (by omega) (fun k hk => hP _ ?_ ?_), ?_⟩
    · rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    · rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      omega
    · rw [show sp + UInt64.ofNat (8 * j) + 8 = sp + UInt64.ofNat (8 * (j + 1)) by
        rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, add_ofNat_add]; congr 2]
      refine ih (j + 1) (by omega) (fun i hi => ?_) ?_
      · have := hs (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rwa [show j + 1 + i = j + (i + 1) by omega]
      · rw [show j + 1 + rest.length = j + (s :: rest).length by simp; omega]
        exact hz

/-! ## The generators' parts -/

theorem scanPiece_ok {a ov : UInt64} {is : List Instr} (hg : scanPiece a ov = .ok is) :
    ∃ f5 f11 f13 f14, cbField (after a 5) (after a 15) = .ok f5 ∧
      cbField (after a 11) (after a 8) = .ok f11 ∧ cbField (after a 13) ov = .ok f13 ∧
      bField (after a 14) (after a 4) = .ok f14 ∧
      is = [.orrReg 11 31 9, .movz 12 0 0, .movz 13 0 0, .movz 10 1 2, .ldr 14 11 0, .cbz 14 f5,
        .addImm 11 11 8, .addImm 12 12 1, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1,
        .cbnz 15 f11, .subsReg 31 13 10, .bcond 2 f13, .b f14] := by
  unfold scanPiece at hg
  cases h1 : cbField (after a 5) (after a 15) with
  | error e => simp [h1, bind, Except.bind] at hg
  | ok f5 =>
  cases h2 : cbField (after a 11) (after a 8) with
  | error e => simp [h1, h2, bind, Except.bind] at hg
  | ok f11 =>
  cases h3 : cbField (after a 13) ov with
  | error e => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok f13 =>
  cases h4 : bField (after a 14) (after a 4) with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok f14 =>
  simp only [h1, h2, h3, h4, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨f5, f11, f13, f14, rfl, rfl, rfl, rfl, hg.symm⟩

/-! ## Steps -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A step of `LDRB Wt, [Xn]` of a byte of Normal memory, with a base other than SP. -/
theorem step_ldrb {s : State} {t n : Fin 32} (ht : t.val < 31) (hn : n.val < 31)
    (hc : code s.pc = some (encode (.ldrb t n 0))) (hmap : P.normal (s.x n) = true) :
    ∃ u, Reach P code s u ∧ u.pc = s.pc + 4 ∧ u.x t = (s.mem (s.x n)).toUInt64 ∧
      (∀ q : Fin 32, q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io := by
  have e : s.x n + UInt64.ofNat (0 : Fin 4096).val = s.x n := add_ofNat_zero _
  have he := exec_ldrb_base P (s := s) (t := t) (imm := 0) hn (by rw [e]; exact hmap)
  rw [e] at he
  exact step_setX P code ht hc he

/-- A step of `MADD Xd, Xn, Xm, Xa`. -/
theorem step_madd {s : State} {d n m r : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.madd d n m r))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x r + s.x n * s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `ADD Xd, Xn, #k` with registers other than SP and the immediate's value `k`. -/
theorem step_addK {s : State} {d n : Fin 32} {imm : Fin 4096} {k : Nat} (hd : d.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.addImm d n imm))) (hk : imm.val = k) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n + UInt64.ofNat k ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  subst hk
  exact step_addImm P code hd hn hc

/-- `SUBS XZR, Xx, Xy` and `B.HS` at `a`: the run reaches `tB` when `Xx` lies at or above `Xy` and
the next instruction otherwise, changing the flags alone. -/
theorem run_hsReg {a tB : UInt64} {g : Fin 524288} {x y : Fin 32}
    (hcode : CodeAt code a [.subsReg 31 x y, .bcond 2 g]) (hg : cbField (after a 1) tB = .ok g)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x y ≤ s.x x then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x x) (s.x y) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsReg 31 x y) s = some s1 := rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 2 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 2 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_succ, after_zero]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x x - s.x y)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 2 = decide (s.x y ≤ s.x x) := by
    rw [condHolds_2]
    rfl
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 2 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x y ≤ s.x x
    · rw [ite_eq_left (by simpa using h), ite_eq_left h]
      exact cbField_target hg
    · rw [ite_eq_right (by simpa using h), ite_eq_right h, ← after_succ]
  · show (s.setX 31 (s.x x - s.x y)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x x - s.x y)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x x - s.x y)).io = _
    exact State.setX_io

/-! ## The loops over a string -/

theorem toUInt64_ne_zero {c : UInt8} (h : c ≠ 0) : c.toUInt64 ≠ 0 := by
  intro e
  apply h
  apply UInt8.toNat_inj.mp
  have := congrArg UInt64.toNat e
  simpa using this

/-- The loop that walks the string at X14 to its zero byte, from `a`: X14 and X13 advance by the
string's length plus one, and X15 ends at 0. -/
theorem run_lenLoop {a : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 g])
    (hg : cbField (after a 3) a = .ok g) :
    ∀ (str : List UInt8) (s : State), s.pc = a → StrAt P s.mem (s.x 14) str →
      ∃ t, Reach P code s t ∧ t.pc = after a 4 ∧
        t.x 14 = s.x 14 + UInt64.ofNat (str.length + 1) ∧
        t.x 13 = s.x 13 + UInt64.ofNat (str.length + 1) ∧
        (∀ q : Fin 32, q ≠ 13 → q ≠ 14 → q ≠ 15 → t.x q = s.x q) ∧ t.sp = s.sp ∧
        t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  intro str
  induction str with
  | nil =>
    intro s hpc ⟨_, _, hn, hz⟩
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldrb P code (s := s) (t := 15) (n := 14)
      (by decide) (by decide) (by rw [hpc]; exact c0) hn
    have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addK P code (s := u1) (d := 14) (n := 14)
      (k := 1) (by decide) (by decide) (by rw [q1]; exact c1) rfl
    have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 13) (n := 13)
      (k := 1) (by decide) (by decide) (by rw [q2]; exact c2) rfl
    have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
    obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_cbnz P code (s := u3) (r := 15) (target := a)
      (by rw [q3]; exact c3) (by rw [q3]; exact cbField_target hg)
    have hz3 : u3.x 15 = 0 := by rw [k3 15 (by decide), k2 15 (by decide), x1, hz]; rfl
    rw [ite_eq_right (by simpa using hz3), q3, ← after_succ] at p4
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), p4, ?_, ?_, ?_, by rw [sp4, sp3, sp2, sp1],
      by rw [m4, m3, m2, m1], by rw [io4, io3, io2, io1]⟩
    · rw [k4, k3 14 (by decide), x2, k1 14 (by decide)]
      rfl
    · rw [k4, x3, k2 13 (by decide), k1 13 (by decide)]
      rfl
    · intro q h13 h14 h15
      rw [k4, k3 q h13, k2 q h14, k1 q h15]
  | cons c cs ih =>
    intro s hpc ⟨_, _, hn, hc, h0, hrest⟩
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldrb P code (s := s) (t := 15) (n := 14)
      (by decide) (by decide) (by rw [hpc]; exact c0) hn
    have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addK P code (s := u1) (d := 14) (n := 14)
      (k := 1) (by decide) (by decide) (by rw [q1]; exact c1) rfl
    have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 13) (n := 13)
      (k := 1) (by decide) (by decide) (by rw [q2]; exact c2) rfl
    have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
    obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_cbnz P code (s := u3) (r := 15) (target := a)
      (by rw [q3]; exact c3) (by rw [q3]; exact cbField_target hg)
    have hnz : u3.x 15 ≠ 0 := by
      rw [k3 15 (by decide), k2 15 (by decide), x1, hc]
      exact toUInt64_ne_zero h0
    rw [ite_eq_left hnz] at p4
    have x14 : u4.x 14 = s.x 14 + 1 := by
      rw [k4, k3 14 (by decide), x2, k1 14 (by decide)]
      rfl
    have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
    obtain ⟨t, rt, pt, t14, t13, kt, spt, mt, iot⟩ :=
      ih u4 p4 (by rw [x14, hm4]; exact hrest)
    refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans rt))), pt, ?_, ?_, ?_,
      by rw [spt, sp4, sp3, sp2, sp1], by rw [mt, hm4], by rw [iot, io4, io3, io2, io1]⟩
    · rw [t14, x14, LeanExe.Linux.succ_ofNat, List.length_cons]
    · rw [t13, k4, x3, k2 13 (by decide), k1 13 (by decide), List.length_cons]
      show s.x 13 + UInt64.ofNat 1 + UInt64.ofNat (cs.length + 1) = _
      rw [add_ofNat_add, Nat.add_comm 1]
    · intro q h13 h14 h15
      rw [kt q h13 h14 h15, k4, k3 q h13, k2 q h14, k1 q h15]

/-- The loop that copies the string at X14 with its zero byte to the bytes from X16 plus 4,092,
from `a`, when they lie below `2^32` in Normal memory: X14 and X16 advance by the string's length
plus one. -/
theorem run_copyLoop {a : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.ldrb 15 14 0, .strb 15 16 4092, .addImm 14 14 1, .addImm 16 16 1,
      .cbnz 15 g])
    (hg : cbField (after a 4) a = .ok g) (hU : P.normal P.uart = false) :
    ∀ (str : List UInt8) (s : State), s.pc = a → StrAt P s.mem (s.x 14) str →
      (s.x 16 + UInt64.ofNat 4092).toNat + str.length + 1 ≤ 2 ^ 32 →
      (∀ j ≤ str.length, P.normal (s.x 16 + UInt64.ofNat 4092 + UInt64.ofNat j) = true) →
      ∃ t, Reach P code s t ∧ t.pc = after a 5 ∧
        t.x 14 = s.x 14 + UInt64.ofNat (str.length + 1) ∧
        t.x 16 = s.x 16 + UInt64.ofNat (str.length + 1) ∧
        (∀ q : Fin 32, q ≠ 14 → q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧ t.sp = s.sp ∧
        t.io = s.io ∧ t.mem = writeList s.mem (s.x 16 + UInt64.ofNat 4092) (str ++ [0]) := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  have c4 := hcode 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4
  -- the first four steps, common to both cases
  have head : ∀ (s : State), s.pc = a → P.normal (s.x 14) = true →
      P.normal (s.x 16 + UInt64.ofNat 4092) = true →
      ∃ u, Reach P code s u ∧ u.pc = after a 4 ∧ u.x 15 = (s.mem (s.x 14)).toUInt64 ∧
        u.x 14 = s.x 14 + 1 ∧ u.x 16 = s.x 16 + 1 ∧
        (∀ q : Fin 32, q ≠ 14 → q ≠ 15 → q ≠ 16 → u.x q = s.x q) ∧ u.sp = s.sp ∧
        u.io = s.io ∧ u.mem = store8 s.mem (s.x 16 + UInt64.ofNat 4092) (s.mem (s.x 14)) := by
    intro s hpc hn hd
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldrb P code (s := s) (t := 15) (n := 14)
      (by decide) (by decide) (by rw [hpc]; exact c0) hn
    have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, k2, sp2, io2, m2⟩ := step_strb P code (s := u1) (t := 15) (n := 16)
      (imm := 4092) (k := 4092) (addr := s.x 16 + UInt64.ofNat 4092) (by decide)
      (by rw [q1]; exact c1) rfl (by rw [k1 16 (by decide)]) hd hU
    have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 14) (n := 14)
      (k := 1) (by decide) (by decide) (by rw [q2]; exact c2) rfl
    have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addK P code (s := u3) (d := 16) (n := 16)
      (k := 1) (by decide) (by decide) (by rw [q3]; exact c3) rfl
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), by rw [p4, q3, ← after_succ], ?_, ?_, ?_, ?_,
      by rw [sp4, sp3, sp2, sp1], by rw [io4, io3, io2, io1], ?_⟩
    · rw [k4 15 (by decide), k3 15 (by decide), k2, x1]
    · rw [k4 14 (by decide), x3, k2, k1 14 (by decide)]
      rfl
    · rw [x4, k3 16 (by decide), k2, k1 16 (by decide)]
      rfl
    · intro q h14 h15 h16
      rw [k4 q h16, k3 q h14, k2, k1 q h15]
    · rw [m4, m3, m2, x1, m1, UInt8.toUInt8_toUInt64]
  intro str
  induction str with
  | nil =>
    intro s hpc ⟨_, _, hn, hz⟩ _ hnd
    obtain ⟨u, r, p, x15, x14, x16, k, sp, io, m⟩ := head s hpc hn
      (by simpa [add_ofNat_zero] using hnd 0 (by simp))
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbnz P code (s := u) (r := 15) (target := a)
      (by rw [p]; exact c4) (by rw [p]; exact cbField_target hg)
    rw [ite_eq_right (by rw [x15, hz]; simp), p, ← after_succ] at p5
    refine ⟨u5, r.trans r5, p5, by rw [k5, x14]; rfl, by rw [k5, x16]; rfl,
      fun q h14 h15 h16 => by rw [k5, k q h14 h15 h16], by rw [sp5, sp], by rw [io5, io], ?_⟩
    rw [m5, m, hz]
    rfl
  | cons c cs ih =>
    intro s hpc ⟨lo, hi, hn, hc, h0, hrest⟩ hb hnd
    obtain ⟨u, r, p, x15, x14, x16, k, sp, io, m⟩ := head s hpc hn
      (by simpa [add_ofNat_zero] using hnd 0 (by simp))
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbnz P code (s := u) (r := 15) (target := a)
      (by rw [p]; exact c4) (by rw [p]; exact cbField_target hg)
    rw [ite_eq_left (by rw [x15, hc]; exact toUInt64_ne_zero h0)] at p5
    have hd : (s.x 16 + UInt64.ofNat 4092).toNat < 2 ^ 32 := by
      simp only [List.length_cons] at hb
      omega
    have hframe : ∀ b : UInt64, 2 ^ 32 ≤ b.toNat → u5.mem b = s.mem b := by
      intro b hb'
      rw [m5, m]
      unfold store8
      rw [ite_eq_right (fun e => by subst e; omega)]
    have u16 : u5.x 16 + UInt64.ofNat 4092 = s.x 16 + UInt64.ofNat 4092 + 1 := by
      rw [k5, x16, UInt64.add_assoc, UInt64.add_comm 1, ← UInt64.add_assoc]
    have hd1 : (s.x 16 + UInt64.ofNat 4092 + 1).toNat =
        (s.x 16 + UInt64.ofNat 4092).toNat + 1 := toNat_add_one (by omega)
    obtain ⟨t, rt, pt, t14, t16, kt, spt, iot, mt⟩ := ih u5 p5
      (by rw [k5, x14]; exact StrAt.frame hframe hrest)
      (by rw [u16, hd1]; simp only [List.length_cons] at hb; omega)
      (fun j hj => by
        rw [u16, LeanExe.Linux.succ_ofNat]
        exact hnd (j + 1) (by simp only [List.length_cons]; omega))
    refine ⟨t, r.trans (r5.trans rt), pt, ?_, ?_, fun q h14 h15 h16 => ?_,
      by rw [spt, sp5, sp], by rw [iot, io5, io], ?_⟩
    · rw [t14, k5, x14, LeanExe.Linux.succ_ofNat, List.length_cons]
    · rw [t16, k5, x16, LeanExe.Linux.succ_ofNat, List.length_cons]
    · rw [kt q h14 h15 h16, k5, k q h14 h15 h16]
    · rw [mt, u16, m5, m, hc, List.cons_append, writeList]

/-! ## The loops over a vector -/

theorem ofNat_eight : UInt64.ofNat 8 = 8 := rfl

/-- A word that a vector's run loads: the vector's word at `v`, from X11, into X14. -/
theorem step_vectorWord {s : State} (hc : code s.pc = some (encode (.ldr 14 11 0)))
    (hw : WordAt P (s.x 11)) :
    ∃ u, Reach P code s u ∧ u.pc = s.pc + 4 ∧ u.x 14 = load64 s.mem (s.x 11) ∧
      (∀ q : Fin 32, q ≠ 14 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io := by
  obtain ⟨u, r, p, x, k, sp, m, io⟩ := step_ldr P code (s := s) (t := 14) (n := 11) (i := 0)
    (by decide) (by decide) (by decide) hc (fun k hk => by simpa using hw.2.2 k hk)
  exact ⟨u, r, p, by rw [x, Nat.mul_zero, add_ofNat_zero], k, sp, m, io⟩

/-- The loop of the scan piece from its head at `after a 4`, with the strings `strs` of the vector
at X11 left, `i` strings counted in X12, and the sum `S` of their sizes in X13: the loop reaches
the piece's end with the count and the sum of all of them when the sum stays below `2^32`, and
`ov` otherwise. -/
theorem run_scanLoop {a ov : UInt64} {f5 f11 f13 : Fin 524288} {f14 : Fin 67108864}
    (hcode : CodeAt code (after a 4) [.ldr 14 11 0, .cbz 14 f5, .addImm 11 11 8, .addImm 12 12 1,
      .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f11, .subsReg 31 13 10,
      .bcond 2 f13, .b f14])
    (h5 : cbField (after a 5) (after a 15) = .ok f5)
    (h11 : cbField (after a 11) (after a 8) = .ok f11) (h13 : cbField (after a 13) ov = .ok f13)
    (h14 : bField (after a 14) (after a 4) = .ok f14) :
    ∀ (strs : List (List UInt8)) (s : State) (i S : Nat), s.pc = after a 4 →
      s.x 10 = 4294967296 → s.x 12 = UInt64.ofNat i → s.x 13 = UInt64.ofNat S → S < 2 ^ 32 →
      VectorAt P s.mem (s.x 11) strs →
      ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
        (∀ q : Fin 32, q ≠ 11 → q ≠ 12 → q ≠ 13 → q ≠ 14 → q ≠ 15 → t.x q = s.x q) ∧
        if S + vectorSize strs < 2 ^ 32 then
          t.pc = after a 15 ∧ t.x 12 = UInt64.ofNat (i + strs.length) ∧
            t.x 13 = UInt64.ofNat (S + vectorSize strs)
        else t.pc = ov := by
  have c := fun k (hk : k < 11) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c10 := c 10 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c0 c1 c2 c3 c10
  have cLen : CodeAt code (after a 8)
      [.ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f11] := by
    simpa [after_after] using CodeAt.drop_take code hcode 4 4 (by simp)
  have cHs : CodeAt code (after a 12) [.subsReg 31 13 10, .bcond 2 f13] := by
    simpa [after_after] using CodeAt.drop_take code hcode 8 2 (by simp)
  intro strs
  induction strs with
  | nil =>
    intro s i S hpc hx10 hx12 hx13 hS ⟨hw, hz⟩
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after a 5 := by rw [p1, hpc, ← after_succ]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after a 15) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h5)
    rw [ite_eq_left (by rw [x1, hz])] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1],
      fun q _ _ _ h14 _ => by rw [k2, k1 q h14], ?_⟩
    rw [vectorSize_nil, Nat.add_zero, ite_eq_left hS]
    refine ⟨p2, ?_, ?_⟩
    · rw [k2, k1 12 (by decide), hx12, List.length_nil, Nat.add_zero]
    · rw [k2, k1 13 (by decide), hx13]
  | cons str rest ih =>
    intro s i S hpc hx10 hx12 hx13 hS ⟨hw, hnz, hstr, hrest⟩
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after a 5 := by rw [p1, hpc, ← after_succ]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after a 15) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h5)
    rw [ite_eq_right (by rw [x1]; exact hnz), q1, ← after_succ] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 11) (n := 11)
      (k := 8) (by decide) (by decide) (by rw [p2]; exact c2) rfl
    have q3 : u3.pc = after a 7 := by rw [p3, p2, ← after_succ]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addK P code (s := u3) (d := 12) (n := 12)
      (k := 1) (by decide) (by decide) (by rw [q3]; exact c3) rfl
    have q4 : u4.pc = after a 8 := by rw [p4, q3, ← after_succ]
    have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
    have u4x14 : u4.x 14 = load64 s.mem (s.x 11) := by
      rw [k4 14 (by decide), k3 14 (by decide), k2, x1]
    obtain ⟨u5, r5, p5, x14', x13', k5, sp5, m5, io5⟩ := run_lenLoop P code cLen
      (by rw [after_after]; exact h11) str u4 q4 (by rw [u4x14, hm4]; exact hstr)
    have hlen := hstr.bound
    have hlo := hstr.low
    have u5x13 : u5.x 13 = UInt64.ofNat (S + (str.length + 1)) := by
      rw [x13', k4 13 (by decide), k3 13 (by decide), k2, k1 13 (by decide), hx13,
        ← UInt64.ofNat_add]
    have u5x10 : u5.x 10 = 4294967296 := by
      rw [k5 10 (by decide) (by decide) (by decide), k4 10 (by decide), k3 10 (by decide), k2,
        k1 10 (by decide), hx10]
    obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := run_hsReg P code cHs
      (by rw [after_after]; exact h13) (by rw [p5, after_after])
    have hS' : (UInt64.ofNat (S + (str.length + 1))).toNat = S + (str.length + 1) :=
      UInt64.toNat_ofNat_of_lt' (show S + (str.length + 1) < 2 ^ 64 by omega)
    have hr6 : Reach P code s u6 := r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))
    have hkeep6 : ∀ q : Fin 32, q ≠ 11 → q ≠ 12 → q ≠ 13 → q ≠ 14 → q ≠ 15 → u6.x q = s.x q :=
      fun q h11 h12 h13 h14 h15 => by
        rw [k6, k5 q h13 h14 h15, k4 q h12, k3 q h11, k2, k1 q h14]
    by_cases hbig : 2 ^ 32 ≤ S + (str.length + 1)
    · have hle : u5.x 10 ≤ u5.x 13 := by
        rw [UInt64.le_iff_toNat_le, u5x10, u5x13, hS']
        exact hbig
      rw [ite_eq_left hle] at p6
      refine ⟨u6, hr6, by rw [sp6, sp5, sp4, sp3, sp2, sp1], by rw [m6, m5, hm4],
        by rw [io6, io5, io4, io3, io2, io1], hkeep6, ?_⟩
      rw [ite_eq_right (by rw [vectorSize_cons]; omega)]
      exact p6
    · have hnle : ¬ u5.x 10 ≤ u5.x 13 := by
        rw [UInt64.le_iff_toNat_le, u5x10, u5x13, hS']
        exact hbig
      rw [ite_eq_right hnle] at p6
      obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_b P code (s := u6) (target := after a 4)
        (by rw [p6, after_after]; exact c10) (by rw [p6, after_after]; exact bField_target h14)
      have u7x11 : u7.x 11 = s.x 11 + 8 := by
        rw [k7, k6, k5 11 (by decide) (by decide) (by decide), k4 11 (by decide), x3, k2,
          k1 11 (by decide), ofNat_eight]
      have u7x12 : u7.x 12 = UInt64.ofNat (i + 1) := by
        rw [k7, k6, k5 12 (by decide) (by decide) (by decide), x4, k3 12 (by decide), k2,
          k1 12 (by decide), hx12, ← UInt64.ofNat_add]
      have hm7 : u7.mem = s.mem := by rw [m7, m6, m5, hm4]
      obtain ⟨t, rt, spt, mt, iot, kt, ht⟩ := ih u7 (i + 1) (S + (str.length + 1)) p7
        (by rw [k7, k6, u5x10]) u7x12 (by rw [k7, k6, u5x13]) (by omega)
        (by rw [u7x11, hm7]; exact hrest)
      refine ⟨t, hr6.trans (r7.trans rt), by rw [spt, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
        by rw [mt, hm7], by rw [iot, io7, io6, io5, io4, io3, io2, io1],
        fun q h11 h12 h13 h14 h15 => by
          rw [kt q h11 h12 h13 h14 h15, k7, hkeep6 q h11 h12 h13 h14 h15],
        ?_⟩
      have e1 : S + (str.length + 1) + vectorSize rest = S + vectorSize (str :: rest) := by
        rw [vectorSize_cons]; omega
      have e2 : i + 1 + rest.length = i + (str :: rest).length := by
        rw [List.length_cons]; omega
      rw [e1, e2] at ht
      exact ht

/-- Bytes written below `2^32` keep every byte from `2^32` up. -/
theorem writeList_frame {m : UInt64 → UInt8} {d : UInt64} {bs : List UInt8}
    (hd : d.toNat + bs.length ≤ 2 ^ 32) :
    ∀ b : UInt64, 2 ^ 32 ≤ b.toNat → writeList m d bs b = m b :=
  fun _ hb => writeList_low hd hb

/-- The loop of the pass that writes the strings' addresses, from its head `h`, with the strings
`strs` of the vector at X11 left, the next string's address in X13, and the next entry of the
array at X16 plus 4,092: each entry receives the low 32 bits of X13, which advances by each
string's size. -/
theorem run_pointerLoop {h : UInt64} {f1 f14 : Fin 524288} {f15 : Fin 67108864}
    (hcode : CodeAt code h ([.ldr 14 11 0, .cbz 14 f1, .addImm 11 11 8] ++ store32 13 15 ++
      [.addImm 16 16 4, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f14, .b f15]))
    (h1 : cbField (after h 1) (after h 16) = .ok f1)
    (h14 : cbField (after h 14) (after h 11) = .ok f14) (h15 : bField (after h 15) h = .ok f15)
    (hU : P.normal P.uart = false) :
    ∀ (strs : List (List UInt8)) (s : State), s.pc = h → VectorAt P s.mem (s.x 11) strs →
      (s.x 16 + UInt64.ofNat 4092).toNat + 4 * strs.length ≤ 2 ^ 32 →
      (∀ j < 4 * strs.length, P.normal (s.x 16 + UInt64.ofNat 4092 + UInt64.ofNat j) = true) →
      ∃ t, Reach P code s t ∧ t.pc = after h 16 ∧
        (∀ q : Fin 32, q ≠ 11 → q ≠ 13 → q ≠ 14 → q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧
        t.sp = s.sp ∧ t.io = s.io ∧
        t.mem = writeList s.mem (s.x 16 + UInt64.ofNat 4092) (pointerBytes (s.x 13) strs) := by
  have c := fun k (hk : k < 16) => hcode k (by simpa [store32] using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c10 := c 10 (by omega)
  have c15 := c 15 (by omega)
  simp only [store32, List.cons_append, List.nil_append, List.getElem_cons_zero,
    List.getElem_cons_succ, after_zero] at c0 c1 c2 c10 c15
  have cS : CodeAt code (after h 3) (store32 13 15) := by
    simpa [store32] using CodeAt.drop_take code hcode 3 7 (by simp [store32])
  have cLen : CodeAt code (after h 11)
      [.ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f14] := by
    simpa [store32] using CodeAt.drop_take code hcode 11 4 (by simp [store32])
  intro strs
  induction strs with
  | nil =>
    intro s hpc ⟨hw, hz⟩ _ _
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after h 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after h 16) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h1)
    rw [ite_eq_left (by rw [x1, hz])] at p2
    exact ⟨u2, r1.trans r2, p2, fun q _ _ h14 _ _ => by rw [k2, k1 q h14], by rw [sp2, sp1],
      by rw [io2, io1], by rw [m2, m1]; rfl⟩
  | cons str rest ih =>
    intro s hpc ⟨hw, hnz, hstr, hrest⟩ hb hn
    simp only [List.length_cons] at hb hn
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after h 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after h 16) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h1)
    rw [ite_eq_right (by rw [x1]; exact hnz), q1, ← after_succ] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 11) (n := 11)
      (k := 8) (by decide) (by decide) (by rw [p2]; exact c2) rfl
    have q3 : u3.pc = after h 3 := by rw [p3, p2, ← after_succ]
    have u3x16 : u3.x 16 = s.x 16 := by rw [k3 16 (by decide), k2, k1 16 (by decide)]
    have u3x13 : u3.x 13 = s.x 13 := by rw [k3 13 (by decide), k2, k1 13 (by decide)]
    obtain ⟨u4, r4, p4, sp4, io4, k4, m4⟩ := run_strb4 P code (v := 13) (t := 15) (s := u3)
      (by decide) (by decide) (by decide) cS q3
      (fun k hk => by rw [u3x16, ← add_ofNat_add]; exact hn k (by omega)) hU
    have hm3 : u3.mem = s.mem := by rw [m3, m2, m1]
    have hm4 : u4.mem = writeList s.mem (s.x 16 + UInt64.ofNat 4092) (word32Bytes (s.x 13)) := by
      rw [m4, u3x16, u3x13, hm3]
      rfl
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_addK P code (s := u4) (d := 16) (n := 16)
      (k := 4) (by decide) (by decide) (by rw [p4, after_after]; exact c10) rfl
    have q5 : u5.pc = after h 11 := by rw [p5, p4, after_after, ← after_succ]
    have hd : (s.x 16 + UInt64.ofNat 4092).toNat + 4 ≤ 2 ^ 32 := by omega
    have hframe5 : ∀ b : UInt64, 2 ^ 32 ≤ b.toNat → u5.mem b = s.mem b := by
      intro b hb'
      rw [m5, hm4]
      exact writeList_frame hd b hb'
    have u5x14 : u5.x 14 = load64 s.mem (s.x 11) := by
      rw [k5 14 (by decide), k4 14 (by decide), k3 14 (by decide), k2, x1]
    obtain ⟨u6, r6, p6, x14', x13', k6, sp6, m6, io6⟩ := run_lenLoop P code cLen
      (by rw [after_after]; exact h14) str u5 q5
      (by rw [u5x14]; exact StrAt.frame hframe5 hstr)
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_b P code (s := u6) (target := h)
      (by rw [p6, after_after]; exact c15) (by rw [p6, after_after]; exact bField_target h15)
    have u7x16 : u7.x 16 = s.x 16 + 4 := by
      rw [k7, k6 16 (by decide) (by decide) (by decide), x5, k4 16 (by decide), u3x16]
      rfl
    have u7x13 : u7.x 13 = s.x 13 + UInt64.ofNat (str.length + 1) := by
      rw [k7, x13', k5 13 (by decide), k4 13 (by decide), u3x13]
    have u7x11 : u7.x 11 = s.x 11 + 8 := by
      rw [k7, k6 11 (by decide) (by decide) (by decide), k5 11 (by decide), k4 11 (by decide), x3,
        k2, k1 11 (by decide)]
      rfl
    have hm7 : u7.mem = u5.mem := by rw [m7, m6]
    have hd7 : u7.x 16 + UInt64.ofNat 4092 = s.x 16 + UInt64.ofNat 4092 + UInt64.ofNat 4 := by
      rw [u7x16, UInt64.add_assoc, UInt64.add_comm 4, ← UInt64.add_assoc]
      rfl
    have hd7n : (u7.x 16 + UInt64.ofNat 4092).toNat = (s.x 16 + UInt64.ofNat 4092).toNat + 4 := by
      rw [hd7, UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 4 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)]
    obtain ⟨t, rt, pt, kt, spt, iot, mt⟩ := ih u7 p7
      (by rw [u7x11, hm7]; exact VectorAt.frame hframe5 hrest)
      (by rw [hd7n]; omega)
      (fun j hj => by rw [hd7, add_ofNat_add]; exact hn (4 + j) (by omega))
    refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans rt)))))),
      pt, fun q h11 h13 h14 h15 h16 => ?_, by rw [spt, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
      by rw [iot, io7, io6, io5, io4, io3, io2, io1], ?_⟩
    · rw [kt q h11 h13 h14 h15 h16, k7, k6 q h13 h14 h15, k5 q h16, k4 q h15, k3 q h11, k2,
        k1 q h14]
    · rw [mt, hm7, m5, hm4, hd7, u7x13, pointerBytes, writeList_append, word32Bytes_length]

/-- The loop of the pass that copies the strings, from its head `h`, with the strings `strs` of the
vector at X11 left and the next byte of the buffer at X16 plus 4,092: the buffer receives each
string with its zero byte. -/
theorem run_copyPass {h : UInt64} {f1 f7 : Fin 524288} {f8 : Fin 67108864}
    (hcode : CodeAt code h [.ldr 14 11 0, .cbz 14 f1, .addImm 11 11 8, .ldrb 15 14 0,
      .strb 15 16 4092, .addImm 14 14 1, .addImm 16 16 1, .cbnz 15 f7, .b f8])
    (h1 : cbField (after h 1) (after h 9) = .ok f1) (h7 : cbField (after h 7) (after h 3) = .ok f7)
    (h8 : bField (after h 8) h = .ok f8) (hU : P.normal P.uart = false) :
    ∀ (strs : List (List UInt8)) (s : State), s.pc = h → VectorAt P s.mem (s.x 11) strs →
      (s.x 16 + UInt64.ofNat 4092).toNat + vectorSize strs ≤ 2 ^ 32 →
      (∀ j < vectorSize strs, P.normal (s.x 16 + UInt64.ofNat 4092 + UInt64.ofNat j) = true) →
      ∃ t, Reach P code s t ∧ t.pc = after h 9 ∧
        (∀ q : Fin 32, q ≠ 11 → q ≠ 14 → q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧
        t.sp = s.sp ∧ t.io = s.io ∧
        t.mem = writeList s.mem (s.x 16 + UInt64.ofNat 4092) (strs.flatMap (· ++ [0])) := by
  have c := fun k (hk : k < 9) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c8 := c 8 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c8
  have cCopy : CodeAt code (after h 3)
      [.ldrb 15 14 0, .strb 15 16 4092, .addImm 14 14 1, .addImm 16 16 1, .cbnz 15 f7] := by
    simpa using CodeAt.drop_take code hcode 3 5 (by simp)
  intro strs
  induction strs with
  | nil =>
    intro s hpc ⟨hw, hz⟩ _ _
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after h 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after h 9) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h1)
    rw [ite_eq_left (by rw [x1, hz])] at p2
    exact ⟨u2, r1.trans r2, p2, fun q _ h14 _ _ => by rw [k2, k1 q h14], by rw [sp2, sp1],
      by rw [io2, io1], by rw [m2, m1]; rfl⟩
  | cons str rest ih =>
    intro s hpc ⟨hw, hnz, hstr, hrest⟩ hb hn
    rw [vectorSize_cons] at hb hn
    obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_vectorWord P code (s := s)
      (by rw [hpc]; exact c0) hw
    have q1 : u1.pc = after h 1 := by rw [p1, hpc, after_one]
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := 14)
      (target := after h 9) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target h1)
    rw [ite_eq_right (by rw [x1]; exact hnz), q1, ← after_succ] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 11) (n := 11)
      (k := 8) (by decide) (by decide) (by rw [p2]; exact c2) rfl
    have q3 : u3.pc = after h 3 := by rw [p3, p2, ← after_succ]
    have u3x16 : u3.x 16 = s.x 16 := by rw [k3 16 (by decide), k2, k1 16 (by decide)]
    have hm3 : u3.mem = s.mem := by rw [m3, m2, m1]
    obtain ⟨u4, r4, p4, x14', x16', k4, sp4, io4, m4⟩ := run_copyLoop P code cCopy
      (by rw [after_after]; exact h7) hU str u3 q3
      (by rw [k3 14 (by decide), k2, x1, hm3]; exact hstr)
      (by rw [u3x16]; omega)
      (fun j hj => by rw [u3x16]; exact hn j (by omega))
    rw [u3x16, hm3] at m4
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_b P code (s := u4) (target := h)
      (by rw [p4, after_after]; exact c8) (by rw [p4, after_after]; exact bField_target h8)
    have hd : (s.x 16 + UInt64.ofNat 4092).toNat + (str ++ [0]).length ≤ 2 ^ 32 := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hframe5 : ∀ b : UInt64, 2 ^ 32 ≤ b.toNat → u5.mem b = s.mem b := by
      intro b hb'
      rw [m5, m4]
      exact writeList_frame hd b hb'
    have hd5 : u5.x 16 + UInt64.ofNat 4092 =
        s.x 16 + UInt64.ofNat 4092 + UInt64.ofNat (str ++ [0]).length := by
      rw [k5, x16', u3x16, List.length_append, List.length_singleton, UInt64.add_assoc,
        UInt64.add_comm (UInt64.ofNat _), ← UInt64.add_assoc]
    have hd5n : (u5.x 16 + UInt64.ofNat 4092).toNat =
        (s.x 16 + UInt64.ofNat 4092).toNat + (str.length + 1) := by
      rw [hd5, UInt64.toNat_add, UInt64.toNat_ofNat', List.length_append, List.length_singleton,
        Nat.mod_eq_of_lt (by omega : str.length + 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    have u5x11 : u5.x 11 = s.x 11 + 8 := by
      rw [k5, k4 11 (by decide) (by decide) (by decide), x3, k2, k1 11 (by decide)]
      rfl
    obtain ⟨t, rt, pt, kt, spt, iot, mt⟩ := ih u5 p5
      (by rw [u5x11]; exact VectorAt.frame hframe5 hrest)
      (by rw [hd5n]; omega)
      (fun j hj => by
        rw [hd5, add_ofNat_add, List.length_append, List.length_singleton]
        exact hn (str.length + 1 + j) (by omega))
    refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans rt)))), pt,
      fun q h11 h14 h15 h16 => ?_, by rw [spt, sp5, sp4, sp3, sp2, sp1],
      by rw [iot, io5, io4, io3, io2, io1], ?_⟩
    · rw [kt q h11 h14 h15 h16, k5, k4 q h14 h15 h16, k3 q h11, k2, k1 q h14]
    · rw [mt, m5, m4, hd5, List.flatMap_cons,
        writeList_append s.mem _ (str ++ [0]) (rest.flatMap (· ++ [0]))]

/-! ## The scan piece -/

theorem movz_zero : UInt64.ofNat (0 : Fin 65536).val <<< UInt64.ofNat (16 * (0 : Fin 4).val) = 0 :=
  by decide

theorem movz_two32 :
    UInt64.ofNat (1 : Fin 65536).val <<< UInt64.ofNat (16 * (2 : Fin 4).val) = 4294967296 :=
  by decide

/-- The scan piece from `a` over the vector at X9 of the strings `strs`: the run reaches the
piece's end with the count in X12 and the sum of the sizes in X13 when the sum lies below `2^32`,
and `ov` otherwise.  X10 to X15 and the flags change. -/
theorem run_scanPiece {a ov : UInt64} {is : List Instr} (hg : scanPiece a ov = .ok is)
    (hcode : CodeAt code a is) {strs : List (List UInt8)} {s : State} (hpc : s.pc = a)
    (hv : VectorAt P s.mem (s.x 9) strs) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → q ≠ 14 → q ≠ 15 → t.x q = s.x q) ∧
      if vectorSize strs < 2 ^ 32 then
        t.pc = after a 15 ∧ t.x 12 = UInt64.ofNat strs.length ∧
          t.x 13 = UInt64.ofNat (vectorSize strs)
      else t.pc = ov := by
  obtain ⟨f5, f11, f13, f14, h5, h11, h13, h14, rfl⟩ := scanPiece_ok hg
  have c := fun k (hk : k < 15) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  have cLoop : CodeAt code (after a 4) [.ldr 14 11 0, .cbz 14 f5, .addImm 11 11 8,
      .addImm 12 12 1, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f11,
      .subsReg 31 13 10, .bcond 2 f13, .b f14] := by
    simpa using CodeAt.drop_take code hcode 4 11 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 11) (m := 9)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_movz P code (s := u1) (d := 12) (imm := 0)
    (hw := 0) (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 13) (imm := 0)
    (hw := 0) (by decide) (by rw [q2]; exact c2)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_movz P code (s := u3) (d := 10) (imm := 1)
    (hw := 2) (by decide) (by rw [q3]; exact c3)
  have q4 : u4.pc = after a 4 := by rw [p4, q3, ← after_succ]
  have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  obtain ⟨t, rt, spt, mt, iot, kt, ht⟩ := run_scanLoop P code cLoop h5 h11 h13 h14 strs u4 0 0 q4
    (by rw [x4, movz_two32]) (by rw [k4 12 (by decide), k3 12 (by decide), x2, movz_zero]; rfl)
    (by rw [k4 13 (by decide), x3, movz_zero]; rfl) (by decide)
    (by rw [k4 11 (by decide), k3 11 (by decide), k2 11 (by decide), x1, hm4]; exact hv)
  refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans rt))), by rw [spt, sp4, sp3, sp2, sp1],
    by rw [mt, hm4], by rw [iot, io4, io3, io2, io1], fun q h10 h11 h12 h13 h14 h15 => ?_, ?_⟩
  · rw [kt q h11 h12 h13 h14 h15, k4 q h10, k3 q h13, k2 q h12, k1 q h11]
  · simpa only [Nat.zero_add] using ht

/-! ## The stubs' shared parts -/

theorem after_eq {a : UInt64} {m n : Nat} (h : m = n) : after a m = after a n := by rw [h]

/-- Placed code split after its first `k` instructions, with the address of the rest named. -/
theorem CodeAt.peelAt {a : UInt64} {l1 l2 : List Instr} {n k m : Nat}
    (h : CodeAt code (after a n) (l1 ++ l2)) (hl : l1.length = k) (hm : n + k = m) :
    CodeAt code (after a n) l1 ∧ CodeAt code (after a m) l2 := by
  subst hm
  exact CodeAt.peel code h hl

/-- Instruction `k` of placed code, at an address named `b`. -/
theorem CodeAt.get {a : UInt64} {l : List Instr} (h : CodeAt code a l) (k : Nat)
    (hk : k < l.length) {b : UInt64} (hb : after a k = b) : code b = some (encode l[k]) := by
  subst hb
  exact h k hk

/-- The scratch's address from `a`: X20 at `X17 + scratch`. -/
theorem run_scratchAddr {a : UInt64} {scratch : Nat} (hcode : CodeAt code a (scratchAddr scratch))
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = after a 5 ∧
      t.x 20 = s.x 17 + UInt64.ofNat scratch ∧ (∀ q : Fin 32, q ≠ 20 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have cs := CodeAt.split code hcode (n := 4) (by simp [movImm])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movImm P code (s := s) (d := 20)
    (v := UInt64.ofNat scratch) (by decide) cs.1 hpc
  have c4 := cs.2 0 (by simp)
  simp only [List.getElem_cons_zero, after_after] at c4
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 20) (n := 20)
    (m := 17) (by decide) (by rw [p1]; exact c4)
  refine ⟨u2, r1.trans r2, by rw [p2, p1, ← after_succ], by rw [x2, x1, k1 17 (by decide),
    UInt64.add_comm], fun q hq => by rw [k2 q hq, k1 q hq], by rw [sp2, sp1], by rw [m2, m1],
    by rw [io2, io1]⟩

theorem movz_eight : UInt64.ofNat (8 : Fin 65536).val <<< UInt64.ofNat (16 * (0 : Fin 4).val) = 8 :=
  by decide

/-- The vector's address from `a`, with the scratch's address in X20 and the initial SP at its
first word: X9 at `vectorAddr`.  X10 and X11 change. -/
theorem run_vectorStart (v : StringVector) {a : UInt64} (hcode : CodeAt code a (vectorStart v))
    {s : State} (hpc : s.pc = a) (hscr : ∀ k < 8, P.normal (s.x 20 + UInt64.ofNat k) = true)
    (hargc : v = .environ →
      ∀ k < 8, P.normal (load64 s.mem (s.x 20) + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after a (vectorStart v).length ∧
      t.x 9 = vectorAddr s.mem (load64 s.mem (s.x 20)) v ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  have c := fun k (hk : k < (vectorStart v).length) => hcode k hk
  have c0 : code a = some (encode (.ldr 9 20 0)) := by
    cases v <;> simpa [vectorStart, after_zero] using c 0 (by simp [vectorStart])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldr P code (s := s) (t := 9) (n := 20)
    (i := 0) (by decide) (by decide) (by decide) (by rw [hpc]; exact c0)
    (fun k hk => by simpa using hscr k hk)
  rw [Nat.mul_zero, add_ofNat_zero] at x1
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  cases v with
  | args =>
    have c1 := c 1 (by simp [vectorStart])
    simp only [vectorStart, List.getElem_cons_succ, List.getElem_cons_zero] at c1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addK P code (s := u1) (d := 9) (n := 9)
      (k := 8) (by decide) (by decide) (by rw [q1]; exact c1) rfl
    refine ⟨u2, r1.trans r2, by rw [p2, q1]; simp [vectorStart, after_succ], by
      rw [x2, x1]; rfl, fun q h9 _ _ => by rw [k2 q h9, k1 q h9], by rw [sp2, sp1],
      by rw [m2, m1], by rw [io2, io1]⟩
  | environ =>
    have c1 := c 1 (by simp [vectorStart])
    have c2 := c 2 (by simp [vectorStart])
    have c3 := c 3 (by simp [vectorStart])
    have c4 := c 4 (by simp [vectorStart])
    simp only [vectorStart, List.getElem_cons_succ, List.getElem_cons_zero] at c1 c2 c3 c4
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldr P code (s := u1) (t := 10) (n := 9)
      (i := 0) (by decide) (by decide) (by decide) (by rw [q1]; exact c1)
      (fun k hk => by rw [x1]; simpa using hargc rfl k hk)
    rw [Nat.mul_zero, add_ofNat_zero, x1, m1] at x2
    have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 11) (imm := 8)
      (hw := 0) (by decide) (by rw [q2]; exact c2)
    have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_madd P code (s := u3) (d := 9) (n := 10)
      (m := 11) (r := 9) (by decide) (by rw [q3]; exact c3)
    have q4 : u4.pc = after a 4 := by rw [p4, q3, ← after_succ]
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_addK P code (s := u4) (d := 9) (n := 9)
      (k := 16) (by decide) (by decide) (by rw [q4]; exact c4) rfl
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by
        rw [p5, q4]; simp [vectorStart, after_succ], ?_,
      fun q h9 h10 h11 => by rw [k5 q h9, k4 q h9, k3 q h11, k2 q h10, k1 q h9],
      by rw [sp5, sp4, sp3, sp2, sp1], by rw [m5, m4, m3, m2, m1],
      by rw [io5, io4, io3, io2, io1]⟩
    rw [x5, x4, k3 9 (by decide), k2 9 (by decide), x1, k3 10 (by decide), x2, x3, movz_eight]
    rfl

/-- The address `X17 + X + 4 + 4092` of a store through X16 is byte `X` of the guest's memory. -/
theorem guest_store (g x : UInt64) :
    g + x + UInt64.ofNat 4 + UInt64.ofNat 4092 = g + UInt64.ofNat (4096 + x.toNat) := by
  apply UInt64.toNat_inj.mp
  have := g.toNat_lt
  have := x.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at *
  omega

/-- The count and the size stored by `store32` at the guest's pointer in X`r` with X16 set from
`a`: the four bytes from byte `X r` of the guest's memory receive the low 32 bits of X`v`. -/
theorem run_guestStore32 {a : UInt64} {r v : Fin 32} (hv : v ≠ 15)
    (hv16 : v ≠ 16)
    (hcode : CodeAt code a ([.addReg 16 17 r, .addImm 16 16 4] ++ store32 v 15))
    {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 4, P.normal (s.x 17 + UInt64.ofNat (4096 + (s.x r).toNat + k)) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.pc = after a 9 ∧
      (∀ q : Fin 32, q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (s.x r).toNat))
        (word32Bytes (s.x v)) := by
  have c0 := hcode 0 (by simp [store32])
  have c1 := hcode 1 (by simp [store32])
  simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  have cS : CodeAt code (after a 2) (store32 v 15) := by
    simpa [store32] using CodeAt.drop_take code hcode 2 7 (by simp [store32])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 16) (n := 17)
    (m := r) (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addK P code (s := u1) (d := 16) (n := 16)
    (k := 4) (by decide) (by decide) (by rw [q1]; exact c1) rfl
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  have u2x16 : u2.x 16 + UInt64.ofNat 4092 = s.x 17 + UInt64.ofNat (4096 + (s.x r).toNat) := by
    rw [x2, x1]
    exact guest_store _ _
  obtain ⟨u3, r3, p3, sp3, io3, k3, m3⟩ := run_strb4 P code (v := v) (t := 15) (s := u2)
    (by decide) hv (by decide) cS q2
    (fun k hk => by rw [← add_ofNat_add, u2x16, add_ofNat_add]; exact hmap k hk) hU
  refine ⟨u3, r1.trans (r2.trans r3), by rw [p3, after_after], fun q h15 h16 => by
    rw [k3 q h15, k2 q h16, k1 q h16], by rw [sp3, sp2, sp1], by rw [io3, io2, io1], ?_⟩
  rw [m3, u2x16, m2, m1, k2 v hv16, k1 v hv16]
  rfl

/-- The registers that the stubs keep: the arguments' registers X0 to X8, X17, X18, and X30. -/
def KeptReg (q : Fin 32) : Prop := q.val < 9 ∨ q.val = 17 ∨ q.val = 18 ∨ q.val = 30

theorem KeptReg.ne {q : Fin 32} (h : KeptReg q) {k : Fin 32}
    (hk : 9 ≤ k.val ∧ k.val ≠ 17 ∧ k.val ≠ 18 ∧ k.val ≠ 30) : q ≠ k := by
  rintro rfl
  unfold KeptReg at h
  omega

theorem keptReg_0 : KeptReg 0 := Or.inl (by decide)
theorem keptReg_1 : KeptReg 1 := Or.inl (by decide)
theorem keptReg_17 : KeptReg 17 := Or.inr (Or.inl rfl)
theorem keptReg_18 : KeptReg 18 := Or.inr (Or.inr (Or.inl rfl))
theorem keptReg_30 : KeptReg 30 := Or.inr (Or.inr (Or.inr rfl))

/-- What the stubs of the vector `v` read at their entry `s`, for a memory of `M` bytes and the
scratch `scratch` bytes above the area: the memory's size at the area's first word, the area's
first word and the guest's bytes in Normal memory and below `2^32`, the initial SP at the scratch's
first word in Normal memory, the initial stack's first word for the environment, the vector of the
strings `strs`, and 32-bit values in X0 and X1. -/
structure StubEntry (P : Platform) (scratch M : Nat) (v : StringVector) (strs : List (List UInt8))
    (s : State) : Prop where
  size : load64 s.mem (s.x 17) + 8 = UInt64.ofNat M
  area : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true
  below : (s.x 17).toNat + 4096 + M ≤ 2 ^ 32
  guest : ∀ j < M, P.normal (s.x 17 + UInt64.ofNat (4096 + j)) = true
  saved : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat scratch + UInt64.ofNat k) = true
  argc : v = .environ → ∀ k < 8,
    P.normal (load64 s.mem (s.x 17 + UInt64.ofNat scratch) + UInt64.ofNat k) = true
  vector : VectorAt P s.mem
    (vectorAddr s.mem (load64 s.mem (s.x 17 + UInt64.ofNat scratch)) v) strs
  arg0 : (s.x 0).toNat < 2 ^ 32
  arg1 : (s.x 1).toNat < 2 ^ 32

/-- The memory's size from the area's first word, from `a`: X`d` at `M`. -/
theorem run_memSize {a : UInt64} {d : Fin 32} (hd : d.val < 31)
    (hcode : CodeAt code a [.ldr d 17 0, .addImm d d 8]) {s : State} (hpc : s.pc = a) {M : Nat}
    (hsize : load64 s.mem (s.x 17) + 8 = UInt64.ofNat M)
    (harea : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after a 2 ∧ t.x d = UInt64.ofNat M ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldr P code (s := s) (t := d) (n := 17)
    (i := 0) (by decide) hd (by decide) (by rw [hpc]; exact c0)
    (fun k hk => by simpa using harea k hk)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addK P code (s := u1) (d := d) (n := d)
    (k := 8) hd hd (by rw [q1]; exact c1) rfl
  refine ⟨u2, r1.trans r2, by rw [p2, q1, ← after_succ], ?_, fun q hq => by rw [k2 q hq, k1 q hq],
    by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩
  rw [x2, x1, Nat.mul_zero, add_ofNat_zero, ← hsize]
  rfl

/-- The check that the four bytes from the guest's pointer in X`r` lie within the memory of `M`
bytes in X9, from `a`: the trap stub `tr` when they do not.  X10 and the flags change. -/
theorem run_word4Check {a tr : UInt64} {r : Fin 32} {g : Fin 524288}
    (hcode : CodeAt code a [.addImm 10 r 4, .subsReg 31 10 9, .bcond 8 g])
    (hg : cbField (after a 2) tr = .ok g) (hr : r.val < 31) {s : State} (hpc : s.pc = a) {M : Nat}
    (h9 : s.x 9 = UInt64.ofNat M) (hM : M < 2 ^ 32) (hx : (s.x r).toNat < 2 ^ 32) :
    ∃ t, Reach P code s t ∧ (t.pc = if (s.x r).toNat + 4 ≤ M then after a 3 else tr) ∧
      (∀ q : Fin 32, q ≠ 10 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  simp only [List.getElem_cons_zero, after_zero] at c0
  have c12 : CodeAt code (after a 1) [.subsReg 31 10 9, .bcond 8 g] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addK P code (s := s) (d := 10) (n := r)
    (k := 4) (by decide) hr (by rw [hpc]; exact c0) rfl
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_hiReg P code c12
    (by rw [after_after]; exact hg) (by rw [p1, hpc, after_one])
  have hlt : u1.x 9 < u1.x 10 ↔ ¬ (s.x r).toNat + 4 ≤ M := by
    rw [k1 9 (by decide), h9, x1, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (show M < 2 ^ 64 by omega), UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  refine ⟨u2, r1.trans r2, ?_, fun q hq => by rw [k2, k1 q hq], by rw [sp2, sp1],
    by rw [m2, m1], by rw [io2, io1]⟩
  rw [p2, after_after]
  by_cases h : (s.x r).toNat + 4 ≤ M
  · rw [ite_eq_right (fun e => (hlt.mp e) h), ite_eq_left h]
  · rw [ite_eq_left (hlt.mpr h), ite_eq_right h]

theorem sizesStub_ok {v : StringVector} {a tr : UInt64} {scratch : Nat} {is : List Instr}
    (hg : sizesStub v a tr scratch = .ok is) :
    ∃ g4 g7 scan, cbField (after a 4) tr = .ok g4 ∧ cbField (after a 7) tr = .ok g7 ∧
      scanPiece (after a (13 + (vectorStart v).length)) (after a (48 + (vectorStart v).length)) =
        .ok scan ∧
      is = [.ldr 9 17 0, .addImm 9 9 8] ++ ([.addImm 10 0 4, .subsReg 31 10 9, .bcond 8 g4] ++
        ([.addImm 10 1 4, .subsReg 31 10 9, .bcond 8 g7] ++ (scratchAddr scratch ++
        (vectorStart v ++
        (scan ++ (([.addReg 16 17 0, .addImm 16 16 4] ++ store32 12 15) ++
        (([.addReg 16 17 1, .addImm 16 16 4] ++ store32 13 15) ++
        [.movz 0 0 0, .ret 30, .movz 0 61 0, .ret 30]))))))) := by
  unfold sizesStub at hg
  cases h1 : cbField (after a 4) tr with
  | error e => simp [h1, bind, Except.bind] at hg
  | ok g4 =>
  cases h2 : cbField (after a 7) tr with
  | error e => simp [h1, h2, bind, Except.bind] at hg
  | ok g7 =>
  cases h3 : scanPiece (after a (13 + (vectorStart v).length))
      (after a (48 + (vectorStart v).length)) with
  | error e => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok scan =>
  simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  refine ⟨g4, g7, scan, rfl, rfl, rfl, ?_⟩
  rw [← hg]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem scanPiece_length {a ov : UInt64} {is : List Instr} (hg : scanPiece a ov = .ok is) :
    is.length = 15 := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := scanPiece_ok hg
  rfl

/-- The run of the stub of `args_sizes_get` or `environ_sizes_get` for the vector `v` from its
entry `a`, with the count's pointer in X0 and the size's in X1: the trap stub `tr` with the memory
unchanged when either's four bytes leave the memory of `M` bytes, and otherwise the return to X30
with errno 0 and the count and the size of `strs` stored at the pointers when the size lies below
`2^32`, and with errno 61 and the memory unchanged otherwise. -/
theorem run_sizesStub {v : StringVector} {a tr : UInt64} {scratch M : Nat} {is : List Instr}
    {strs : List (List UInt8)} (hg : sizesStub v a tr scratch = .ok is) (hcode : CodeAt code a is)
    (hU : P.normal P.uart = false) {s : State} (hpc : s.pc = a)
    (he : StubEntry P scratch M v strs s) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if (s.x 0).toNat + 4 ≤ M ∧ (s.x 1).toNat + 4 ≤ M then
        t.pc = s.x 30 ∧
          if vectorSize strs < 2 ^ 32 then
            t.x 0 = 0 ∧ t.mem = writeList (writeList s.mem
              (s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat))
              (word32Bytes (UInt64.ofNat strs.length)))
              (s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat))
              (word32Bytes (UInt64.ofNat (vectorSize strs)))
          else t.x 0 = 61 ∧ t.mem = s.mem
      else t.pc = tr ∧ t.mem = s.mem := by
  obtain ⟨g4, g7, scan, hg4, hg7, hscan, rfl⟩ := sizesStub_ok hg
  have hsl := scanPiece_length hscan
  set n := (vectorStart v).length with hn
  have hM32 : M < 2 ^ 32 := by have := he.below; omega
  obtain ⟨cSize, h1⟩ := CodeAt.peelAt code (n := 0) (k := 2) (m := 2)
    (by rw [after_zero]; exact hcode) rfl rfl
  obtain ⟨cC0, h2⟩ := CodeAt.peelAt code (k := 3) (m := 5) h1 rfl rfl
  obtain ⟨cC1, h3⟩ := CodeAt.peelAt code (k := 3) (m := 8) h2 rfl rfl
  obtain ⟨cScr, h4⟩ := CodeAt.peelAt code (k := 5) (m := 13) h3 (by simp [scratchAddr, movImm]) rfl
  obtain ⟨cVec, h5⟩ := CodeAt.peelAt code (k := n) (m := 13 + n) h4 rfl rfl
  obtain ⟨cScan, h6⟩ := CodeAt.peelAt code (k := 15) (m := 28 + n) h5 hsl (by omega)
  obtain ⟨cSt0, h7⟩ := CodeAt.peelAt code (k := 9) (m := 37 + n) h6 (by simp [store32])
    (by omega)
  obtain ⟨cSt1, cEnd⟩ := CodeAt.peelAt code (k := 9) (m := 46 + n) h7 (by simp [store32])
    (by omega)
  rw [after_zero] at cSize
  have e0 := cEnd.get code 0 (by simp) (b := after a (46 + n)) (after_zero _)
  have e1 := cEnd.get code 1 (by simp) (b := after a (47 + n))
    (by rw [after_after]; exact after_eq (by omega))
  have e2 := cEnd.get code 2 (by simp) (b := after a (48 + n))
    (by rw [after_after]; exact after_eq (by omega))
  have e3 := cEnd.get code 3 (by simp) (b := after a (49 + n))
    (by rw [after_after]; exact after_eq (by omega))
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3
  -- the memory's size and the checks
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_memSize P code (d := 9) (by decide) cSize
    hpc he.size he.area
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_word4Check P code (r := 0) cC0
    (by rw [after_after]; exact hg4) (by decide) p1 x1 hM32
    (by rw [k1 0 (by decide)]; exact he.arg0)
  have hK2 : ∀ q : Fin 32, KeptReg q → u2.x q = s.x q := fun q hq => by
    rw [k2 q (hq.ne (by decide)), k1 q (hq.ne (by decide))]
  rw [k1 0 (by decide)] at p2
  by_cases hc : (s.x 0).toNat + 4 ≤ M
  swap
  · rw [ite_eq_right hc] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], hK2 17 keptReg_17,
      hK2 18 keptReg_18, ?_⟩
    rw [ite_eq_right (fun h => hc h.1)]
    exact ⟨p2, by rw [m2, m1]⟩
  rw [ite_eq_left hc, after_after] at p2
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_word4Check P code (r := 1) cC1
    (by rw [after_after]; exact hg7) (by decide) p2 (by rw [k2 9 (by decide), x1]) hM32
    (by rw [hK2 1 keptReg_1]; exact he.arg1)
  have hK3 : ∀ q : Fin 32, KeptReg q → u3.x q = s.x q := fun q hq => by
    rw [k3 q (hq.ne (by decide)), hK2 q hq]
  rw [k2 1 (by decide), k1 1 (by decide)] at p3
  have hm3 : u3.mem = s.mem := by rw [m3, m2, m1]
  by_cases hs : (s.x 1).toNat + 4 ≤ M
  swap
  · rw [ite_eq_right hs] at p3
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
      hK3 17 keptReg_17, hK3 18 keptReg_18, ?_⟩
    rw [ite_eq_right (fun h => hs h.2)]
    exact ⟨p3, hm3⟩
  rw [ite_eq_left hs, after_after] at p3
  -- the scratch's address and the vector's
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_scratchAddr P code cScr p3
  have hK4 : ∀ q : Fin 32, KeptReg q → u4.x q = s.x q := fun q hq => by
    rw [k4 q (hq.ne (by decide)), hK3 q hq]
  have hm4 : u4.mem = s.mem := by rw [m4, hm3]
  have u4x20 : u4.x 20 = s.x 17 + UInt64.ofNat scratch := by rw [x4, hK3 17 keptReg_17]
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_vectorStart P code v cVec
    (by rw [p4, after_after])
    (fun k hk => by rw [u4x20]; exact he.saved k hk)
    (fun hv k hk => by rw [u4x20, hm4]; exact he.argc hv k hk)
  rw [u4x20, hm4] at x5
  have hK5 : ∀ q : Fin 32, KeptReg q → u5.x q = s.x q := fun q hq => by
    rw [k5 q (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide)), hK4 q hq]
  have hm5 : u5.mem = s.mem := by rw [m5, hm4]
  -- the scan
  obtain ⟨u6, r6, sp6, m6, io6, k6, h6⟩ := run_scanPiece P code hscan cScan
    (by rw [p5, after_after]) (by rw [x5, hm5]; exact he.vector)
  have hK6 : ∀ q : Fin 32, KeptReg q → u6.x q = s.x q := fun q hq => by
    rw [k6 q (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide))
      (hq.ne (by decide)) (hq.ne (by decide)), hK5 q hq]
  have hm6 : u6.mem = s.mem := by rw [m6, hm5]
  have hr6 : Reach P code s u6 :=
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))
  by_cases hfit : vectorSize strs < 2 ^ 32
  swap
  · rw [ite_eq_right hfit] at h6
    obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_movz P code (s := u6) (d := 0) (imm := 61)
      (hw := 0) (by decide) (by rw [h6]; exact e2)
    obtain ⟨u8, r8, p8, k8, sp8, m8, io8⟩ := step_ret P code (s := u7) (n := 30)
      (by rw [p7, h6, ← after_succ, after_eq (show 48 + n + 1 = 49 + n by omega)]; exact e3)
    refine ⟨u8, hr6.trans (r7.trans r8), by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
      by rw [io8, io7, io6, io5, io4, io3, io2, io1],
      by rw [k8, k7 17 (by decide), hK6 17 keptReg_17],
      by rw [k8, k7 18 (by decide), hK6 18 keptReg_18], ?_⟩
    rw [ite_eq_left ⟨hc, hs⟩, ite_eq_right hfit]
    exact ⟨by rw [p8, k7 30 (by decide), hK6 30 keptReg_30], by rw [k8, x7]; decide,
      by rw [m8, m7, hm6]⟩
  rw [ite_eq_left hfit] at h6
  obtain ⟨p6, x12, x13⟩ := h6
  -- the stores
  obtain ⟨u7, r7, p7, k7, sp7, io7, m7⟩ := run_guestStore32 P code (r := 0) (v := 12)
    (by decide) (by decide) cSt0 (by rw [p6, after_after]; exact after_eq (by omega))
    (fun k hk => by
      rw [hK6 17 keptReg_17, hK6 0 keptReg_0, Nat.add_assoc]
      exact he.guest _ (by omega)) hU
  rw [hK6 17 keptReg_17, hK6 0 keptReg_0, x12, hm6] at m7
  obtain ⟨u8, r8, p8, k8, sp8, io8, m8⟩ := run_guestStore32 P code (r := 1) (v := 13)
    (by decide) (by decide) cSt1 (by rw [p7, after_after]; exact after_eq (by omega))
    (fun k hk => by
      rw [k7 17 (by decide) (by decide), k7 1 (by decide) (by decide), hK6 17 keptReg_17,
        hK6 1 keptReg_1]
      rw [Nat.add_assoc]; exact he.guest _ (by omega)) hU
  rw [k7 17 (by decide) (by decide), k7 1 (by decide) (by decide), k7 13 (by decide) (by decide),
    hK6 17 keptReg_17, hK6 1 keptReg_1, x13, m7] at m8
  have q8 : u8.pc = after a (46 + n) := by rw [p8, after_after]; exact after_eq (by omega)
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_movz P code (s := u8) (d := 0) (imm := 0)
    (hw := 0) (by decide) (by rw [q8]; exact e0)
  obtain ⟨u10, r10, p10, k10, sp10, m10, io10⟩ := step_ret P code (s := u9) (n := 30)
    (by rw [p9, q8, ← after_succ, after_eq (show 46 + n + 1 = 47 + n by omega)]; exact e1)
  have hK8 : ∀ q : Fin 32, KeptReg q → u8.x q = s.x q := fun q hq => by
    rw [k8 q (hq.ne (by decide)) (hq.ne (by decide)), k7 q (hq.ne (by decide)) (hq.ne (by decide)),
      hK6 q hq]
  refine ⟨u10, hr6.trans (r7.trans (r8.trans (r9.trans r10))),
    by rw [sp10, sp9, sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [io10, io9, io8, io7, io6, io5, io4, io3, io2, io1],
    by rw [k10, k9 17 (by decide), hK8 17 keptReg_17],
    by rw [k10, k9 18 (by decide), hK8 18 keptReg_18], ?_⟩
  rw [ite_eq_left ⟨hc, hs⟩, ite_eq_left hfit]
  exact ⟨by rw [p10, k9 30 (by decide), hK8 30 keptReg_30], by rw [k10, x9, movz_zero],
    by rw [m10, m9, m8]⟩

/-! ## The strings stub -/

/-- The checks of the strings stub, from `c`, with the count `len` in X12 and the size `size` in
X13: the trap stub `tr` unless the array of `len` words of four bytes at X0 and the `size` bytes at
X1 lie within the memory of `M` bytes.  X14, X15, and the flags change. -/
theorem run_stringsChecks {c tr : UInt64} {g6 g9 : Fin 524288}
    (hcode : CodeAt code c [.ldr 15 17 0, .addImm 15 15 8, .addReg 14 12 12, .addReg 14 14 14,
      .addReg 14 14 0, .subsReg 31 14 15, .bcond 8 g6, .addReg 14 1 13, .subsReg 31 14 15,
      .bcond 8 g9])
    (hg6 : cbField (after c 6) tr = .ok g6) (hg9 : cbField (after c 9) tr = .ok g9)
    {s : State} (hpc : s.pc = c) {M len size : Nat}
    (hsize : load64 s.mem (s.x 17) + 8 = UInt64.ofNat M)
    (harea : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) (hM : M < 2 ^ 32)
    (h12 : s.x 12 = UInt64.ofNat len) (h13 : s.x 13 = UInt64.ofNat size) (hlen : len < 2 ^ 32)
    (hsz : size < 2 ^ 32) (h0 : (s.x 0).toNat < 2 ^ 32) (h1 : (s.x 1).toNat < 2 ^ 32) :
    ∃ t, Reach P code s t ∧
      (t.pc = if (s.x 0).toNat + 4 * len ≤ M ∧ (s.x 1).toNat + size ≤ M then after c 10
        else tr) ∧
      (∀ q : Fin 32, q ≠ 14 → q ≠ 15 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  have cM : CodeAt code c [.ldr 15 17 0, .addImm 15 15 8] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  have c4 := hcode 4 (by simp)
  have c7 := hcode 7 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c3 c4 c7
  have c56 : CodeAt code (after c 5) [.subsReg 31 14 15, .bcond 8 g6] := by
    simpa using CodeAt.drop_take code hcode 5 2 (by simp)
  have c89 : CodeAt code (after c 8) [.subsReg 31 14 15, .bcond 8 g9] := by
    simpa using CodeAt.drop_take code hcode 8 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_memSize P code (d := 15) (by decide) cM hpc
    hsize harea
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 14) (n := 12)
    (m := 12) (by decide) (by rw [p1]; exact c2)
  have q2 : u2.pc = after c 3 := by rw [p2, p1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addReg P code (s := u2) (d := 14) (n := 14)
    (m := 14) (by decide) (by rw [q2]; exact c3)
  have q3 : u3.pc = after c 4 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 14) (n := 14)
    (m := 0) (by decide) (by rw [q3]; exact c4)
  have q4 : u4.pc = after c 5 := by rw [p4, q3, ← after_succ]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_hiReg P code c56
    (by rw [after_after]; exact hg6) q4
  have u4x15 : u4.x 15 = UInt64.ofNat M := by
    rw [k4 15 (by decide), k3 15 (by decide), k2 15 (by decide), x1]
  have u4x14 : (u4.x 14).toNat = 4 * len + (s.x 0).toNat := by
    rw [x4, x3, x2, k1 12 (by decide), h12, k3 0 (by decide), k2 0 (by decide), k1 0 (by decide)]
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at *
    omega
  have hM' : (UInt64.ofNat M).toNat = M := UInt64.toNat_ofNat_of_lt' (show M < 2 ^ 64 by omega)
  have hrest : ∀ q : Fin 32, q ≠ 14 → q ≠ 15 → u4.x q = s.x q := fun q h14 h15 => by
    rw [k4 q h14, k3 q h14, k2 q h14, k1 q h15]
  by_cases hv : (s.x 0).toNat + 4 * len ≤ M
  swap
  · have hlt : u4.x 15 < u4.x 14 := by
      rw [UInt64.lt_iff_toNat_lt, u4x15, hM', u4x14]
      omega
    rw [ite_eq_left hlt] at p5
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), ?_,
      fun q h14 h15 => by rw [k5, hrest q h14 h15], by rw [sp5, sp4, sp3, sp2, sp1],
      by rw [m5, m4, m3, m2, m1], by rw [io5, io4, io3, io2, io1]⟩
    rw [ite_eq_right (fun h => hv h.1)]
    exact p5
  have hnlt : ¬ u4.x 15 < u4.x 14 := by
    rw [UInt64.lt_iff_toNat_lt, u4x15, hM', u4x14]
    omega
  rw [ite_eq_right hnlt, after_after] at p5
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addReg P code (s := u5) (d := 14) (n := 1)
    (m := 13) (by decide) (by rw [p5]; exact c7)
  have q6 : u6.pc = after c 8 := by rw [p6, p5, ← after_succ]
  obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := run_hiReg P code c89
    (by rw [after_after]; exact hg9) q6
  have u6x15 : u6.x 15 = UInt64.ofNat M := by rw [k6 15 (by decide), k5, u4x15]
  have u6x14 : (u6.x 14).toNat = (s.x 1).toNat + size := by
    rw [x6, k5, k5, hrest 1 (by decide) (by decide), hrest 13 (by decide) (by decide), h13,
      UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  refine ⟨u7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))), ?_,
    fun q h14 h15 => by rw [k7, k6 q h14, k5, hrest q h14 h15],
    by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1], by rw [m7, m6, m5, m4, m3, m2, m1],
    by rw [io7, io6, io5, io4, io3, io2, io1]⟩
  rw [p7]
  by_cases hb : (s.x 1).toNat + size ≤ M
  · have hn : ¬ u6.x 15 < u6.x 14 := by
      rw [UInt64.lt_iff_toNat_lt, u6x15, hM', u6x14]
      omega
    rw [ite_eq_right hn, ite_eq_left ⟨hv, hb⟩, after_after]
  · have hl : u6.x 15 < u6.x 14 := by
      rw [UInt64.lt_iff_toNat_lt, u6x15, hM', u6x14]
      omega
    rw [ite_eq_left hl, ite_eq_right (fun h => hb h.2)]

/-- The pass that writes the strings' addresses, from `p`: the array at the guest's pointer in X0
receives the low 32 bits of the address of each string's copy from the guest's pointer in X1, for
the strings of the vector at X9. -/
theorem run_pointerPass {p : UInt64} {f1 f14 : Fin 524288} {f15 : Fin 67108864}
    (hcode : CodeAt code p ([.orrReg 11 31 9, .addReg 16 17 0, .addImm 16 16 4, .orrReg 13 31 1] ++
      (([.ldr 14 11 0, .cbz 14 f1, .addImm 11 11 8] ++ store32 13 15) ++
      [.addImm 16 16 4, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f14, .b f15])))
    (h1 : cbField (after p 5) (after p 20) = .ok f1)
    (h14 : cbField (after p 18) (after p 15) = .ok f14)
    (h15 : bField (after p 19) (after p 4) = .ok f15) (hU : P.normal P.uart = false)
    {s : State} (hpc : s.pc = p) {strs : List (List UInt8)}
    (hv : VectorAt P s.mem (s.x 9) strs)
    (hb : (s.x 17).toNat + 4096 + (s.x 0).toNat + 4 * strs.length ≤ 2 ^ 32)
    (hn : ∀ j < 4 * strs.length,
      P.normal (s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat + j)) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after p 20 ∧
      (∀ q : Fin 32, q ≠ 11 → q ≠ 13 → q ≠ 14 → q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat))
        (pointerBytes (s.x 1) strs) := by
  obtain ⟨cHead, cLoop⟩ := CodeAt.peelAt code (n := 0) (k := 4) (m := 4)
    (by rw [after_zero]; exact hcode) rfl rfl
  rw [after_zero] at cHead
  have c0 := cHead 0 (by simp)
  have c1 := cHead 1 (by simp)
  have c2 := cHead 2 (by simp)
  have c3 := cHead 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 11) (m := 9)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after p 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 16) (n := 17)
    (m := 0) (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after p 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 16) (n := 16)
    (k := 4) (by decide) (by decide) (by rw [q2]; exact c2) rfl
  have q3 : u3.pc = after p 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_mov P code (s := u3) (d := 13) (m := 1)
    (by decide) (by rw [q3]; exact c3)
  have q4 : u4.pc = after p 4 := by rw [p4, q3, ← after_succ]
  have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  have u4x16 : u4.x 16 + UInt64.ofNat 4092 =
      s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat) := by
    rw [k4 16 (by decide), x3, x2, k1 17 (by decide), k1 0 (by decide)]
    exact guest_store _ _
  have hd : (s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat)).toNat =
      (s.x 17).toNat + 4096 + (s.x 0).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  obtain ⟨t, rt, pt, kt, spt, iot, mt⟩ := run_pointerLoop P code cLoop
    (by rw [after_after, after_after]; exact h1) (by rw [after_after, after_after]; exact h14)
    (by rw [after_after]; exact h15) hU strs u4 q4
    (by rw [k4 11 (by decide), k3 11 (by decide), k2 11 (by decide), x1, hm4]; exact hv)
    (by rw [u4x16, hd]; omega)
    (fun j hj => by rw [u4x16, add_ofNat_add]; exact hn j hj)
  refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans rt))), by rw [pt, after_after],
    fun q h11 h13 h14 h15 h16 => by
      rw [kt q h11 h13 h14 h15 h16, k4 q h13, k3 q h16, k2 q h16, k1 q h11],
    by rw [spt, sp4, sp3, sp2, sp1], by rw [iot, io4, io3, io2, io1], ?_⟩
  rw [mt, u4x16, hm4, x4, k3 1 (by decide), k2 1 (by decide), k1 1 (by decide)]

/-- The pass that copies the strings and the return, from `b`: the buffer at the guest's pointer in
X1 receives the strings of the vector at X9 with their zero bytes, and the run returns errno 0 to
X30. -/
theorem run_copyStrings {b : UInt64} {e1 e7 : Fin 524288} {e8 : Fin 67108864}
    (hcode : CodeAt code b ([.orrReg 11 31 9, .addReg 16 17 1, .addImm 16 16 4] ++
      ([.ldr 14 11 0, .cbz 14 e1, .addImm 11 11 8, .ldrb 15 14 0, .strb 15 16 4092,
        .addImm 14 14 1, .addImm 16 16 1, .cbnz 15 e7, .b e8] ++ [.movz 0 0 0, .ret 30])))
    (h1 : cbField (after b 4) (after b 12) = .ok e1)
    (h7 : cbField (after b 10) (after b 6) = .ok e7)
    (h8 : bField (after b 11) (after b 3) = .ok e8) (hU : P.normal P.uart = false)
    {s : State} (hpc : s.pc = b) {strs : List (List UInt8)}
    (hv : VectorAt P s.mem (s.x 9) strs)
    (hb : (s.x 17).toNat + 4096 + (s.x 1).toNat + vectorSize strs ≤ 2 ^ 32)
    (hn : ∀ j < vectorSize strs,
      P.normal (s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat + j)) = true) :
    ∃ t, Reach P code s t ∧ t.pc = s.x 30 ∧ t.x 0 = 0 ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 11 → q ≠ 14 → q ≠ 15 → q ≠ 16 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat))
        (strs.flatMap (· ++ [0])) := by
  obtain ⟨cHead, cRest⟩ := CodeAt.peelAt code (n := 0) (k := 3) (m := 3)
    (by rw [after_zero]; exact hcode) rfl rfl
  obtain ⟨cLoop, cEnd⟩ := CodeAt.peelAt code (k := 9) (m := 12) cRest rfl rfl
  rw [after_zero] at cHead
  have c0 := cHead 0 (by simp)
  have c1 := cHead 1 (by simp)
  have c2 := cHead 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  have d0 := cEnd 0 (by simp)
  have d1 := cEnd 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at d0 d1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 11) (m := 9)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after b 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 16) (n := 17)
    (m := 1) (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after b 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addK P code (s := u2) (d := 16) (n := 16)
    (k := 4) (by decide) (by decide) (by rw [q2]; exact c2) rfl
  have q3 : u3.pc = after b 3 := by rw [p3, q2, ← after_succ]
  have hm3 : u3.mem = s.mem := by rw [m3, m2, m1]
  have u3x16 : u3.x 16 + UInt64.ofNat 4092 =
      s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat) := by
    rw [x3, x2, k1 17 (by decide), k1 1 (by decide)]
    exact guest_store _ _
  have hd : (s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat)).toNat =
      (s.x 17).toNat + 4096 + (s.x 1).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  obtain ⟨u4, r4, p4, k4, sp4, io4, m4⟩ := run_copyPass P code cLoop
    (by rw [after_after, after_after]; exact h1) (by rw [after_after, after_after]; exact h7)
    (by rw [after_after]; exact h8) hU strs u3 q3
    (by rw [k3 11 (by decide), k2 11 (by decide), x1, hm3]; exact hv)
    (by rw [u3x16, hd]; omega)
    (fun j hj => by rw [u3x16, add_ofNat_add]; exact hn j hj)
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_movz P code (s := u4) (d := 0) (imm := 0)
    (hw := 0) (by decide) (by rw [p4, after_after]; exact d0)
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := step_ret P code (s := u5) (n := 30)
    (by rw [p5, p4, after_after, ← after_succ]; exact d1)
  have hkeep : ∀ q : Fin 32, q ≠ 0 → q ≠ 11 → q ≠ 14 → q ≠ 15 → q ≠ 16 → u5.x q = s.x q :=
    fun q h0 h11 h14 h15 h16 => by
      rw [k5 q h0, k4 q h11 h14 h15 h16, k3 q h16, k2 q h16, k1 q h11]
  refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))),
    by rw [p6, hkeep 30 (by decide) (by decide) (by decide) (by decide) (by decide)],
    by rw [k6, x5, movz_zero], fun q h0 h11 h14 h15 h16 => by rw [k6, hkeep q h0 h11 h14 h15 h16],
    by rw [sp6, sp5, sp4, sp3, sp2, sp1], by rw [io6, io5, io4, io3, io2, io1], ?_⟩
  rw [m6, m5, m4, u3x16, hm3]

theorem stringsStub_ok {v : StringVector} {a tr : UInt64} {scratch : Nat} {is : List Instr}
    (hg : stringsStub v a tr scratch = .ok is) :
    ∃ scan g6 g9 f1 f14 f15 e1 e7 e8,
      scanPiece (after a (5 + (vectorStart v).length)) tr = .ok scan ∧
      cbField (after a (20 + (vectorStart v).length + 6)) tr = .ok g6 ∧
      cbField (after a (20 + (vectorStart v).length + 9)) tr = .ok g9 ∧
      cbField (after a (30 + (vectorStart v).length + 5))
        (after a (30 + (vectorStart v).length + 20)) = .ok f1 ∧
      cbField (after a (30 + (vectorStart v).length + 18))
        (after a (30 + (vectorStart v).length + 15)) = .ok f14 ∧
      bField (after a (30 + (vectorStart v).length + 19))
        (after a (30 + (vectorStart v).length + 4)) = .ok f15 ∧
      cbField (after a (50 + (vectorStart v).length + 4))
        (after a (50 + (vectorStart v).length + 12)) = .ok e1 ∧
      cbField (after a (50 + (vectorStart v).length + 10))
        (after a (50 + (vectorStart v).length + 6)) = .ok e7 ∧
      bField (after a (50 + (vectorStart v).length + 11))
        (after a (50 + (vectorStart v).length + 3)) = .ok e8 ∧
      is = scratchAddr scratch ++ (vectorStart v ++ (scan ++
        ([.ldr 15 17 0, .addImm 15 15 8, .addReg 14 12 12, .addReg 14 14 14, .addReg 14 14 0,
          .subsReg 31 14 15, .bcond 8 g6, .addReg 14 1 13, .subsReg 31 14 15, .bcond 8 g9] ++
        (([.orrReg 11 31 9, .addReg 16 17 0, .addImm 16 16 4, .orrReg 13 31 1] ++
          (([.ldr 14 11 0, .cbz 14 f1, .addImm 11 11 8] ++ store32 13 15) ++
          [.addImm 16 16 4, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1, .cbnz 15 f14,
            .b f15])) ++
        ([.orrReg 11 31 9, .addReg 16 17 1, .addImm 16 16 4] ++
          ([.ldr 14 11 0, .cbz 14 e1, .addImm 11 11 8, .ldrb 15 14 0, .strb 15 16 4092,
            .addImm 14 14 1, .addImm 16 16 1, .cbnz 15 e7, .b e8] ++
          [.movz 0 0 0, .ret 30])))))) := by
  unfold stringsStub at hg
  cases h0 : scanPiece (after a (5 + (vectorStart v).length)) tr with
  | error e => simp [h0, bind, Except.bind] at hg
  | ok scan =>
  cases h1 : cbField (after a (20 + (vectorStart v).length + 6)) tr with
  | error e => simp [h0, h1, bind, Except.bind] at hg
  | ok g6 =>
  cases h2 : cbField (after a (20 + (vectorStart v).length + 9)) tr with
  | error e => simp [h0, h1, h2, bind, Except.bind] at hg
  | ok g9 =>
  cases h3 : cbField (after a (30 + (vectorStart v).length + 5))
      (after a (30 + (vectorStart v).length + 20)) with
  | error e => simp [h0, h1, h2, h3, bind, Except.bind] at hg
  | ok f1 =>
  cases h4 : cbField (after a (30 + (vectorStart v).length + 18))
      (after a (30 + (vectorStart v).length + 15)) with
  | error e => simp [h0, h1, h2, h3, h4, bind, Except.bind] at hg
  | ok f14 =>
  cases h5 : bField (after a (30 + (vectorStart v).length + 19))
      (after a (30 + (vectorStart v).length + 4)) with
  | error e => simp [h0, h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok f15 =>
  cases h6 : cbField (after a (50 + (vectorStart v).length + 4))
      (after a (50 + (vectorStart v).length + 12)) with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, bind, Except.bind] at hg
  | ok e1 =>
  cases h7 : cbField (after a (50 + (vectorStart v).length + 10))
      (after a (50 + (vectorStart v).length + 6)) with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at hg
  | ok e7 =>
  cases h8 : bField (after a (50 + (vectorStart v).length + 11))
      (after a (50 + (vectorStart v).length + 3)) with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at hg
  | ok e8 =>
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  refine ⟨scan, g6, g9, f1, f14, f15, e1, e7, e8, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [← hg]
  simp only [store32, List.append_assoc, List.cons_append, List.nil_append]

/-- The run of the stub of `args_get` or `environ_get` for the vector `v` from its entry `a`, with
the array's pointer in X0 and the buffer's in X1: the return to X30 with errno 0 and the strings'
addresses written into the array and then the strings into the buffer when their size lies below
`2^32` and both regions lie within the memory of `M` bytes, and the trap stub `tr` with the memory
unchanged otherwise. -/
theorem run_stringsStub {v : StringVector} {a tr : UInt64} {scratch M : Nat} {is : List Instr}
    {strs : List (List UInt8)} (hg : stringsStub v a tr scratch = .ok is) (hcode : CodeAt code a is)
    (hU : P.normal P.uart = false) {s : State} (hpc : s.pc = a)
    (he : StubEntry P scratch M v strs s) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if vectorSize strs < 2 ^ 32 ∧ (s.x 0).toNat + 4 * strs.length ≤ M ∧
          (s.x 1).toNat + vectorSize strs ≤ M then
        t.pc = s.x 30 ∧ t.x 0 = 0 ∧
          t.mem = writeList (writeList s.mem (s.x 17 + UInt64.ofNat (4096 + (s.x 0).toNat))
            (pointerBytes (s.x 1) strs)) (s.x 17 + UInt64.ofNat (4096 + (s.x 1).toNat))
            (strs.flatMap (· ++ [0]))
      else t.pc = tr ∧ t.mem = s.mem := by
  obtain ⟨scan, g6, g9, f1, f14, f15, e1, e7, e8, hscan, hg6, hg9, hf1, hf14, hf15, he1, he7,
    he8, rfl⟩ := stringsStub_ok hg
  have hsl := scanPiece_length hscan
  set n := (vectorStart v).length with hn
  have hM32 : M < 2 ^ 32 := by have := he.below; omega
  obtain ⟨cScr, h1⟩ := CodeAt.peelAt code (n := 0) (k := 5) (m := 5)
    (by rw [after_zero]; exact hcode) (by simp [scratchAddr, movImm]) rfl
  obtain ⟨cVec, h2⟩ := CodeAt.peelAt code (k := n) (m := 5 + n) h1 rfl rfl
  obtain ⟨cScan, h3⟩ := CodeAt.peelAt code (k := 15) (m := 20 + n) h2 hsl (by omega)
  obtain ⟨cChk, h4⟩ := CodeAt.peelAt code (k := 10) (m := 30 + n) h3 rfl (by omega)
  obtain ⟨cPtr, cCopy⟩ := CodeAt.peelAt code (k := 20) (m := 50 + n) h4 (by simp [store32])
    (by omega)
  rw [after_zero] at cScr
  -- the scratch's address and the vector's
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_scratchAddr P code cScr hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_vectorStart P code v cVec p1
    (fun k hk => by rw [x1]; exact he.saved k hk)
    (fun hv k hk => by rw [x1, m1]; exact he.argc hv k hk)
  rw [x1, m1] at x2
  have hK2 : ∀ q : Fin 32, KeptReg q → u2.x q = s.x q := fun q hq => by
    rw [k2 q (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide)), k1 q (hq.ne (by decide))]
  have hm2 : u2.mem = s.mem := by rw [m2, m1]
  -- the scan
  obtain ⟨u3, r3, sp3, m3, io3, k3, h3'⟩ := run_scanPiece P code hscan cScan
    (by rw [p2, after_after]) (by rw [x2, hm2]; exact he.vector)
  have hK3 : ∀ q : Fin 32, KeptReg q → u3.x q = s.x q := fun q hq => by
    rw [k3 q (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide))
      (hq.ne (by decide)) (hq.ne (by decide)), hK2 q hq]
  have hm3 : u3.mem = s.mem := by rw [m3, hm2]
  have u3x9 : u3.x 9 = u2.x 9 := k3 9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hr3 : Reach P code s u3 := r1.trans (r2.trans r3)
  by_cases hfit : vectorSize strs < 2 ^ 32
  swap
  · rw [ite_eq_right hfit] at h3'
    refine ⟨u3, hr3, by rw [sp3, sp2, sp1], by rw [io3, io2, io1], hK3 17 keptReg_17,
      hK3 18 keptReg_18, ?_⟩
    rw [ite_eq_right (fun h => hfit h.1)]
    exact ⟨h3', hm3⟩
  rw [ite_eq_left hfit] at h3'
  obtain ⟨p3, x12, x13⟩ := h3'
  have hlen := length_le_vectorSize strs
  -- the checks
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_stringsChecks P code cChk
    (by rw [after_after]; exact hg6) (by rw [after_after]; exact hg9)
    (by rw [p3, after_after]; exact after_eq (by omega))
    (by rw [hm3, hK3 17 keptReg_17]; exact he.size)
    (fun k hk => by rw [hK3 17 keptReg_17]; exact he.area k hk) hM32 x12 x13 (by omega) hfit
    (by rw [hK3 0 keptReg_0]; exact he.arg0) (by rw [hK3 1 keptReg_1]; exact he.arg1)
  rw [hK3 0 keptReg_0, hK3 1 keptReg_1] at p4
  have hK4 : ∀ q : Fin 32, KeptReg q → u4.x q = s.x q := fun q hq => by
    rw [k4 q (hq.ne (by decide)) (hq.ne (by decide)), hK3 q hq]
  have hm4 : u4.mem = s.mem := by rw [m4, hm3]
  by_cases hreg : (s.x 0).toNat + 4 * strs.length ≤ M ∧ (s.x 1).toNat + vectorSize strs ≤ M
  swap
  · rw [ite_eq_right hreg] at p4
    refine ⟨u4, hr3.trans r4, by rw [sp4, sp3, sp2, sp1], by rw [io4, io3, io2, io1],
      hK4 17 keptReg_17, hK4 18 keptReg_18, ?_⟩
    rw [ite_eq_right (fun h => hreg h.2)]
    exact ⟨p4, hm4⟩
  rw [ite_eq_left hreg, after_after] at p4
  have u4x9 : u4.x 9 = vectorAddr s.mem (load64 s.mem (s.x 17 + UInt64.ofNat scratch)) v :=
    by rw [k4 9 (by decide) (by decide), u3x9, x2]
  -- the passes
  obtain ⟨u5, r5, p5, k5, sp5, io5, m5⟩ := run_pointerPass P code cPtr
    (by rw [after_after, after_after]; exact hf1) (by rw [after_after, after_after]; exact hf14)
    (by rw [after_after, after_after]; exact hf15) hU
    (by rw [p4]; exact after_eq (by omega)) (by rw [u4x9, hm4]; exact he.vector)
    (by rw [hK4 17 keptReg_17, hK4 0 keptReg_0]; have := he.below; omega)
    (fun j hj => by
      rw [hK4 17 keptReg_17, hK4 0 keptReg_0, Nat.add_assoc]
      exact he.guest _ (by omega))
  rw [hK4 17 keptReg_17, hK4 0 keptReg_0, hK4 1 keptReg_1, hm4] at m5
  have hframe5 : ∀ b : UInt64, 2 ^ 32 ≤ b.toNat → u5.mem b = s.mem b := by
    intro b hb
    rw [m5]
    refine writeList_frame ?_ b hb
    rw [pointerBytes_length, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := he.below
    omega
  obtain ⟨u6, r6, p6, x6, k6, sp6, io6, m6⟩ := run_copyStrings P code cCopy
    (by rw [after_after, after_after]; exact he1) (by rw [after_after, after_after]; exact he7)
    (by rw [after_after, after_after]; exact he8) hU
    (by rw [p5, after_after]; exact after_eq (by omega))
    (by
      rw [k5 9 (by decide) (by decide) (by decide) (by decide) (by decide), u4x9]
      exact VectorAt.frame hframe5 he.vector)
    (by
      rw [k5 17 (by decide) (by decide) (by decide) (by decide) (by decide),
        k5 1 (by decide) (by decide) (by decide) (by decide) (by decide), hK4 17 keptReg_17,
        hK4 1 keptReg_1]
      have := he.below
      omega)
    (fun j hj => by
      rw [k5 17 (by decide) (by decide) (by decide) (by decide) (by decide),
        k5 1 (by decide) (by decide) (by decide) (by decide) (by decide), hK4 17 keptReg_17,
        hK4 1 keptReg_1]
      rw [Nat.add_assoc]; exact he.guest _ (by omega))
  have hK5 : ∀ q : Fin 32, KeptReg q → u5.x q = s.x q := fun q hq => by
    rw [k5 q (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide)) (hq.ne (by decide))
      (hq.ne (by decide)), hK4 q hq]
  refine ⟨u6, hr3.trans (r4.trans (r5.trans r6)), by rw [sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [io6, io5, io4, io3, io2, io1],
    by rw [k6 17 (by decide) (by decide) (by decide) (by decide) (by decide), hK5 17 keptReg_17],
    by rw [k6 18 (by decide) (by decide) (by decide) (by decide) (by decide), hK5 18 keptReg_18],
    ?_⟩
  rw [ite_eq_left ⟨hfit, hreg⟩]
  refine ⟨by rw [p6, hK5 30 keptReg_30], x6, ?_⟩
  rw [m6, m5, hK5 17 keptReg_17, hK5 1 keptReg_1]

end LeanExe.A64
