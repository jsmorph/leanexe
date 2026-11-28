module

public import LeanExe.A64.Proof.LinuxProgram
public import LeanExe.A64.Stamp

@[expose] public section

/-!
The code of the stamp program's entry routine `genStampMain` and of its program
`genStampProgram`.  `gen_stampMain` gives the instructions of `genStampMain` with the branch
fields that the generator computed, as `gen_sysMain` gives those of `genSysMain`, and
`storeWords_code` the instructions that store the words of a path in the frame.
`genStampMain_length` and `genStampProgram_length` count the instructions.
-/

namespace LeanExe.A64

open Wasm

theorem bind_ok {α β : Type} {e : GenM α} {f : α → GenM β} {v : β} (h : (e >>= f) = .ok v) :
    ∃ x, e = .ok x ∧ f x = .ok v := by
  cases e with
  | error => cases h
  | ok x => exact ⟨x, rfl, h⟩

theorem bField_congr {h1 h2 t1 t2 : UInt64} {x : Fin 67108864} (e1 : h1 = h2) (e2 : t1 = t2)
    (h : bField h2 t2 = .ok x) : bField h1 t1 = .ok x := by
  subst e1 e2
  exact h

theorem cbField_congr {h1 h2 t1 t2 : UInt64} {x : Fin 524288} (e1 : h1 = h2) (e2 : t1 = t2)
    (h : cbField h2 t2 = .ok x) : cbField h1 t1 = .ok x := by
  subst e1 e2
  exact h

/-- `n` and `m` instructions after `a` name the same address when `n = m`. -/
theorem after_congr (a : UInt64) {n m : Nat} (h : n = m) : after a n = after a m := by rw [h]

/-- The results of `mapM` in `GenM`: one for each element, each the function's result. -/
theorem mapM_ok {α β : Type} {f : α → GenM β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = .ok bs →
      bs.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < bs.length), f l[i] = .ok bs[i]
  | [], bs, h => by
    rw [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs', hbs', h⟩ := bind_ok h
    cases h
    obtain ⟨hl, hi⟩ := mapM_ok hbs'
    refine ⟨by simp [hl], fun i h h' => ?_⟩
    cases i with
    | zero => exact hb
    | succ i => exact hi i (by simpa using h) (by simpa using h')

/-- The parts of `storeWords ws slot`: for each word `i`, a `movImm` of the word into X16 and
its store into slot `slot + i`. -/
theorem storeWords_parts {ws : List UInt64} {slot : Nat} {is : List Instr}
    (hg : storeWords ws slot = .ok is) :
    ∃ parts : List (List Instr), is = parts.flatten ∧ parts.length = ws.length ∧
      ∀ i (h : i < parts.length), ∃ h' : slot + i < 4096,
        parts[i] = movImm 16 (ws.getD i 0) ++ [.str 16 31 ⟨slot + i, h'⟩] := by
  unfold storeWords at hg
  obtain ⟨parts, hp, hg⟩ := bind_ok hg
  cases hg
  obtain ⟨hl, hi⟩ := mapM_ok hp
  simp only [List.length_range] at hl hi
  refine ⟨parts, rfl, hl, fun i h => ?_⟩
  have := hi i (by omega) h
  simp only [List.getElem_range] at this
  by_cases h' : slot + i < 4096
  · rw [dite_eq_left h'] at this
    exact ⟨h', (Except.ok.inj this).symm⟩
  · rw [dite_eq_right h'] at this
    cases this

theorem flatten_five : ∀ (ps : List (List Instr)), (∀ p ∈ ps, p.length = 5) →
    ps.flatten.length = 5 * ps.length
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h p List.mem_cons_self, flatten_five ps fun q hq => h q (List.mem_cons_of_mem _ hq)]
    omega

theorem CodeAt.flatten_five {code : UInt64 → Option UInt32} :
    ∀ (ps : List (List Instr)) (b : UInt64), (∀ p ∈ ps, p.length = 5) →
      CodeAt code b ps.flatten → ∀ i (h : i < ps.length), CodeAt code (after b (5 * i)) ps[i]
  | [], _, _, _, i, h => absurd h (by simp)
  | p :: ps, b, h, hcb, i, hi => by
    rw [List.flatten_cons] at hcb
    have hs := CodeAt.split code hcb (h p List.mem_cons_self)
    cases i with
    | zero => simpa [after_zero] using hs.1
    | succ i =>
      have := CodeAt.flatten_five ps (after b 5) (fun q hq => h q (List.mem_cons_of_mem _ hq))
        hs.2 i (by simpa using hi)
      rw [after_after] at this
      simpa [show 5 + 5 * i = 5 * (i + 1) by omega] using this

theorem storeWords_length {ws : List UInt64} {slot : Nat} {is : List Instr}
    (hg : storeWords ws slot = .ok is) : is.length = 5 * ws.length := by
  obtain ⟨parts, rfl, hl, hp⟩ := storeWords_parts hg
  rw [flatten_five parts fun p hm => ?_, hl]
  obtain ⟨i, h, rfl⟩ := List.getElem_of_mem hm
  obtain ⟨h', e⟩ := hp i h
  rw [e]
  rfl

/-- The code of `storeWords ws slot` at `a`: for each word `i`, five instructions from
`after a (5 * i)`, a `movImm` of the word into X16 and its store into slot `slot + i`. -/
theorem storeWords_code {code : UInt64 → Option UInt32} {ws : List UInt64} {slot : Nat}
    {is : List Instr} (hg : storeWords ws slot = .ok is) {a : UInt64} (hc : CodeAt code a is) :
    ∀ i < ws.length, ∃ h : slot + i < 4096,
      CodeAt code (after a (5 * i)) (movImm 16 (ws.getD i 0) ++ [.str 16 31 ⟨slot + i, h⟩]) := by
  obtain ⟨parts, rfl, hl, hp⟩ := storeWords_parts hg
  have h5 : ∀ p ∈ parts, p.length = 5 := fun p hm => by
    obtain ⟨i, h, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨h', e⟩ := hp i h
    rw [e]
    rfl
  intro i hi
  obtain ⟨h', e⟩ := hp i (by omega)
  exact ⟨h', e ▸ CodeAt.flatten_five parts a h5 hc i (by omega)⟩

/-- The code of `genStampMain` at `a`, with `wi` and `wo` the numbers of words of the two paths:
the frame, X18, and the allocation (17 instructions); the call of `clock_gettime` (5) and of
`getrandom` (7); the input path's stores (`5 * wi`); the input's `openat` (20); the read loop
(10); the store of the count, the input's `close`, and the call of the function (20); the output
path's stores (`5 * wo`); the output's `openat` (17); the write loop (10); the output's `close` and
the return (11); and the stubs of statuses 64, 67, 68, 69, 70, 71, 72, 73, and 74 (5 each). -/
theorem gen_stampMain {a e a0 svc inMax room base : UInt64} {pin pout : List UInt8}
    {main : List Instr} (hg : genStampMain a e a0 svc inMax room base pin pout = .ok main) :
    ∃ (wi wo : Nat) (fr outSlot : Fin 4096) (sIn sOut : List Instr)
      (ga c20 c26 cI cR g64 cC gk cO cW gb cD : Fin 67108864)
      (f72 f73 f67 fe f68 fr' f69 f70 fd fz fw f71 : Fin 524288)
      (x64 x67 x68 x69 x70 x71 x72 x73 x74 : Fin 67108864),
      wi = (pathWords pin).length ∧ wo = (pathWords pout).length ∧
      pathOk pin = true ∧ pathOk pout = true ∧ fr.val = stampFrame pin pout ∧
      outSlot.val = 32 + 8 * wi ∧
      storeWords (pathWords pin) 4 = .ok sIn ∧ storeWords (pathWords pout) (4 + wi) = .ok sOut ∧
      bField (after a 12) a0 = .ok ga ∧
      bField (after a 20) svc = .ok c20 ∧
      cbField (after a 21) (after a (147 + 5 * wi + 5 * wo)) = .ok f72 ∧
      bField (after a 26) svc = .ok c26 ∧
      cbField (after a 28) (after a (152 + 5 * wi + 5 * wo)) = .ok f73 ∧
      bField (after a (40 + 5 * wi)) svc = .ok cI ∧
      cbField (after a (42 + 5 * wi)) (after a (122 + 5 * wi + 5 * wo)) = .ok f67 ∧
      bField (after a (51 + 5 * wi)) svc = .ok cR ∧
      cbField (after a (52 + 5 * wi)) (after a (59 + 5 * wi)) = .ok fe ∧
      cbField (after a (54 + 5 * wi)) (after a (127 + 5 * wi + 5 * wo)) = .ok f68 ∧
      cbField (after a (57 + 5 * wi)) (after a (49 + 5 * wi)) = .ok fr' ∧
      bField (after a (58 + 5 * wi)) (after a (117 + 5 * wi + 5 * wo)) = .ok g64 ∧
      bField (after a (67 + 5 * wi)) svc = .ok cC ∧
      cbField (after a (68 + 5 * wi)) (after a (132 + 5 * wi + 5 * wo)) = .ok f69 ∧
      bField (after a (72 + 5 * wi)) e = .ok gk ∧
      bField (after a (90 + 5 * wi + 5 * wo)) svc = .ok cO ∧
      cbField (after a (92 + 5 * wi + 5 * wo)) (after a (137 + 5 * wi + 5 * wo)) = .ok f70 ∧
      cbField (after a (96 + 5 * wi + 5 * wo)) (after a (106 + 5 * wi + 5 * wo)) = .ok fd ∧
      bField (after a (99 + 5 * wi + 5 * wo)) svc = .ok cW ∧
      cbField (after a (100 + 5 * wi + 5 * wo)) (after a (157 + 5 * wi + 5 * wo)) = .ok fz ∧
      cbField (after a (102 + 5 * wi + 5 * wo)) (after a (157 + 5 * wi + 5 * wo)) = .ok fw ∧
      bField (after a (105 + 5 * wi + 5 * wo)) (after a (96 + 5 * wi + 5 * wo)) = .ok gb ∧
      bField (after a (108 + 5 * wi + 5 * wo)) svc = .ok cD ∧
      cbField (after a (109 + 5 * wi + 5 * wo)) (after a (142 + 5 * wi + 5 * wo)) = .ok f71 ∧
      bField (after a (121 + 5 * wi + 5 * wo)) base = .ok x64 ∧
      bField (after a (126 + 5 * wi + 5 * wo)) base = .ok x67 ∧
      bField (after a (131 + 5 * wi + 5 * wo)) base = .ok x68 ∧
      bField (after a (136 + 5 * wi + 5 * wo)) base = .ok x69 ∧
      bField (after a (141 + 5 * wi + 5 * wo)) base = .ok x70 ∧
      bField (after a (146 + 5 * wi + 5 * wo)) base = .ok x71 ∧
      bField (after a (151 + 5 * wi + 5 * wo)) base = .ok x72 ∧
      bField (after a (156 + 5 * wi + 5 * wo)) base = .ok x73 ∧
      bField (after a (161 + 5 * wi + 5 * wo)) base = .ok x74 ∧
      main = ([.subImm 31 31 fr, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
          [.subReg 18 18 16] ++ movImm 0 (inMax + 33) ++
          [.bl ga, .str 0 31 1, .addReg 19 17 0, .addImm 19 19 2048, .addImm 19 19 2048]) ++
        ([.movz 0 0 0, .addImm 1 19 0, .movz 8 113 0, .bl c20, .cbnz 0 f72] ++
        ([.addImm 0 19 16, .movz 1 16 0, .movz 2 0 0, .movz 8 278 0, .bl c26, .subsImm 31 0 16,
          .bcond 1 f73] ++
        (sIn ++
        ((movImm 0 atFdcwd ++ [.addImm 1 31 32] ++ movImm 2 stampInFlags ++
          [.movz 3 0 0, .movz 8 56 0, .bl cI, .lsrImm 16 0 31, .cbnz 16 f67, .str 0 31 2,
            .addImm 1 19 32] ++ movImm 2 (inMax + 1)) ++
        ([.ldr 0 31 2, .movz 8 63 0, .bl cR, .cbz 0 fe, .subsReg 31 0 2, .bcond 8 f68,
          .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr', .b g64] ++
        ((movImm 16 (inMax + 1) ++ [.subReg 16 16 2, .str 16 31 3, .ldr 0 31 2, .movz 8 57 0,
          .bl cC, .cbnz 0 f69, .ldr 0 31 1, .ldr 1 31 3, .addImm 1 1 32, .bl gk, mov 2 1,
          .addReg 1 17 0, .addImm 1 1 2048, .addImm 1 1 2048, .str 1 31 1, .str 2 31 3]) ++
        (sOut ++
        ((movImm 0 atFdcwd ++ [.addImm 1 31 outSlot] ++ movImm 2 stampOutFlags ++
          [.movz 3 stampOutMode 0, .movz 8 56 0, .bl cO, .lsrImm 16 0 31, .cbnz 16 f70,
            .str 0 31 2, .ldr 1 31 1, .ldr 2 31 3]) ++
        ([.cbz 2 fd, .ldr 0 31 2, .movz 8 64 0, .bl cW, .cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw,
          .addReg 1 1 0, .subReg 2 2 0, .b gb] ++
        (([.ldr 0 31 2, .movz 8 57 0, .bl cD, .cbnz 0 f71] ++ movImm 0 0 ++
          [.ldr 30 31 0, .addImm 31 31 fr, .ret 30]) ++
        ((movImm 0 (UInt64.ofNat 64) ++ [.b x64]) ++ (movImm 0 (UInt64.ofNat 67) ++ [.b x67]) ++
          (movImm 0 (UInt64.ofNat 68) ++ [.b x68]) ++ (movImm 0 (UInt64.ofNat 69) ++ [.b x69]) ++
          (movImm 0 (UInt64.ofNat 70) ++ [.b x70]) ++ (movImm 0 (UInt64.ofNat 71) ++ [.b x71]) ++
          (movImm 0 (UInt64.ofNat 72) ++ [.b x72]) ++ (movImm 0 (UInt64.ofNat 73) ++ [.b x73]) ++
          (movImm 0 (UInt64.ofNat 74) ++ [.b x74])))))))))))) := by
  unfold genStampMain at hg
  simp only at hg
  by_cases hp : (pathOk pin && pathOk pout) = true
  swap
  · rw [ite_eq_right hp] at hg
    cases hg
  rw [ite_eq_left hp] at hg
  by_cases hf : stampFrame pin pout < 4096
  swap
  · rw [dite_eq_right hf] at hg
    cases hg
  rw [dite_eq_left hf] at hg
  obtain ⟨fr, hfr, hg⟩ := bind_ok hg
  cases hfr
  by_cases ho : 32 + 8 * (pathWords pin).length < 4096
  swap
  · rw [dite_eq_right ho] at hg
    cases hg
  rw [dite_eq_left ho] at hg
  obtain ⟨os, hos, hg⟩ := bind_ok hg
  cases hos
  obtain ⟨ga, hga, hg⟩ := bind_ok hg
  obtain ⟨sIn, hsIn, hg⟩ := bind_ok hg
  obtain ⟨sOut, hsOut, hg⟩ := bind_ok hg
  obtain ⟨y1, hy, hg⟩ := bind_ok hg
  obtain ⟨c20, hc20, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f72, hf72, hg⟩ := bind_ok hg
  obtain ⟨y2, hy, hg⟩ := bind_ok hg
  obtain ⟨c26, hc26, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f73, hf73, hg⟩ := bind_ok hg
  obtain ⟨y3, hy, hg⟩ := bind_ok hg
  obtain ⟨cI, hcI, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f67, hf67, hg⟩ := bind_ok hg
  obtain ⟨y4, hy, hg⟩ := bind_ok hg
  obtain ⟨cR, hcR, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨fe, hfe, hg⟩ := bind_ok hg
  obtain ⟨f68, hf68, hg⟩ := bind_ok hg
  obtain ⟨fr', hfr', hg⟩ := bind_ok hg
  obtain ⟨g64, hg64, hg⟩ := bind_ok hg
  obtain ⟨y5, hy, hg⟩ := bind_ok hg
  obtain ⟨cC, hcC, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f69, hf69, hg⟩ := bind_ok hg
  obtain ⟨gk, hgk, hg⟩ := bind_ok hg
  obtain ⟨y6, hy, hg⟩ := bind_ok hg
  obtain ⟨cO, hcO, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f70, hf70, hg⟩ := bind_ok hg
  obtain ⟨fd, hfd, hg⟩ := bind_ok hg
  obtain ⟨y7, hy, hg⟩ := bind_ok hg
  obtain ⟨cW, hcW, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨fz, hfz, hg⟩ := bind_ok hg
  obtain ⟨fw, hfw, hg⟩ := bind_ok hg
  obtain ⟨gb, hgb, hg⟩ := bind_ok hg
  obtain ⟨y8, hy, hg⟩ := bind_ok hg
  obtain ⟨cD, hcD, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨f71, hf71, hg⟩ := bind_ok hg
  obtain ⟨s64, hy, hg⟩ := bind_ok hg
  obtain ⟨x64, hx64, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s67, hy, hg⟩ := bind_ok hg
  obtain ⟨x67, hx67, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s68, hy, hg⟩ := bind_ok hg
  obtain ⟨x68, hx68, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s69, hy, hg⟩ := bind_ok hg
  obtain ⟨x69, hx69, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s70, hy, hg⟩ := bind_ok hg
  obtain ⟨x70, hx70, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s71, hy, hg⟩ := bind_ok hg
  obtain ⟨x71, hx71, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s72, hy, hg⟩ := bind_ok hg
  obtain ⟨x72, hx72, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s73, hy, hg⟩ := bind_ok hg
  obtain ⟨x73, hx73, hy⟩ := bind_ok hy
  cases hy
  obtain ⟨s74, hy, hg⟩ := bind_ok hg
  obtain ⟨x74, hx74, hy⟩ := bind_ok hy
  cases hy
  cases hg
  simp only [Bool.and_eq_true] at hp
  refine ⟨_, _, ⟨stampFrame pin pout, hf⟩, ⟨32 + 8 * (pathWords pin).length, ho⟩, sIn, sOut, ga,
    c20, c26, cI, cR, g64, cC, gk, cO, cW, gb, cD, f72, f73, f67, fe, f68, fr', f69, f70, fd, fz,
    fw, f71, x64, x67, x68, x69, x70, x71, x72, x73, x74, rfl, rfl, hp.1, hp.2, rfl, rfl, hsIn,
    hsOut, hga, hc20,
    cbField_congr rfl (after_congr a (by omega)) hf72, hc26, cbField_congr rfl (after_congr a (by omega)) hf73,
    bField_congr (after_congr a (by omega)) rfl hcI, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hf67,
    bField_congr (after_congr a (by omega)) rfl hcR, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hfe, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hf68,
    cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hfr', bField_congr (after_congr a (by omega)) (after_congr a (by omega)) hg64,
    bField_congr (after_congr a (by omega)) rfl hcC, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hf69, bField_congr (after_congr a (by omega)) rfl hgk,
    bField_congr (after_congr a (by omega)) rfl hcO, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hf70,
    cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hfd, bField_congr (after_congr a (by omega)) rfl hcW, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hfz, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hfw,
    bField_congr (after_congr a (by omega)) (after_congr a (by omega)) hgb, bField_congr (after_congr a (by omega)) rfl hcD, cbField_congr (after_congr a (by omega)) (after_congr a (by omega)) hf71,
    bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx64, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx67, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx68,
    bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx69, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx70, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx71,
    bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx72, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx73, bField_congr ((after_congr a (by omega)).trans (after_after a _ 4).symm) rfl hx74, ?_⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem genStampMain_length {a e a0 svc inMax room base : UInt64} {pin pout : List UInt8}
    {main : List Instr} (hg : genStampMain a e a0 svc inMax room base pin pout = .ok main) :
    main.length = stampMainSize pin pout := by
  obtain ⟨wi, wo, fr, os, sIn, sOut, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hwi, hwo, -, -, -, -, hsIn, hsOut, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    rfl⟩ := gen_stampMain hg
  simp only [List.length_append, movImm_length, List.length_cons, List.length_nil,
    storeWords_length hsIn, storeWords_length hsOut, stampMainSize, ← hwi, ← hwo]
  omega

/-- The program of `genStampProgram`: `genProgramWith` with the functions that may store bytes,
whose `main` is `genStampMain` with the entries of function `k` and of the allocator, function 0
among the functions that calls reach from function `k`. -/
theorem gen_stampProgram {m : Module} {k : Nat} {inMax svc base room : UInt64} {cap : Nat}
    {pin pout : List UInt8} {is : List Instr}
    (hg : genStampProgram m k inMax svc base room cap pin pout = .ok is) :
    ∃ gts fs first T main fns e pk rk a0 p0 r0 g1 g2 g3 g4,
      areaOk m cap = true ∧ globalTypesOf m = some gts ∧ gts.length ≤ 511 ∧
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) (stampMainSize pin pout) ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      entryIn (sigIn (callTargets m k) fs) first fs 0 = some (a0, p0, r0) ∧
      genStampMain (after base 1) e a0 svc inMax room base pin pout = .ok main ∧
      genFunctions (tableOf (callTargets m k) first fs)
        ⟨T, after T 5, after T 10, after T 15, cap, gts, true⟩ first fs = .ok fns ∧
      is = main ++ fns ++ (movImm 0 (UInt64.ofNat 1) ++ [.b g1] ++
        (movImm 0 (UInt64.ofNat 2) ++ [.b g2]) ++ (movImm 0 (UInt64.ofNat 3) ++ [.b g3]) ++
        (movImm 0 (UInt64.ofNat 4) ++ [.b g4])) ∧
      bField (after T 4) base = .ok g1 ∧ bField (after (after T 5) 4) base = .ok g2 ∧
      bField (after (after T 10) 4) base = .ok g3 ∧
      bField (after (after T 15) 4) base = .ok g4 := by
  obtain ⟨gts, fs, first, T, main, fns, e, pk, rk, g1, g2, g3, g4, hok, hgt, hgl, hfs, hfirst,
    hT, hen, hps, hmg, hfg, his, hb1, hb2, hb3, hb4⟩ := gen_programWith hg
  simp only [hfs, bind, Except.bind] at hmg
  rw [← hfirst] at hmg
  cases h0 : entryIn (sigIn (callTargets m k) fs) first fs 0 with
  | none => simp [h0, throw, throwThe, MonadExceptOf.throw] at hmg
  | some c =>
      obtain ⟨a0, p0, r0⟩ := c
      simp only [h0] at hmg
      exact ⟨gts, fs, first, T, main, fns, e, pk, rk, a0, p0, r0, g1, g2, g3, g4, hok, hgt, hgl,
        hfs, hfirst, hT, hen, h0, hmg, hfg, his, hb1, hb2, hb3, hb4⟩

theorem genStampProgram_length {m : Module} {k : Nat} {inMax svc base room : UInt64}
    {cap : Nat} {pin pout : List UInt8} {is : List Instr}
    (hg : genStampProgram m k inMax svc base room cap pin pout = .ok is)
    {fs : List (Nat × Function)} (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs) :
    is.length = stampMainSize pin pout +
      (fs.map fun x => functionSize (sigIn (callTargets m k) fs) x.2).sum + 20 :=
  genProgramWith_length hg (fun e main hmg => by
    simp only [bind, Except.bind] at hmg
    split at hmg
    · cases hmg
    · split at hmg
      · exact genStampMain_length hmg
      · cases hmg) hfs

end LeanExe.A64
