import LeanExe.A64.Proof.LinuxMain
import LeanExe.A64.Proof.BytesProgram

/-!
The run of a program of `genSysProgram`, a Linux executable's program, from `main`: the call of
the allocator with `inMax + 1`, the read loop of `run_readLoop` into the block that it returns,
the call of the function over bytes on the bytes read, and the write loop of `run_writeLoop'`.
`sysProgram_run` follows the run at one fuel of Talos's runs of the two calls, as
`bytesProgram_run` does for the UART's entry routine.  An input longer than `inMax` ends the run
at the exit word with status 64 and nothing written; otherwise the process does what `SysResult`
states for Talos's run of the function on the buffer of the input, or reaches the stub of an
overflow of the stack.  No call fails.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- `genSysMain`'s code: the frame and X18, the allocation, the read loop, the call of the
function, the write loop, the return, and the stubs of statuses 64, 65, and 66. -/
theorem gen_sysMain {a e a0 rd wr inMax room base : UInt64} {main : List Instr}
    (hg : genSysMain a e a0 rd wr inMax room base = .ok main) :
    ∃ ga gr fe fl fr go gk fd gw fz fw gb x64 x65 x66,
      bField (after a 12) a0 = .ok ga ∧ bField (after a 22) rd = .ok gr ∧
      cbField (after a 23) (after a 30) = .ok fe ∧ cbField (after a 25) (after a 62) = .ok fl ∧
      cbField (after a 28) (after a 21) = .ok fr ∧ bField (after a 29) (after a 57) = .ok go ∧
      bField (after a 36) e = .ok gk ∧ cbField (after a 41) (after a 50) = .ok fd ∧
      bField (after a 43) wr = .ok gw ∧ cbField (after a 44) (after a 67) = .ok fz ∧
      cbField (after a 46) (after a 67) = .ok fw ∧ bField (after a 49) (after a 41) = .ok gb ∧
      bField (after (after a 57) 4) base = .ok x64 ∧
      bField (after (after a 62) 4) base = .ok x65 ∧
      bField (after (after a 67) 4) base = .ok x66 ∧
      main = ([.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
          [.subReg 18 18 16]) ++
        (movImm 0 (inMax + 1) ++ ([.bl ga, .str 0 31 1, .addReg 1 17 0, .addImm 1 1 2048,
          .addImm 1 1 2048] ++ (movImm 2 (inMax + 1) ++ ([.movz 0 0 0, .bl gr, .cbz 0 fe,
          .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b go] ++
          (movImm 16 (inMax + 1) ++ ([.subReg 1 16 2, .ldr 0 31 1, .bl gk, mov 2 1,
          .addReg 1 17 0, .addImm 1 1 2048, .addImm 1 1 2048] ++ ([.cbz 2 fd, .movz 0 1 0,
          .bl gw, .cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw, .addReg 1 1 0, .subReg 2 2 0,
          .b gb] ++ (movImm 0 0 ++ ([.ldr 30 31 0, .addImm 31 31 16, .ret 30] ++
          ((movImm 0 64 ++ [.b x64]) ++ ((movImm 0 65 ++ [.b x65]) ++
          (movImm 0 66 ++ [.b x66])))))))))))) := by
  unfold genSysMain at hg
  obtain ⟨ga, h1⟩ : ∃ v, bField (after a 12) a0 = .ok v := by
    cases h : bField (after a 12) a0 with
    | error e => simp [h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gr, h2⟩ : ∃ v, bField (after a 22) rd = .ok v := by
    cases h : bField (after a 22) rd with
    | error e => simp [h1, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fe, h3⟩ : ∃ v, cbField (after a 23) (after a 30) = .ok v := by
    cases h : cbField (after a 23) (after a 30) with
    | error e => simp [h1, h2, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fl, h4⟩ : ∃ v, cbField (after a 25) (after a 62) = .ok v := by
    cases h : cbField (after a 25) (after a 62) with
    | error e => simp [h1, h2, h3, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fr, h5⟩ : ∃ v, cbField (after a 28) (after a 21) = .ok v := by
    cases h : cbField (after a 28) (after a 21) with
    | error e => simp [h1, h2, h3, h4, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨go, h6⟩ : ∃ v, bField (after a 29) (after a 57) = .ok v := by
    cases h : bField (after a 29) (after a 57) with
    | error e => simp [h1, h2, h3, h4, h5, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gk, h7⟩ : ∃ v, bField (after a 36) e = .ok v := by
    cases h : bField (after a 36) e with
    | error e => simp [h1, h2, h3, h4, h5, h6, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fd, h8⟩ : ∃ v, cbField (after a 41) (after a 50) = .ok v := by
    cases h : cbField (after a 41) (after a 50) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gw, h9⟩ : ∃ v, bField (after a 43) wr = .ok v := by
    cases h : bField (after a 43) wr with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fz, h10⟩ : ∃ v, cbField (after a 44) (after a 67) = .ok v := by
    cases h : cbField (after a 44) (after a 67) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨fw, h11⟩ : ∃ v, cbField (after a 46) (after a 67) = .ok v := by
    cases h : cbField (after a 46) (after a 67) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨gb, h12⟩ : ∃ v, bField (after a 49) (after a 41) = .ok v := by
    cases h : bField (after a 49) (after a 41) with
    | error e => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x64, h13⟩ : ∃ v, bField (after (after a 57) 4) base = .ok v := by
    cases h : bField (after (after a 57) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x65, h14⟩ : ∃ v, bField (after (after a 62) 4) base = .ok v := by
    cases h : bField (after (after a 62) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h, bind, Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  obtain ⟨x66, h15⟩ : ∃ v, bField (after (after a 67) 4) base = .ok v := by
    cases h : bField (after (after a 67) 4) base with
    | error e =>
      simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h, bind,
        Except.bind] at hg
    | ok v => exact ⟨v, rfl⟩
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, bind,
    Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  refine ⟨ga, gr, fe, fl, fr, go, gk, fd, gw, fz, fw, gb, x64, x65, x66, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_⟩
  rw [← hg]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem genSysMain_length {a e a0 rd wr inMax room base : UInt64} {main : List Instr}
    (hg : genSysMain a e a0 rd wr inMax room base = .ok main) : main.length = sysMainSize := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, rfl⟩ := gen_sysMain hg
  simp only [List.length_append, movImm_length, List.length_cons, List.length_nil, sysMainSize]

/-- The program of `genSysProgram`: `genProgramWith` with the functions that may store bytes,
whose `main` is `genSysMain` with the entries of function `k` and of the allocator, function 0
among the functions that calls reach from function `k`. -/
theorem gen_sysProgram {m : Module} {k : Nat} {inMax rd wr base room : UInt64} {cap : Nat}
    {is : List Instr} (hg : genSysProgram m k inMax rd wr base room cap = .ok is) :
    ∃ gts fs first T main fns e pk rk a0 p0 r0 g1 g2 g3 g4,
      areaOk m cap = true ∧ globalTypesOf m = some gts ∧ gts.length ≤ 511 ∧
      (reachFrom m k).mapM (funcOf m) = .ok fs ∧
      first = after (after base 1) sysMainSize ∧
      T = endOf (sigIn (callTargets m k) fs) first fs ∧
      entryIn (sigIn (callTargets m k) fs) first fs k = some (e, pk, rk) ∧
      entryIn (sigIn (callTargets m k) fs) first fs 0 = some (a0, p0, r0) ∧
      genSysMain (after base 1) e a0 rd wr inMax room base = .ok main ∧
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

end LeanExe.A64
