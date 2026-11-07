import LeanExe.A64.Startup

/-!
The startup's instructions as `startupCode` gives them, with the fields of its branches and the
instructions of its addresses named.  `addrOf_ok` unpacks the `ADRP` and `ADD` of an address, and
`startupCode_ok` the whole startup, whose instruction `k` lies at `after (L.image + 64) k`.
-/

namespace LeanExe.A64

open Wasm

theorem addrOf_ok {d : Fin 32} {here target : UInt64} {is : List Instr}
    (h : addrOf d here target = .ok is) :
    ∃ pages : Int, -(2 ^ 20) ≤ pages ∧ pages < 2 ^ 20 ∧
      pages = Int.ofNat (target.toNat / 4096) - Int.ofNat (here.toNat / 4096) ∧
      is = [.adrp d ⟨(pages % (2 ^ 21 : Int)).toNat % 4, Nat.mod_lt _ (by decide)⟩
          ⟨(pages % (2 ^ 21 : Int)).toNat / 4 % 524288, Nat.mod_lt _ (by decide)⟩,
        .addImm d d ⟨target.toNat % 4096, Nat.mod_lt _ (by decide)⟩] := by
  unfold addrOf at h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨_, by omega, by omega, rfl, h.symm⟩

theorem addrOf_length {d : Fin 32} {here target : UInt64} {is : List Instr}
    (h : addrOf d here target = .ok is) : is.length = 2 := by
  obtain ⟨_, _, _, _, rfl⟩ := addrOf_ok h
  rfl

theorem startupCode_ok {L : Layout} {is : List Instr} (h : startupCode L = .ok is) :
    ∃ toHalt skip vec tab clr fin stk ar call back,
      cbField (after (L.image + 64) 3) (after (L.image + 64) 66) = .ok toHalt ∧
      cbField (after (L.image + 64) 29) (after (L.image + 64) 31) = .ok skip ∧
      addrOf 1 (after (L.image + 64) 4) L.vectors = .ok vec ∧
      addrOf 1 (after (L.image + 64) 23) L.table = .ok tab ∧
      addrOf 0 (after (L.image + 64) 40) L.clear = .ok clr ∧
      addrOf 1 (after (L.image + 64) 42) L.areaEnd = .ok fin ∧
      addrOf 1 (after (L.image + 64) 49) L.stackTop = .ok stk ∧
      addrOf 17 (after (L.image + 64) 52) L.area = .ok ar ∧
      bField (after (L.image + 64) 54) (after L.base 1) = .ok call ∧
      bField L.base (after (L.image + 64) 55) = .ok back ∧
      is = [mrsOf 1 .currentEL, .lsrImm 1 1 2, .subsImm 31 1 1, .bcond 1 toHalt] ++
        vec ++ [msrOf .vbar 1] ++ movImm 1 (sctlrOn - 1) ++ [msrOf .sctlr 1, msrOf .cpacr 31] ++
        movImm 1 mairValue ++ [msrOf .mair 1] ++ movImm 1 tcrValue ++ [msrOf .tcr 1] ++
        tab ++ [msrOf .ttbr0 1, mrsOf 1 .mmfr3, .movz 2 15 0, .andReg 1 1 2, .cbz 1 skip,
          msrOf .tcr2 31, .isb, .tlbiVmalle1, .dsbIsh] ++
        movImm 1 sctlrOn ++ [msrOf .sctlr 1, .isb] ++ clr ++ fin ++ clearLoop ++ stk ++
        [.addImm 31 1 0] ++ ar ++ [.bl call] ++
        movImm 1 uartAddr ++ [.strb 0 1 0, .dsbSy] ++ movImm 0 0x84000008 ++
        [.hvc0, .b 0, .b back] := by
  unfold startupCode at h
  dsimp only at h
  cases h0 : cbField (after (L.image + 64) 3) (after (L.image + 64) 66) with
  | error e => simp [h0, bind, Except.bind] at h
  | ok toHalt => ?_
  cases h1 : cbField (after (L.image + 64) 29) (after (L.image + 64) 31) with
  | error e => simp [h0, h1, bind, Except.bind] at h
  | ok skip => ?_
  cases h2 : addrOf 1 (after (L.image + 64) 4) L.vectors with
  | error e => simp [h0, h1, h2, bind, Except.bind] at h
  | ok vec => ?_
  cases h3 : addrOf 1 (after (L.image + 64) 23) L.table with
  | error e => simp [h0, h1, h2, h3, bind, Except.bind] at h
  | ok tab => ?_
  cases h4 : addrOf 0 (after (L.image + 64) 40) L.clear with
  | error e => simp [h0, h1, h2, h3, h4, bind, Except.bind] at h
  | ok clr => ?_
  cases h5 : addrOf 1 (after (L.image + 64) 42) L.areaEnd with
  | error e => simp [h0, h1, h2, h3, h4, h5, bind, Except.bind] at h
  | ok fin => ?_
  cases h6 : addrOf 1 (after (L.image + 64) 49) L.stackTop with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, bind, Except.bind] at h
  | ok stk => ?_
  cases h7 : addrOf 17 (after (L.image + 64) 52) L.area with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at h
  | ok ar => ?_
  cases h8 : bField (after (L.image + 64) 54) (after L.base 1) with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at h
  | ok call => ?_
  cases h9 : bField L.base (after (L.image + 64) 55) with
  | error e => simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind] at h
  | ok back => ?_
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind,
    pure, Except.pure, Except.ok.injEq] at h
  exact ⟨toHalt, skip, vec, tab, clr, fin, stk, ar, call, back,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.symm⟩

end LeanExe.A64
