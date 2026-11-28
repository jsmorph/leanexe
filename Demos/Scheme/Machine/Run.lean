module

public import Demos.Scheme.Machine.Read
public import Demos.Scheme.Machine.Print
public import Demos.Scheme.Machine.Convert
public import Demos.Scheme.Machine.Eval

@[expose] public section

/-! The driver of the executable interpreter: the initial machine, the dispatch of one step on the
phase, and the bytes of the outcome, a status byte followed by text, as [the profile](../profile.md)
states them.  `runWith names mode cap outCap fuel src` runs at most `fuel` steps on the program
whose bytes are `src`, with an arena of `cap` slots and an output buffer of `outCap` bytes, both at
most `2^24`, and `mode` 0 to read and write the data, 1 to expand and write the code, and 2 to
evaluate and write the value. -/

namespace Demos.Scheme.Machine

/-- The largest arena and output buffer. -/
def MAXCAP : UInt64 := 16777216

/-- The initial machine, with the status byte 0 in the output buffer. -/
def initMachine (cap outCap runMode : UInt64) : Machine :=
  let cap := min cap MAXCAP
  let outCap := min outCap MAXCAP
  let m : Machine := ⟨LeanExe.build cap fun _ => ⟨0, 0, 0, 0, 0⟩,
    LeanExe.build outCap fun _ => 0, 1, cap, 0, outCap, READ, 0, 0, 0, 0, NONE, 0, NILV, 0, NONE,
    NONE, NONE, NONE, runMode⟩
  emit m 0

/-- The next top-level datum: in mode 0, the datum to write. -/
def topStep (m : Machine) : Machine :=
  if m.forms == NILV || !isPair m.heap m.forms then { m with mode := DONE }
  else
    let d := fa m.heap m.forms
    let rest := fb m.heap m.forms
    { m with
      x := d
      forms := rest
      aux := LINE
      mode := PRINT }

/-- The next top-level datum in mode 1: its forms to expand and write. -/
def topExpandNext (m : Machine) : Machine :=
  if m.forms == NILV || !isPair m.heap m.forms then { m with mode := DONE }
  else
    let d := fa m.heap m.forms
    let rest := fb m.heap m.forms
    topExpand { m with forms := rest } d

/-- The chain of a datum's forms in `val`: in mode 1, the forms to write. -/
def topCode (m : Machine) : Machine :=
  let m := pushFrame m V_TOP m.val 0 0
  { m with mode := M1NEXT }

/-- One step of the machine. -/
def step (names : Array UInt64) (src : LeanExe.Bytes) (m : Machine) : Machine :=
  let mode := m.mode
  if mode == EVAL then evalStep m
  else if mode == RETURN then returnStep m
  else if mode == APPLY then applyStep m
  else if mode == READ then readStep names src m
  else if mode == EXPAND then expandStep m
  else if mode == EXPANDED then expandReturn m
  else if mode == EXP_OR then expandOrAnd m F_OR
  else if mode == EXP_AND then expandOrAnd m F_AND
  else if mode == EXP_COND then expandCondStep m
  else if mode == EXP_QQ then expandQQ m
  else if mode == CASECL then caseClause m
  else if mode == TOPWALK then topWalk m
  else if mode == TOP then
    if m.runMode == 0 then topStep m else if m.runMode == 1 then topExpandNext m else startEval m
  else if mode == TOPCODE then if m.runMode == 1 then topCode m else topRun m
  else if mode == CONV then convStep m
  else if mode == CONVK then convReturn m
  else if mode == M1NEXT then m1Next m
  else if mode == PRINT then printStep names m
  else if mode == PRINTK then printFrame m
  else if mode == LINE then { (emit m 10) with mode := if m.runMode == 1 then M1NEXT else TOP }
  else { m with mode := DONE }

/-- The output buffer with the bytes of an outcome other than a value: its status byte, and for a
read error, a syntax error, an error, or a restriction, its text and irritant. -/
def renderOutcome (names : Array UInt64) (m : Machine) : Machine :=
  let cls := if m.status == 0 then 6 else m.status / 256
  let entry := m.status % 256
  let detail := m.detail
  let spelling := fa m.heap detail
  let m := emit { m with outLen := 0, status := 0 } cls
  if cls == 0 || cls > 4 then m
  else
    let code := names[(entry * 6).toNat]!
    let m := emitEntry names m entry
    if code == T_KEYWORD then emitEntry names m (detail - 1)
    else if code == T_SYMBOL then emitString m spelling false
    else if code == T_OFFSET then emitInt (emitEntry names m M_T_AT) detail.toInt64
    else m

/-- The bytes of the run's outcome. -/
def finish (names : Array UInt64) (m : Machine) : LeanExe.Bytes :=
  let m := if m.status == 0 && m.mode == DONE then m else renderOutcome names m
  LeanExe.Bytes.build (min m.outLen m.outCap) fun i => m.out[i.toNat]!

/-- The run of at most `fuel` steps on the program `src`. -/
def runWith (names : Array UInt64) (mode cap outCap fuel : UInt64) (src : LeanExe.Bytes) :
    LeanExe.Bytes :=
  let m := LeanExe.repeatWhile fuel (initMachine cap outCap mode)
    (fun m => m.status == 0 && m.mode != DONE) fun m => step names src m
  finish names m

end Demos.Scheme.Machine
