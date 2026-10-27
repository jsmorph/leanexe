import LeanExe.Native.Proof.Calls
import LeanExe.Native.Proof.MemOps
import LeanExe.Native.Proof.Floats

/-!
The simulation of every instruction, and of instruction lists at every fuel up to a bound, for
code whose calls go to functions whose `CallSim` holds below that bound.
-/

namespace LeanExe.Native

open Wasm LClight

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem sim_zero {CallOk : Nat → Prop} (inst : Instruction) :
    InstrSimL A X E mod c CallOk 0 inst := by
  intro L σ n s σ' n' _ _ _ _ α st sl le m env _
  rw [execOne_zero]; trivial

theorem instr_sim (hE : EnvOk E) (hG : c.nglobals = E.globals.length) (hcap : c.cap = E.cap)
    (h64 : mod.memIs64 = false) (hres : ResOk E c.results) {CallOk : Nat → Prop}
    {F : Nat} (hP : ∀ g, g < F → ProgSim A X E mod c CallOk g)
    (hC : ∀ k, CallOk k → ∀ g, g < F → CallSim A X E mod c g k) (inst : Instruction) :
    InstrSimL A X E mod c CallOk F inst := by
  cases inst
  case localGet i => exact (sim_localGet mod F i).toL
  case localSet i => exact (sim_localSet mod F i).toL
  case localTee i => exact (sim_localTee mod F i).toL
  case globalGet i => exact (sim_globalGet hE hG F i).toL
  case globalSet i => exact (sim_globalSet hE hG F i).toL
  case const k => exact (sim_const F k).toL
  case constI64 k => exact (sim_constI64 F k).toL
  case addI64 => exact (sim_addI64 F).toL
  case subI64 => exact (sim_subI64 F).toL
  case mulI64 => exact (sim_mulI64 F).toL
  case andI64 => exact (sim_andI64 F).toL
  case orI64 => exact (sim_orI64 F).toL
  case xorI64 => exact (sim_xorI64 F).toL
  case shlI64 => exact (sim_shlI64 F).toL
  case shrUI64 => exact (sim_shrUI64 F).toL
  case divUI64 => exact (sim_divUI64 hE F).toL
  case remUI64 => exact (sim_remUI64 hE F).toL
  case eqI64 => exact (sim_eqI64 F).toL
  case neI64 => exact (sim_neI64 F).toL
  case ltUI64 => exact (sim_ltUI64 F).toL
  case leUI64 => exact (sim_leUI64 F).toL
  case geUI64 => exact (sim_geUI64 F).toL
  case eqzI64 => exact (sim_eqzI64 F).toL
  case eq => exact (sim_eq F).toL
  case eqz => exact (sim_eqz F).toL
  case and => exact (sim_and F).toL
  case wrapI64 => exact (sim_wrapI64 F).toL
  case extendUI32 => exact (sim_extendUI32 F).toL
  case unreachable => exact (sim_unreachable hE F).toL
  case load64 off => exact (sim_load64 hE F off).toL
  case store64 off => exact (sim_store64 hE F off).toL
  case memorySize => exact (sim_memorySize hE h64 F).toL
  case memoryGrow => exact (sim_memoryGrow hE hcap F).toL
  case f64Const v => exact (sim_f64Const hE F v).toL
  case f64Add => exact (sim_f64Add hE F).toL
  case f64Sub => exact (sim_f64Sub hE F).toL
  case f64Mul => exact (sim_f64Mul hE F).toL
  case f64Div => exact (sim_f64Div hE F).toL
  case f64Sqrt => exact (sim_f64Sqrt hE F).toL
  case f64Eq => exact (sim_f64Eq F).toL
  case f64Lt => exact (sim_f64Lt F).toL
  case f64Le => exact (sim_f64Le F).toL
  case f64Abs => exact (sim_f64Abs F).toL
  case f64ConvertI64U => exact (sim_f64ConvertI64U F).toL
  case f64ReinterpretI64 => exact (sim_f64ReinterpretI64 hE F).toL
  case i64ReinterpretF64 => exact (sim_i64ReinterpretF64 hE F).toL
  case i64TruncSatF64U => exact (sim_i64TruncSatF64U F).toL
  case br k => exact sim_br F k
  case br_if k => exact sim_br_if F k
  case ret => exact sim_ret hE hres F
  case block pa ra body pts rts =>
      cases F with
      | zero => exact sim_zero _
      | succ f => exact sim_block (hP f (by omega)) pa ra body pts rts
  case iff pa ra thn els pts rts =>
      cases F with
      | zero => exact sim_zero _
      | succ f => exact sim_iff (hP f (by omega)) pa ra thn els pts rts
  case loop pa ra body pts rts => exact sim_loop hP pa ra body pts rts
  case call k =>
      cases F with
      | zero => exact sim_zero _
      | succ f => exact sim_call hE f k (fun hk => hC k hk f (by omega))
  all_goals
    intro L σ n s σ' n' htr
    simp [trInstr] at htr

/-- Instruction lists simulate at every fuel up to `Fmax`, for code whose calls go to functions
whose simulation holds below `Fmax`. -/
theorem body_sim (hE : EnvOk E) (hG : c.nglobals = E.globals.length) (hcap : c.cap = E.cap)
    (h64 : mod.memIs64 = false) (hres : ResOk E c.results) {CallOk : Nat → Prop}
    {Fmax : Nat} (hC : ∀ k, CallOk k → ∀ g, g < Fmax → CallSim A X E mod c g k) :
    ∀ F, F ≤ Fmax → ProgSim A X E mod c CallOk F := by
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
      intro hF
      exact prog_sim (fun inst => instr_sim hE hG hcap h64 hres (fun g hg => ih g hg (by omega))
        (fun k hk g hg => hC k hk g (by omega)) inst)

end

end LeanExe.Native
