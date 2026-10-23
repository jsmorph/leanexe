import Verified.Wasi.Relocation

namespace Verified.Wasi.PureTransport

open Wasm

def atomic : Instruction → Bool
  | .call _ | .block _ _ _ _ _ | .loop _ _ _ _ _ | .iff _ _ _ _ _ _ => false
  | _ => true

def integerAtomic : Instruction → Bool
  | .eqz | .eq | .ltU | .gtU | .leU | .geU | .add | .and
  | .eqzI64 | .eqI64 | .neI64 | .ltUI64 | .leUI64 | .geUI64
  | .addI64 | .subI64 | .mulI64 | .divUI64 | .remUI64
  | .andI64 | .orI64 | .xorI64 | .shlI64 | .shrUI64
  | .wrapI64 | .extendUI32 | .extend8S => true
  | _ => false

def floatAtomic : Instruction → Bool
  | .f32Const _ | .f64Const _
  | .f32Eq | .f32Lt | .f32Le | .f32Abs | .f32Nearest | .f32Sqrt
  | .f32Add | .f32Sub | .f32Mul | .f32Div
  | .f64Eq | .f64Lt | .f64Le | .f64Abs | .f64Sqrt
  | .f64Add | .f64Sub | .f64Mul | .f64Div
  | .f32ConvertI32S | .f32ConvertI64U | .f64ConvertI64U
  | .i32TruncSatF32S | .i64TruncSatF32U | .i64TruncSatF64U
  | .f32DemoteF64 | .f64PromoteF32
  | .i32ReinterpretF32 | .i64ReinterpretF64 | .f32ReinterpretI32 | .f64ReinterpretI64 => true
  | _ => false

def stateAtomic : Instruction → Bool
  | .unreachable | .nop | .ret | .drop | .memorySize | .memoryGrow
  | .br _ | .br_if _ | .localGet _ | .localSet _ | .localTee _
  | .globalGet _ | .globalSet _ | .load32 _ | .load64 _ | .load8U _
  | .store32 _ | .store64 _ | .store8 _ | .const _ | .constI64 _ => true
  | _ => false

def localAtomic : Instruction → Bool
  | .unreachable | .nop | .ret | .drop | .br _ | .br_if _
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _
  | .const _ | .constI64 _ => true
  | _ => false

def memoryAtomic : Instruction → Bool
  | .load32 _ | .load64 _ | .load8U _ | .store32 _ | .store64 _ | .store8 _ => true
  | _ => false

def growthAtomic : Instruction → Bool
  | .memorySize | .memoryGrow => true
  | _ => false

def noReturnCallFlag : Continuation State → Bool
  | .ReturnCall _ _ _ => false
  | _ => true

theorem noReturnCall_iff_flag (result : Continuation State) :
    NoReturnCall result ↔ noReturnCallFlag result = true := by
  cases result <;> simp [NoReturnCall, noReturnCallFlag]

theorem state_cases {inst : Instruction} (hForm : Encoding.InstructionForm inst)
    (hState : stateAtomic inst = true) :
    localAtomic inst = true ∨ memoryAtomic inst = true ∨ growthAtomic inst = true := by
  cases hForm <;> simp_all [stateAtomic, localAtomic, memoryAtomic, growthAtomic]

theorem atomic_cases {inst : Instruction} (hForm : Encoding.InstructionForm inst)
    (hAtomic : atomic inst = true) :
    integerAtomic inst = true ∨ floatAtomic inst = true ∨ stateAtomic inst = true := by
  cases hForm <;> simp_all [atomic, integerAtomic, floatAtomic, stateAtomic]

theorem relocate_atomic {inst : Instruction} (hForm : Encoding.InstructionForm inst)
    (hAtomic : atomic inst = true) : Relocation.instruction inst = inst := by
  cases hForm <;> simp_all only [atomic, Relocation.instruction, Bool.false_eq_true]

@[simp] theorem restore_mem (world : World) (store : Store Unit) :
    (restore world store).mem = store.mem := rfl

@[simp] theorem restore_globals (world : World) (store : Store Unit) :
    (restore world store).globals = store.globals := rfl

@[simp] theorem restore_memoryCap (world : World) (store : Store Unit) (m : Module)
    (index : Nat) : (restore world store).memoryCap m index = store.memoryCap m index := rfl

theorem memoryCap_zero_eq {source target : Module} (h : target.memoryCap = source.memoryCap)
    (store : Store State) : store.memoryCap target 0 = store.memoryCap source 0 := by
  simp only [Store.memoryCap, ite_true, h]

@[simp] theorem restore_update_mem (world : World) (store : Store Unit) (mem : Mem) :
    { restore world store with mem := mem } = restore world { store with mem := mem } := rfl

@[simp] theorem restore_update_globals (world : World) (store : Store Unit) (globals : Globals) :
    { restore world store with globals := globals } =
      restore world { store with globals := globals } := rfl

end Verified.Wasi.PureTransport
