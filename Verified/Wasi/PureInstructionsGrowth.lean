import Verified.Wasi.PureInstructionsBasic

namespace Verified.Wasi.PureTransport

open Wasm

theorem growth_transport {World : Type} {source target : Module}
    (hMemory64 : target.memIs64 = source.memIs64)
    (hMemoryCap : target.memoryCap = source.memoryCap)
    {inst : Instruction} (hForm : Encoding.InstructionForm inst)
    (hGrowth : growthAtomic inst = true)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals inst targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost) := by
  have hCap := memoryCap_zero_eq hMemoryCap initial
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    cases hForm <;> simp_all only [growthAtomic, Bool.false_eq_true]
    case memorySize =>
      simp only [execOne.eq_def, restore_mem, hMemory64,
        liftContinuation, NoReturnCall, and_self]
    case memoryGrow =>
      constructor
      · simp only [execOne.eq_def, restore_mem, restore_memoryCap, hMemory64, hCap]
        cases hValues : locals.values with
        | nil => rfl
        | cons value rest =>
          cases value with
          | i32 delta =>
            simp only []
            cases hGrow : initial.mem.grow delta (initial.memoryCap source 0) with
            | none => rfl
            | some result => rcases result with ⟨mem, pages⟩; rfl
          | i64 delta =>
            by_cases hLarge : delta.toNat ≥ 2 ^ 32
            · simp only [if_pos hLarge]
              rfl
            · simp only [if_neg hLarge]
              cases hGrow : initial.mem.grow delta.toUInt32 (initial.memoryCap source 0) with
              | none => rfl
              | some result => rcases result with ⟨mem, pages⟩; rfl
          | f32 _ => rfl
          | f64 _ => rfl
          | funcref _ => rfl
          | externref _ => rfl
          | exnref _ => rfl
          | v128 _ => rfl
          | anyref _ => rfl
      · apply (noReturnCall_iff_flag _).2
        simp only [execOne.eq_def]
        repeat' first | rfl | split

end Verified.Wasi.PureTransport
