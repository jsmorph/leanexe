import Verified.Wasi.ProcessState
import Verified.Bytes.LiteralFrame

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

structure ProcessMemory (type : Ty) (pool : Bytes.LiteralPool) (heap : Heap)
    (store : Store Unit) (words : List Value) (value : type.denote) : Prop where
  at_ : heap.At store
  rep : type.Rep .owned heap store words value
  static : pool.Static heap store
  apart : ∀ region ∈ pool.regions, ∀ block ∈ type.blocks store words value,
    regionsDisjoint region block

theorem ProcessMemory.state {type : Ty} {pool : Bytes.LiteralPool} {heap : Heap}
    {store : Store Unit} {words : List Value} {value : ProcessStep type.denote}
    (memory : ProcessMemory (processResultTy type) pool heap store words (processValue type value)) :
    ProcessMemory type pool heap store (words.drop 2) value.state := by
  obtain ⟨stateWords, wordsEq, stateRep⟩ := processValue_rep.mp memory.rep
  have dropped : words.drop 2 = stateWords := by simp [wordsEq]
  refine ⟨memory.at_, ?_, memory.static, ?_⟩
  · simpa only [dropped] using stateRep
  · intro region member block blockMember
    apply memory.apart region member block
    rw [processValue_blocks]
    exact blockMember

end Verified.Wasi
