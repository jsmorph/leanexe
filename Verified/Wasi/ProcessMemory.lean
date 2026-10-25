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

theorem ProcessMemory.afterStep {oldType resultType : Ty} {pool : Bytes.LiteralPool}
    {heap middleHeap finalHeap : Heap} {initial middle final : Store Unit}
    {oldWords resultWords : List Value} {oldValue : oldType.denote}
    {resultValue : resultType.denote}
    (current : ProcessMemory oldType pool heap initial oldWords oldValue)
    (poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (called : Step heap initial (fun region => regionsDisjoint region ABI.scratch)
      middleHeap middle (resultType.blocks middle resultWords resultValue))
    (resultRep : resultType.Rep .owned middleHeap middle resultWords resultValue)
    (released : Step middleHeap middle
      (fun region => ∀ block ∈ oldType.blocks middle oldWords oldValue,
        regionsDisjoint region block) finalHeap final []) :
    ProcessMemory resultType pool finalHeap final resultWords resultValue ∧
      final.memoryCaps = initial.memoryCaps := by
  obtain ⟨_, oldRegions, freshApart⟩ := current.rep.step called (fun region member =>
    regionsDisjoint_symm (owned_scratch current.rep region member))
  change oldType.blocks middle oldWords oldValue =
    oldType.blocks initial oldWords oldValue at oldRegions
  obtain ⟨middleStatic, poolFresh⟩ := current.static.step called poolScratch
  obtain ⟨finalRep, resultRegions, _⟩ := resultRep.step released (by
    intro region member block oldMember
    rw [oldRegions] at oldMember
    exact regionsDisjoint_symm (freshApart block oldMember region member))
  change resultType.blocks final resultWords resultValue =
    resultType.blocks middle resultWords resultValue at resultRegions
  have poolOld : ∀ region ∈ pool.regions,
      ∀ block ∈ oldType.blocks middle oldWords oldValue, regionsDisjoint region block := by
    intro region member block oldMember
    rw [oldRegions] at oldMember
    exact current.apart region member block oldMember
  have finalStatic := (middleStatic.step released poolOld).1
  refine ⟨⟨released.at_, finalRep, finalStatic, ?_⟩, released.caps.trans called.caps⟩
  intro region member block blockMember
  rw [resultRegions] at blockMember
  exact poolFresh region member block blockMember

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
