import Verified.Wasi.AfterScratch

namespace Verified.Wasi

open LeanExe.Runtime

theorem pool_regions_apart_scratch (pool : Bytes.LiteralPool) (base : 16 ≤ pool.base) :
    ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch := by
  intro region member
  by_cases empty : pool.payload = []
  · simp [Bytes.LiteralPool.regions, empty] at member
  · have equal : region = (pool.base, pool.payload.length) := by
      simpa [Bytes.LiteralPool.regions, empty] using member
    subst region
    exact Or.inr base

end Verified.Wasi
