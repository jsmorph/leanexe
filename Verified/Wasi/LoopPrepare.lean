import Verified.Wasi.LoopPrepareGuarded

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopPrepare {World : Type} {S : List Sig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {count : Expr S context .word} {initial : Expr S context type}
    {env : Env context} {slots : List Slot} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {store : Store World} {locals : Locals} {h base : Nat}
    {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (countSpec : CodeSpec source funs flags bounds fits sourceHost params count env slots []
      (fun i => live i || initial.uses i) pool)
    (initialSpec : CodeSpec source funs flags bounds fits sourceHost params initial env slots [] live pool)
    (countForm : Encoding.ProgramForm
      (count.code (pool := pool) h slots base (fun i => live i || initial.uses i)))
    (countClosed : Relocation.programClosed source.funcs.length
      (count.code (pool := pool) h slots base (fun i => live i || initial.uses i)) = true)
    (initialForm : Encoding.ProgramForm
      (initial.code (pool := pool) h slots (base + 1) live ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)))
    (initialClosed : Relocation.programClosed source.funcs.length
      (initial.code (pool := pool) h slots (base + 1) live ++
        coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1)) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => (live i || initial.uses i) || count.uses i) base heap
      (PureTransport.erase store) locals)
    (at_ : heap.At (PureTransport.erase store))
    (safe : pool.Safe env slots (fun i => (live i || initial.uses i) || count.uses i) heap
      (PureTransport.erase store) locals)
    (scratch : Holds.ApartFrom env slots (fun i => (live i || initial.uses i) || count.uses i)
      (PureTransport.erase store) locals ABI.scratch)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (countRoom : base + max count.width (copyWidth .word) ≤ h)
    (initialRoom : base + 1 + max initial.width (copyWidth type) ≤ h)
    (stateRoom : base + 2 + type.width ≤ h)
    (countPlace : count.placeArgs = true) (initialPlace : initial.placeArgs = true)
    (resource : ∀ final : Store World, final.host = store.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap final finalLocals words,
      After env slots (fun i => (live i || initial.uses i) || count.uses i) live base
        heap store locals (.value type) (initial.denote funs env) finalHeap final finalLocals words →
      final.host = store.host →
      finalLocals.get base = some (.i64 (count.denote funs env)) →
      finalLocals.get (base + 1) = some (.i64 0) →
      LocalsHold finalLocals (base + 2) type.types words → finalLocals.values = locals.values →
      (count.fits funs fits env = true → initial.fits funs fits env = true →
        finalHeap.top.toNat ≤ heap.top.toNat +
          (count.allocs funs flags bounds (slots.map Slot.mode) []
              (fun i => live i || initial.uses i) env +
            (initial.allocs funs flags bounds (slots.map Slot.mode) [] live env +
              coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote funs env)))) →
      wp target rest Q final finalLocals targetHost) :
    wp target (loopPrepareCode h base slots pool count initial live ++ rest) Q store locals targetHost := by
  exact wp_loopPrepareGuarded runtime layout profile countSpec initialSpec countForm countClosed
    initialForm initialClosed positions parameters vars at_ safe scratch poolApart cap low
    countRoom initialRoom stateRoom countPlace initialPlace (fun _ final same => resource final same) next

end Verified.Wasi
