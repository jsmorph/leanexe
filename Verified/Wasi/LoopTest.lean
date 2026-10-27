import Verified.Wasi.LoopTestGuarded

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopTest {World : Type} {S : List Sig} {context : List Ty} {type : Ty}
    {source target : Wasm.Module} {funs : Funs S} {flags : Flags S} {bounds : Bounds S}
    {fits : Fits S} {sourceHost : HostEnv Unit} {targetHost : HostEnv World}
    {pool : Bytes.LiteralPool} {test : Expr S (type :: .word :: context) .bool}
    {env : Env context} {slots : List Slot} {liveIn live testLive : Nat → Bool}
    {state : type.denote} {index : UInt64} {words : List Value} {params : List Value}
    {heap currentHeap : Heap} {initial current : Store World} {locals currentLocals : Locals}
    {h base : Nat} {rest : Program} {Q : Assertion World}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params test
      (.cons state (.cons (t := .word) index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) [] testLive pool)
    (form : Encoding.ProgramForm (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive))
    (closed : Relocation.programClosed source.funcs.length (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive) = true)
    (positions : currentLocals.positions = h) (parameters : currentLocals.params = params)
    (after : After env slots liveIn live base heap initial locals (.value type) state
      currentHeap current currentLocals words)
    (scratch : Holds.ApartFrom env slots live (PureTransport.erase current) currentLocals ABI.scratch)
    (static : pool.Static currentHeap (PureTransport.erase current))
    (held : LocalsHold currentLocals (base + 2) type.types words)
    (counter : currentLocals.get (base + 1) = some (.i64 index))
    (selected : ∀ i, (testLive (i + 2) || test.uses (i + 2)) = true → live i = true)
    (cap : (PureTransport.erase current).memoryCap source 0 ≤ 65535)
    (low : currentLocals.params.length ≤ base + 2 + type.width)
    (room : base + 2 + type.width + max test.width (copyWidth .bool) ≤ h)
    (place : test.placeArgs = true)
    (resource : ∀ final : Store World, final.host = current.host → Q (.Trap final "unreachable"))
    (next : ∀ finalHeap final finalLocals,
      After env slots liveIn live base heap initial locals (.value type) state
        finalHeap final finalLocals words →
      Frame (base + 2 + type.width) currentLocals finalLocals →
      final.host = current.host →
      (test.fits funs fits (.cons state (.cons (t := .word) index env)) = true →
        finalHeap.top.toNat ≤ currentHeap.top.toNat +
          test.allocs funs flags bounds
            ((⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots).map Slot.mode)
            [] testLive (.cons state (.cons (t := .word) index env))) →
      wp target rest Q final { finalLocals with
        values := .i64 (boolWord (test.denote funs (.cons state (.cons (t := .word) index env)))) ::
          currentLocals.values } targetHost) :
    wp target (Relocation.program (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) testLive) ++ rest) Q current currentLocals targetHost := by
  exact wp_loopTestGuarded runtime layout profile spec form closed positions parameters after scratch static
    held counter selected cap low room place (fun _ final same => resource final same) next

end Verified.Wasi
