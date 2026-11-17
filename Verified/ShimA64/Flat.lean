import Verified.ShimA64.Clocks

/-!
The flat stubs against the shim's host environment: `flatStub_sim` states that the code of each
stub of `flatStubs` at its address meets `Machine.StubSim` on `shimMachine` for the function of
`linuxEnv` of every call of `shimCalls` whose import is the stub's.  `wasiElf_run` takes the
simulation of every flat import of a module from it.  `flatStub_call` states that the call of
`shimCalls` whose import is a stub's is the stub's call, so the lemma takes one case for each stub.
`flatStubs` lists the stubs of `clock_time_get` and `random_get`, whose cases `clockStub_sim` and
`randomStub_sim` give, and each increment that adds a stub to `flatStubs` adds its case here.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- The call of `shimCalls` whose import is a flat stub's is the stub's call. -/
theorem flatStub_call :
    ∀ s ∈ flatStubs, ∀ c ∈ shimCalls, ABI.callImport c = s.decl → c = s.call := by
  decide

/-- The code of a stub of `flatStubs` at `a`, generated with the routine `SVC #0; RET` at `svc`,
the trap stub, the routine of errnos at `en`, and the scratch `areaSize S.cap` bytes above the
area, stands for the shim's function of the call `c` of `shimCalls` whose import is the stub's,
when the area and the scratch lie in the data segment. -/
theorem flatStub_sim {s : FlatStub} (hs : s ∈ flatStubs) {c : LeanExe.Wasi.Call}
    (hc : c ∈ shimCalls) (hd : ABI.callImport c = s.decl) (S : Shared) (n : Nat)
    {a svc en : UInt64} {is : List Instr}
    (hg : s.gen a svc S.trapUnreachable en (areaSize S.cap) = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)]) (hen : CodeAt code en errnoRoutine)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false)
    (hsize : S.cap * 65536 ≤ size) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      s.decl.params s.decl.results
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) c) a := by
  obtain rfl := flatStub_call s hs c hc hd
  simp only [flatStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact clockStub_sim S n hg hcode hsvc hen hGb hdata
  · exact randomStub_sim S n hg hcode hsvc hen hGb hdata hsize

end Verified.ShimA64
