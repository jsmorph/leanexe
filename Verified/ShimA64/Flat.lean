import Verified.ShimA64.Preopen

/-!
The flat stubs against the shim's host environment: `flatStub_sim` states that the code of each
stub of `flatStubs` at its address meets `Machine.StubSim` on `shimMachine` for the function of
`linuxEnv` of every call of `shimCalls` whose import is the stub's.  `wasiElf_run` takes the
simulation of every flat import of a module from it.  Each stub's case finds the call from the
import's name (`shimCall_named`) and applies the stub's simulation: `prestatStub_sim` and
`dirNameStub_sim` for the stubs of the preopened directory.
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

/-- The code of a stub of `flatStubs` at `a`, generated with the routine `SVC #0; RET` at `svc`,
the trap stub, the routine of errnos at `en`, and the scratch `areaSize S.cap` bytes above the
area, stands for the shim's function of the call `c` of `shimCalls` whose import is the stub's,
when the area and the scratch lie in the data segment. -/
/-- The call of `shimCalls` whose import has the name of the call `c'` of `shimCalls`: `c'`. -/
theorem shimCall_named {c c' : LeanExe.Wasi.Call} (hc : c ∈ shimCalls) (hc' : c' ∈ shimCalls)
    (h : (ABI.callImport c).name = c'.name) : c = c' := by
  simp only [shimCalls, List.mem_cons, List.not_mem_nil, or_false] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd h (by decide)

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
  simp only [flatStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hscr := scratch_wasi (sp := sp₀) (top := top) hL hGb hdata
  -- the stubs of the preopened directory
  rcases hs with rfl | rfl
  · obtain rfl : c = Call.fdPrestatGet :=
      shimCall_named hc (by decide) (congrArg ImportDecl.name hd)
    exact prestatStub_sim S n hg hcode hGb hscr
  · obtain rfl : c = Call.fdPrestatDirName :=
      shimCall_named hc (by decide) (congrArg ImportDecl.name hd)
    exact dirNameStub_sim S n hg hcode hGb hscr

end Verified.ShimA64
