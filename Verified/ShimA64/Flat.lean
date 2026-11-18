import Verified.ShimA64.Strings
import Verified.ShimA64.Clocks
import Verified.ShimA64.Preopen

/-!
The flat stubs against the shim's host environment: `flatStub_sim` states that the code of each
stub of `flatStubs` at its address meets `Machine.StubSim` on `shimMachine` for the function of
`linuxEnv` of every call of `shimCalls` whose import is the stub's.  `wasiElf_run` takes the
simulation of every flat import of a module from it.  `flatStubs` lists the stubs of the arguments
and the environment, whose cases `stringStub_sim` of `Verified/ShimA64/Strings.lean` proves, and
those of `clock_time_get` and `random_get`, whose cases `clockStubs_sim` of
`Verified/ShimA64/Clocks.lean` proves, and the stubs of the preopened directory, whose cases
`preopenStub_sim` of `Verified/ShimA64/Preopen.lean` proves.  Each increment that adds a stub to
`flatStubs` adds its case here.
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
when the area and the scratch lie in the data segment, the UART lies outside the module's Normal
memory, and the cap's linear memory lies within the machine's `size` bytes. -/
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
  simp only [flatStubs, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · exact stringStub_sim hs hc hd S n hg hcode hGb hdata hU
  · exact clockStubs_sim hs hc hd S n hg hcode hsvc hen hGb hdata hsize
  · exact preopenStub_sim hs hc hd S n hg hcode hGb hdata

end Verified.ShimA64
