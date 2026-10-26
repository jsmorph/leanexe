import Verified.Wasi.ProgramIn
import Verified.Wasi.CompactCode
import LeanExe.Wasi.Process

namespace Verified.Wasi

open Wasm

def processResultTy : Ty → Ty
  | .elem element => .elem (.prod .bool (.prod .word element))
  | state => .pair .bool (.pair .word state)

structure ProcessEntry (effectSigs : List EffectSig) where
  state : Ty
  beginName : String
  stepName : String
  begin : EffectVar effectSigs
    ⟨beginName, [], [], .value (processResultTy state)⟩
  step : EffectVar effectSigs
    ⟨stepName, [state], [.borrowed], .value (processResultTy state)⟩

abbrev ProcessEntry.result (entry : ProcessEntry effectSigs) : Ty :=
  processResultTy entry.state

/-- The first of the process entry's compaction scalars: after the result's words.  It holds
the heap base, the heap top when `_start` begins. -/
def processAux (state : Ty) : Nat := (processResultTy state).width

/-- The positions of the process entry's function: the result's words, the five compaction
scalars, and the scratch of the state's copy. -/
def processPositions (state : Ty) : Nat := processAux state + 5 + state.copyScratch

/-- The compaction of the state, whose words follow the running flag and the status. -/
def processCompaction (state : Ty) : Program :=
  compactCode (processPositions state) state 2 (processAux state)

/-- One step of the process loop: stop when the state is not running, and otherwise call the
step on the state, store its result over the current one, and compact the new state.  The step
borrows the state, so the old state is garbage once the result is stored, and the compaction
reclaims it with everything else the step allocated. -/
def ProcessEntry.iteration (source : Wasm.Module) (entry : ProcessEntry effectSigs) : Program :=
  let positions := processPositions entry.state
  [.localGet 0, .eqzI64, .br_if 1, .constI64 0] ++
    loadCode positions 2 entry.state.types ++
    [.call (Wrappers.effectIndex source entry.step.index)] ++
    storeCode positions 0 entry.result.types ++
    Relocation.program (processCompaction entry.state) ++ [.br 0]

def ProcessEntry.function (source : Wasm.Module) (entry : ProcessEntry effectSigs)
    (typeIdx : Nat) : Function :=
  let positions := processPositions entry.state
  { params := []
    locals := List.replicate positions .i64 ++ List.replicate positions .f64 ++
      List.replicate positions .f32
    body := [.globalGet 0, .localSet (processAux entry.state), .constI64 0,
        .call (Wrappers.effectIndex source entry.begin.index)] ++
      storeCode positions 0 entry.result.types ++
      Relocation.program (processCompaction entry.state) ++
      [.block 0 0 [.loop 0 0 (entry.iteration source) [] []] [] []] ++
      [.localGet 1, .wrapI64, .call 2, .unreachable]
    results := []
    typeIdx := some typeIdx }

def ProcessEntry.extension (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) : Module.Extension :=
  { types := program.types ++ [startType]
    funcs := program.functions source pool ++
      [entry.function source (effectTypeIndex source effectSigs.length)]
    exports := [{ name := "_start", funcIdx := effectSigs.length }] }

def compileProcess (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) : Wasm.Module :=
  let assembled := Module.assemble source (Wrappers.extension source (entry.extension source program pool))
  { assembled with
    exports := [{ name := "_start", funcIdx := Wrappers.effectIndex source effectSigs.length }]
    globalExports := []
    memoryExports := [("memory", 0)] }

theorem compileProcess_functionsIn (source : Wasm.Module) (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) :
    program.FunctionsIn source (compileProcess source program entry pool) pool := by
  intro index bound
  change (Module.assemble source (Wrappers.extension source (entry.extension source program pool))).funcs[
    source.funcs.length + (3 + index)]? = (program.functions source pool)[index]?
  rw [Wrappers.next_function]
  exact List.getElem?_append_left (by rw [program.functions_length source pool]; exact bound)

theorem compileProcess_layout {source : Wasm.Module} (program : EffectProg pureSigs effectSigs)
    (entry : ProcessEntry effectSigs) (pool : Bytes.LiteralPool) (imports : source.imports = []) :
    Relocation.Layout source (compileProcess source program entry pool) := by
  refine ⟨imports, ?_, ?_, rfl, rfl⟩
  · exact ABI.imports_length
  · intro index function selected
    exact Module.pure_function (Wrappers.extension source (entry.extension source program pool)) selected

theorem compileProcess_base {source : Wasm.Module} {pure : Resource.PureContext pureSigs}
    (program : EffectProg pureSigs effectSigs) (entry : ProcessEntry effectSigs)
    (pool : Bytes.LiteralPool) (runtime : Runtime source) (profile : Relocation.Profile source)
    (calls : Calls source pure.funs pure.flags pure.bounds pure.fits pool)
    (poolApart : ∀ region ∈ pool.regions, LeanExe.Runtime.regionsDisjoint region ABI.scratch) :
    CompilerBase source (compileProcess source program entry pool) pure pool :=
  { runtime
    layout := compileProcess_layout program entry pool runtime.imports
    profile
    calls
    imports := rfl
    read := ⟨_, Wrappers.read_function source (entry.extension source program pool)⟩
    stdout := ⟨_, Wrappers.stdout_function source (entry.extension source program pool)⟩
    stderr := ⟨_, Wrappers.stderr_function source (entry.extension source program pool)⟩
    poolApart }

end Verified.Wasi
