import LeanExe.Smalltalk.Runtime
import Project.Compiler.Command

namespace Project.Smalltalk
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime
leanexe_compile smalltalk := [
  write, fail, seedCell, seedNext, init, allocateCell, allocate, clearNext,
  markReady, mark, markRoots, scanCell, scanNext, reclaim, sweepNext,
  finishCollection, collectReady, collect, stressCollection, spaceCollection, reserve,
  walk, lexical, localSlot, self, home, onChain, objectClass, lookup,
  programTablesValid, programValid, advance, pushReady, push, literalReady, literal,
  pop, loadSlot, storeSlot, fieldSlot, bindOne, bindNext, enterReady,
  fillOne, fillNext, newReady, bootReady, bootValid, boot,
  retire, unwindNext, returnCallerReady, returnCaller, returnReady, returnReserved, ret,
  sendMethodReady, callMethod, arithmeticOK, primitiveValue, finishPrimitive,
  binaryReady, primitiveBinaryReady, primitiveBinary, primitiveNewReady, primitiveNew,
  primitiveCollect, dispatchBlock, dispatch, send, branch, accessLocal, accessField,
  execute, step, runNext, run, resultWord
]
end Project.Smalltalk
