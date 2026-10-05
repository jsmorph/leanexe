import LeanExe.Scheme.Runtime
import Project.Compiler.Command

namespace Project.Scheme
open LeanExe.Scheme.Arena LeanExe.Scheme.Runtime

leanexe_compile scheme := [
  write, fail, seedCell, seedNext, init, allocateCell, allocate,
  clearMark, clearNext, mark, markRoots, scanCell, scanOne, reclaim, sweepCell, sweepNext, scanNext,
  finishCollection, collectReady, collect, stressCollection, spaceCollection, reserve,
  lookup, operand, advance,
  wire, descriptorValid, setExec, setApply, setReturn, boxLiteral, pushReady, pushLiteral,
  reserveAccess, loadReady, loadName, storeReady, storeName, captureFound, captureOne,
  captureNext, reserveClose, finishClose, closeReady, close, drop, branch, reserveBinary,
  boxBinary, binaryReady, binary, walkArgs, reserveEntry, frameCall, enterReady, enter, ret,
  reserveGlobal, globalReady, global, bindReady, bindOne, bindNext, reserveClosure,
  closureReady, applyClosure, applyContinuation, reserveCallcc, callccReady, applyCallcc,
  apply, reserveReturn, returnReady, deliverFrame, deliver, execute, step, runNext, run,
  resultWord
]

end Project.Scheme
