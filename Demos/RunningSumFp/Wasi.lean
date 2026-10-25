import Demos.RunningSumFp.Stream
import Verified.Wasi.ReflectCommand

namespace Demos.RunningSumFp

open LeanExe LeanExe.Wasi LeanExe.Pipeline
open Library.Numerics.Arithmetic.Uscale
open Library.Numerics.Decimal.ParseFloat
open Library.Numerics.Decimal.PrintFloat

instance : Flat State (Float × Array UInt64 × Bytes × UInt64 × Bytes × UInt64 × Bool) :=
  ⟨fun state => (state.total, state.line, state.input, state.cursor, state.output, state.written, state.eof)⟩

instance : Flat (ProcessStep State) (Bool × UInt64 × State) :=
  ⟨fun result => (result.running, result.status, result.state)⟩

set_option Elab.async false
verified_compile_wasi io :=
  [limb, mulSmall, shl, cmpStep, le, sub, wordBits, bitLen, divStep, divBits, scaledQuot,
    pow10Word, mulPow10, isDigitW, isHexW, hexValW, lowerW, span, matchLower, expDigits,
    expPart, digitPos, leadingZeros, anyNonzero, chunkVal, digitsVal, hexVal, roundUnits,
    decRound, decParse, hexParse, pow10Float, fastPath, parse64,
    limbsOf, quotAt, range, found, nearest, clamp, startExp, shortest, numDigits, digitAt,
    digitsFrom, byte1, noBytes, zeros, sciLayoutW, ecmaLayoutW, fixed, special, print64With,
    print64, stripCR, parse, render, initial, completeLine, consumeInput, remainingOutput,
    afterWrite, afterRead, writeStep, readStep, step, begin]

end Demos.RunningSumFp
