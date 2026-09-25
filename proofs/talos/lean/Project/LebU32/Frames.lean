import Project.LebU32.Shape

namespace Project.LebU32.Spec
open Wasm Project.ProofKit

structure RunningFrame (frame : Locals) (fuel value pointer length : UInt64) : Prop where
  params : frame.params = [.i64 fuel, .i64 value, .i64 pointer, .i64 pointer, .i64 length]
  locals : frame.locals.length = 36
  typed : I64Values frame.locals
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 pointer)
  done : frame.locals[4]? = some (.i64 0)

structure BranchFrame (frame : Locals) (fuel value pointer length : UInt64)
    extends RunningFrame frame fuel value pointer length where
  low : frame.locals[5]? = some (.i64 (value % 128))
  quotient : frame.locals[6]? = some (.i64 (value / 128))

structure FinishedFrame (frame : Locals) (fuel pointer length : UInt64) : Prop where
  params : frame.params.length = 5
  fuel : frame.params[0]? = some (.i64 fuel)
  locals : frame.locals.length = 36
  typed : I64Values frame.locals
  values : frame.values = []
  owner : frame.locals[1]? = some (.i64 pointer)
  pointer : frame.locals[2]? = some (.i64 pointer)
  length : frame.locals[3]? = some (.i64 length)
  done : frame.locals[4]? = some (.i64 1)

structure AdvanceFrame (frame : Locals) (fuel value previous length output : UInt64) : Prop where
  params : frame.params = [.i64 fuel, .i64 value, .i64 previous, .i64 previous, .i64 length]
  locals : frame.locals.length = 36
  typed : I64Values frame.locals
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 previous)
  done : frame.locals[4]? = some (.i64 0)
  quotient : frame.locals[11]? = some (.i64 (value / 128))
  owner : frame.locals[16]? = some (.i64 output)
  pointer : frame.locals[17]? = some (.i64 output)
  length : frame.locals[18]? = some (.i64 (length + 1))

theorem masked_byte (value : UInt64) : (value &&& 255).toUInt8 = value.toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_and, BitVec.setWidth_and]
  exact BitVec.and_allOnes

end Project.LebU32.Spec
