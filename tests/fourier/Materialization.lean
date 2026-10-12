import Verified.Examples.Elements
import Verified.Examples.Tables
import Verified.Examples.Recursion

open Lean Elab Command

run_cmd do
  if Verified.Reflect.materializeModule.get (← getOptions) then
    throwError "materializeModule default must be false"

set_option Verified.Reflect.materializeModule true in
run_cmd do
  unless Verified.Reflect.materializeModule.get (← getOptions) do
    throwError "materializeModule scoped value must be true"

run_cmd do
  if Verified.Reflect.materializeModule.get (← getOptions) then
    throwError "materializeModule scope must restore the default"

namespace Verified.Tests.Fourier.Materialization

namespace Elements

set_option Verified.Reflect.materializeModule true in
verified_compile compiled := [
  Verified.Examples.Elements.total, Verified.Examples.Elements.dot,
  Verified.Examples.Elements.largest, Verified.Examples.Elements.grid,
  Verified.Examples.Elements.axpy, Verified.Examples.Elements.extend,
  Verified.Examples.Elements.negatives, Verified.Examples.Elements.countTrue,
  Verified.Examples.Elements.select, Verified.Examples.Elements.flip,
  Verified.Examples.Elements.pushFlag, Verified.Examples.Elements.sieve]

#print axioms compiled.module_literal_eq
#print axioms compiled.bytes
#print axioms compiled.axpy.implements
#print axioms compiled.sieve.implements
end Elements

namespace Tables

set_option Verified.Reflect.materializeModule true in
verified_compile compiled := [
  Verified.Examples.Tables.squareWith, Verified.Examples.Tables.sumWith,
  Verified.Examples.Tables.setWith, Verified.Examples.Tables.square,
  Verified.Examples.Tables.sum, Verified.Examples.Tables.setSquare]

#print axioms compiled.module_literal_eq
#print axioms compiled.bytes
#print axioms compiled.square.implements
#print axioms compiled.setSquare.implements
end Tables

namespace Recursion

set_option Verified.Reflect.materializeModule true in
verified_compile compiled := [
  Verified.Examples.Recursion.gcd, Verified.Examples.Recursion.pow,
  Verified.Examples.Recursion.sumRange, Verified.Examples.Recursion.fill,
  Verified.Examples.Recursion.chain, Verified.Examples.Recursion.fibPair,
  Verified.Examples.Recursion.walk, Verified.Examples.Recursion.sumXs,
  Verified.Examples.Recursion.powGcd, Verified.Examples.Recursion.top2,
  Verified.Examples.Recursion.top1, Verified.Examples.Recursion.deep]

#print axioms compiled.module_literal_eq
#print axioms compiled.bytes
#print axioms compiled.gcd.implements
#print axioms compiled.deep.implements
end Recursion

run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt
  let declarations := #[
    ``Elements.compiled.module_literal_eq, ``Elements.compiled.bytes,
    ``Elements.compiled.axpy.implements, ``Elements.compiled.sieve.implements,
    ``Tables.compiled.module_literal_eq, ``Tables.compiled.bytes,
    ``Tables.compiled.square.implements, ``Tables.compiled.setSquare.implements,
    ``Recursion.compiled.module_literal_eq, ``Recursion.compiled.bytes,
    ``Recursion.compiled.gcd.implements, ``Recursion.compiled.deep.implements]
  for declaration in declarations do
    let actual ← collectAxioms declaration
    unless actual.qsort Name.lt == permitted do
      throwError "{declaration} has axioms {actual}; expected {permitted}"

end Verified.Tests.Fourier.Materialization
