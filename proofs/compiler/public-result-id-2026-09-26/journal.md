# Id annotations on public scalar results

The signature parser recognizes exact Id.{0} around an inner signature only
when its arity is zero. The independent Arrow.idResult source rule has the same
restriction. Arbitrarily nested result annotations and existing metadata preserve
the word/Boolean result kind. Id around a function signature, custom Id heads,
wrong universe arguments and non-scalar result types remain rejected.

Source signature admission, extraction correctness and the Boolean zero/one
result theorem pass on the first focused build. Body compilation and all three
word/scalar/loop paths are unchanged. Native fixtures pass 180 comparisons for
word and Boolean results, nested Id, pure/bind, captures, yielding ranges, break
and continue. Original annotated declarations are compiled; expected-native
adapters only expose their values to the existing comparison harness.

The prior public Boolean syntax test now retains its negative annotation check
using a wrong Id universe; standard Id is part of the accepted signature grammar.
The new matrix includes positive nested-Id signatures with the same native values
and equivalent explicit-word conversions. Invalid checks also cover custom heads,
extra universe arguments and Id applied to a function type. All result bodies
remain checked, including unsupported or incomplete expressions.

The completed new suite passes 33,204 native/IR comparisons, 20,352 invalid-input
checks and 1,536 explicit-word-conversion controls. The prior suite passes 93,130
comparisons, 67,023 rejection checks and 3,456 controls. No extraction/lowering
changes beyond signature recognition were needed.

The general compiler theorem and nineteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1076 declarations.
