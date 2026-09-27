import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let convert (value : Lean.Expr) := Lean.Expr.app (.const ``Nat.toUInt64 []) value
  let numeral (type : Lean.Expr) (number evidence : Nat) := Lean.mkAppN (.const ``OfNat.ofNat [.zero])
    #[type, .lit (.natVal number), .app (.const ``instOfNatNat []) (.lit (.natVal evidence))]
  let decorate (depth : Nat) (value : Lean.Expr) := (List.range depth).foldl (fun e _ => .mdata {} e) value
  let numbers : List Nat := [0, 1, 5, 18446744073709551615, 18446744073709551616,
    18446744073709551621, 340282366920938463463374607431768211455, 340282366920938463463374607431768211456]
  let mut accepted : Nat := 0
  let mut rejected : Nat := 0
  for n in numbers do
    for typeDepth in [0, 1, 3] do
      for valueDepth in [0, 1, 3] do
        let natType := decorate typeDepth (.const ``Nat [])
        for value in [.lit (.natVal n), numeral natType n n] do
          let value := decorate valueDepth value
          unless extractScalarExprWith [] (convert value) == some (.u64 n) do
            throwError "Nat.toUInt64 literal mismatch"
          accepted := accepted + 1
        for bad in [numeral natType n (n + 1), numeral (.const ``UInt64 []) n n,
            numeral (.app (.const ``Id [.zero]) natType) n n,
            .app (.const ``Nat.succ []) (.lit (.natVal n)),
            Lean.mkAppN (.const ``OfNat.ofNat [.zero]) #[natType, .lit (.natVal n), .bvar 0],
            .const `unsupportedNatural []] do
          unless (extractScalarExprWith [] (convert (decorate valueDepth bad))).isNone do
            throwError "invalid Nat.toUInt64 literal admitted"
          rejected := rejected + 1
        unless (extractScalarExprWith [] (.app (.const ``Nat.toUInt64 [.zero])
            (decorate valueDepth (numeral natType n n)))).isNone do
          throwError "Nat.toUInt64 accepted a universe argument"
        rejected := rejected + 1
    for index in [0, 1, 2, 3] do
      let locals := List.replicate index (ScalarBinding.word (.u64 99)) ++ [.natural (.u64 n)]
      unless extractScalarExprWith locals (convert (.bvar index)) == some (.u64 n) do
        throwError "captured Nat.toUInt64 index mismatch"
      accepted := accepted + 1
      for bad in ([.word (.u64 n), .boolean (.u64 0), .unit,
          .function false (fun _ => some (.u64 n)), .predicateFunction (fun _ => some (.u64 1)),
          .booleanPredicateFunction (fun _ => some (.u64 1))] : List ScalarBinding) do
        let locals := List.replicate index (ScalarBinding.word (.u64 99)) ++ [bad]
        unless (extractScalarExprWith locals (convert (.bvar index))).isNone do
          throwError "Nat.toUInt64 accepted wrong binding kind"
        rejected := rejected + 1
      unless (extractScalarExprWith locals (convert (.bvar (index + 1)))).isNone do
        throwError "Nat.toUInt64 accepted an absent binding"
      rejected := rejected + 1
  unless accepted == 176 && rejected == 728 do throwError "unexpected counts {accepted}, {rejected}"
  Lean.logInfo m!"{accepted} Nat.toUInt64 admission/encoding controls and {rejected} invalid-input tests passed"
