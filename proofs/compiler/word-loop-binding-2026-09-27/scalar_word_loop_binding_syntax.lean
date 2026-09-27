import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for booleanSetup in [false, true] do
    for savedDepth in ([1, 2] : List Nat) do
      for monadic in [false, true] do
        for annotationDepth in ([0, 2] : List Nat) do
          let type := (List.range annotationDepth).foldl (fun value _ => BooleanType.identity value) .boolean
          let resultType := (List.range (2 - annotationDepth)).foldl (fun value _ => ResultType.identity value) .word
          for flagFirst in [false, true] do
            let domains := if flagFirst then [boolean, word] else [word, boolean]
            let kinds := if flagFirst then [PublicArgument.boolean, .word] else [.word, .boolean]
            let originalFlag := if flagFirst then 1 else 0
            let originalWord := if flagFirst then 0 else 1
            let flagIndex := if booleanSetup then 0 else originalFlag + 1
            let wordIndex := if booleanSetup then originalWord + 1 else 0
            for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
              for kind in ([0, 1, 2] : List Nat) do
                for mode in ([0, 1] : List Nat) do
                  for tailForm in ([0, 1] : List Nat) do
                    for wrapped in [false, true] do
                      let signature := domains.foldr (fun input rest => Lean.Expr.forallE `parameter input rest binder) resultType.expr
                      let wrap (body : Lean.Expr) := domains.foldr (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                      let flag : BooleanLocal := .var 0 flagIndex
                      let initial := add (.bvar wordIndex) (toWord flag.expr)
                      let advanced := add (add (.bvar 0) indexWord) (literalExpr 1)
                      let step := if kind == 0 then Step.yieldDirect advanced
                        else if kind == 1 then Step.branch .beq .word (modWord advanced (literalExpr 7)) (literalExpr 0)
                          (Step.doneDirect advanced) (Step.yieldDirect advanced)
                        else Step.branch .beq .word (modWord indexWord (literalExpr 2)) (literalExpr 0)
                          (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                      let loop := Range.call (modWord (.bvar wordIndex) (literalExpr 17)) initial `i `a binder binder step
                      let loopTail : BooleanLocal := .junction 0 .disjunction
                        (.compare .eq (modWord (.bvar 0) (literalExpr 7)) (literalExpr 0)) (.var 0 (flagIndex + 1))
                      let loopBody := Lean.Expr.letE `value word loop loopTail.expr false
                      let wordBranch := Lean.Expr.letE `value word loop
                        (add (.bvar 0) (.bvar (wordIndex + 1))) flagFirst
                      let booleanBranch := Lean.Expr.letE `flag type.expr loopBody
                        (add (toWord (.bvar 0)) (.bvar (wordIndex + 1))) flagFirst
                      let scalar := add (Lean.mkApp2 (.const ``UInt64.mul []) (.bvar wordIndex) (literalExpr 3))
                        (toWord (.bvar flagIndex))
                      let action := WordRange.choiceExpr resultType flag.condition flag.evidence
                        (if mode == 0 then wordBranch else booleanBranch) scalar
                      let action := if wrapped then .mdata {} (Identity.run (Identity.pure action resultType) resultType) else action
                      let tail := if tailForm == 0 then add (.bvar 0) (.bvar (wordIndex + 1))
                        else add (Lean.mkApp2 (.const ``UInt64.mul []) (.bvar 0) (literalExpr 3))
                          (toWord (.bvar (flagIndex + 1)))
                      let bindBody (value tail : Lean.Expr) := if monadic then
                          Identity.bind `saved binder value tail resultType resultType
                        else Lean.Expr.letE `saved resultType.expr value tail flagFirst
                      let setupType := if booleanSetup then type.expr else resultType.expr
                      let setupFlag : BooleanLocal := .junction 0 .disjunction (.var 1 originalFlag)
                        (.compare .eq (modWord (.bvar originalWord) (literalExpr 3)) (literalExpr 0))
                      let setupValue := if booleanSetup then setupFlag.expr
                        else add (.bvar originalWord) (toWord (.bvar originalFlag))
                      let setup (monadic : Bool) (value body : Lean.Expr) := if !monadic then
                          Lean.Expr.letE `setup setupType value body flagFirst
                        else if booleanSetup then BooleanWordRange.bind `setup binder type resultType value body
                        else Identity.bind `setup binder value body resultType resultType
                      let save (monadic : Bool) (value : Lean.Expr) := (List.range savedDepth).foldl
                        (fun body _ => if monadic then Identity.bind `saved binder body
                            (add (.bvar 0) (.bvar (wordIndex + 1))) resultType resultType
                          else Lean.Expr.letE `saved resultType.expr body
                            (add (.bvar 0) (.bvar (wordIndex + 1))) flagFirst) value
                      let core := bindBody action tail
                      let body := setup monadic setupValue (save monadic core)
                      let body := if wrapped then .mdata {} (Identity.run (Identity.pure body resultType) resultType) else body
                      let some func := extractScalarFunc `wordBinding (some "entry") signature (wrap body) |
                        throwError "result binding rejected: {monadic}, {annotationDepth}, {flagFirst}, {kind}, {mode}, {tailForm}, {wrapped}"
                      let some plan := extractScalarWordRangeWith (publicBindings kinds) 2 body |
                        throwError "direct result binding rejected"
                      let direct := plan.func `wordBinding (some "entry") 2
                      let some control := extractScalarWordRangeWith (publicBindings kinds) 2
                          (setup false setupValue (save false (.letE `saved resultType.expr action tail flagFirst))) |
                        throwError "lexical control rejected"
                      unless direct == control.func `wordBinding (some "entry") 2 do
                        throwError "monadic result binding changed the loop plan"
                      controls := controls + 1
                      let some unsaved := extractScalarWordRangeWith (publicBindings kinds) 2 (setup monadic setupValue action) |
                        throwError "unsaved word conditional rejected"
                      let some lexical := extractScalarWordRangeWith (publicBindings kinds) 2 (setup false setupValue action) |
                        throwError "lexical word conditional rejected"
                      unless unsaved.func `wordBinding (some "entry") 2 == lexical.func `wordBinding (some "entry") 2 do
                        throwError "setup bind changed conditional loop"
                      controls := controls + 1
                      let unsavedModule : LeanExe.IR.Module := { funcs := #[unsaved.func `wordBinding (some "entry") 2] }
                      let module_ : LeanExe.IR.Module := { funcs := #[func] }
                      let directModule : LeanExe.IR.Module := { funcs := #[direct] }
                      for (x, y) in inputs do
                        let rawFlag := if flagFirst then x else y
                        let rawWord := if flagFirst then y else x
                        let flag := if booleanSetup then !(rawFlag != 0) || rawWord % 3 == 0 else rawFlag != 0
                        let rawWord := if booleanSetup then rawWord else rawWord + (rawFlag != 0).toUInt64
                        let initial := rawWord + flag.toUInt64
                        let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                          let advanced := a + i.toUInt64 + 1
                          if kind == 0 then .yield advanced
                          else if kind == 1 then if advanced % 7 == 0 then .done advanced else .yield advanced
                          else .yield (if i % 2 == 0 then a else advanced)
                        let result := if flag then
                            (if mode == 0 then value else (value % 7 == 0 || flag).toUInt64) + rawWord
                          else rawWord * 3 + flag.toUInt64
                        let expected := if tailForm == 0 then result + rawWord else result * 3 + flag.toUInt64
                        let expected := expected + UInt64.ofNat savedDepth * rawWord
                        for (actual, expected) in [(module_.evalFunc 0 [x, y], expected),
                            (directModule.evalFunc 0 [x, y], expected),
                            (unsavedModule.evalFunc 0 [x, y], result)] do
                          unless actual == expected do
                            throwError "word result binding produced {actual}, expected {expected}"
                          comparisons := comparisons + 1
                      let bad := Lean.Expr.const `unsupportedBooleanResultBinding []
                      let bindHead := Lean.Expr.const ``Bind.bind [.zero, .zero]
                      let bindInstance := Lean.mkAppN (.const ``Monad.toBind [.zero, .zero])
                        #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]
                      let raw (head input domain output evidence : Lean.Expr) := Lean.mkAppN head
                        #[.const ``Id [.zero], evidence, input, output, action, .lam `saved domain tail binder]
                      let invalid := [
                        bindBody bad tail,
                        bindBody action bad,
                        bindBody (.bvar 999) tail,
                        bindBody action (.bvar 999),
                        bindBody (.bvar flagIndex) tail,
                        bindBody action (toWord (.bvar 0)),
                        bindBody (WordRange.choiceExpr resultType flag.condition flag.evidence action bad) tail,
                        raw bindHead resultType.expr boolean resultType.expr bindInstance,
                        raw bindHead resultType.expr resultType.expr boolean bindInstance,
                        raw bindHead (.app (.const ``Id [.succ .zero]) word)
                          (.app (.const ``Id [.succ .zero]) word) resultType.expr bindInstance,
                        raw bindHead resultType.expr resultType.expr (.app (.const ``Id [.succ .zero]) word) bindInstance,
                        raw (.const `customBind [.zero, .zero]) resultType.expr resultType.expr resultType.expr bindInstance,
                        raw (.const ``Bind.bind [.succ .zero, .zero]) resultType.expr resultType.expr resultType.expr bindInstance,
                        raw bindHead resultType.expr resultType.expr resultType.expr (.const `customBindInstance []),
                        setup monadic bad (save monadic core),
                        setup monadic (if booleanSetup then .bvar originalWord else .bvar originalFlag) (save monadic core),
                        setup monadic setupValue bad,
                        setup monadic setupValue (Identity.bind `saved binder action (toWord (.bvar 0)) resultType resultType),
                        setup monadic setupValue (.letE `saved boolean action tail flagFirst),
                        setup monadic setupValue (.letE `saved resultType.expr action (.bvar 999) flagFirst),
                        setup monadic setupValue (.letE `unused resultType.expr bad (core.liftLooseBVars 0 1) flagFirst),
                        setup monadic setupValue (.letE `first resultType.expr action (action.liftLooseBVars 0 1) flagFirst),
                        setup monadic setupValue (Identity.bind `first binder action (action.liftLooseBVars 0 1) resultType resultType),
                        setup monadic setupValue (.letE `first resultType.expr action ((bindBody action tail).liftLooseBVars 0 1) flagFirst)]
                      for value in invalid do
                        if (extractScalarFunc `invalidBooleanWordResult (some "entry") signature (wrap value)).isSome then
                          throwError "invalid result binding accepted: {monadic}, {annotationDepth}, {kind}, {mode}, {tailForm}"
                        rejected := rejected + 1
  unless comparisons == 129024 && rejected == 73728 && controls == 6144 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/word-loop bindings syntax comparisons, {rejected} invalid-input tests and {controls} binding controls passed"
