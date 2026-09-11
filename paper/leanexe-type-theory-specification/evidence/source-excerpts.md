# Source evidence for the submitted report

All excerpts come from checkpoint `2f3ec33f6e98ad98ac94df277c91e5319763cf9d`.  The file digests and compared paths appear in [Source identities](source-identities.json).  This record preserves inspected declarations.  It records no new Lean checks or runtime reproducer.

## Entry-name exclusion

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Extract/Core.lean#L7005) in `LeanExe/Extract/Core.lean`.

```text
7005: def reservedExportNames : List String :=
7006:   ["memory", "alloc", "reset"]
7007: 
7008: def extractFunction
7009:     (exportEntry : Bool)
7010:     (ctx : Context)
7011:     (entry name : Name)
7012:     (info : ConstantInfo)
7013:     (sig : Signature) : Except String IRFunc := do
7014:   let value ←
7015:     match info.value? with
7016:     | some value => .ok (betaSpecializeExpr ctx.env ctx.root 32 value)
7017:     | none => .error s!"declaration has no executable value: {name}"
7018:   let exportName ←
7019:     if exportEntry && name == entry then
7020:       let candidate := shortExportName name
7021:       if reservedExportNames.contains candidate then
7022:         .error s!"entry export name is reserved by the runtime ABI: {candidate}"
7023:       else
7024:         .ok (some candidate)
7025:     else
7026:       .ok none
7027:   match sig.params with
7028:   | .nat :: _ =>
7029:       if containsConstantInExpr ``Nat.brecOn value then
7030:         extractNatRecFunc ctx name sig.params sig.result value exportName
7031:       else
7032:         extractPlainFunc ctx name sig.params sig.result value exportName
7033:   | .sum _ _ :: _ =>
7034:       if containsConstantInExpr ``WellFounded.Nat.fix value then
```

## Natural-number child mask

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Extract/Values.lean#L1745) in `LeanExe/Extract/Values.lean`.

```text
1745:   partial def heapChildMaskFromType (slot : Nat) : Ty → Nat × Nat
1746:     | .recVariant _ _ => (2 ^ slot, slot + 1)
1747:     | .product left right =>
1748:         let leftResult := heapChildMaskFromType slot left
1749:         let rightResult := heapChildMaskFromType leftResult.snd right
1750:         (leftResult.fst + rightResult.fst, rightResult.snd)
1751:     | .sum left right =>
1752:         let leftResult := heapChildMaskFromType (slot + 1) left
1753:         let rightResult := heapChildMaskFromType leftResult.snd right
1754:         (leftResult.fst + rightResult.fst, rightResult.snd)
1755:     | .struct _ _ fields => heapChildMaskFromTypes slot fields
1756:     | .variant _ _ ctors => heapChildMaskFromTypes (slot + 1) ctors.flatten
1757:     | .byteArray => (2 ^ slot, slot + 3)
1758:     | .array _ => (2 ^ slot, slot + 2)
1759:     | .unit => (0, slot + 1)
1760:     | .bool => (0, slot + 1)
1761:     | .u8 => (0, slot + 1)
1762:     | .u32 => (0, slot + 1)
1763:     | .u64 => (0, slot + 1)
1764:     | .nat => (0, slot + 1)
1765: 
1766:   partial def heapChildMaskFromTypes : Nat → List Ty → Nat × Nat
1767:     | slot, [] => (0, slot)
1768:     | slot, ty :: rest =>
1769:         let head := heapChildMaskFromType slot ty
1770:         let tail := heapChildMaskFromTypes head.snd rest
1771:         (head.fst + tail.fst, tail.snd)
1772: end
1773: 
1774: def heapChildMaskForCtors (ctors : List (List (Ty × ExtractedValue))) : Nat :=
1775:   (heapChildMaskFromTypes 1 (ctors.flatten.map Prod.fst)).fst
1776: 
1777: def maskBitSet (mask slot : Nat) : Bool :=
1778:   (mask / (2 ^ slot)) % 2 == 1
```

## Serialized i64 constant

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/Binary.lean#L163) in `LeanExe/Wasm/Binary.lean`.

```text
163: def i64Const (n : Nat) : List UInt8 :=
164:   let bits := n % (2 ^ 64)
165:   let signed :=
166:     if bits < 2 ^ 63 then
167:       Int.ofNat bits
168:     else
169:       Int.ofNat bits - Int.ofNat (2 ^ 64)
```

## Runtime child-mask scan

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/Binary.lean#L4198) in `LeanExe/Wasm/Binary.lean`.

```text
4198: def coreReleaseInstrs (releaseIndex : Nat) : List Instr :=
4199:   let rcLocal := 1
4200:   let kindLocal := 2
4201:   let limitLocal := 3
4202:   let widthLocal := 4
4203:   let maskLocal := 5
4204:   let slotLocal := 6
4205:   let itemLocal := 7
4206:   let childLocal := 8
4207:   let callReleaseChild := localGet childLocal ++ call releaseIndex
4208:   let slotReleaseLoop :=
4209:     i64Const 0 ++ localSet slotLocal ++
4210:       ([Instr.block [Instr.loop (localGet slotLocal ++ localGet limitLocal ++ i64GeU ++
4211:           [Instr.brIf 1] ++
4212:         localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
4213:           i64Const 0 ++ i64Ne ++
4214:           ([Instr.iff false (localGet 0 ++ localGet slotLocal ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
4215:               i32WrapI64 ++ i64Load ++ localSet childLocal ++
4216:             callReleaseChild) none]) ++
4217:         localGet slotLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet slotLocal ++
4218:         [Instr.br 0])]])
4219:   let arrayReleaseLoop :=
4220:     localGet 0 ++ i32WrapI64 ++ i64Load ++ localSet limitLocal ++
4221:       rcHeaderLoad (localGet 0) 16 ++ localSet widthLocal ++
4222:       rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
4223:       i64Const 0 ++ localSet itemLocal ++
4224:       ([Instr.block [Instr.loop (localGet itemLocal ++ localGet limitLocal ++ i64GeU ++
4225:           [Instr.brIf 1] ++
4226:         i64Const 0 ++ localSet slotLocal ++
4227:         ([Instr.block [Instr.loop (localGet slotLocal ++ localGet widthLocal ++ i64GeU ++
4228:             [Instr.brIf 1] ++
4229:           localGet maskLocal ++ localGet slotLocal ++ i64ShrU ++ i64Const 1 ++ i64And ++
4230:             i64Const 0 ++ i64Ne ++
4231:             ([Instr.iff false (localGet 0 ++ i64Const 8 ++ [Instr.addI64] ++
4232:                 localGet itemLocal ++ localGet widthLocal ++ [Instr.mulI64] ++
4233:                 localGet slotLocal ++ [Instr.addI64] ++ i64Const 8 ++ [Instr.mulI64, Instr.addI64] ++
4234:                 i32WrapI64 ++ i64Load ++ localSet childLocal ++
4235:               callReleaseChild) none]) ++
4236:           localGet slotLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet slotLocal ++
4237:           [Instr.br 0])]]) ++
4238:         localGet itemLocal ++ i64Const 1 ++ [Instr.addI64] ++ localSet itemLocal ++
4239:         [Instr.br 0])]])
4240:   let freeCurrent :=
4241:     incGlobal (runtimeStatGlobal .frees) ++
4242:       rcHeaderStore (localGet 0) 40 (i64Const 0) ++
4243:       rcHeaderStore (localGet 0) 8 (globalGet 1) ++
4244:       localGet 0 ++ globalSet 1
4245:   (localGet 0 ++ i64Const 0 ++ i64Eq ++
4246:       ([Instr.iff false (returnOp) none]) ++
4247:       rcHeaderLoad (localGet 0) 48 ++ i64Const rcMagic ++ i64Ne ++
4248:         ([Instr.iff false (unreachable) none]) ++
4249:       rcHeaderLoad (localGet 0) 40 ++ localSet rcLocal ++
4250:       localGet rcLocal ++ i64Const 0 ++ i64Eq ++
4251:         ([Instr.iff false (unreachable) none]) ++
4252:       incGlobal (runtimeStatGlobal .releases) ++
4253:       i64Const 1 ++ localGet rcLocal ++ i64LtU ++
4254:         ([Instr.iff false (rcHeaderStore (localGet 0) 40 (localGet rcLocal ++ i64Const 1 ++ [Instr.subI64]) ++
4255:           returnOp) none]) ++
4256:       rcHeaderLoad (localGet 0) 24 ++ localSet kindLocal ++
4257:       localGet kindLocal ++ i64Const rcKindSlots ++ i64Eq ++
4258:         ([Instr.iff false (rcHeaderLoad (localGet 0) 16 ++ localSet limitLocal ++
4259:           rcHeaderLoad (localGet 0) 8 ++ localSet maskLocal ++
4260:           slotReleaseLoop) none]) ++
4261:       localGet kindLocal ++ i64Const rcKindArray ++ i64Eq ++
4262:         ([Instr.iff false (arrayReleaseLoop) none]) ++
4263:       freeCurrent)
4264: 
4265: def imageUserFunction (releaseIndex : Nat) (func : Func) :
4266:     Except String LeanExe.Wasm.Image.Function := do
4267:   let body ← LeanExe.Wasm.Image.encodeInstrList (emitFuncInstrs releaseIndex func)
4268:   return {
4269:     params := func.params
4270:     results := func.results.length
4271:     locals := func.locals - func.params + funcScratch func
4272:     body
4273:   }
4274: 
4275: def imageRuntimeFunctions (releaseIndex : Nat) :
```

## Production serializer

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/Binary.lean#L4357) in `LeanExe/Wasm/Binary.lean`.

```text
4357: def moduleBytes (module_ : Module) : ByteArray :=
4358:   legacyModuleBytes module_
4359: 
4360: def annotationDocument (module_ : Module) (bytes : ByteArray) : Annotations.Document :=
4361:   let releaseIndex := module_.funcs.size + 3
4362:   let functions : List Annotations.Function :=
4363:     (enumerate module_.funcs.toList).map fun item =>
4364:       let functionIndex := item.fst
```

## Export section

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/Binary.lean#L77) in `LeanExe/Wasm/Binary.lean`.

```text
77: def exportSection : List UInt8 :=
78:   wasmSection 7 <| vec [
79:     exportEntry "memory" 2 0,
80:     exportEntry "alloc" 0 0,
81:     exportEntry "reset" 0 1,
82:     exportEntry "validate" 0 2
83:   ]
84: 
85: def body (locals code : List UInt8) : List UInt8 :=
86:   byteVec (locals ++ code ++ ofNats [11])
87: 
88: def allocBody : List UInt8 :=
89:   body
90:     (ofNats [0])
91:     (ofNats [
92:       35, 0,
93:       35, 0,
94:       32, 0,
95:       106,
96:       36, 0
97:     ])
98: 
99: def resetBody : List UInt8 :=
100:   body
101:     (ofNats [0])
102:     (ofNats [65] ++ u32leb 4096 ++ ofNats [36, 0])
103: 
104: def validateBody (validator : LeanExe.Core.LoweredValidator) : List UInt8 :=
105:   body
106:     (ofNats [1, 2, 127])
107:     (ofNats [
108:       65, 0,
109:       33, 2,
110:       2, 64,
111:       2, 64,
```

## Export section

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/Binary.lean#L4148) in `LeanExe/Wasm/Binary.lean`.

```text
4148: def exportSection (module_ : Module) : List UInt8 :=
4149:   wasmSection 7 <| vec <|
4150:     [exportEntry "memory" 2 0] ++
4151:       (enumerate module_.funcs.toList |>.filterMap fun item =>
4152:         item.snd.exportName.map (fun exportName => exportEntry exportName 0 item.fst)) ++
4153:       [exportEntry "alloc" 0 module_.funcs.size,
4154:         exportEntry "reset" 0 (module_.funcs.size + 1),
4155:         exportEntry "retain" 0 (module_.funcs.size + 2),
4156:         exportEntry "release" 0 (module_.funcs.size + 3),
4157:         exportEntry "free" 0 (module_.funcs.size + 3),
4158:         exportEntry "allocCount" 3 (runtimeStatGlobal .allocs),
4159:         exportEntry "retainCount" 3 (runtimeStatGlobal .retains),
4160:         exportEntry "releaseCount" 3 (runtimeStatGlobal .releases),
4161:         exportEntry "freeCount" 3 (runtimeStatGlobal .frees)]
4162: 
4163: def bodyI (locals : List UInt8) (code : List Instr) : List UInt8 :=
4164:   body locals (encodeInstrs code)
4165: 
4166: def coreAllocInstrs : List Instr :=
4167:   rcAllocRawObject 1 (localGet 0)
4168: 
4169: def coreAllocBody : List UInt8 :=
4170:   bodyI (ofNats [1, 6, 126]) coreAllocInstrs
4171: 
4172: def coreResetInstrs : List Instr :=
4173:   (i64Const 4096 ++ globalSet 0 ++
4174:       i64Const 0 ++ globalSet 1 ++
4175:       i64Const 0 ++ globalSet (runtimeStatGlobal .allocs) ++
4176:       i64Const 0 ++ globalSet (runtimeStatGlobal .retains) ++
4177:       i64Const 0 ++ globalSet (runtimeStatGlobal .releases) ++
4178:       i64Const 0 ++ globalSet (runtimeStatGlobal .frees))
4179: 
4180: def coreResetBody : List UInt8 :=
4181:   bodyI (ofNats [0]) coreResetInstrs
4182: 
```

## Scalar emitter equality

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/LeanExe/Wasm/ScalarCertificate.lean#L14) in `LeanExe/Wasm/ScalarCertificate.lean`.

```text
14: theorem Expr.ofIR_emitWithRelease
15:     (releaseIndex scratch : Nat) (expression : LeanExe.IR.Expr)
16:     (descriptor : Expr)
17:     (hReify : Expr.ofIR expression = some descriptor) :
18:     Binary.CoreWasm.emitExprWithRelease releaseIndex scratch expression =
19:       descriptor.emit scratch := by
20:   unfold Binary.CoreWasm.emitExprWithRelease
21:   rw [hReify]
22: 
23: theorem Cond.ofIR_emitWithRelease
```

## Decoder theorem

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean#L1473) in `proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean`.

```text
1473: theorem decode_sound {bytes : ByteArray} {module_ : RawModule}
1474:     (h : decode bytes = .ok module_) :
1475:     Grammar.Encodes bytes module_ := by
1476:   exact Parser.runAll_sound moduleParser_sound h
1477: 
1478: end Wasm.Binary.Proof
```

## Validator theorem

[Source declaration](https://github.com/jsmorph/leanexe/blob/2f3ec33f6e98ad98ac94df277c91e5319763cf9d/proofs/talos/lean/Project/Artifact/Binary/Proof/Validate.lean#L1197) in `proofs/talos/lean/Project/Artifact/Binary/Proof/Validate.lean`.

```text
1197: theorem validate_sound {module_ : RawModule} {validated : ValidatedModule}
1198:     (h : validate module_ = .ok validated) :
1199:     CoreValid module_ := by
1200:   unfold validate at h
1201:   dsimp [Bind.bind, Monad.toBind, Except.bind] at h
1202:   split at h
1203:   · contradiction
1204:   · rename_i parsed _ hraw
1205:     exact validateRaw_sound hraw
```
