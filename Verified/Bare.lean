import Verified.Native
import LeanExe.Native.Proof.Main

/-!
The theorems of bare-metal programs (`docs/native-bare-metal.md`).  `bare_of_nativeTables` is
`bare_of_nativeA` for a wrapper, whose `NativeTablesImpl` adds that the tables are borrowed arrays
apart from the blocks that the call consumes.  `bare_program p.f := (x) [args]` states and proves
`p.f.program`: for every list of CompCert's declarations that `PrefixOk` accepts, the program
`bareProgram` of the translation with `main` calling the entry of `f` on the words `args`, the
words of the argument `x`, terminates with result 0 after writing the bytes of `f x` to `lx_out`,
`encodeWord` for a `UInt64` and `encodeArray` for an `Array UInt64`, or, when `f` may abort,
with no event and the code of `unreachable`.  The command reads the entry, the flag `aborts`,
the kind of theorem, and the result's type from `p.f.implements`, and proves the theorem from
`p.f.native` and `p.initial`.
-/

namespace Verified

open Wasm LClight LeanExe.Native LeanExe.Pipeline

theorem borrowed_nativeStore {heap : Heap} {m : Module} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Borrowed (m.initialStore : Store Unit) ptr words) (cap : Nat) :
    heap.Borrowed (nativeStore m cap) ptr words :=
  ⟨h.values, h.below, h.separate⟩

/-- `bare_of_nativeA` for a wrapper of the tables `tables`, each a borrowed array of the module's
initial store, for an argument that moves no block. -/
theorem bare_of_nativeTables {α β : Type} [Represent α] [Represent β] {A : Archi} {X : ExtSem}
    {cap : Nat} {m : Module} {T : Translation} (h : translate cap m = some T)
    {pre : List (ident × globdef (fundef function) type)} (hpre : PrefixOk pre) {k : Nat}
    {aborts : Bool} {f : α → β} {tables : List (UInt64 × Array UInt64)}
    {Pre : α → Heap → Store Unit → Prop}
    {Post : α → Heap → Store Unit → Heap → Store Unit → Prop}
    (hn : ∃ fd ps rs, (funId k, globdef.Gfun (fundef.Internal fd)) ∈ T.cprogram.prog_defs ∧
      (∀ g, m.funcs[k]? = some g → signatureOf g = some (ps, rs)) ∧
      NativeTablesA A X cap m T ps rs fd aborts f tables Pre Post)
    (args : List UInt64)
    (hk : (m.funcs[k]?).bind signatureOf = some (args.map fun _ => .i64, [.i64]))
    (kind : OutKind) (x : α) (heap : Heap) {bs : List UInt8}
    (hheap : heap.At (m.initialStore : Store Unit))
    (htables : ∀ t ∈ tables, heap.Borrowed (m.initialStore : Store Unit) t.1 t.2)
    (hPre : Pre x heap (nativeStore m cap))
    (hb : Represent.borrowed heap (nativeStore m cap) (args.map Value.i64) x)
    (hmoves : Represent.moves (nativeStore m cap) (args.map Value.i64) x = [])
    (hsep : Separate (nativeStore m cap) (Represent.moves (nativeStore m cap) (args.map .i64) x)
      (Represent.reads (nativeStore m cap) (args.map .i64) x))
    (hcap : cap ≤ 65535)
    (hout : ∀ (E : LeanExe.Native.Env) vs vres m' (heap' : Heap) final, ResultRel E [.i64] vs [] vres m' →
      Represent.owned heap' final vs.reverse (f x) → OutOk kind final vres bs) :
    bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind)) (outTrace bs) 0 ∨
      (aborts = true ∧ bigstep_program_terminates A X (bareProgram pre T (bareMain cap k args kind))
        E0 (UInt32.ofNat trapUnreachable)) := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := hn
  obtain ⟨rfl, rfl⟩ := sig_eq hsig hk
  have hty := entry_type h hfd hsig
  rw [funType_i64] at hty
  refine bare_program h hpre hfd args kind hty A X fun E hE hG hcap' hnres hF m1 hst hs => ?_
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap' hnres hF
    (nativeStore m cap) heap (args.map .i64) x (heapAt_nativeStore hheap cap) hPre
    (fun t ht => ⟨borrowed_nativeStore (htables t ht) cap, by rw [hmoves]; exact Apart.nil⟩) hb
    hsep hcap (argsTyped_i64 args) m1 hst hs
  rw [argVals_i64] at hcall
  refine ⟨t, m', vres, final, hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | habort
  · have hd : (args.map Value.i64).reverse.drop (args.map fun _ => VT.i64).length = [] := by
      simp
    rw [hd] at hr
    exact .inl ⟨hs', hout E vs vres m' heap' final hr hown⟩
  · exact .inr habort

/-! ## The command -/

open Lean Elab Command

syntax (name := bareProgramCmd)
  "bare_program " ident ppSpace term:max ppSpace "[" term,* "]" ppSpace term:max : command

/-- `bare_program p.f x [a₁, …] r` adds `p.f.program`, the theorem of the bare-metal program
whose `main` calls the entry of `f` on the words `a₁, …` of the argument `x`, with the result
`r`, which must be `f x`. -/
@[command_elab bareProgramCmd]
def elabBareProgram : CommandElab
  | `(bare_program $pf:ident $x:term [$args,*] $res:term) => do
    let implName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo
      (mkIdent (pf.getId ++ `implements))
    let ty := (← getConstInfo implName).type
    let some head := ty.getAppFn.constName?
      | throwError "bare_program: the theorem {implName}"
    let targs := ty.getAppArgs
    let tables := head == ``Verified.ImplementsTables
    unless tables || head == ``LeanExe.Pipeline.ImplementsA do
      throwError "bare_program: {implName} states neither ImplementsA nor ImplementsTables"
    let some k := targs[6]!.nat?
      | throwError "bare_program: the entry of {implName}"
    let aborts ← if targs[4]!.isConstOf ``Bool.true then `(true)
      else if targs[4]!.isConstOf ``Bool.false then `(false)
      else throwError "bare_program: the flag aborts of {implName}"
    let β := targs[1]!
    let word := β.isConstOf ``UInt64
    unless word || β == mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64) do
      throwError "bare_program: the result of {implName} is neither UInt64 nor Array UInt64"
    let f := implName.getPrefix
    let p := f.getPrefix
    let kind ← if word then `(LeanExe.Native.OutKind.word) else `(LeanExe.Native.OutKind.array)
    let enc ← if word then `(LeanExe.Native.encodeWord) else `(LeanExe.Native.encodeArray)
    let outOk ← if word then `(LeanExe.Native.outOk_word) else `(LeanExe.Native.outOk_array)
    let kStx := Syntax.mkNumLit (toString k)
    let trans := mkCIdent (p ++ `translation)
    let eqn := mkCIdent (p ++ `translation_eq)
    let initial := mkCIdent (p ++ `initial)
    let native := mkCIdent (f ++ `native)
    let prog ← `(LeanExe.Native.bareProgram pre $trans
      (LeanExe.Native.bareMain LeanExe.Native.nativeCap $kStx [$args,*] $kind))
    let proof ← if tables then
        `(Verified.bare_of_nativeTables $eqn hpre ($native A X) [$args,*] rfl $kind $x _
          $initial.1
          (fun t ht => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            repeat' (first | (obtain rfl | ht := ht) | subst ht)
            all_goals first
              | exact $initial.2.2 0 (by decide) | exact $initial.2.2 1 (by decide)
              | exact $initial.2.2 2 (by decide) | exact $initial.2.2 3 (by decide))
          trivial rfl rfl LeanExe.Pipeline.Separate.nil (by decide)
          (fun _ _ _ _ _ _ hr hown => $outOk hr rfl hown))
      else
        `(LeanExe.Native.bare_of_nativeA $eqn hpre ($native A X) [$args,*] rfl $kind $x _
          $initial.1 trivial rfl LeanExe.Pipeline.Separate.nil (by decide)
          (fun _ _ _ _ _ _ hr hown => $outOk hr rfl hown))
    elabCommand (← `(
      set_option maxRecDepth 100000 in
      theorem $(mkIdent (`_root_ ++ f ++ `program)) (A : LClight.Archi) (X : LClight.ExtSem)
          (pre : List (LClight.ident × LClight.globdef (LClight.fundef LClight.function)
            LClight.type))
          (hpre : LeanExe.Native.PrefixOk pre) :
          LClight.bigstep_program_terminates A X $prog (LeanExe.Native.outTrace ($enc $res)) 0 ∨
            ($aborts = true ∧ LClight.bigstep_program_terminates A X $prog LClight.E0
              (UInt32.ofNat LeanExe.Native.trapUnreachable)) :=
        $proof))
  | _ => throwUnsupportedSyntax

end Verified
