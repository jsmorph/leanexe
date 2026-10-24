import Verified.Wasi.Exit
import Verified.Wasi.CommandSpec
import Verified.Wasi.Return

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_command_exit {World : Type} {source target : Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {context : List Ty} {status : Expr pureSigs context .word}
    {env : Env context} {slots : List Slot} {paid : List Bool} {live : Nat → Bool}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {h base : Nat} {aborts : Bool} {result : ResultTy}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (hHost : targetHost.Satisfies target (hostSpec host))
    (spec : CodeSpec source funs flags bounds fits sourceHost params status env slots paid live pool)
    (form : Encoding.ProgramForm (status.code (pool := pool) h slots base live ++
      coerceCode h .word (status.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (status.code (pool := pool) h slots base live ++
        coerceCode h .word (status.mode (slots.map Slot.mode)) .owned base) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots (fun i => live i || status.uses i) base heap
      (PureTransport.erase initial) locals)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots (fun i => live i || status.uses i) heap
      (PureTransport.erase initial) locals)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (room : base + max status.width 1 ≤ h) (place : status.placeArgs = true)
    (prefixFailure : (!(status.fits funs fits env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds status env slots paid live
          (PureTransport.erase initial) locals))) = true → aborts = true) :
    wp target ((Command.exit (effectSigs := effectSigs) (result := result) status).code
        (pool := pool) source h slots base live)
      (CommandResult host env slots (fun i => live i || status.uses i) live base result
        ((Command.exit (result := result) status).denote funs effectFuns env)
        heap initial locals aborts) initial locals targetHost := by
  let Q := CommandResult host env slots (fun i => live i || status.uses i) live base result
    ((Command.exit (result := result) status).denote funs effectFuns env) heap initial locals aborts
  have prefixRoom : base + max status.width (copyWidth .word) ≤ h := by
    have hWidth := Nat.le_max_left status.width 1
    simpa only [copyWidth, Ty.scalar, ite_true, Nat.max_zero] using
      (show base + status.width ≤ h by omega)
  have noCoerce : coerceCode h .word (status.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have execution := wp_return (targetHost := targetHost) runtime layout profile spec form closed positions parameters
    vars at_ safe cap low prefixRoom place (rest := [.localSet base] ++ exitCode base) (Q := Q)
    (fun failure final sameWorld => CommandResult.resource_refl (prefixFailure failure) sameWorld)
    (fun middleHeap middle middleLocals words first sameWorld _ => by
      have wordsEq : words = [.i64 (status.denote funs env)] := first.rep
      subst words
      have middleLow : middleLocals.params.length ≤ base := by
        rw [first.frame.params]
        exact low
      have middleHigh : base < middleLocals.params.length + middleLocals.locals.length := by
        apply Locals.lt_total
        rw [first.frame.positions, positions]
        have hOne := Nat.le_max_right status.width 1
        omega
      simp only [List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil]
      refine wp_localSet_local (env := targetHost) (s := middleLocals) (i := base)
        (v := .i64 (status.denote funs env)) (vs := locals.values) middleLow middleHigh ?_
      have codeLocal : (setLocal { middleLocals with values := locals.values }
          base (.i64 (status.denote funs env))).get base =
          some (.i64 (status.denote funs env)) :=
        Locals.get_setLocal_same middleLow middleHigh
      have terminal : wp target (exitCode base ++ []) Q middle
          (setLocal { middleLocals with values := locals.values }
            base (.i64 (status.denote funs env))) targetHost := by
        refine wp_exit hImports hHost codeLocal ?_ ?_
        · intro final accepted _
          have hostExit : (observedHost host).exit initial.host
              (exitStatus (status.denote funs env)) final.host := by
            rw [← sameWorld]
            exact accepted
          have sourceExit : Exec (observedHost host)
              ((Command.exit (result := result) status).denote funs effectFuns env)
              initial.host [.exit (exitStatus (status.denote funs env))]
              (.exited (exitStatus (status.denote funs env))) final.host :=
            Exec.exit (α := result.denote) hostExit
          exact CommandResult.terminal (result := result) final
            [.exit (exitStatus (status.denote funs env))]
            (.exited (exitStatus (status.denote funs env))) exitTrap sourceExit rfl
        · intro final message rejected _
          have hostTrap : (observedHost host).exitTrap initial.host
              (exitStatus (status.denote funs env)) message final.host := by
            rw [← sameWorld]
            exact rejected
          have sourceTrap : Exec (observedHost host)
              ((Command.exit (result := result) status).denote funs effectFuns env)
              initial.host [.exitTrap (exitStatus (status.denote funs env)) message]
              (.trapped message) final.host := Exec.exitTrap (α := result.denote) hostTrap
          exact CommandResult.terminal (result := result) final
            [.exitTrap (exitStatus (status.denote funs env)) message]
            (.trapped message) message sourceTrap rfl
      simpa only [List.append_nil] using terminal)
  simpa only [noCoerce, List.append_nil, Command.code, Q, List.append_assoc] using execution

end Verified.Wasi
