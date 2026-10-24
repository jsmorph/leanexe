import Verified.Wasi.CommandIte

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_command_ite {World : Type} {source target : Wasm.Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty} {result : ResultTy}
    {funs : Funs pureSigs} {effectFuns : EffectFuns effectSigs}
    {flags : Flags pureSigs} {bounds : Bounds pureSigs} {fits : Fits pureSigs}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)}
    {pool : Bytes.LiteralPool} {env : Env context} {slots : List Slot} {paid : List Bool}
    {live : Nat → Bool} {params : List Value} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {h base : Nat} {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source)
    (spec : CodeSpec source funs flags bounds fits sourceHost params condition env slots paid
      (fun i => live i || yes.uses i || no.uses i) pool)
    (form : Encoding.ProgramForm
      (condition.code (pool := pool) h slots base (fun i => live i || yes.uses i || no.uses i) ++
        coerceCode h .bool (condition.mode (slots.map Slot.mode)) .owned base))
    (closed : Relocation.programClosed source.funcs.length
      (condition.code (pool := pool) h slots base (fun i => live i || yes.uses i || no.uses i) ++
        coerceCode h .bool (condition.mode (slots.map Slot.mode)) .owned base) = true)
    (cleanupForm : ∀ choice : Bool, Encoding.ProgramForm (releaseWhere context slots
      (fun i => (live i || yes.uses i || no.uses i) &&
        !(live i || (bif choice then yes else no).uses i))))
    (cleanupClosed : ∀ choice : Bool, Relocation.programClosed source.funcs.length
      (releaseWhere context slots (fun i => (live i || yes.uses i || no.uses i) &&
        !(live i || (bif choice then yes else no).uses i))) = true)
    (positions : locals.positions = h) (parameters : locals.params = params)
    (vars : Holds env slots
      (fun i => (live i || yes.uses i || no.uses i) || condition.uses i) base heap
      (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots
      (fun i => (live i || yes.uses i || no.uses i) || condition.uses i)
      (PureTransport.erase initial) locals ABI.scratch)
    (at_ : heap.At (PureTransport.erase initial))
    (safe : pool.Safe env slots
      (fun i => (live i || yes.uses i || no.uses i) || condition.uses i) heap
      (PureTransport.erase initial) locals)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (conditionRoom : base + max condition.width (copyWidth .bool) ≤ h)
    (resultRoom : base + result.width ≤ h)
    (place : condition.placeArgs = true)
    (prefixFailure : (!(condition.fits funs fits env) || !decide
      (heap.Within (PureTransport.erase initial) source
        (returnCost funs flags bounds condition env slots paid
          (fun i => live i || yes.uses i || no.uses i)
          (PureTransport.erase initial) locals))) = true → aborts = true)
    (branch :
      let mid := fun i => live i || yes.uses i || no.uses i
      let picked := bif condition.denote funs env then yes else no
      ∀ (prefixHeap : Heap) (conditionStore : Store (Observed World)) (prefixLocals : Locals),
      After env slots (fun i => mid i || condition.uses i) mid base heap initial locals
        (.value .bool) (condition.denote funs env) prefixHeap conditionStore prefixLocals
        [.i64 (boolWord (condition.denote funs env))] →
      conditionStore.host = initial.host →
      (condition.fits funs fits env = true → prefixHeap.top.toNat ≤ heap.top.toNat +
        returnCost funs flags bounds condition env slots paid mid
          (PureTransport.erase initial) locals) →
      ∀ (middleHeap : Heap) (middle : Store (Observed World)),
      Evolves env slots mid (fun i => live i || picked.uses i) (base + result.width)
        prefixHeap (PureTransport.erase conditionStore) { prefixLocals with values := locals.values }
        middleHeap (PureTransport.erase middle) { prefixLocals with values := locals.values } →
      middleHeap.top = prefixHeap.top → middle.host = conditionStore.host →
      middleHeap.At (PureTransport.erase middle) →
      Holds env slots (fun i => live i || picked.uses i) (base + result.width)
        middleHeap (PureTransport.erase middle) { prefixLocals with values := locals.values } →
      pool.Safe env slots (fun i => live i || picked.uses i) middleHeap
        (PureTransport.erase middle) { prefixLocals with values := locals.values } →
      Holds.ApartFrom env slots (fun i => live i || picked.uses i)
        (PureTransport.erase middle) { prefixLocals with values := locals.values } ABI.scratch →
      (PureTransport.erase middle).memoryCap source 0 ≤ 65535 →
      wp target (picked.code (pool := pool) source h slots (base + result.width) live)
        (CommandResult host env slots (fun i => live i || picked.uses i) live
          (base + result.width) result (picked.denote funs effectFuns env) middleHeap middle
          { prefixLocals with values := locals.values } aborts)
        middle { prefixLocals with values := locals.values } targetHost) :
    wp target ((Command.ite condition yes no).code (pool := pool) source h slots base live)
      (CommandResult host env slots
        (fun i => (live i || yes.uses i || no.uses i) || condition.uses i) live base result
        ((Command.ite condition yes no).denote funs effectFuns env) heap initial locals aborts)
      initial locals targetHost := by
  let mid := fun i => live i || yes.uses i || no.uses i
  let picked := bif condition.denote funs env then yes else no
  let branchLive := fun i => live i || picked.uses i
  let yesCode := Relocation.program (releaseWhere context slots
      (fun i => mid i && !(live i || yes.uses i))) ++
    yes.code (pool := pool) source h slots (base + result.width) live ++
    storeCode h base result.types
  let noCode := Relocation.program (releaseWhere context slots
      (fun i => mid i && !(live i || no.uses i))) ++
    no.code (pool := pool) source h slots (base + result.width) live ++
    storeCode h base result.types
  let Q := CommandResult host env slots (fun i => mid i || condition.uses i) live base result
    ((Command.ite condition yes no).denote funs effectFuns env) heap initial locals aborts
  have midSelected : ∀ i, mid i = true → (mid i || condition.uses i) = true := by
    intro i selected
    simp only [selected, Bool.true_or]
  have branchSelected : ∀ i, branchLive i = true → mid i = true := by
    intro i selected
    cases truth : condition.denote funs env <;>
      simp [branchLive, picked, truth, Bool.or_eq_true] at selected <;>
      simp only [mid, Bool.or_eq_true] <;> tauto
  have liveSelected : ∀ i, live i = true → branchLive i = true := by
    intro i selected
    simp only [branchLive, selected, Bool.true_or]
  have actionEq : (Command.ite condition yes no).denote funs effectFuns env =
      picked.denote funs effectFuns env := by
    cases truth : condition.denote funs env <;> simp [Command.denote, picked, truth]
  have codeEq : (if condition.denote funs env then yesCode else noCode) =
      Relocation.program (releaseWhere context slots (fun i => mid i && !branchLive i)) ++
        picked.code (pool := pool) source h slots (base + result.width) live ++
        storeCode h base result.types := by
    cases truth : condition.denote funs env <;>
      simp [yesCode, noCode, picked, branchLive, truth]
  have noCoerce : coerceCode h .bool (condition.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have execution := wp_return (targetHost := targetHost) runtime layout profile spec form closed
    positions parameters vars at_ safe cap low conditionRoom place
    (rest := [.eqzI64, .iff 0 0 noCode yesCode [] []] ++ loadCode h base result.types)
    (Q := Q)
    (fun failure final sameWorld => CommandResult.resource_refl (prefixFailure failure) sameWorld)
    (fun prefixHeap conditionStore prefixLocals words first sameWorld prefixTop => by
      have wordsEq : words = [.i64 (boolWord (condition.denote funs env))] := first.rep
      subst words
      have reset : Frame base prefixLocals { prefixLocals with values := locals.values } :=
        Frame.ofValues
      have first' := first.reframe reset
      have prefixSafe := (first'.pool_safe safe vars apart midSelected poolApart).1
      have prefixApart := first'.scratch vars apart midSelected
      have selectedBranch : wp target
          (if condition.denote funs env then yesCode else noCode)
          (ItePost targetHost target (loadCode h base result.types) Q locals.values)
          conditionStore { prefixLocals with values := locals.values } targetHost := by
        rw [codeEq]
        refine wp_ite_branch (host := host) (sourceHost := sourceHost) (aborts := aborts)
          (action := picked.denote funs effectFuns env)
          runtime layout profile (cleanupForm (condition.denote funs env))
          (cleanupClosed (condition.denote funs env)) first'.holds prefixApart prefixSafe poolApart
          first'.step.at_ (by rw [first'.step.cap source]; exact cap)
          branchSelected liveSelected (first'.frame.positions.trans positions)
          (by rw [first'.frame.params]; exact low) resultRoom ?_ ?_ ?_ ?_
        · intro middleHeap middle evolution top world at_ held safe apart cap
          exact branch prefixHeap conditionStore prefixLocals first sameWorld prefixTop middleHeap middle
            evolution top world at_ held safe apart cap
        · intro finalHeap final stored words value trace sourceExecution after held
          change wp target (loadCode h base result.types) Q final
            { stored with values := locals.values } targetHost
          have combined := After.thenEmpty vars apart first'
            (ResultTy.fresh_scalar (result := .value .bool) rfl) after midSelected
            (fun i selected => branchSelected i (liveSelected i selected))
          have sourceExecution' : Exec (observedHost host)
              ((Command.ite condition yes no).denote funs effectFuns env)
              initial.host trace (.returned value) final.host := by
            rw [actionEq, ← sameWorld]
            exact sourceExecution
          have loaded : wp target (loadCode h base result.types ++ []) Q final
              { stored with values := locals.values } targetHost := by
            refine wp_loadCode words after.rep.typed (combined.frame.positions.trans positions)
              held ?_
            rw [wp_nil]
            exact CommandResult.returned (result := result) value finalHeap final stored words trace
              sourceExecution' combined
          simpa only [List.append_nil] using loaded
        · intro final trace outcome message sourceExecution terminal
          change Q (.Trap final message)
          apply CommandResult.terminal final trace outcome message ?_ terminal
          rw [actionEq, ← sameWorld]
          exact sourceExecution
        · intro final trace residual allowed progress
          change Q (.Trap final "unreachable")
          apply CommandResult.resource final trace residual allowed
          rw [actionEq, ← sameWorld]
          exact progress
      have branchExecution := wp_ite_bool (condition := condition.denote funs env)
        (yes := yesCode) (no := noCode) (rest := loadCode h base result.types)
        (Q := Q) selectedBranch
      simpa only [List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil]
        using branchExecution)
  simpa only [Command.code, noCoerce, List.append_nil, List.cons_append, List.nil_append,
    List.append_assoc, mid, yesCode, noCode, Q] using execution

end Verified.Wasi
