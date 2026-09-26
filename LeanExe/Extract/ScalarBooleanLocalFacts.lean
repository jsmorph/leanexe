import LeanExe.Extract.ScalarBooleanLocalCore

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (BooleanLocal booleanLetExpr booleanWordLetExpr booleanLetBooleans)

theorem extractBooleanLocal_operands (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target) :
    ∀ operand member, ∃ expression, compile operand member = some expression := by
  induction guard generalizing target compileFunctions with
  | var n index | literal n index =>
    intro operand member
    simp [BooleanLocal.operands] at member
  | predicate n index argument =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨function, hf, value, hv, result, hr, _⟩ := compiled
    intro operand member
    have same : operand = argument := by simpa [BooleanLocal.operands] using member
    subst operand
    exact ⟨value, hv⟩
  | compare op a b =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨left, hl⟩
    · exact ⟨right, hr⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl operand first
    · exact ihb _ _ _ hr operand second
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl operand first
    · exact ihb _ _ _ hr operand second
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_append] at member
    rcases member with member | member | member | member
    · exact iha _ _ _ hl operand member
    · exact ihb _ _ _ hr operand member
    · exact iht _ _ _ ht operand member
    · exact ihe _ _ _ he operand member
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro operand member
    rcases List.mem_append.mp member with first | rest
    · exact extractGuard_operands g.value _ hc operand first
    · rcases List.mem_append.mp rest with second | third
      · exact iht _ _ _ ht operand second
      · exact ihe _ _ _ he operand third
  | binding n name form value body type ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro operand member
    simp only [BooleanLocal.operands, List.mem_append, List.mem_map] at member
    rcases member with first | ⟨inner, innerMember, equality⟩
    · exact ihv _ _ _ hl operand first
    · subst operand
      exact ihb _ _ _ hr inner innerMember
  | decision n g =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, _⟩ := compiled
    exact extractGuard_operands g.value compile hc

  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      intro operand member
      simp only [BooleanLocal.operands, List.mem_cons, List.mem_map] at member
      rcases member with equality | ⟨inner, innerMember, equality⟩
      · subst operand; exact ⟨word, hv⟩
      · subst operand; exact ihb _ _ _ hb inner innerMember
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact ih compileFunctions compileVariables compile hc


theorem extractBooleanLocal_variables (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target) :
    ∀ index member, ∃ expression, compileVariables index member = some expression := by
  induction guard generalizing target compileFunctions with
  | literal | compare | decision | predicate =>
    intro index member
    simp [BooleanLocal.variables] at member
  | var n index =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨expression, found, _⟩ := compiled
    intro other member
    have same : other = index := by simpa [BooleanLocal.variables] using member
    subst other
    exact ⟨expression, found⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl index first
    · exact ihb _ _ _ hr index second
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl index first
    · exact ihb _ _ _ hr index second
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    intro index member
    simp only [BooleanLocal.variables, List.mem_append] at member
    rcases member with member | member | member | member
    · exact iha _ _ _ hl index member
    · exact ihb _ _ _ hr index member
    · exact iht _ _ _ ht index member
    · exact ihe _ _ _ he index member
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iht _ _ _ ht index first
    · exact ihe _ _ _ he index second
  | binding n name form value body type ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact ihv _ _ _ hl index first
    · exact booleanLetLookup_external _ _ _ (ihb _ _ _ hr) index second

  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      exact booleanWordLetLookup_external _ _ _ (ihb _ _ _ hb)
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact ih compileFunctions compileVariables compile hc


theorem extractBooleanLocal_functions (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target) :
    compileFunctions.Present guard.functions := by
  induction guard generalizing target compileFunctions with
  | literal | compare | decision | var =>
    intro index member
    simp [BooleanLocal.functions] at member
  | predicate n index argument =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨function, found, value, hv, result, hr, _⟩ := compiled
    intro other member
    have same : other = index := by simpa [BooleanLocal.functions] using member
    subst other
    exact ⟨function, found⟩
  | junction n op a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl index first
    · exact ihb _ _ _ hr index second
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iha _ _ _ hl index first
    · exact ihb _ _ _ hr index second
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    intro index member
    simp only [BooleanLocal.functions, List.mem_append] at member
    rcases member with member | member | member | member
    · exact iha _ _ _ hl index member
    · exact ihb _ _ _ hr index member
    · exact iht _ _ _ ht index member
    · exact ihe _ _ _ he index member
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact iht _ _ _ ht index first
    · exact ihe _ _ _ he index second
  | binding n name form value body type ihv ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    intro index member
    rcases List.mem_append.mp member with first | second
    · exact ihv _ _ _ hl index first
    · exact (ihb _ _ _ hr).external index second

  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      exact (ihb _ _ _ hb).external
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact ih compileFunctions compileVariables compile hc


theorem extractBooleanLocal_scoped (guard : BooleanLocal) (compileFunctions : BooleanFunctionLookup)
    (compileVariables : (index : Nat) → index ∈ guard.variables → Option LeanExe.IR.Expr)
    (compile : (operand : Lean.Expr) → operand ∈ guard.operands → Option LeanExe.IR.Expr)
    {target : LeanExe.IR.Cond} (compiled : extractBooleanLocal compileFunctions guard compileVariables compile = some target) :
    guard.WellScoped := by
  induction guard generalizing target compileFunctions with
  | var | literal | compare | decision | predicate => trivial
  | junction n op a b iha ihb
  | equality n unequal a b iha ihb
  | relationDecision n unequal a b iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    exact ⟨iha _ _ _ hl, ihb _ _ _ hr⟩
  | binding n name form a b type iha ihb =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, _⟩ := compiled
    exact ⟨iha _ _ _ hl, ihb _ _ _ hr,
      (extractBooleanLocal_functions b compileFunctions.shift _ _ hr).no_local⟩
  | choice n unequal a b t e iha ihb iht ihe
  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨left, hl, right, hr, yes, ht, no, he, _⟩ := compiled
    exact ⟨iha _ _ _ hl, ihb _ _ _ hr, iht _ _ _ ht, ihe _ _ _ he⟩
  | proposition n g t e iht ihe
  | dependentProposition n shape g t e iht ihe =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨test, hc, yes, ht, no, he, _⟩ := compiled
    exact ⟨iht _ _ _ ht, ihe _ _ _ he⟩
  | wordBinding n name form value body type ihb =>
    simp only [extractBooleanLocal] at compiled
    split at compiled
    · rename_i noLocal
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨word, hv, condition, hb, _⟩ := compiled
      exact ⟨noLocal, ihb _ _ _ hb,
        (extractBooleanLocal_functions body compileFunctions.shift _ _ hb).no_local⟩
    · contradiction
  | wrapped n wrapper body ih =>
    simp only [extractBooleanLocal, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨condition, hc, rfl⟩ := compiled
    exact ih compileFunctions compileVariables compile hc


end LeanExe.Extract.Core
