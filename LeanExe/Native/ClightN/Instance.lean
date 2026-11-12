import LeanExe.Native.ClightN.Reads
import LeanExe.Native.Proof.Ctl

/-!
What the instances of `clightn/check.sh` share: decidable equality of the copy's syntax, so that
the kernel compares a program it computes with the definitions of a Coq file, the copy's syntax
as terms (`Lean.ToExpr`), so that a tactic states a program as a literal, the renaming from a
whole program to the file's program, and the theorems that carry a whole program's theorem in the
copy to N's statement of an instance.  The renaming reads the file's identifiers off the two lists
of definitions, which list the same definitions in the same order: a global's identifier at its
position, and a temporary's at its position among a function's parameters and temporaries.
`preOf` gives CompCert's declarations the identifiers of the whole program, and
`inj_of_nodup_map` reduces injectivity on a list to the absence of repetitions in its image, a
check in proportion to the list's length.

An instance names the file's definitions `fd` and `main` `fm`, the translation `T`, and the
definitions `post` that follow the translation's in the whole program: `lx_out` and `main` of a
bare-metal program, `lx_in`, `lx_out`, and `main` of a program with input or a controller, and
`lx_reg` and `main` of a program with requests.  `InstOk post T fd fm` states what the kernel
checks of an instance: renaming the whole program `wholeOf post T fd` gives the file's program,
the renaming is injective, CompCert's declarations satisfy `PrefixOk`, and `progOk` accepts the
file's program with the functions that `main` reaches, `reach fd fm`.  The tactic `inst_ok`
proves it, with the translation's definitions as literals that the kernel checks in parts
against `translate` (`defs_of_parts`).  From it, `terminates_n` carries a termination of the
whole program to N's `nprog`, `bare_n` the theorem of a bare-metal program that `bare_program`
states, from `BareOk`, which adds the trace of the program's output, `reads_n` the terminations
of a program with input whose traces read every sequence, and `reacts_n` the runs of a `main`
that runs forever to N's `nreacts` with the reads of every prefix of its windows.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

deriving instance DecidableEq for LClight.expr
deriving instance DecidableEq for LClight.statement, LClight.labeled_statements
deriving instance DecidableEq for LClight.function
deriving instance DecidableEq for LClight.fundef
deriving instance DecidableEq for LClight.globvar
deriving instance DecidableEq for LClight.globdef

deriving instance Lean.ToExpr for LClight.typ
deriving instance Lean.ToExpr for LClight.xtype
deriving instance Lean.ToExpr for LClight.calling_convention
deriving instance Lean.ToExpr for LClight.signature
deriving instance Lean.ToExpr for LClight.memory_chunk
deriving instance Lean.ToExpr for LClight.external_function
deriving instance Lean.ToExpr for LClight.signedness
deriving instance Lean.ToExpr for LClight.intsize
deriving instance Lean.ToExpr for LClight.floatsize
deriving instance Lean.ToExpr for LClight.attr
deriving instance Lean.ToExpr for LClight.type
deriving instance Lean.ToExpr for LClight.unary_operation
deriving instance Lean.ToExpr for LClight.binary_operation
deriving instance Lean.ToExpr for LClight.expr
deriving instance Lean.ToExpr for LClight.statement, LClight.labeled_statements
deriving instance Lean.ToExpr for LClight.function
deriving instance Lean.ToExpr for LClight.fundef
deriving instance Lean.ToExpr for LClight.init_data
deriving instance Lean.ToExpr for LClight.globvar
deriving instance Lean.ToExpr for LClight.globdef

/-- CompCert's declarations with the identifiers that the whole program gives them:
`__builtin_fsqrt` takes `sqrtId`, and the `j`-th of the others `4 j + 5`. -/
def preOf : Defs → Nat → Defs
  | [], _ => []
  | (_, d) :: rest, j =>
      if d = sqrtDef then (sqrtId, d) :: preOf rest j
      else (4 * j + 5, d) :: preOf rest (j + 1)

/-! ## Maps from identifiers -/

/-- A map from numbers to identifiers: a binary trie on a number's bits from the lowest.  The
root holds the value of 0, and for `k ≥ 1` the subtrie `z` or `o` of `k`'s lowest bit holds the
value of `k / 2`.  The kernel finds a number's value in a number of steps in proportion to its
bits, where a list of pairs takes steps in proportion to the list's length.  The kernel reduces
terms lazily, so `insert` matches on the trie that each recursive call gives, and `build` on the
trie that it carries, which makes the kernel reduce each node once it is built: a trie built by
`List.foldr` would be a chain of insertions as long as the list, which the kernel reduces by a
recursion as deep. -/
inductive Trie where
  | nil
  | node (v : Option ident) (z o : Trie)

namespace Trie

def root : Trie → Option ident
  | nil => none
  | node v _ _ => v

def zero : Trie → Trie
  | nil => nil
  | node _ z _ => z

def one : Trie → Trie
  | nil => nil
  | node _ _ o => o

def find : Trie → Nat → Option ident
  | nil, _ => none
  | node v z o, k => if k = 0 then v else if k % 2 = 0 then z.find (k / 2) else o.find (k / 2)

/-- `node r z o`, after the reduction of `z`. -/
def nodeZ (r : Option ident) (z o : Trie) : Trie :=
  match z with
  | nil => node r nil o
  | node a b c => node r (node a b c) o

/-- `node r z o`, after the reduction of `o`. -/
def nodeO (r : Option ident) (z o : Trie) : Trie :=
  match o with
  | nil => node r z nil
  | node a b c => node r z (node a b c)

/-- `t` with the value `v` at `k`, for `k` at most `f`. -/
def insert (v : ident) : Nat → Trie → Nat → Trie
  | _, t, 0 => node (some v) t.zero t.one
  | 0, t, _ + 1 => t
  | f + 1, t, k + 1 =>
      if (k + 1) % 2 = 0 then nodeZ t.root (insert v f t.zero ((k + 1) / 2)) t.one
      else nodeO t.root t.zero (insert v f t.one ((k + 1) / 2))

/-- `t` with the value `v` at `k` unless `t` has a value at `k`. -/
def insertNew (v : ident) (k : Nat) (t : Trie) : Trie :=
  if (t.find k).isSome then t else insert v k t k

/-- `t` with the pairs `l` that `insertNew` adds in order. -/
def build : Trie → List (Nat × ident) → Trie
  | t, [] => t
  | nil, (k, v) :: l => build (insertNew v k nil) l
  | node a b c, (k, v) :: l => build (insertNew v k (node a b c)) l

/-- The map of the pairs `l`, the first pair of a number giving its value, as `List.lookup`. -/
def ofList (l : List (Nat × ident)) : Trie := build nil l

/-- Whether the numbers of `l` are distinct and have no value in `t`. -/
def fresh : Trie → List Nat → Bool
  | _, [] => true
  | t, x :: l => (t.find x).isNone && fresh (insert 0 x t x) l

theorem nodeZ_eq (r : Option ident) (z o : Trie) : nodeZ r z o = node r z o := by
  cases z <;> rfl

theorem nodeO_eq (r : Option ident) (z o : Trie) : nodeO r z o = node r z o := by
  cases o <;> rfl

theorem find_eq (t : Trie) (k : Nat) :
    t.find k = if k = 0 then t.root else if k % 2 = 0 then t.zero.find (k / 2)
      else t.one.find (k / 2) := by
  cases t <;> simp [find, root, zero, one]

theorem find_insert (v : ident) : ∀ (f : Nat) (t : Trie) (k k' : Nat), k ≤ f →
    (insert v f t k).find k' = if k' = k then some v else t.find k'
  | f, t, 0, k', _ => by
      rw [insert, find_eq t k']
      simp only [find]
      by_cases h : k' = 0 <;> simp [h]
  | 0, t, k + 1, k', h => absurd h (by omega)
  | f + 1, t, k + 1, k', h => by
      have hk : (k + 1) / 2 ≤ f := by omega
      rw [insert, find_eq t k', nodeZ_eq, nodeO_eq]
      by_cases he : (k + 1) % 2 = 0
      · simp only [he, ite_true, find, find_insert v f _ _ _ hk]
        by_cases h0 : k' = 0
        · simp [h0]
        · by_cases h2 : k' % 2 = 0
          · have : (k' / 2 = (k + 1) / 2) ↔ k' = k + 1 := by omega
            simp [h0, h2, this]
          · have : k' ≠ k + 1 := by omega
            simp [h0, h2, this]
      · simp only [he, ite_false, find, find_insert v f _ _ _ hk]
        by_cases h0 : k' = 0
        · simp [h0]
        · by_cases h2 : k' % 2 = 0
          · have : k' ≠ k + 1 := by omega
            simp [h0, h2, this]
          · have : (k' / 2 = (k + 1) / 2) ↔ k' = k + 1 := by omega
            simp [h0, h2, this]

theorem find_insertNew (v : ident) (k : Nat) (t : Trie) (k' : Nat) :
    (insertNew v k t).find k' = match t.find k' with
      | some w => some w
      | none => if k' = k then some v else none := by
  unfold insertNew
  by_cases hs : (t.find k).isSome
  · simp only [hs, ite_true]
    cases h : t.find k' with
    | some w => rfl
    | none =>
        by_cases e : k' = k
        · subst e
          simp [h] at hs
        · simp [e]
  · simp only [hs, Bool.false_eq_true, ite_false, find_insert v k t k k' (Nat.le_refl k)]
    have hn : t.find k = none := by
      cases h : t.find k with
      | none => rfl
      | some w => simp [h] at hs
    by_cases e : k' = k
    · subst e
      simp [hn]
    · cases t.find k' <;> simp [e]

theorem find_build : ∀ (t : Trie) (l : List (Nat × ident)) (k : Nat),
    (build t l).find k = match t.find k with
      | some w => some w
      | none => l.lookup k
  | t, [], k => by
      simp only [build]
      cases t.find k <;> rfl
  | t, (a, b) :: l, k => by
      have e : build t ((a, b) :: l) = build (insertNew b a t) l := by
        cases t <;> rfl
      rw [e, find_build _ l k, find_insertNew, List.lookup_cons]
      cases t.find k with
      | some w => rfl
      | none =>
          by_cases h : k = a
          · simp [h]
          · simp [h, beq_eq_false_iff_ne.mpr h]

theorem find_ofList (l : List (Nat × ident)) (k : Nat) : (ofList l).find k = l.lookup k := by
  rw [ofList, find_build]
  rfl

theorem nodup_of_fresh : ∀ (t : Trie) (l : List Nat), t.fresh l = true →
    l.Nodup ∧ ∀ x ∈ l, t.find x = none
  | _, [], _ => ⟨List.nodup_nil, fun _ h => by cases h⟩
  | t, x :: l, h => by
      simp only [fresh, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨hl, hf⟩ := nodup_of_fresh _ l h.2
      have hy : ∀ y ∈ l, y ≠ x ∧ t.find y = none := fun y hy => by
        have := hf y hy
        rw [find_insert 0 x t x y (Nat.le_refl x)] at this
        by_cases e : y = x
        · simp [e] at this
        · simp only [e, ite_false] at this
          exact ⟨e, this⟩
      refine ⟨List.nodup_cons.mpr ⟨fun hx => (hy x hx).1 rfl, hl⟩, fun y hy' => ?_⟩
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact h.1
      · exact (hy y hy').2

end Trie

/-- A key that `List.lookup` finds in the pairs of two lists is in the first list. -/
theorem mem_of_lookup_zip : ∀ {ks vs : List ident} {x y : ident},
    (ks.zip vs).lookup x = some y → x ∈ ks
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | k :: ks, v :: vs, x, y, h => by
      rw [List.zip_cons_cons, List.lookup_cons] at h
      by_cases e : x = k
      · exact e ▸ List.mem_cons_self ..
      · simp only [beq_eq_false_iff_ne.mpr e] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup_zip h)

/-! ## The comparison of definitions

The derived `DecidableEq` of statements and of lists reduces the equality of the rest of a
sequence or a list inside the reduction of the whole, so the kernel's recursion is as deep as the
sequence or the list, which a function of several thousand statements or declarations makes too
deep.  `stmtEq` compares the second statement of a sequence, a loop, or an `if` last, and
`defsEq` compares a function's parameters and temporaries by `listEq`, so that the kernel
compares along a sequence or a list by iteration. -/

/-- The equality of statements, comparing the second statement of a sequence, a loop, or an `if`
last. -/
def stmtEq (s s' : statement) : Bool :=
  match s, s' with
  | .Ssequence a b, .Ssequence c d => stmtEq a c && stmtEq b d
  | .Sloop a b, .Sloop c d => stmtEq a c && stmtEq b d
  | .Sifthenelse e a b, .Sifthenelse e' c d => (decide (e = e') && stmtEq a c) && stmtEq b d
  | _, _ => decide (s = s')

theorem stmtEq_eq (s s' : statement) (h : stmtEq s s' = true) : s = s' := by
  fun_induction stmtEq s s' with
  | case1 a b c d iha ihb =>
      simp only [Bool.and_eq_true] at h
      rw [iha h.1, ihb h.2]
  | case2 a b c d iha ihb =>
      simp only [Bool.and_eq_true] at h
      rw [iha h.1, ihb h.2]
  | case3 e a b e' c d iha ihb =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, iha h.1.2, ihb h.2]
  | case4 => exact of_decide_eq_true h

/-- The equality of lists, comparing the rest of a list last. -/
def listEq {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], [] => true
  | a :: l, b :: l' => decide (a = b) && listEq l l'
  | _, _ => false

theorem listEq_eq {α : Type} [DecidableEq α] : ∀ {l l' : List α}, listEq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
      simp only [listEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1, listEq_eq h.2]
  | [], _ :: _, h => by simp [listEq] at h
  | _ :: _, [], h => by simp [listEq] at h

/-- The equality of global definitions, comparing a function's parameters and temporaries by
`listEq` and its body by `stmtEq`. -/
def globdefEq (d d' : globdef (fundef function) type) : Bool :=
  match d, d' with
  | .Gfun (.Internal f), .Gfun (.Internal f') =>
      ((decide (f.fn_return = f'.fn_return ∧ f.fn_callconv = f'.fn_callconv ∧
          f.fn_vars = f'.fn_vars) && listEq f.fn_params f'.fn_params) &&
        listEq f.fn_temps f'.fn_temps) && stmtEq f.fn_body f'.fn_body
  | _, _ => decide (d = d')

theorem globdefEq_eq {d d' : globdef (fundef function) type} (h : globdefEq d d' = true) :
    d = d' := by
  unfold globdefEq at h
  split at h
  · rename_i f f'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩, h6⟩ := h
    obtain ⟨r, cc, ps, vs, ts, b⟩ := f
    obtain ⟨r', cc', ps', vs', ts', b'⟩ := f'
    have e1 : r = r' := h1
    have e2 : cc = cc' := h2
    have e3 : vs = vs' := h3
    have e4 : ps = ps' := listEq_eq h4
    have e5 : ts = ts' := listEq_eq h5
    have e6 : b = b' := stmtEq_eq _ _ h6
    subst e1 e2 e3 e4 e5 e6
    rfl
  · exact of_decide_eq_true h

/-- The equality of lists of definitions, comparing each definition by `globdefEq`. -/
def defsEq : Defs → Defs → Bool
  | [], [] => true
  | (x, d) :: l, (x', d') :: l' => (decide (x = x') && globdefEq d d') && defsEq l l'
  | _, _ => false

theorem defsEq_eq : ∀ {l l' : Defs}, defsEq l l' = true → l = l'
  | [], [], _ => rfl
  | (x, d) :: l, (x', d') :: l', h => by
      simp only [defsEq, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [h.1.1, globdefEq_eq h.1.2, defsEq_eq h.2]
  | [], _ :: _, h => by simp [defsEq] at h
  | _ :: _, [], h => by simp [defsEq] at h

/-- The pairs of the identifiers of the definitions `wd` and `fd`, by position. -/
def gPairs (wd fd : Defs) : List (ident × ident) := (wd.map (·.1)).zip (fd.map (·.1))

/-- The identifier in the definitions `fd` of each global of the definitions `wd`, by position. -/
def gOfL (wd fd : Defs) (x : ident) : ident := ((Trie.ofList (gPairs wd fd)).find x).getD x

/-- The pairs of the identifiers of the parameters and temporaries of the function `fid` of `wd`
and of its function in `fd`, by position. -/
def tempsZipL (wd fd : Defs) (fid : ident) : List (ident × ident) :=
  match wd.lookup fid, fd.lookup (gOfL wd fd fid) with
  | some (.Gfun (.Internal f)), some (.Gfun (.Internal f')) =>
      ((f.fn_params ++ f.fn_temps).map (·.1)).zip ((f'.fn_params ++ f'.fn_temps).map (·.1))
  | _, _ => []

/-- The identifier in `fd` of each temporary of the function `fid` of `wd`, by position. -/
def tOfL (wd fd : Defs) (fid x : ident) : ident :=
  ((Trie.ofList (tempsZipL wd fd fid)).find x).getD x

/-- The parameters and temporaries that the function `fid` of `wd` declares. -/
def declOfL (wd : Defs) (fid : ident) : List ident :=
  match wd.lookup fid with
  | some (.Gfun (.Internal f)) => (f.fn_params ++ f.fn_temps).map (·.1)
  | _ => []

theorem mem_ids_of_find {wd fd : Defs} {x y : ident}
    (h : (Trie.ofList (gPairs wd fd)).find x = some y) : x ∈ wd.map (·.1) := by
  rw [Trie.find_ofList] at h
  exact mem_of_lookup_zip h

theorem mem_declOfL_of_find {wd fd : Defs} {fid x y : ident}
    (h : (Trie.ofList (tempsZipL wd fd fid)).find x = some y) : x ∈ declOfL wd fid := by
  rw [Trie.find_ofList] at h
  unfold tempsZipL at h
  split at h
  · rename_i f _ hw _
    simp only [declOfL, hw]
    exact mem_of_lookup_zip h
  · simp at h

/-- A map whose images of the list `l` are distinct is injective on `l`. -/
theorem inj_of_nodup_map {f : ident → ident} :
    ∀ {l : List ident}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, _, hx, _, _, _ => by cases hx
  | a :: l, h, x, hx, y, hy, e => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd e.symm (h.1 y hy')
      · exact absurd e (h.1 x hx')
      · exact inj_of_nodup_map h.2 x hx' y hy' e

/-- The renaming of temporaries is injective on each function's temporaries when it is on the
declared ones of each identifier of the program. -/
theorem tinj_of {p : program function} {τ : ident → ident → ident}
    (hsub : ∀ id ∈ p.prog_defs.map (·.1), ∀ x ∈ tempsOf p.prog_defs id, x ∈ declOfL p.prog_defs id)
    (hnd : ∀ id ∈ p.prog_defs.map (·.1), ((declOfL p.prog_defs id).map (τ id)).Nodup) :
    ∀ id, ∀ x ∈ tempsOf p.prog_defs id, ∀ y ∈ tempsOf p.prog_defs id,
      τ id x = τ id y → x = y := by
  intro id
  by_cases hid : id ∈ p.prog_defs.map (·.1)
  · exact fun x hx y hy e => inj_of_nodup_map (hnd id hid) x (hsub id hid x hx) y
      (hsub id hid y hy) e
  · have : tempsOf p.prog_defs id = [] := by
      simp only [tempsOf, List.flatMap_eq_nil_iff, List.mem_filter, beq_iff_eq, and_imp]
      intro d hd e
      exact absurd (e ▸ List.mem_map_of_mem (f := (·.1)) hd) hid
    simp [this]

/-- The declarations of `pre` that `PrefixOk` requires to be functions. -/
theorem prefix_of {pre : Defs} (hsq : (sqrtId, sqrtDef) ∈ pre)
    (hf : pre.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true)
    (hnd : (pre.map (·.1)).Nodup)
    (hids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1)) : PrefixOk pre := by
  refine ⟨hsq, fun d hd => ?_, hnd, hids⟩
  have := List.all_eq_true.mp hf d hd
  match d, this with
  | (_, .Gfun f), _ => exact ⟨f, rfl⟩
  | (_, .Gvar _), h => simp at h

/-! ## The functions that `main` reaches -/

/-- The functions that the statement `s` calls by name. -/
def callsOf : statement → List ident
  | .Scall _ (.Evar x _) _ => [x]
  | .Ssequence s1 s2 | .Sloop s1 s2 | .Sifthenelse _ s1 s2 => callsOf s1 ++ callsOf s2
  | _ => []

/-- The internal functions of `defs` that the functions `todo` reach by calls, added to `seen`,
in at most `fuel` steps. -/
def reachFrom (defs : Defs) : Nat → List ident → List ident → List ident
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, x :: todo, seen =>
      if seen.contains x then reachFrom defs fuel todo seen
      else match defs.lookup x with
        | some (.Gfun (.Internal f)) => reachFrom defs fuel (callsOf f.fn_body ++ todo) (x :: seen)
        | _ => reachFrom defs fuel todo seen

/-- The internal functions of `defs` that `main` reaches by calls, `main` among them: the list of
functions that `progOk` takes for a program whose other functions N need not cover. -/
def reach (defs : Defs) (main : ident) : List ident := reachFrom defs 1048576 [main] []

/-! ## The kernel's check of an instance -/

/-- CompCert's declarations among the file's definitions `fd`, for the whole program of the
translation `T` with the definitions `post` after the translation's: the definitions before the
translation's, of which the whole program leaves out `__builtin_fsqrt`, with the whole program's
identifiers. -/
def preIn (fd : Defs) (T : Translation) (post : Defs) : Defs :=
  preOf (fd.take (fd.length - T.cprogram.prog_defs.length - (post.length - 1))) 0

/-- The whole program of `T` and `post` with CompCert's declarations among `fd`. -/
def wholeOf (post : Defs) (T : Translation) (fd : Defs) : program function :=
  wholeProgram (preIn fd T post) post T

/-- The file's program of the definitions `fd` and `main` `fm`. -/
def fileProgram (fd : Defs) (fm : ident) : program function :=
  { prog_defs := fd, prog_public := [], prog_main := fm }

/-- Renaming the program `w` by position gives the definitions `fd` and `main` `fm`, every global
that occurs in `w` is a definition, the renaming of the definitions has no repetitions, and the
temporaries of each function are among those it declares, whose renaming has no repetitions.
The tests of membership find a number in a trie, and those of repetitions insert the numbers
into a trie, so that the kernel's work grows with the occurrences and the number of their bits.
The conditions over long lists are `List.all`, and the comparison is `defsEq`, along which the
kernel iterates. -/
def RenameOk (w : program function) (fd : Defs) (fm : ident) : Prop :=
  defsEq fd (renDefs (gOfL w.prog_defs fd) (tOfL w.prog_defs fd) w.prog_defs) = true ∧
    fm = gOfL w.prog_defs fd w.prog_main ∧
    (progG w).all (fun x => ((Trie.ofList (gPairs w.prog_defs fd)).find x).isSome) = true ∧
    Trie.nil.fresh ((w.prog_defs.map (·.1)).map (gOfL w.prog_defs fd)) = true ∧
    (w.prog_defs.map (·.1)).all (fun id => (tempsOf w.prog_defs id).all fun x =>
      ((Trie.ofList (tempsZipL w.prog_defs fd id)).find x).isSome) = true ∧
    (w.prog_defs.map (·.1)).all (fun id =>
      Trie.nil.fresh ((declOfL w.prog_defs id).map (tOfL w.prog_defs fd id))) = true

/-- The conditions of `PrefixOk`, each decidable. -/
def PreOk (pre : Defs) : Prop :=
  (sqrtId, sqrtDef) ∈ pre ∧
    pre.all (fun d => match d.2 with | .Gfun _ => true | .Gvar _ => false) = true ∧
    (pre.map (·.1)).Nodup ∧ ∀ x ∈ pre.map (·.1), x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1)

/-- What the kernel checks of an instance: the renaming from the whole program to the file's,
the conditions of `PrefixOk` on CompCert's declarations, and `progOk` of the file's program with
the functions that `main` reaches.  Each condition is decidable, and `inst_ok` proves them. -/
def InstOk (post : Defs) (T : Translation) (fd : Defs) (fm : ident) : Prop :=
  RenameOk (wholeOf post T fd) fd fm ∧ PreOk (preIn fd T post) ∧ progOk fd fm (reach fd fm) = true

/-- What the kernel checks of a bare-metal instance whose output has the bytes `bs`: `InstOk`,
and that the renaming of the whole program takes the trace of `bs` to the file's trace `ft`. -/
def BareOk (main : function) (T : Translation) (fd : Defs) (fm : ident) (bs : List UInt8)
    (ft : trace) : Prop :=
  InstOk (bareTail main) T fd fm ∧
    renTrace (gOfL (wholeOf (bareTail main) T fd).prog_defs fd) (outTrace bs) = ft

/-! ## The translation's definitions in parts

`verified_compile` defines a program's translation `p.translation` as `translate cap m` of the
module `m`, and the module as `compileWith` of the program, so a condition of `InstOk` on the
translation's definitions makes the kernel compile the module and translate it, and a condition
in a declaration of its own repeats that work.  `inst_ok` evaluates the translation by compiled
code and adds its definitions as literals in parts: `pre`, the definitions before the functions,
the body of each function, and the body of `lx_init`.  The kernel checks each function's part,
`trFunOk`, in a declaration of its own, which compiles and translates that function alone, and
the rest, `trRestOk`, in one more.  `defs_of_parts` joins the parts by `translate_defs`, with the
theorems `p.translation_eq` and `p.translation_funcs` of `verified_compile`, which give the
guards of `translate` and its list of functions.  `InstOk.of_defs` then states the conditions of
`InstOk` on the translation `withDefs T D` with the literal definitions `D`, which the kernel
reads without computing the translation. -/

/-- The translation `T` with the definitions `D`. -/
def withDefs (T : Translation) (D : Defs) : Translation :=
  { T with cprogram := { T.cprogram with prog_defs := D } }

theorem InstOk.of_defs (post : Defs) (T : Translation) (fd : Defs) (fm : ident) (D : Defs)
    (hD : T.cprogram.prog_defs = D) (h : InstOk post (withDefs T D) fd fm) :
    InstOk post T fd fm := by
  subst hD
  exact h

theorem BareOk.of_defs (main : function) (T : Translation) (fd : Defs) (fm : ident)
    (bs : List UInt8) (ft : trace) (D : Defs) (hD : T.cprogram.prog_defs = D)
    (h : BareOk main (withDefs T D) fd fm bs ft) : BareOk main T fd fm bs ft := by
  subst hD
  exact h

/-- The function `k` of `m` translates to the function `f`. -/
def trFunOk (cap : Nat) (m : Wasm.Module) (k : Nat) (f : function) : Bool :=
  match (fdefsOf cap m)[k]?.join with
  | some g => globdefEq (.Gfun (.Internal g)) (.Gfun (.Internal f))
  | none => false

theorem funDef_of_trFunOk {cap : Nat} {m : Wasm.Module} {k : Nat} {f : function}
    (h : trFunOk cap m k f = true) : funDef cap m k = some (funId k, .Gfun (.Internal f)) := by
  unfold trFunOk at h
  split at h
  · rename_i g hg
    cases globdefEq_eq h
    simp [funDef, hg]
  · cases h

/-- `trFunOk` of each function of `ks` and its body in `fs`. -/
def TrFunsOk (cap : Nat) (m : Wasm.Module) : List Nat → List function → Prop
  | [], [] => True
  | k :: ks, f :: fs => trFunOk cap m k f = true ∧ TrFunsOk cap m ks fs
  | _, _ => False

theorem TrFunsOk.nil (cap : Nat) (m : Wasm.Module) : TrFunsOk cap m [] [] := trivial

theorem TrFunsOk.cons (cap : Nat) (m : Wasm.Module) (k : Nat) (ks : List Nat) (f : function)
    (fs : List function) (h : trFunOk cap m k f = true) (hs : TrFunsOk cap m ks fs) :
    TrFunsOk cap m (k :: ks) (f :: fs) := And.intro h hs

/-- The definitions of the functions `ks` with the bodies `fs`. -/
def funsOf : List Nat → List function → Defs
  | k :: ks, f :: fs => (funId k, .Gfun (.Internal f)) :: funsOf ks fs
  | _, _ => []

theorem mapM_funDef {cap : Nat} {m : Wasm.Module} :
    ∀ {ks : List Nat} {fs : List function}, TrFunsOk cap m ks fs →
      ks.mapM (funDef cap m) = some (funsOf ks fs)
  | [], [], _ => rfl
  | k :: ks, f :: fs, h => by
      have h' : trFunOk cap m k f = true ∧ TrFunsOk cap m ks fs := h
      simp [List.mapM_cons, funDef_of_trFunOk h'.1, mapM_funDef h'.2, funsOf]
  | [], _ :: _, h => by simp [TrFunsOk] at h
  | _ :: _, [], h => by simp [TrFunsOk] at h

/-- The definitions of a translation before its functions. -/
def preDefs (cap : Nat) (decl : Wasm.MemDecl) (gdefs : List (globvar type)) (nres : Nat) : Defs :=
  (statusId, .Gvar statusVar) ::
    (gdefs.zipIdx.map (fun x => (globalId x.2, globdef.Gvar x.1)) ++
      (pagesId, .Gvar (pagesDef decl.pagesMin.toNat)) :: (memId, .Gvar (memDef cap)) ::
        (punId, .Gvar punDef) :: (sqrtId, sqrtDef) :: resDefs nres)

theorem progDefs_eq (cap : Nat) (decl : Wasm.MemDecl) (gdefs : List (globvar type)) (nres : Nat)
    (funs : Defs) : progDefs cap decl gdefs nres funs =
      preDefs cap decl gdefs nres ++
        (funs ++ [(initId, .Gfun (.Internal (initFunction cap decl.data)))]) := by
  simp [progDefs, preDefs]

/-- The translation of `m` with the functions `ks` has the definitions `pre` before its functions
and `lx_init` with the body `init` after them. -/
def trRestOk (cap : Nat) (m : Wasm.Module) (ks : List Nat) (pre : Defs) (init : function) : Bool :=
  match m.memory, m.globals.mapM globalDef with
  | some decl, some gdefs =>
      defsEq (preDefs cap decl gdefs (maxResults m ks)) pre &&
        globdefEq (.Gfun (.Internal (initFunction cap decl.data))) (.Gfun (.Internal init))
  | _, _ => false

theorem funcs_of_translate {cap : Nat} {m : Wasm.Module} {T : Translation}
    (h : translate cap m = some T) : T.funcs = includedOf cap m := by
  simp [translate, Option.bind_eq_some_iff] at h
  obtain ⟨-, decl, -, -, gdefs, -, -, funs, -, rfl⟩ := h
  rfl

/-- The definitions of the translation `T` of `m` from its parts. -/
theorem defs_of_parts (cap : Nat) (m : Wasm.Module) (T : Translation) (ks : List Nat) (pre : Defs)
    (fs : List function) (init : function) (hT : translate cap m = some T)
    (hks : (translate cap m).map Translation.funcs = some ks)
    (hr : trRestOk cap m ks pre init = true) (hf : TrFunsOk cap m ks fs) :
    T.cprogram.prog_defs = pre ++ (funsOf ks fs ++ [(initId, .Gfun (.Internal init))]) := by
  obtain ⟨decl, gdefs, funs, hd, -, -, -, hg, hfuns, he⟩ := translate_defs hT
  have hk : T.funcs = ks := translate_funcs_eq hT hks
  rw [← funcs_of_translate hT, hk, mapM_funDef hf, Option.some.injEq] at hfuns
  subst hfuns
  simp only [trRestOk, hd, hg, Bool.and_eq_true] at hr
  rw [he, translate_nres hT, hk, progDefs_eq, defsEq_eq hr.1]
  cases globdefEq_eq hr.2
  rfl

section Tactic

open Lean Meta Elab Tactic

unsafe def evalTranslateUnsafe (e : Expr) : MetaM (Option Translation) :=
  evalExpr (Option Translation) (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Translation)) e
    (checkMeta := false)

/-- The value of the term `e` of type `Option Translation`, by compiled code. -/
@[implemented_by evalTranslateUnsafe]
opaque evalTranslate (e : Expr) : MetaM (Option Translation)

/-- Adds the definition `name : type := value`, which the kernel checks before `inst_ok` goes
on. -/
def addLiteralDef (name : Name) (type value : Expr) : MetaM Unit :=
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl (mkDefinitionValEx name [] type value .abbrev .safe [name]))

/-- Adds the theorem `name : prop`, which the kernel proves by evaluating `decide prop` before
`inst_ok` goes on, and returns it. -/
def addByKernel (name : Name) (prop : Expr) : MetaM Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Decidable) prop)
  let pf := mkApp3 (mkConst ``of_decide_eq_true) prop inst
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type := prop, value := pf })
  return mkConst name

/-- Proves `InstOk post T fd fm` or `BareOk main T fd fm bs ft` for the translation
`T := p.translation` of `verified_compile`.  The tactic evaluates `translate cap m` of
`p.translation_eq` by compiled code, adds the parts of its definitions as literals under an
auxiliary name, has the kernel check each part in a declaration of its own, and states the
conditions of the goal on `withDefs T D` with the joined literal definitions `D`.  The kernel
proves each condition by evaluation in a declaration of its own, so that it holds the terms of
one condition at a time.  The kernel counts these evaluations against `maxHeartbeats`, and when
one exceeds it, `decide` reports that the instance did not reduce, so the instances raise the
limit. -/
elab "inst_ok" : tactic => do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  unless type.isAppOfArity ``InstOk 4 || type.isAppOfArity ``BareOk 6 do
    throwError "inst_ok: the goal is neither InstOk nor BareOk{indentExpr type}"
  let T := type.getArg! 1
  let .const tc [] := T | throwError "inst_ok: the translation {T} is not a constant"
  let hT := mkConst (tc.getPrefix ++ `translation_eq)
  let hks := mkConst (tc.getPrefix ++ `translation_funcs)
  let some (_, lhs, _) := (← inferType hT).eq? | throwError "inst_ok: the type of {hT}"
  unless lhs.isAppOfArity ``translate 3 && (lhs.getArg! 2).isConstOf ``Bool.false do
    throwError "inst_ok: {hT} is not about translate with the test of alignment"
  let cap := lhs.getArg! 0
  let m := lhs.getArg! 1
  let some (_, _, rhs) := (← inferType hks).eq? | throwError "inst_ok: the type of {hks}"
  unless rhs.isAppOfArity ``Option.some 2 do throwError "inst_ok: the type of {hks}"
  let ks := rhs.getArg! 1
  let some t ← evalTranslate lhs | throwError "inst_ok: {lhs} is none"
  let defs := t.cprogram.prog_defs
  let n := t.funcs.length
  let nPre := defs.length - n - 1
  let fs ← ((defs.drop nPre).take n).mapM fun
    | (_, .Gfun (.Internal f)) => pure f
    | _ => throwError "inst_ok: the definitions of {lhs} do not end with its functions"
  let some (_, .Gfun (.Internal init)) := defs.getLast?
    | throwError "inst_ok: the definitions of {lhs} do not end with lx_init"
  let base ← mkAuxDeclName `_inst
  let funTy := mkConst ``LClight.function
  let preC := mkConst (base ++ `pre)
  addLiteralDef (base ++ `pre) (mkConst ``Defs) (toExpr (defs.take nPre))
  let initC := mkConst (base ++ `init)
  addLiteralDef (base ++ `init) funTy (toExpr init)
  let hr ← addByKernel (base ++ `rest)
    (← mkEq (mkApp5 (mkConst ``trRestOk) cap m ks preC initC) (mkConst ``Bool.true))
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for (k, f) in t.funcs.zip fs do
    let fC := mkConst (base ++ Name.mkSimple s!"fun_{k}")
    addLiteralDef (base ++ Name.mkSimple s!"fun_{k}") funTy (toExpr f)
    let kE := toExpr k
    let h ← addByKernel (base ++ Name.mkSimple s!"fun_{k}_ok")
      (← mkEq (mkApp4 (mkConst ``trFunOk) cap m kE fC) (mkConst ``Bool.true))
    parts := parts.push (kE, fC, h)
  let natTy := mkConst ``Nat
  let (ksE, fsE, hf) := parts.foldr (init :=
      (mkApp (mkConst ``List.nil [Level.zero]) natTy, mkApp (mkConst ``List.nil [Level.zero]) funTy,
        mkApp2 (mkConst ``TrFunsOk.nil) cap m))
    fun (kE, fC, h) (ksE, fsE, hf) =>
      (mkApp3 (mkConst ``List.cons [Level.zero]) natTy kE ksE,
        mkApp3 (mkConst ``List.cons [Level.zero]) funTy fC fsE,
        mkAppN (mkConst ``TrFunsOk.cons) #[cap, m, kE, ksE, fC, fsE, h, hf])
  unless ← isDefEq ksE ks do
    throwError "inst_ok: {lhs} gives the functions {ksE}, and {hks} states {ks}"
  let hD := mkAppN (mkConst ``defs_of_parts) #[cap, m, T, ks, preC, fsE, initC, hT, hks, hr, hf]
  let some (_, _, D) := (← inferType hD).eq? | throwError "inst_ok: the type of defs_of_parts"
  let args := type.getAppArgs
  if type.isAppOfArity ``InstOk 4 then
    replaceMainGoal (← goal.apply (mkAppN (mkConst ``InstOk.of_defs) (args.push D |>.push hD)))
    evalTactic (← `(tactic| (
      unfold ClightN.Proof.InstOk ClightN.Proof.RenameOk ClightN.Proof.PreOk
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> decide +kernel)))
  else
    replaceMainGoal (← goal.apply (mkAppN (mkConst ``BareOk.of_defs) (args.push D |>.push hD)))
    evalTactic (← `(tactic| (
      unfold ClightN.Proof.BareOk ClightN.Proof.InstOk ClightN.Proof.RenameOk ClightN.Proof.PreOk
      refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;> decide +kernel)))

end Tactic

section

variable {post : Defs} {T : Translation} {fd : Defs} {fm : ident}

theorem InstOk.inj (h : InstOk post T fd fm) :
    ∀ x ∈ progG (wholeOf post T fd), ∀ y ∈ progG (wholeOf post T fd),
      gOfL (wholeOf post T fd).prog_defs fd x = gOfL (wholeOf post T fd).prog_defs fd y → x = y :=
  have hs : ∀ x ∈ progG (wholeOf post T fd), x ∈ (wholeOf post T fd).prog_defs.map (·.1) :=
    fun x hx => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h.1.2.2.1 x hx)
      exact mem_ids_of_find hy
  fun x hx y hy e =>
    inj_of_nodup_map (Trie.nodup_of_fresh _ _ h.1.2.2.2.1).1 x (hs x hx) y (hs y hy) e

theorem InstOk.tinj (h : InstOk post T fd fm) :
    ∀ id, ∀ x ∈ tempsOf (wholeOf post T fd).prog_defs id,
      ∀ y ∈ tempsOf (wholeOf post T fd).prog_defs id,
        tOfL (wholeOf post T fd).prog_defs fd id x = tOfL (wholeOf post T fd).prog_defs fd id y →
          x = y :=
  tinj_of (fun id hid x hx => by
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
        (List.all_eq_true.mp (List.all_eq_true.mp h.1.2.2.2.2.1 id hid) x hx)
      exact mem_declOfL_of_find hy)
    fun id hid => (Trie.nodup_of_fresh _ _ (List.all_eq_true.mp h.1.2.2.2.2.2 id hid)).1

theorem InstOk.defs_eq (h : InstOk post T fd fm) :
    fd = renDefs (gOfL (wholeOf post T fd).prog_defs fd) (tOfL (wholeOf post T fd).prog_defs fd)
      (wholeOf post T fd).prog_defs :=
  defsEq_eq h.1.1

theorem InstOk.prefix (h : InstOk post T fd fm) : PrefixOk (preIn fd T post) :=
  prefix_of h.2.1.1 h.2.1.2.1 h.2.1.2.2.1 h.2.1.2.2.2

/-- A termination of the whole program is one of the file's program in N, with the trace renamed
by a map that agrees with the renaming by position on the program's globals. -/
theorem terminates_n (hok : InstOk post T fd fm) {t : trace} {r : int}
    (h : bigstep_program_terminates Archi.aarch64 ExtSem.none (wholeOf post T fd) t r) :
    ∃ g : ident → ident,
      (∀ x ∈ progG (wholeOf post T fd), g x = gOfL (wholeOf post T fd).prog_defs fd x) ∧
        nprog fd fm (renTrace g t) r := by
  obtain ⟨g, hg, hp⟩ := bigstep_program_terminates_rename_on (p' := fileProgram fd fm) hok.inj
    hok.tinj hok.defs_eq hok.1.2.1 h ExtSem.none
  exact ⟨g, hg, program_to_n (p := fileProgram fd fm) (reach fd fm) hok.2.2 hp⟩

end

theorem outId_mem (pre : Defs) (T : Translation) (main : function) :
    outId ∈ progG (bareProgram pre T main) :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(outId, .Gvar outVar),
    List.mem_append_right _ (List.mem_cons_self ..), List.mem_cons_self ..⟩)

theorem renTrace_outTrace {g g' : ident → ident} (h : g outId = g' outId) (bs : List UInt8) :
    renTrace g (outTrace bs) = renTrace g' (outTrace bs) := by
  simp only [renTrace, outTrace, List.map_map, Function.comp_def, renEvent, renEventval, h]

/-- The theorem of a bare-metal program that `bare_program` states is the file's in N: the
program terminates with the trace `ft` of the file's identifiers for the output bytes `bs` and
the result 0, or, when the entry may abort, with no event and the code of `unreachable`. -/
theorem bare_n {T : Translation} {main : function} {fd : Defs} {fm : ident} {bs : List UInt8}
    {aborts : Bool} {ft : trace} (hok : BareOk main T fd fm bs ft)
    (h : ∀ pre, PrefixOk pre →
      bigstep_program_terminates Archi.aarch64 ExtSem.none (bareProgram pre T main) (outTrace bs)
          0 ∨
        (aborts = true ∧ bigstep_program_terminates Archi.aarch64 ExtSem.none
          (bareProgram pre T main) E0 (UInt32.ofNat trapUnreachable))) :
    nprog fd fm ft 0 ∨ (aborts = true ∧ nprog fd fm [] (UInt32.ofNat trapUnreachable)) := by
  rcases h _ hok.1.prefix with hp | ⟨ha, hp⟩
  · obtain ⟨g, hg, hn⟩ := terminates_n hok.1 hp
    rw [renTrace_outTrace (hg outId (outId_mem ..)), hok.2] at hn
    exact .inl hn
  · obtain ⟨g, -, hn⟩ := terminates_n hok.1 hp
    exact .inr ⟨ha, hn⟩

/-- The terminations of a program with input whose traces read every sequence `σ` are the file's
in N, with traces that satisfy `nreads σ 0`. -/
theorem reads_n {post : Defs} {T : Translation} {fd : Defs} {fm : ident}
    (hok : InstOk post T fd fm)
    (h : ∀ pre, PrefixOk pre → ∀ σ : Nat → int, ∃ t r,
      bigstep_program_terminates Archi.aarch64 ExtSem.none (wholeProgram pre post T) t r ∧
        Reads σ t) :
    ∀ σ : Nat → UInt32, ∃ t r, nprog fd fm t r ∧ nreads σ Nat.zero t := by
  intro σ
  obtain ⟨t, r, hp, hr⟩ := h _ hok.prefix σ
  obtain ⟨g, -, hn⟩ := terminates_n hok hp
  exact ⟨renTrace g t, r, hn, nreads_ren g (reads_nreads hr (events_ren g (nprog_events hn)))⟩

/-- Each window of a `main` that runs forever in N holds only volatile loads and stores. -/
theorem nreacts_events {defs : Defs} {main : ident} {t0 : trace} {W : Nat → trace}
    (h : nreacts defs main t0 W) (n : Nat) : (W n).all isLS = true := by
  match h with
  | .nr_intro _ _ _ _ _ _ _ _ _ _ _ _ inv _ _ _ _ _ h0 hs =>
      have hinv : ∀ k, ∃ le gv mb, inv k le gv mb := by
        intro k
        induction k with
        | zero =>
            obtain ⟨le, gv, mb, -, hi⟩ := h0
            exact ⟨le, gv, mb, hi⟩
        | succ k ih =>
            obtain ⟨le, gv, mb, hi⟩ := ih
            obtain ⟨le2, gv2, mb2, -, hi2⟩ := hs k le gv mb hi
            exact ⟨le2, gv2, mb2, hi2⟩
      obtain ⟨le, gv, mb, hi⟩ := hinv n
      obtain ⟨_, _, _, hx, -⟩ := hs n le gv mb hi
      exact nexec_events hx

theorem windows_ls {W : Nat → trace} (h : ∀ n, (W n).all isLS = true) :
    ∀ n, (LeanExe.Requests.windows W n).all isLS = true
  | 0 => rfl
  | n + 1 => by
      simp only [LeanExe.Requests.windows, List.all_append, windows_ls h n, h n, Bool.and_self]

/-- The runs of a whole program whose `main` runs forever, for every sequence `σ` of the values
that its volatile loads read, with no event before the loop and the windows `W σ`, are the file's
in N: there are windows `W'` and the traces `P σ n` of their first `n` such that for every `σ`,
N's `nreacts` holds with the windows `W' σ`, and `P σ n` reads `σ`. -/
theorem reacts_n {post : Defs} {T : Translation} {fd : Defs} {fm : ident}
    (hok : InstOk post T fd fm) {W : (Nat → int) → Nat → trace}
    (h : ∀ pre, PrefixOk pre → ∀ σ,
      LoopReacts Archi.aarch64 ExtSem.none (wholeProgram pre post T) E0 (W σ))
    (hr : ∀ σ n, Reads σ (E0 ++ LeanExe.Requests.windows (W σ) n)) :
    ∃ W' P : (Nat → UInt32) → Nat → List event, ∀ σ : Nat → UInt32,
      nreacts fd fm [] (W' σ) ∧ P σ Nat.zero = [] ∧
        (∀ n, P σ (Nat.succ n) = ClightN.Base.app (P σ n) (W' σ n)) ∧
        ∀ n, nreads σ Nat.zero (P σ n) := by
  obtain ⟨g, τ, hinj, hτ, heq, hsame⟩ := exists_injective_renaming hok.inj hok.tinj
  have hx : ∀ σ, nreacts fd fm [] (fun n => renTrace g (W σ n)) := fun σ =>
    reacts_to_n (p := fileProgram fd fm) (reach fd fm) hok.2.2
      (loopReacts_rename (p := wholeOf post T fd) hinj hτ (ExtRen.none g ExtSem.none)
        (hok.defs_eq.trans hsame.symm) (hok.1.2.1.trans (heq _ (List.mem_cons_self ..)).symm)
        (h _ hok.prefix σ))
  refine ⟨fun σ n => renTrace g (W σ n), fun σ n => renTrace g (LeanExe.Requests.windows (W σ) n),
    fun σ => ⟨hx σ, rfl, fun n => ?_, fun n => ?_⟩⟩
  · simp only [LeanExe.Requests.windows, renTrace_append, ClightN.Base.app]
  · have hr' := hr σ n
    simp only [E0, List.nil_append] at hr'
    exact nreads_ren g (reads_nreads hr'
      (windows_ls (fun k => events_ren g (nreacts_events (hx σ) k)) n))

end ClightN.Proof
