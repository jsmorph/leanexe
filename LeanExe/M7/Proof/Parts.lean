import LeanExe.M7.Parts
import LeanExe.M7.Proof.Boot

/-!
The checks of `LeanExe/M7/Parts.lean` give the generator's program and its bytes.  `slice_append`
joins the bytes of two adjacent slices of a number, and `genFunctions_slices` joins the parts of
the functions, from each function's code at its entry and the sizes `ns`, into the code that
`genFunctions` returns.  With the sizes, `entriesFrom` and `endOf` give the layout that the parts
assume, and the table's numbers of parameters and results are those of the functions.
`genProgram_parts` concludes, for a program whose functions do not access the area, that
`genProgram` succeeds with code whose bytes are a slice of the number, and `fileOk_parts` and `bootFileOk_parts` give the checks of a file that the theorems over
an image take.
-/

namespace LeanExe.M7

open Wasm LeanExe.CallGraph LeanExe.FileNat

/-! ## Bytes -/

theorem natOfBytes_append : ∀ l1 l2 : List UInt8,
    natOfBytes (l1 ++ l2) = natOfBytes l1 + 256 ^ l1.length * natOfBytes l2
  | [], l2 => by simp [natOfBytes]
  | b :: l1, l2 => by
      simp only [List.cons_append, natOfBytes, List.length_cons]
      rw [natOfBytes_append l1 l2, Nat.pow_succ, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc,
        Nat.mul_comm 256 (256 ^ l1.length)]

/-- The bytes of `l1 ++ l2` are those of the number `n` from byte `o` when the bytes of `l1` are
those from `o` and the bytes of `l2` those that follow. -/
theorem slice_append {l1 l2 : List UInt8} {n o : Nat}
    (h1 : natOfBytes l1 = n / 256 ^ o % 256 ^ l1.length)
    (h2 : natOfBytes l2 = n / 256 ^ (o + l1.length) % 256 ^ l2.length) :
    natOfBytes (l1 ++ l2) = n / 256 ^ o % 256 ^ (l1 ++ l2).length := by
  rw [List.length_append, natOfBytes_append, h1, h2, Nat.pow_add 256 l1.length l2.length,
    Nat.mod_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem imageBytes_append (a b : List Instr) :
    imageBytes (a ++ b) = imageBytes a ++ imageBytes b := by
  simp [imageBytes, List.flatMap_append]

/-- Code takes two bytes for each halfword. -/
theorem length_imageBytes : ∀ is : List Instr, (imageBytes is).length = 2 * halfwordsOf is
  | [] => rfl
  | i :: is => by
      have he := length_encode i
      rw [size_halfwords] at he
      have hi : imageBytes (i :: is) = (encode i).flatMap halfBytes ++ imageBytes is := by
        simp [imageBytes]
      rw [hi, List.length_append, length_halfBytes, length_imageBytes is]
      simp only [halfwordsOf, List.map_cons, List.sum_cons]
      omega

theorem sliceOk_ok {g : GenM (List Instr)} {n off len : Nat} (h : sliceOk g n off len = true) :
    ∃ is, g = .ok is ∧ (imageBytes is).length = len ∧
      natOfBytes (imageBytes is) = n / 256 ^ off % 256 ^ len := by
  unfold sliceOk at h
  split at h
  · rename_i is
    simp only [Bool.and_eq_true, beq_iff_eq, natOfBytesPaired_eq] at h
    exact ⟨is, rfl, h.1, h.2⟩
  · cases h

/-! ## The layout from the sizes -/

theorem find_entriesOfSizes (j : Nat) : ∀ (a : UInt32) (fs : List (Nat × Function))
    (ns : List Nat), ns.length = fs.length →
    ((entriesOfSizes a fs ns).find? (·.1 = j)).map (fun x => (x.2.2.1.length, x.2.2.2.length)) =
      (fs.find? (·.1 = j)).map (fun x => (x.2.params.length, x.2.results.length))
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => by simp at h
  | a, (j', f) :: rest, _ :: ns, h => by
      by_cases hj : j' = j
      · simp [entriesOfSizes, hj]
      · simp only [entriesOfSizes, List.find?_cons, hj, decide_false]
        exact find_entriesOfSizes j _ rest ns (by simpa using h)

/-- The table of the layout from the sizes gives the numbers of parameters and results of the
functions. -/
theorem sigOf_tableOf_sizes (targets : List Nat) (a : UInt32) (fs : List (Nat × Function))
    (ns : List Nat) (h : ns.length = fs.length) :
    sigOf (tableOf targets (entriesOfSizes a fs ns)) = sigIn targets fs := by
  funext j
  simp only [sigOf, tableOf, sigIn]
  split
  · rw [Option.map_map]
    exact find_entriesOfSizes j a fs ns h
  · rfl

/-- With the functions' sizes, `entriesFrom` and `endOf` give the layout from the sizes. -/
theorem entriesFrom_sizes (sig : Nat → Option (Nat × Nat)) :
    ∀ (a : UInt32) (fs : List (Nat × Function)) (ns : List Nat),
      fs.map (fun x => functionSize sig x.2) = ns →
      entriesFrom sig a fs = entriesOfSizes a fs ns ∧ endOf sig a fs = after a ns.sum
  | a, [], ns, h => by
      subst h
      exact ⟨rfl, by rw [after_eq]; simp [endOf]⟩
  | a, (j, f) :: rest, ns, h => by
      subst h
      obtain ⟨h1, h2⟩ := entriesFrom_sizes sig (after a (functionSize sig f)) rest _ rfl
      simp only [entriesFrom, endOf, entriesOfSizes, List.map_cons, List.sum_cons]
      rw [h1, h2, after_after]
      exact ⟨rfl, rfl⟩

/-! ## The functions -/

/-- The code of the functions `fs` that `genFunctions` lays out from `a` with the sizes `ns` has
the bytes of `n` from byte `o` when each function's size is its entry of `ns` and its code at its
entry has the bytes that follow those of the functions before it. -/
theorem genFunctions_slices {callee : Table} {S : Shared} {n : Nat} :
    ∀ (fs : List (Nat × Function)) (ns : List Nat) (a : UInt32) (o : Nat),
      ns.length = fs.length →
      (∀ i (h1 : i < fs.length) (h2 : i < ns.length),
        functionSize (sigOf callee) fs[i].2 = ns[i] ∧
        sliceOk (genFunction callee S (after a (ns.take i).sum) fs[i].2) n
          (o + 4 * (ns.take i).sum) (4 * ns[i]) = true) →
      ∃ fns, genFunctions callee S a fs = .ok fns ∧ (imageBytes fns).length = 4 * ns.sum ∧
        natOfBytes (imageBytes fns) = n / 256 ^ o % 256 ^ (4 * ns.sum)
  | [], ns, a, o, hl, _ => by
      have : ns = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      exact ⟨[], rfl, rfl, by
        rw [show 4 * ([] : List Nat).sum = 0 from rfl, Nat.pow_zero, Nat.mod_one]; rfl⟩
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (j, f) :: rest, s :: ns, a, o, hl, h => by
      obtain ⟨hs, h0⟩ := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero, List.take_zero, List.sum_nil, Nat.mul_zero,
        Nat.add_zero] at hs h0
      rw [show after a 0 = a by rw [after_eq]; simp] at h0
      obtain ⟨is1, h1, hl1, hn1⟩ := sliceOk_ok h0
      have hrest : ∀ i (h1 : i < rest.length) (h2 : i < ns.length),
          functionSize (sigOf callee) rest[i].2 = ns[i] ∧
          sliceOk (genFunction callee S (after (after a s) (ns.take i).sum) rest[i].2) n
            (o + 4 * s + 4 * (ns.take i).sum) (4 * ns[i]) = true := by
        intro i hi1 hi2
        have := h (i + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.sum_cons] at this
        rw [after_after, show o + 4 * s + 4 * (ns.take i).sum = o + 4 * (s + (ns.take i).sum) by
          omega]
        exact this
      obtain ⟨fns, hf, hlf, hnf⟩ :=
        genFunctions_slices rest ns (after a s) (o + 4 * s) (by simpa using hl) hrest
      have hhw : halfwordsOf is1 = 2 * functionSize (sigOf callee) f := by
        have := length_imageBytes is1
        omega
      refine ⟨is1 ++ fns, ?_, ?_, ?_⟩
      · simp only [genFunctions]
        rw [except_bind_ok]
        refine ⟨is1, h1, ?_⟩
        simp only [hhw, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [hs, except_bind_ok]
        exact ⟨fns, hf, rfl⟩
      · rw [imageBytes_append, List.length_append, hl1, hlf, List.sum_cons]
        omega
      · rw [imageBytes_append, List.sum_cons,
          show 4 * (s + ns.sum) = (imageBytes is1 ++ imageBytes fns).length by
            rw [List.length_append, hl1, hlf]; omega]
        exact slice_append (by rw [hl1]; exact hn1) (by rw [hl1, hlf]; exact hnf)

theorem functionsPartOk_iff {m : Module} {k : Nat} {s0 : List UInt64} {base limit : UInt32}
    {ns : List Nat} {n off lo hi : Nat} :
    functionsPartOk m k s0 base limit ns n off lo hi = true ↔
      ∀ i, lo ≤ i → i < hi → functionPartOk m k s0 base limit ns n off i = true := by
  simp only [functionsPartOk, List.all_eq_true, List.mem_range'_1]
  constructor
  · intro h i h1 h2
    exact h i ⟨h1, by omega⟩
  · intro h i hi
    exact h i hi.1 (by omega)

/-- The parts of the functions from `lo` to `mid` and from `mid` to `hi` give those from `lo` to
`hi`. -/
theorem functionsPartOk_append {m : Module} {k : Nat} {s0 : List UInt64} {base limit : UInt32}
    {ns : List Nat} {n off lo mid hi : Nat}
    (h1 : functionsPartOk m k s0 base limit ns n off lo mid = true)
    (h2 : functionsPartOk m k s0 base limit ns n off mid hi = true) :
    functionsPartOk m k s0 base limit ns n off lo hi = true := by
  rw [functionsPartOk_iff] at h1 h2 ⊢
  intro i hl hh
  by_cases hm : i < mid
  · exact h1 i hl hm
  · exact h2 i (by omega) hh

/-! ## The program -/

/-- A program whose functions do not access the area has none. -/
theorem areaOf_none {m : Module} {fs : List (Nat × Function)} {limit : UInt32}
    (h : (fs.any fun x => listArea x.2.body) = false) : areaOf m fs limit = .ok none := by
  unfold areaOf
  rw [h]
  rfl

/-- `genProgram` from its parts, the converse of `gen_program` for the entry after `main`, for a
program whose functions do not access the area. -/
theorem genProgram_of {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {div : List Instr} {fs : List (Nat × Function)} {main fns : List Instr}
    (hfs : (reachFrom m k).mapM (funcOf m) = .ok fs)
    (hen : ((entriesFrom (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs).find?
        (·.1 = k)).map (·.2) =
      some (after base (mainSize s0), List.replicate (s0.length + 1) .i64,
        List.replicate (s0.length + 1) .i64))
    (hmain : genMain base (after base (mainSize s0)) dev s0 = .ok main)
    (hml : main.length = mainSize s0)
    (hA : (fs.any fun x => listArea x.2.body) = false)
    (hfns : genFunctions (tableOf (callTargets m k)
        (entriesFrom (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs))
      (progShared (endOf (sigIn (callTargets m k) fs) (after base (mainSize s0)) fs) limit none)
      (after base (mainSize s0)) fs = .ok fns) :
    genProgram m k s0 base limit dev div =
      .ok (main ++ fns ++ [Instr.bTo (-4), Instr.bTo (-4), Instr.bTo (-4)] ++ div) := by
  unfold genProgram
  rw [except_bind_ok]
  refine ⟨fs, hfs, ?_⟩
  dsimp only
  split
  · rename_i e ps rs heq
    have h2 := heq.symm.trans hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp only [and_self, ↓reduceIte]
    rw [except_bind_ok]
    refine ⟨after base (mainSize s0), rfl, ?_⟩
    rw [except_bind_ok]
    refine ⟨main, hmain, ?_⟩
    simp only [hml, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [except_bind_ok]
    refine ⟨none, areaOf_none hA, ?_⟩
    rw [except_bind_ok]
    exact ⟨fns, hfns, rfl⟩
  · rename_i heq
    exact absurd (heq.symm.trans hen) (by simp)

/-- The program of step `k` of `m` from the state `s0` at `base`, from its parts at byte `off` of
the number `n`: `main`, the functions with the sizes `ns`, and the trap stubs with `div`, of `len`
bytes.  `genProgram` succeeds, and its code's bytes are those of `n` from `off`. -/
theorem genProgram_parts {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {div : List Instr} {ns : List Nat} {n off len : Nat}
    (hmain : mainPartOk m k s0 base dev n off = true)
    (hlen : ns.length = (reachedFns m k).length)
    (hfun : functionsPartOk m k s0 base limit ns n off 0 ns.length = true)
    (htail : tailPartOk s0 ns div n off len = true) :
    ∃ is, genProgram m k s0 base limit dev div = .ok is ∧
      (imageBytes is).length = 4 * (mainSize s0 + ns.sum) + len ∧
      natOfBytes (imageBytes is) = n / 256 ^ off % 256 ^ (4 * (mainSize s0 + ns.sum) + len) := by
  unfold mainPartOk at hmain
  split at hmain
  · rename_i x rest hfs
    obtain ⟨j, f⟩ := x
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmain
    obtain ⟨⟨⟨⟨hjk, hps⟩, hrs⟩, hA⟩, hm⟩ := hmain
    replace hA : (((j, f) :: rest : List (Nat × Function)).any fun y => listArea y.2.body) =
        false := by
      simpa using hA
    subst hjk
    -- `main`
    obtain ⟨mc, hgm, hml, hmn⟩ := sliceOk_ok hm
    rw [except_bind_ok] at hgm
    obtain ⟨main, hgen, hif⟩ := hgm
    have hmain' : main.length = mainSize s0 ∧ main = mc := by
      split at hif
      · rename_i hl
        exact ⟨hl, except_pure_ok.mp hif⟩
      · exact absurd hif except_throw_ok
    obtain ⟨hmlen, rfl⟩ := hmain'
    -- the functions
    have hreach : reachedFns m j = (j, f) :: rest := by simp [reachedFns, hfs]
    rw [hreach] at hlen
    generalize hfsd : ((j, f) :: rest : List (Nat × Function)) = fs at hfs hlen hreach hA
    have hsig := sigOf_tableOf_sizes (callTargets m j) (after base (mainSize s0)) fs ns hlen
    have hparts : ∀ i (h1 : i < fs.length) (h2 : i < ns.length),
        functionSize (sigOf (tableOf (callTargets m j)
          (entriesOfSizes (after base (mainSize s0)) fs ns))) fs[i].2 = ns[i] ∧
        sliceOk (genFunction (tableOf (callTargets m j)
            (entriesOfSizes (after base (mainSize s0)) fs ns))
            (progShared (after (after base (mainSize s0)) ns.sum) limit none)
            (after (after base (mainSize s0)) (ns.take i).sum) fs[i].2) n
          (off + 4 * mainSize s0 + 4 * (ns.take i).sum) (4 * ns[i]) = true := by
      intro i h1 h2
      have := (functionsPartOk_iff.mp hfun) i (Nat.zero_le _) h2
      simp only [functionPartOk, hreach, List.getElem?_eq_getElem h1,
        List.getElem?_eq_getElem h2, Bool.and_eq_true, beq_iff_eq] at this
      rw [show off + 4 * mainSize s0 + 4 * (ns.take i).sum =
        off + 4 * (mainSize s0 + (ns.take i).sum) by omega]
      exact this
    obtain ⟨fns, hfns, hlf, hnf⟩ := genFunctions_slices fs ns (after base (mainSize s0))
      (off + 4 * mainSize s0) hlen hparts
    have hsizes : fs.map (fun x => functionSize (sigIn (callTargets m j) fs) x.2) = ns := by
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      have := (hparts i (by simpa using h1) h2).1
      rw [hsig] at this
      simp only [List.getElem_map]
      exact this
    obtain ⟨hent, hend⟩ := entriesFrom_sizes _ (after base (mainSize s0)) fs ns hsizes
    -- the tail
    obtain ⟨tl, htl, hll, hnl⟩ := sliceOk_ok (by unfold tailPartOk at htail; exact htail)
    rw [except_pure_ok] at htl
    subst htl
    have hen : ((entriesFrom (sigIn (callTargets m j) fs) (after base (mainSize s0)) fs).find?
        (·.1 = j)).map (·.2) =
        some (after base (mainSize s0), List.replicate (s0.length + 1) .i64,
          List.replicate (s0.length + 1) .i64) := by
      subst hfsd
      simp [entriesFrom, hps, hrs]
    refine ⟨main ++ fns ++ [Instr.bTo (-4), Instr.bTo (-4), Instr.bTo (-4)] ++ div,
      genProgram_of hfs hen hgen hmlen hA (by rw [hent, hend]; exact hfns), ?_, ?_⟩
    · rw [List.append_assoc, List.append_assoc, imageBytes_append, imageBytes_append,
        List.length_append, List.length_append, hml, hlf, hll]
      omega
    · rw [List.append_assoc, List.append_assoc, imageBytes_append, imageBytes_append,
        show 4 * (mainSize s0 + ns.sum) + len = (imageBytes main ++ (imageBytes fns ++
            imageBytes ([Instr.bTo (-4), Instr.bTo (-4), Instr.bTo (-4)] ++ div))).length by
          simp only [List.length_append, hml, hlf, hll]; omega]
      refine slice_append (by rw [hml]; exact hmn) (slice_append (by rw [hml, hlf]; exact hnf) ?_)
      rw [hml, hlf, hll, show off + 4 * mainSize s0 + 4 * ns.sum =
        off + 4 * (mainSize s0 + ns.sum) by omega]
      exact hnl
  · cases hmain

/-- The check of a file of the program's code from its parts: the file's number `n` has `len`
bytes, which hold the parts from byte 0. -/
theorem fileOk_parts {m : Module} {k : Nat} {s0 : List UInt64} {base limit dev : UInt32}
    {div : List Instr} {ns : List Nat} {n len tail : Nat}
    (hmain : mainPartOk m k s0 base dev n 0 = true)
    (hlen : ns.length = (reachedFns m k).length)
    (hfun : functionsPartOk m k s0 base limit ns n 0 0 ns.length = true)
    (htail : tailPartOk s0 ns div n 0 tail = true)
    (hsize : len = 4 * (mainSize s0 + ns.sum) + tail) (hn : n < 256 ^ len) :
    fileOk (genProgram m k s0 base limit dev div) n len = true := by
  obtain ⟨is, hg, hl, hb⟩ := genProgram_parts hmain hlen hfun htail
  rw [hg]
  unfold fileOk
  simp only [Bool.and_eq_true, beq_iff_eq, natOfBytesPaired_eq]
  rw [hl, hb, ← hsize, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hn]
  exact ⟨rfl, rfl⟩

theorem bootBytes_eq (B : Boot) (is : List Instr) :
    bootBytes B is = (B.table.flatMap wordHalfs).flatMap halfBytes ++ imageBytes is := by
  simp only [bootBytes, bootHalfs, List.flatMap_append, imageBytes, List.flatMap_assoc]

/-- The check of a file of an image from reset from its parts: the file's number `n` has `len`
bytes, which hold `bootHead` and then the program's parts. -/
theorem bootFileOk_parts {B : Boot} {m : Module} {k : Nat} {s0 : List UInt64}
    {limit dev : UInt32} {ns : List Nat} {n len tail : Nat}
    (hhead : bootHeadOk B n = true)
    (hmain : mainPartOk m k s0 B.base dev n (bootHead B).length = true)
    (hlen : ns.length = (reachedFns m k).length)
    (hfun : functionsPartOk m k s0 B.base limit ns n (bootHead B).length 0 ns.length = true)
    (htail : tailPartOk s0 ns udivmod64 n (bootHead B).length tail = true)
    (hsize : len = (bootHead B).length + (4 * (mainSize s0 + ns.sum) + tail))
    (hn : n < 256 ^ len) :
    bootFileOk B (bootProgram B m k s0 limit dev) n len = true := by
  obtain ⟨is, hg, hl, hb⟩ := genProgram_parts hmain hlen hfun htail
  have hbp : bootProgram B m k s0 limit dev = .ok ((.bTo (-4) :: B.init) ++ is) := by
    unfold bootProgram
    rw [hg]
    rfl
  have hbytes : bootBytes B ((.bTo (-4) :: B.init) ++ is) = bootHead B ++ imageBytes is := by
    rw [bootBytes_eq, imageBytes_append, bootHead, List.append_assoc]
  have hh : natOfBytes (bootHead B) = n / 256 ^ 0 % 256 ^ (bootHead B).length := by
    unfold bootHeadOk at hhead
    rw [Nat.pow_zero, Nat.div_one, ← natOfBytesPaired_eq]
    exact beq_iff_eq.mp hhead
  rw [hbp]
  unfold bootFileOk
  simp only [Bool.and_eq_true, beq_iff_eq, natOfBytesPaired_eq]
  rw [hbytes, List.length_append, hl, ← hsize]
  refine ⟨?_, rfl⟩
  have := slice_append (o := 0) hh (by rw [Nat.zero_add, hl]; exact hb)
  rw [List.length_append, hl, ← hsize, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hn] at this
  exact this

end LeanExe.M7
