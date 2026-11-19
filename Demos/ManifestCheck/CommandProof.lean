import Demos.ManifestCheck.Command
import Demos.ManifestCheck.CommandSpec
import Demos.ManifestCheck.Proof
import Library.Hashing.Sha256.StreamProof
import Verified.Wasi.FunctionEntry
import Verified.Wasi.Handles
import LeanExe.Wasi.Bind

/-! Every run of the command's `main` followed by its exit, under every host, that ends with an
exit status meets the request (`exec_main`): its events are those of `Meets` followed by the exit.

The proof follows `main`.  `argument_cases` relates the program's test of the argument buffer to
`OneArgument`.  `manifest_loop` follows the reads of the manifest into the buffer of its reported
size: the buffer's first bytes are those that the reads returned (`splice_take`), so a buffer that
the reads fill holds the manifest's bytes.  `readManifest_run` adds the call of `fd_filestat_get`
and the last read.  `Hashed` relates the state of `hashFile`'s loop to the bytes that the reads
returned: the hash value after their whole buffers of 65,536 bytes, and the bytes after those,
which the read buffer holds at its start.  `hashed_step` keeps it across a read, through
`update_toVec32` and `blocksFold_append`, and `hashed_finish` gives the digest bytes of
`SHS.SHA256.Impl.sha256` of the bytes through `finish_bytes`.  `hash_loop` follows the loop of
`hashFile` by induction on its passes and gives the reads of `FileReads`.  `withOpen_run` gives the
events of a bracket whose body never exits, and `entry_check` the events of `FileCheck` for a line
and the program's verdict, which `hexMatchesSpec_iff` and `digestOf_iff` relate to `DigestOf`.
`line_writes` gives `LineWrites` from `WriteAllRun.taken`, and `checks_loop` follows the loop of
`checkLines` by induction on the lines and gives `Checks`.  `Handled.append` and the confinement of
each part give `Handled` and `Confined` of the whole run. -/

namespace Demos.ManifestCheck

open LeanExe LeanExe.Wasi Library.Hashing.Words Library.Hashing.Sha256

/-! ## Bytes -/

theorem build_toList (count : UInt64) (f : UInt64 → UInt64) :
    (Bytes.build count f).data.data.toList =
      List.ofFn (n := count.toNat) fun i => (f (UInt64.ofNat i)).toUInt8 := by
  simp [Bytes.build, Array.toList_ofFn]

theorem build_size (count : UInt64) (f : UInt64 → UInt64) :
    (Bytes.build count f).data.size = count.toNat := by
  simp

theorem get_toUInt8 (b : Bytes) (i : Nat) (hi : i < b.data.size) (h64 : i < 2 ^ 64) :
    (b.get (UInt64.ofNat i)).toUInt8 = b.data.data.toList[i]'(by simpa using hi) := by
  rw [Bytes.get_eq_get!, toNat_ofNat h64, Bytes.get!_of_lt _ hi, UInt8.toUInt8_toUInt64,
    Array.getElem_toList]
  rfl

theorem slice_toList (b : Bytes) (start len : Nat) (h : start + len ≤ b.data.size)
    (h64 : b.data.size < 2 ^ 64) :
    (slice b (UInt64.ofNat start) (UInt64.ofNat len)).data.data.toList =
      (b.data.data.toList.drop start).take len := by
  unfold slice
  rw [build_toList]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data, toNat_ofNat (show len < 2 ^ 64 by omega)]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    have hi : i < len := by
      simp only [List.length_ofFn, toNat_ofNat (show len < 2 ^ 64 by omega)] at h1
      exact h1
    have hadd : UInt64.ofNat start + UInt64.ofNat i = UInt64.ofNat (start + i) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega),
        toNat_ofNat (by omega)]
      omega
    rw [show UInt64.ofNat i = UInt64.ofNat i from rfl, hadd,
      get_toUInt8 b _ (by omega) (by omega)]

theorem bytesOf_append (l₁ l₂ : List UInt8) :
    (bytesOf (l₁ ++ l₂)).data = (bytesOf l₁).data ++ (bytesOf l₂).data := by
  apply ByteArray.ext
  simp [bytesOf]

theorem bytesOf_size (l : List UInt8) : (bytesOf l).data.size = l.length := rfl

theorem bytesOf_data (b : Bytes) : (bytesOf b.data.data.toList).data = b.data := by
  apply ByteArray.ext
  simp [bytesOf]

theorem bytesOf_toList (b : Bytes) : bytesOf b.data.data.toList = b := by
  cases b
  rw [show bytesOf _ = ⟨(bytesOf _).data⟩ from rfl, bytesOf_data]

theorem toList_length (b : Bytes) : b.data.data.toList.length = b.data.size := by simp

/-- The first bytes of a buffer after a splice at `f`, up to `c` bytes past `f`: the buffer's bytes
before `f`, then the first `c` bytes spliced. -/
theorem splice_take {B R : Bytes} {f c : Nat} (hfit : f + R.data.size ≤ B.data.size)
    (hc : c ≤ R.data.size) :
    (B.splice f R).data.data.toList.take (f + c) =
      B.data.data.toList.take f ++ R.data.data.toList.take c := by
  have hsize := Bytes.splice_size hfit
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases hi : i < f + c
  · rw [ite_eq_left hi]
    have hin : i < (B.splice f R).data.size := by omega
    rw [List.getElem?_eq_getElem (by simpa using hin), Array.getElem_toList,
      ← ByteArray.getElem_eq_getElem_data]
    by_cases hlow : i < f
    · rw [Bytes.splice_get_before hfit hlow, List.getElem?_append_left (by simp; omega),
        List.getElem?_take, ite_eq_left hlow, List.getElem?_eq_getElem (by simp; omega),
        Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
    · have hlen : (B.data.data.toList.take f).length = f := by simp; omega
      rw [Bytes.splice_get_inside hfit (by omega) (by omega),
        List.getElem?_append_right (by omega), hlen, List.getElem?_take, ite_eq_left (by omega),
        List.getElem?_eq_getElem (by simp; omega), Array.getElem_toList,
        ← ByteArray.getElem_eq_getElem_data]
  · rw [ite_eq_right hi]
    symm
    apply List.getElem?_eq_none
    simp
    omega

/-! ## The argument -/

/-- The state of `argScan` after the first `k` bytes of `l`. -/
def argState (l : List UInt8) (k : Nat) : UInt64 × UInt64 × UInt64 :=
  (UInt64.ofNat ((l.take k).count 0), UInt64.ofNat (if (0 : UInt8) ∈ l.take k then l.idxOf 0 else 0),
    UInt64.ofNat k)

theorem argScan_eq (a : Bytes) (h : a.data.size < 2 ^ 63) :
    argScan a = argState a.data.data.toList a.data.size := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hlen : a.data.data.toList.length = a.data.size := by simp
  have key := LeanExe.Dialect.loop_induction (n := a.size)
    (init := ((0 : UInt64), (0 : UInt64), (0 : UInt64)))
    (f := fun i st => argStep st (a.get i))
    (fun k st => st = argState a.data.data.toList k) (by simp [argState])
    (by
      intro k st hk hst
      rw [hs] at hk
      subst hst
      have hget : a.get (UInt64.ofNat k) = (a.data.data.toList[k]'(by omega)).toUInt64 := by
        rw [Bytes.get_eq_getD, toNat_ofNat (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega)]
        rfl
      have htake : a.data.data.toList.take (k + 1) =
          a.data.data.toList.take k ++ [a.data.data.toList[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hcount : (a.data.data.toList.take k).count 0 ≤ k := by
        have := List.count_le_length (l := a.data.data.toList.take k) (a := 0)
        simp at this
        omega
      show argStep (argState _ k) (a.get (UInt64.ofNat k)) = argState _ (k + 1)
      rw [hget]
      unfold argStep argState
      rw [htake]
      generalize hb : a.data.data.toList[k]'(by omega) = b
      by_cases hb0 : b = 0
      · subst hb0
        have hz : ((0 : UInt8).toUInt64 == 0) = true := rfl
        rw [hz]
        simp only [↓reduceIte, List.count_append, List.count_singleton_self, List.mem_append,
          List.mem_singleton, or_true]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, toNat_ofNat (show (a.data.data.toList.take k).count 0 < 2 ^ 64
            by omega), toNat_ofNat (show (a.data.data.toList.take k).count 0 + 1 < 2 ^ 64 by omega)]
          simp
          omega
        · dsimp only
          by_cases hmem : (0 : UInt8) ∈ a.data.data.toList.take k
          · have hne : (a.data.data.toList.take k).count 0 ≠ 0 :=
              List.count_pos_iff.mpr hmem |>.ne'
            have hneq : (UInt64.ofNat ((a.data.data.toList.take k).count 0) == 0) = false := by
              rw [beq_toNat, toNat_ofNat (by omega)]
              simpa using hne
            simp [hmem, hneq]
          · have hz' : (a.data.data.toList.take k).count 0 = 0 := List.count_eq_zero.mpr hmem
            have hidx : a.data.data.toList.idxOf 0 = k := by
              rw [← List.take_append_drop k a.data.data.toList, List.idxOf_append_of_notMem hmem,
                List.drop_eq_getElem_cons (by omega), hb]
              simp
              omega
            simp [hz', hidx]
        · apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
          simp only [UInt64.reduceToNat]
          omega
      · have hz : (b.toUInt64 == 0) = false := by
          have : b.toUInt64 ≠ 0 := fun e => hb0 (by
            have := congrArg UInt64.toNat e
            simp at this
            exact UInt8.toNat_inj.mp (by simpa using this))
          simpa using this
        rw [hz]
        have hb0' : (0 : UInt8) ≠ b := fun e => hb0 e.symm
        simp only [Bool.false_eq_true, ↓reduceIte, List.count_append, List.mem_append,
          List.mem_singleton, hb0', or_false]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp [hb0]
        · rfl
        · apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
          simp only [UInt64.reduceToNat]
          omega)
  rw [hs] at key
  exact key

theorem count_append_cons (p r : List UInt8) (b : UInt8) :
    (p ++ b :: r).count 0 = p.count 0 + (if b = 0 then 1 else 0) + r.count 0 := by
  simp [List.count_append, List.count_cons]
  split <;> omega

/-- The buffer of one argument after the program name holds two zero bytes, the last one at its
end, and the argument is the bytes between them. -/
theorem oneArgument_shape {l name : List UInt8} (h : OneArgument l name) :
    l.count 0 = 2 ∧ l.getLastD 1 = 0 ∧ l.idxOf 0 + name.length + 2 = l.length ∧
      name = (l.drop (l.idxOf 0 + 1)).take (l.length - l.idxOf 0 - 2) := by
  obtain ⟨program, rfl, hp, hn⟩ := h
  have hidx : (program ++ 0 :: (name ++ [0])).idxOf 0 = program.length := by
    rw [List.idxOf_append_of_notMem hp, List.idxOf_cons_self]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [count_append_cons, List.count_append, List.count_eq_zero.mpr hp,
      List.count_eq_zero.mpr hn]
    simp
  · have e : program ++ 0 :: (name ++ [0]) = (program ++ 0 :: name) ++ [0] := by simp
    rw [e, List.getLastD_eq_getLast?, List.getLast?_concat]
    rfl
  · rw [hidx, List.length_append, List.length_cons, List.length_append, List.length_singleton]
    omega
  · rw [hidx]
    have e : program ++ 0 :: (name ++ [0]) = (program ++ [0]) ++ (name ++ [0]) := by simp
    rw [e, List.drop_left' (by simp), List.take_left' (by simp)]

/-- A buffer with two zero bytes, the last one at its end, holds one argument. -/
theorem oneArgument_of {l : List UInt8} (hc : l.count 0 = 2) (hl : l.getLastD 1 = 0) :
    OneArgument l ((l.drop (l.idxOf 0 + 1)).take (l.length - l.idxOf 0 - 2)) := by
  have hmem : (0 : UInt8) ∈ l := List.count_pos_iff.mp (by omega)
  have hidx := List.idxOf_lt_length_iff.mpr hmem
  have hsplit : l = l.take (l.idxOf 0) ++ 0 :: l.drop (l.idxOf 0 + 1) := by
    conv_lhs => rw [← List.take_append_drop (l.idxOf 0) l]
    rw [List.drop_eq_getElem_cons hidx, List.getElem_idxOf hidx]
  have hpre : (0 : UInt8) ∉ l.take (l.idxOf 0) := fun h =>
    lt_irrefl _ ((List.mem_take_iff_idxOf_lt hmem).mp h)
  generalize hr : l.drop (l.idxOf 0 + 1) = r at hsplit
  have hrc : r.count 0 = 1 := by
    have := hc
    rw [hsplit, count_append_cons, List.count_eq_zero.mpr hpre] at this
    simp at this
    omega
  have hrne : r ≠ [] := by
    intro e
    rw [e] at hrc
    simp at hrc
  have hrl : r.getLastD 1 = 0 := by
    rw [hsplit] at hl
    rw [List.getLastD_eq_getLast?] at hl ⊢
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at hl
    rw [List.getLast?_cons] at hl
    cases e : r.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp e) hrne
    | some x => rw [e] at hl; simpa using hl
  have hrsplit : r = r.dropLast ++ [0] := by
    conv_lhs => rw [← List.dropLast_append_getLast hrne]
    congr 2
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hrne] at hrl
    simpa using hrl
  have hname : (0 : UInt8) ∉ r.dropLast := by
    intro hm
    have := hrc
    rw [hrsplit, List.count_append, List.count_singleton_self] at this
    have := List.count_pos_iff.mpr hm
    omega
  have hlen : l.length = l.idxOf 0 + 1 + r.length := by
    rw [← hr, List.length_drop]
    omega
  refine ⟨l.take (l.idxOf 0), ?_, hpre, ?_⟩
  · have htake : r.take (l.length - l.idxOf 0 - 2) = r.dropLast := by
      rw [List.dropLast_eq_take]
      congr 1
      omega
    rw [htake]
    conv_lhs => rw [hsplit, hrsplit]
  · have htake : r.take (l.length - l.idxOf 0 - 2) = r.dropLast := by
      rw [List.dropLast_eq_take]
      congr 1
      omega
    rw [htake]
    exact hname

theorem getLastD_eq_get (a : Bytes) (h : a.data.size < 2 ^ 32) (hpos : 0 < a.data.size) :
    a.get (a.size - 1) = (a.data.data.toList.getLastD 1).toUInt64 := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hi : (a.size - 1).toNat = a.data.size - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hs]; simp; omega), hs]
    rfl
  have hne : a.data.data.toList ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [Array.length_toList, ByteArray.size_data]
    exact hpos
  rw [Bytes.get_eq_getD, hi, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- The program's test of the argument buffer refuses it exactly when it does not hold one
argument after the program name, and otherwise the slice that names the manifest is that
argument. -/
theorem argument_cases (a : Bytes) (h : a.data.size < 2 ^ 32) :
    (((argScan a).1 != 2 || a.get (a.size - 1) != 0) = true →
      ∀ name, ¬ OneArgument a.data.data.toList name) ∧
    (((argScan a).1 != 2 || a.get (a.size - 1) != 0) = false →
      OneArgument a.data.data.toList
        (slice a ((argScan a).2.1 + 1) (a.size - (argScan a).2.1 - 2)).data.data.toList) := by
  have hs : a.size.toNat = a.data.size := Bytes.size_toNat a (by omega)
  have hlen : a.data.data.toList.length = a.data.size := by simp
  rw [argScan_eq a (by omega)]
  unfold argState
  generalize hl : a.data.data.toList = l at hlen
  rw [List.take_of_length_le (by omega)]
  have hcl : l.count 0 ≤ l.length := List.count_le_length
  constructor
  · intro hrefuse name hone
    obtain ⟨hc, hlast, -, -⟩ := oneArgument_shape hone
    have hpos : 0 < a.data.size := by
      rw [← hlen]
      rcases l with _ | ⟨x, l⟩
      · simp at hc
      · simp
    rw [getLastD_eq_get a h hpos, hl, hlast] at hrefuse
    simp only [hc] at hrefuse
    simp at hrefuse
  · intro haccept
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at haccept
    obtain ⟨hc2, hlast0⟩ := haccept
    have hc : l.count 0 = 2 := by
      have := congrArg UInt64.toNat hc2
      rw [toNat_ofNat (by omega)] at this
      simpa using this
    have hpos : 0 < a.data.size := by
      rw [← hlen]
      rcases l with _ | ⟨x, l⟩
      · simp at hc
      · simp
    rw [getLastD_eq_get a h hpos, hl] at hlast0
    have hlast : l.getLastD 1 = 0 := by
      have := congrArg UInt64.toNat hlast0
      simp at this
      exact UInt8.toNat_inj.mp (by simpa using this)
    have hmem : (0 : UInt8) ∈ l := List.count_pos_iff.mp (by omega)
    have hone := oneArgument_of hc hlast
    obtain ⟨-, -, hsum, -⟩ := oneArgument_shape hone
    simp only [hmem, ↓reduceIte]
    have hi : (UInt64.ofNat (l.idxOf 0) + 1) = UInt64.ofNat (l.idxOf 0 + 1) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
      simp
      omega
    have hn : a.size - UInt64.ofNat (l.idxOf 0) - 2 =
        UInt64.ofNat (l.length - l.idxOf 0 - 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, hs, toNat_ofNat (by omega)]; omega), hs,
            toNat_ofNat (by omega)]
          simp
          omega),
        UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, hs, toNat_ofNat (by omega)]; omega),
        hs, toNat_ofNat (by omega), toNat_ofNat (by omega)]
      simp
      omega
    rw [hi, hn, slice_toList a _ _ (by omega) (by omega), hl]
    exact hone

/-! ## Calls -/

theorem fdRead_accepted (fd length : UInt64) (hfd : fd.toNat < 2 ^ 32)
    (hlength : length.toNat < 2 ^ 32) :
    Call.fdRead.reject [.word fd, .space length] = 0 := by
  have h : fd.toNat < 4294967296 := hfd
  have h' : length.toNat < 4294967296 := hlength
  simp [Call.reject, rejectArgs, Call.fdRead, Param.takesArg, Param.reject, Arg.capacity,
    Arg.value, h, h']

theorem fdFilestatGet_accepted (fd : UInt64) (hfd : fd.toNat < 2 ^ 32) :
    Call.fdFilestatGet.reject [.word fd] = 0 := by
  have h : fd.toNat < 4294967296 := hfd
  simp [Call.reject, rejectArgs, Call.fdFilestatGet, Param.takesArg, Param.reject, Arg.value, h]

theorem fdClose_accepted (fd : UInt64) (hfd : fd.toNat < 2 ^ 32) :
    Call.fdClose.reject [.word fd] = 0 := by
  have h : fd.toNat < 4294967296 := hfd
  simp [Call.reject, rejectArgs, Call.fdClose, Param.takesArg, Param.reject, Arg.value, h]

theorem pathOpen_accepted (name : Bytes) (h : name.data.size < 2 ^ 32) (rights : UInt64)
    (hr : rights = 2 ∨ rights = 2097154) :
    Call.pathOpen.reject [.word 3, .word 1, .bytes name, .word 0, .word rights, .word 0,
      .word 0] = 0 := by
  have h' : name.data.size < 4294967296 := h
  rcases hr with rfl | rfl <;>
    simp [Call.reject, rejectArgs, Call.pathOpen, Param.takesArg, Param.reject, Arg.value,
      Arg.length, h'] <;> decide

/-- A read into a window of `length` bytes returns an errno of at most 76, and with errno 0 the
window's bytes and a count. -/
theorem read_reply {World : Type} {host : Host World} {world after : World}
    {fd length errno : UInt64} {committed : List Bytes}
    (permitted : host.sys world .fdRead [.word fd, .space length] (.returned errno committed)
      after) :
    errno.toNat ≤ 76 ∧ ∃ bytes count, committed = [bytes, count] ∧
      bytes.data.size = length.toNat := by
  obtain ⟨shape, valid⟩ := host.sys_bound permitted
  refine ⟨valid, ?_⟩
  have hsizes : committed.map (·.data.size) = [length.toNat, 4] := shape
  rcases committed with _ | ⟨bytes, _ | ⟨count, _ | ⟨_, _⟩⟩⟩ <;> simp at hsizes
  exact ⟨bytes, count, rfl, hsizes.1⟩

/-- The bytes that `returned` gives are the first bytes of the window's output, as many as the
count of the fill. -/
theorem returned_eq (length : UInt64) (bytes count : Bytes) :
    returned length [bytes, count] =
      bytes.data.data.toList.take (Min.min ((⟨0, [bytes, count]⟩ : Reply).word 1) length).toNat := rfl

/-- A loop from a state at which the test fails returns that state and has no event. -/
theorem loop_done {World σ : Type} {host : Host World} {test : UInt64 → σ → Bool}
    {step : UInt64 → σ → Action σ} {s : σ} (stops : ∀ i, test i s = false) :
    ∀ {remaining index : Nat} {world : World} {trace : List Event} {outcome : Outcome σ}
      {final : World},
      LoopExec host remaining index s test step .pure world trace outcome final →
      trace = [] ∧ outcome = .returned s
  | 0, _, _, _, _, _, run => by
    cases run with
    | zero next => exact ⟨(Verified.Wasi.exec_pure_shape next).1,
        (Verified.Wasi.exec_pure_shape next).2.1⟩
  | _ + 1, _, _, _, _, _, run => by
    cases run with
    | stop _ next => exact ⟨(Verified.Wasi.exec_pure_shape next).1,
        (Verified.Wasi.exec_pure_shape next).2.1⟩
    | next test => rw [stops] at test; cases test
    | exit test => rw [stops] at test; cases test
    | trap test => rw [stops] at test; cases test


/-- The fill of a read that returned errno 0 places the window's output at the window's start. -/
theorem fill_ok (buffer : Bytes) (start count used : UInt64) (bytes : Bytes) :
    FillResult.of buffer start count 0 used bytes =
      ⟨0, used, buffer.splice (buffer.window start count).1 bytes⟩ := by
  simp [FillResult.of]

/-- The fill of a read that returned an errno sets the window's bytes to 0. -/
theorem fill_failed {errno : UInt64} (nonzero : errno ≠ 0) (buffer : Bytes)
    (start count used : UInt64) (bytes : Bytes) :
    FillResult.of buffer start count errno used bytes =
      ⟨errno, 0, buffer.splice (buffer.window start count).1
        (Bytes.zeros (buffer.window start count).2)⟩ := by
  simp [FillResult.of, nonzero, Bytes.clear]

theorem sysReply_errno (errno : UInt64) (committed : List Bytes) :
    (sysReply errno committed).errno = errno := rfl

theorem sysReply_zero (committed : List Bytes) : sysReply 0 committed = ⟨0, committed⟩ := rfl

/-- The bytes that `ByteArray.extract` keeps, as a list. -/
theorem extract_toList (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) := by
  simp [ByteArray.data_extract, List.extract_eq_take_drop]

theorem byteArray_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

/-! ## The streaming hash -/

/-- A fold over the first `q` blocks of a list's bytes reads only its first `64 q` bytes. -/
theorem fold_take (l : List UInt8) (q : Nat) (hq : 64 * q ≤ l.length)
    (s : SHS.SHA256.Impl.State) :
    blocksFold (bytesOf l).data q s = blocksFold (bytesOf (l.take (64 * q))).data q s := by
  conv_lhs => rw [← List.take_append_drop (64 * q) l]
  rw [bytesOf_append, blocksFold_append_tail _ _ _ (by rw [bytesOf_size, List.length_take]; omega)]

/-- A fold over the first `q` blocks of a byte string reads only its first `64 q` bytes. -/
theorem fold_bytes (b : Bytes) (q : Nat) (hq : 64 * q ≤ b.data.size)
    (s : SHS.SHA256.Impl.State) :
    blocksFold b.data q s = blocksFold (bytesOf (b.data.data.toList.take (64 * q))).data q s := by
  have := fold_take b.data.data.toList q (by simp; omega) s
  rwa [bytesOf_data] at this

/-- The state of `hashFile`'s loop after the reads returned the bytes `done`: the read buffer holds
65,536 bytes, the first `fill` of which are the bytes of `done` after its whole buffers of 65,536
bytes, `total` counts the bytes of `done`, fewer than `2^61`, and `h` is the implementation's hash
value after those whole buffers. -/
structure Hashed (h : Words8) (buffer : Bytes) (fill total : UInt64) (done : List UInt8) :
    Prop where
  size : buffer.data.size = 65536
  filled : fill.toNat = done.length % 65536
  counted : total.toNat = done.length
  small : done.length < 2 ^ 61
  held : buffer.data.data.toList.take fill.toNat = done.drop (65536 * (done.length / 65536))
  hashed : h.toVec32 =
    blocksFold (bytesOf done).data (1024 * (done.length / 65536)) SHS.SHA256.Impl.H256_256

theorem hashed_init {buffer : Bytes} (size : buffer.data.size = 65536) :
    Hashed iv256 buffer 0 0 [] where
  size := size
  filled := rfl
  counted := rfl
  small := by decide
  held := by simp
  hashed := rfl

/-- A splice at the position `f` keeps the buffer's first `f` bytes. -/
theorem splice_take_self {B R : Bytes} {f : Nat} (hfit : f + R.data.size ≤ B.data.size) :
    (B.splice f R).data.data.toList.take f = B.data.data.toList.take f := by
  have := splice_take (c := 0) hfit (Nat.zero_le _)
  simpa using this

/-- A splice into the window after the bytes that the buffer holds keeps the state. -/
theorem Hashed.keep {h : Words8} {B : Bytes} {fill total : UInt64} {done : List UInt8}
    (hs : Hashed h B fill total done) {X : Bytes} (hfit : fill.toNat + X.data.size ≤ 65536) :
    Hashed h (B.splice fill.toNat X) fill total done where
  size := (Bytes.splice_size (by rw [hs.size]; exact hfit)).trans hs.size
  filled := hs.filled
  counted := hs.counted
  small := hs.small
  held := by rw [splice_take_self (by rw [hs.size]; exact hfit), hs.held]
  hashed := hs.hashed

/-- A read of `count` bytes that leaves room in the buffer adds them to the bytes it holds. -/
theorem Hashed.part {h : Words8} {B : Bytes} {fill total : UInt64} {done : List UInt8}
    (hs : Hashed h B fill total done) {R : Bytes} {count : UInt64}
    (hfit : fill.toNat + R.data.size ≤ 65536) (hc : count.toNat ≤ R.data.size)
    (hpart : fill.toNat + count.toNat < 65536) (hsmall : done.length + count.toNat < 2 ^ 61) :
    Hashed h (B.splice fill.toNat R) (fill + count) (total + count)
      (done ++ R.data.data.toList.take count.toNat) := by
  have hn := hs.filled
  have hlen : (done ++ R.data.data.toList.take count.toNat).length =
      done.length + count.toNat := by simp; omega
  have hdiv : (done.length + count.toNat) / 65536 = done.length / 65536 := by omega
  have hsum : (fill + count).toNat = fill.toNat + count.toNat := by
    rw [UInt64.toNat_add]
    omega
  refine ⟨(Bytes.splice_size (by rw [hs.size]; exact hfit)).trans hs.size, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsum, hlen]
    omega
  · rw [hlen, UInt64.toNat_add, hs.counted]
    omega
  · rw [hlen]
    exact hsmall
  · rw [hsum, splice_take (by rw [hs.size]; exact hfit) hc, hs.held, hlen, hdiv,
      List.drop_append_of_le_length (by omega)]
  · rw [hlen, hdiv, hs.hashed, bytesOf_append,
      blocksFold_append_tail _ _ _ (by rw [bytesOf_size]; omega)]

/-- A read of `count` bytes that fills the buffer compresses it and empties it. -/
theorem Hashed.full {h : Words8} {B : Bytes} {fill total : UInt64} {done : List UInt8}
    (hs : Hashed h B fill total done) {R : Bytes} {count : UInt64}
    (hfit : fill.toNat + R.data.size ≤ 65536) (hc : count.toNat ≤ R.data.size)
    (hfull : fill.toNat + count.toNat = 65536) (hsmall : done.length + count.toNat < 2 ^ 61) :
    Hashed (update h (B.splice fill.toNat R) 1024) (B.splice fill.toNat R) 0 (total + count)
      (done ++ R.data.data.toList.take count.toNat) := by
  have hn := hs.filled
  have hB : (B.splice fill.toNat R).data.size = 65536 :=
    (Bytes.splice_size (by rw [hs.size]; exact hfit)).trans hs.size
  have hlen : (done ++ R.data.data.toList.take count.toNat).length =
      done.length + count.toNat := by simp; omega
  have hdiv : (done.length + count.toNat) / 65536 = done.length / 65536 + 1 := by omega
  have hwhole : (B.splice fill.toNat R).data.data.toList =
      done.drop (65536 * (done.length / 65536)) ++ R.data.data.toList.take count.toNat := by
    rw [← hs.held, ← splice_take (by rw [hs.size]; exact hfit) hc, hfull,
      List.take_of_length_le (by simp [hB])]
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen]
    simp only [UInt64.toNat_zero]
    omega
  · rw [hlen, UInt64.toNat_add, hs.counted]
    omega
  · rw [hlen]
    exact hsmall
  · rw [hlen, UInt64.toNat_zero, List.take_zero, List.drop_eq_nil_of_le (by rw [hlen]; omega)]
  · rw [update_toVec32 _ _ 1024 (by decide), hs.hashed, hlen, hdiv]
    simp only [UInt64.reduceToNat]
    have hsplit : done ++ R.data.data.toList.take count.toNat =
        done.take (65536 * (done.length / 65536)) ++ (B.splice fill.toNat R).data.data.toList := by
      rw [hwhole, ← List.append_assoc, List.take_append_drop]
    rw [hsplit, bytesOf_append, bytesOf_data,
      show 1024 * (done.length / 65536 + 1) = 1024 * (done.length / 65536) + 1024 by omega,
      blocksFold_append _ _ (1024 * (done.length / 65536))
        (by rw [bytesOf_size, List.length_take]; omega),
      fold_take done (1024 * (done.length / 65536)) (by omega),
      show 64 * (1024 * (done.length / 65536)) = 65536 * (done.length / 65536) by omega]

/-- The digest that `hashFile` computes from the state after the bytes `done` is the
implementation's SHA-256 of them. -/
theorem hashed_finish {h : Words8} {B : Bytes} {fill total : UInt64} {done : List UInt8}
    (hs : Hashed h B fill total done) :
    (finish (update h B (fill >>> 6)) B ((fill >>> 6) <<< 6) (fill &&& 63) total).bytes 32 =
      SHS.SHA256.Impl.sha256 (bytesOf done).data := by
  have hn := hs.filled
  have hf : fill.toNat < 65536 := by omega
  have h6 : (fill >>> 6).toNat = fill.toNat / 64 := by
    rw [UInt64.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  have hs6 : ((fill >>> 6) <<< 6).toNat = 64 * (fill.toNat / 64) := by
    rw [UInt64.toNat_shiftLeft, h6]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  have h63 : (fill &&& 63).toNat = fill.toNat % 64 := by
    rw [UInt64.toNat_and, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hheld := hs.held
  have hhash := hs.hashed
  have hcount := hs.counted
  have hsmall := hs.small
  have hBsize := hs.size
  generalize hk : done.length / 65536 = k at hheld hhash
  generalize hq : fill.toNat / 64 = q at h6 hs6
  have hlenB : B.data.data.toList.length = 65536 := by simp [hBsize]
  have hpre : done.take (65536 * k + 64 * q) =
      done.take (65536 * k) ++ B.data.data.toList.take (64 * q) := by
    rw [List.take_add, ← hheld, List.take_take, Nat.min_eq_left (by omega)]
  have hupd : (update h B (fill >>> 6)).toVec32 =
      blocksFold (bytesOf (done.take (65536 * k + 64 * q))).data (1024 * k + q)
        SHS.SHA256.Impl.H256_256 := by
    rw [update_toVec32 _ _ _ (by rw [h6]; omega), h6, hhash, hpre, bytesOf_append,
      blocksFold_append _ _ (1024 * k) (by rw [bytesOf_size, List.length_take]; omega),
      fold_take done (1024 * k) (by omega), show 64 * (1024 * k) = 65536 * k by omega,
      fold_bytes B q (by omega)]
  have hpsize : (bytesOf (done.take (65536 * k + 64 * q))).data.size = 64 * (1024 * k + q) := by
    rw [bytesOf_size, List.length_take]
    omega
  rw [finish_bytes _ (1024 * k + q) hpsize _ hupd B ((fill >>> 6) <<< 6) (fill &&& 63) total
    (by rw [hs6, h63, hBsize]; omega) (by rw [hBsize]; decide)
    (by rw [hpsize, h63, hcount]; omega) (by rw [hcount]; exact hsmall)]
  congr 1
  apply byteArray_ext
  rw [ByteArray.data_append, Array.toList_append, extract_toList, hs6, h63]
  show (done.take (65536 * k + 64 * q)) ++ _ = done
  rw [hpre, List.append_assoc, ← List.take_add,
    show 64 * q + (64 * q + fill.toNat % 64 - 64 * q) = fill.toNat by omega, hheld,
    List.take_append_drop]

/-- The state of `hashFile`'s loop: the hash value, the read buffer, the bytes that it holds, the
bytes read, and how the reads ended. -/
abbrev HashState := Words8 × Bytes × UInt64 × UInt64 × UInt64

/-- The state of `hashFile`'s loop after a read whose fill is `got`, from the state `s`. -/
def hashNext (s : HashState) (got : FillResult) : Action HashState :=
  if got.errno != 0 then .pure (s.1, got.buffer, s.2.2.1, s.2.2.2.1, 2)
  else if got.count == 0 then .pure (s.1, got.buffer, s.2.2.1, s.2.2.2.1, 1)
  else if s.2.2.1 + got.count == chunk then
    .pure (update s.1 got.buffer 1024, got.buffer, 0, s.2.2.2.1 + got.count, 0)
  else .pure (s.1, got.buffer, s.2.2.1 + got.count, s.2.2.2.1 + got.count, 0)

/-- A step of `hashFile`'s loop on the descriptor `fd`, written out. -/
def HashStep (fd : UInt64) (step : UInt64 → HashState → Action HashState) : Prop :=
  ∀ i (s : HashState), step i s =
    .sys .fdRead [.word fd, .space (s.2.1.windowLength s.2.2.1 (chunk - s.2.2.1))] fun reply =>
      hashNext s (FillResult.of s.2.1 s.2.2.1 (chunk - s.2.2.1) reply.errno
        (Min.min (reply.word 1) (s.2.1.windowLength s.2.2.1 (chunk - s.2.2.1))) (reply.bytes 0))

theorem hashNext_pure (s : HashState) (got : FillResult) : ∃ v, hashNext s got = .pure v := by
  unfold hashNext
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

theorem hashNext_not_exited {World : Type} {host : Host World} {s : HashState} {got : FillResult}
    {world final : World} {trace : List Event} {code : UInt64}
    (run : Exec host (hashNext s got) world trace (.exited code) final) : False := by
  obtain ⟨v, hv⟩ := hashNext_pure s got
  rw [hv] at run
  cases run

theorem hashNext_failed (s : HashState) {errno : UInt64} (nonzero : errno ≠ 0) (count : UInt64)
    (buffer : Bytes) :
    hashNext s ⟨errno, count, buffer⟩ = .pure (s.1, buffer, s.2.2.1, s.2.2.2.1, 2) := by
  simp [hashNext, nonzero]

theorem hashNext_eof (s : HashState) (buffer : Bytes) :
    hashNext s ⟨0, 0, buffer⟩ = .pure (s.1, buffer, s.2.2.1, s.2.2.2.1, 1) := by
  simp [hashNext]

theorem hashNext_full (s : HashState) {count : UInt64} (nonzero : count ≠ 0)
    (filled : s.2.2.1 + count = chunk) (buffer : Bytes) :
    hashNext s ⟨0, count, buffer⟩ =
      .pure (update s.1 buffer 1024, buffer, 0, s.2.2.2.1 + count, 0) := by
  simp [hashNext, nonzero, filled]

theorem hashNext_part (s : HashState) {count : UInt64} (nonzero : count ≠ 0)
    (room : s.2.2.1 + count ≠ chunk) (buffer : Bytes) :
    hashNext s ⟨0, count, buffer⟩ =
      .pure (s.1, buffer, s.2.2.1 + count, s.2.2.2.1 + count, 0) := by
  simp [hashNext, nonzero, room]

theorem reply_bytes (bytes count : Bytes) : (⟨0, [bytes, count]⟩ : Reply).bytes 0 = bytes := rfl

/-- How the reads of `hashFile` ended, as its state records it. -/
def endCode : Ending → UInt64
  | .eof => 1
  | .failed _ => 2
  | .cut => 0

theorem min_toNat_le (a b : UInt64) : (Min.min a b).toNat ≤ b.toNat := by
  show (if a ≤ b then a else b).toNat ≤ b.toNat
  split
  · exact UInt64.le_iff_toNat_le.mp ‹_›
  · exact Nat.le_refl _

theorem window_toNat (done : List UInt8) : (window done).toNat = 65536 - done.length % 65536 := by
  unfold window
  rw [toNat_ofNat (by omega)]

/-- The window of a read of `hashFile`: the bytes of the read buffer after those that it holds. -/
theorem hash_window {B : Bytes} {fill : UInt64} {done : List UInt8} (size : B.data.size = 65536)
    (filled : fill.toNat = done.length % 65536) :
    B.windowLength fill (chunk - fill) = window done ∧ (B.window fill (chunk - fill)).1 = fill.toNat ∧
      (B.window fill (chunk - fill)).2 = 65536 - fill.toNat := by
  have hf : fill.toNat < 65536 := by rw [filled]; omega
  have hc : (chunk - fill).toNat = 65536 - fill.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; show fill.toNat ≤ 65536; omega)]
    rfl
  have hsecond : (B.window fill (chunk - fill)).2 = 65536 - fill.toNat := by
    rw [Bytes.window_snd, hc, size]
    omega
  refine ⟨?_, ?_, hsecond⟩
  · unfold Bytes.windowLength window
    rw [hsecond, filled]
  · rw [Bytes.window_fst, size]
    omega

/-- The loop of `hashFile` on `fd` from the state after the bytes `done`, with `remaining`
passes, never exits, and when it returns it made the reads of `FileReads`, its state is the state
after the bytes that they returned, and it records how they ended. -/
theorem hash_loop {World : Type} {host : Host World} {fd : UInt64}
    {test : UInt64 → HashState → Bool} {step : UInt64 → HashState → Action HashState}
    (tested : ∀ i s, test i s = (s.2.2.2.2 == 0)) (stepped : HashStep fd step)
    (hfd : fd.toNat < 2 ^ 32) :
    ∀ (remaining index : Nat) (h : Words8) (buffer : Bytes) (fill total : UInt64)
      (done : List UInt8) {world : World} {trace : List Event} {outcome : Outcome HashState}
      {final : World},
      Hashed h buffer fill total done → done.length + 65536 * remaining < 2 ^ 61 →
      LoopExec host remaining index (h, buffer, fill, total, 0) test step .pure world trace
        outcome final →
      (∀ c, outcome ≠ .exited c) ∧
      ∀ s, outcome = .returned s → ∃ more ending, FileReads fd remaining done trace more ending ∧
        Hashed s.1 s.2.1 s.2.2.1 s.2.2.2.1 (done ++ more) ∧ s.2.2.2.2 = endCode ending
  | 0, _, h, buffer, fill, total, done, _, _, _, _, hs, _, run => by
    cases run with
    | zero next =>
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
      cases e
      exact ⟨[], .cut, .cut, by simpa using hs, rfl⟩
  | remaining + 1, index, h, buffer, fill, total, done, _, _, _, _, hs, hbound, run => by
    obtain ⟨hL, hfirst, hsecond⟩ := hash_window hs.size hs.filled
    have hfilled := hs.filled
    have hcounted := hs.counted
    have hfill : fill.toNat < 65536 := by rw [hs.filled]; omega
    have hLsmall : (buffer.windowLength fill (chunk - fill)).toNat < 2 ^ 32 := by
      rw [hL, window_toNat]
      omega
    cases run with
    | stop test _ => simp [tested] at test
    | trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
    | exit _ step =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd _ hfd hLsmall) fits
      | sys_return _ _ next => exact (hashNext_not_exited next).elim
    | next _ step rest =>
      rw [stepped] at step
      cases step with
      | sys_reject fits => exact absurd (fdRead_accepted fd _ hfd hLsmall) fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        beta_reduce at next
        obtain ⟨-, bytes, count, rfl, hbytes⟩ := read_reply permitted
        rw [hL, window_toNat] at hbytes
        rw [hL]
        by_cases zero : errno = 0
        · subst zero
          rw [sysReply_zero] at next
          dsimp only at next
          rw [fill_ok, hfirst, hL, reply_bytes] at next
          generalize hused : Min.min ((⟨0, [bytes, count]⟩ : Reply).word 1) (window done) = used
            at next
          have hret : returned (window done) [bytes, count] =
              bytes.data.data.toList.take used.toNat := by
            rw [returned_eq, hused]
          have husedle : used.toNat ≤ 65536 - fill.toNat := by
            have := min_toNat_le ((⟨0, [bytes, count]⟩ : Reply).word 1) (window done)
            rw [hused, window_toNat] at this
            omega
          have hfit : fill.toNat + bytes.data.size ≤ 65536 := by rw [hbytes]; omega
          by_cases empty : used = 0
          · subst empty
            rw [hashNext_eof] at next
            obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
            have hs'' := Outcome.returned.inj hs'
            subst hs''
            obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
            refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
            cases e
            refine ⟨[], .eof, ?_, by simpa using hs.keep hfit, rfl⟩
            exact .eof (by rw [hret]; simp)
          · have hpos : 0 < used.toNat := by
              rcases Nat.eq_zero_or_pos used.toNat with h0 | h0
              · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) empty
              · exact h0
            have hc : used.toNat ≤ bytes.data.size := by omega
            have hne : returned (window done) [bytes, count] ≠ [] := by
              rw [hret]
              exact List.ne_nil_of_length_pos (by rw [List.length_take, toList_length]; omega)
            have hsmall : done.length + used.toNat < 2 ^ 61 := by omega
            have hmore : (done ++ bytes.data.data.toList.take used.toNat).length +
                65536 * remaining < 2 ^ 61 := by simp; omega
            by_cases full : fill + used = chunk
            · have hfull : fill.toNat + used.toNat = 65536 := by
                have := congrArg UInt64.toNat full
                rw [UInt64.toNat_add] at this
                have hchunk : chunk.toNat = 65536 := rfl
                omega
              rw [hashNext_full _ empty full] at next
              obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
              have hs'' := Outcome.returned.inj hs'
              subst hs''
              obtain ⟨noExit, results⟩ := hash_loop tested stepped hfd remaining (index + 1) _ _ _ _
                _ (hs.full hfit hc hfull hsmall) hmore rest
              refine ⟨noExit, fun s e => ?_⟩
              obtain ⟨more, ending, reads, hashed, code⟩ := results s e
              refine ⟨returned (window done) [bytes, count] ++ more, ending, ?_, ?_, code⟩
              · exact .more hne (by rw [hret]; exact reads)
              · rw [hret, ← List.append_assoc]
                exact hashed
            · have hpart : fill.toNat + used.toNat < 65536 := by
                have hne' : (fill + used).toNat ≠ chunk.toNat := fun e => full (UInt64.toNat_inj.mp e)
                rw [UInt64.toNat_add] at hne'
                have hchunk : chunk.toNat = 65536 := rfl
                omega
              rw [hashNext_part _ empty full] at next
              obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
              have hs'' := Outcome.returned.inj hs'
              subst hs''
              obtain ⟨noExit, results⟩ := hash_loop tested stepped hfd remaining (index + 1) _ _ _ _
                _ (hs.part hfit hc hpart hsmall) hmore rest
              refine ⟨noExit, fun s e => ?_⟩
              obtain ⟨more, ending, reads, hashed, code⟩ := results s e
              refine ⟨returned (window done) [bytes, count] ++ more, ending, ?_, ?_, code⟩
              · exact .more hne (by rw [hret]; exact reads)
              · rw [hret, ← List.append_assoc]
                exact hashed
        · rw [sysReply_errno, fill_failed zero, hfirst, hsecond, hashNext_failed _ zero] at next
          obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
          have hs'' := Outcome.returned.inj hs'
          subst hs''
          obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
          refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
          cases e
          refine ⟨[], .failed errno, .failed zero, ?_, rfl⟩
          simpa using hs.keep (by rw [Bytes.zeros_size]; omega)

theorem fileReads_eq : fileReads.toNat = 35184372088831 := rfl

/-- A run of `hashFile` on `fd` with a read buffer of 65,536 bytes never exits, and when it
returns, it made the reads of `FileReads` within `2^45 - 1` reads, its digest is the
implementation's SHA-256 of the bytes that they returned, it records how they ended, and it
returns a read buffer of 65,536 bytes. -/
theorem hashFile_run {World : Type} {host : Host World} {fd : UInt64} (hfd : fd.toNat < 2 ^ 32)
    {buffer : Bytes} (hsize : buffer.data.size = 65536) {world final : World}
    {trace : List Event} {outcome : Outcome (Words4 × UInt64 × Bytes)}
    (run : Exec host (hashFile ⟨fd⟩ buffer) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧
      ∀ r, outcome = .returned r → ∃ bytes ending,
        FileReads fd 35184372088831 [] trace bytes ending ∧ bytes.length < 2 ^ 61 ∧
        r.1.bytes 32 = SHS.SHA256.Impl.sha256 (bytesOf bytes).data ∧
        r.2.1 = endCode ending ∧ r.2.2.data.size = 65536 := by
  unfold hashFile at run
  obtain ⟨after, first, middle, rest, loopRun, cont, rfl⟩ := Exec.unbind _ run
  cases loopRun with
  | loop loopRun =>
  rw [fileReads_eq] at loopRun
  obtain ⟨noExit, results⟩ := hash_loop (fun _ _ => rfl) (fun _ _ => rfl) hfd _ 0 _ _ _ _ []
    (hashed_init hsize) (by norm_num) loopRun
  cases middle with
  | exited c => exact absurd rfl (noExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | returned s =>
    obtain ⟨more, ending, reads, hashed, code⟩ := results s rfl
    obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape cont
    refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
    cases e
    simp only [List.nil_append] at hashed
    exact ⟨more, ending, by simpa using reads, hashed.small, hashed_finish hashed, code,
      hashed.size⟩


/-! ## The manifest -/

/-- The state of `readManifest`'s loop: the manifest's buffer, the bytes read, and how the reads
ended. -/
abbrev ManifestState := Bytes × UInt64 × UInt64

/-- The state of `readManifest`'s loop after a read whose fill is `got`, from the state `s`. -/
def manifestNext (s : ManifestState) (got : FillResult) : Action ManifestState :=
  if got.errno != 0 then .pure (got.buffer, s.2.1, got.errno)
  else if got.count == 0 then .pure (got.buffer, s.2.1, 1)
  else .pure (got.buffer, s.2.1 + got.count, 0)

/-- A step of `readManifest`'s loop on the descriptor `fd` for a manifest of `size` bytes, written
out. -/
def ManifestStep (fd size : UInt64) (step : UInt64 → ManifestState → Action ManifestState) :
    Prop :=
  ∀ i (s : ManifestState), step i s =
    .sys .fdRead [.word fd, .space (s.1.windowLength s.2.1 (size - s.2.1))] fun reply =>
      manifestNext s (FillResult.of s.1 s.2.1 (size - s.2.1) reply.errno
        (Min.min (reply.word 1) (s.1.windowLength s.2.1 (size - s.2.1))) (reply.bytes 0))

theorem manifestNext_not_exited {World : Type} {host : Host World} {s : ManifestState}
    {got : FillResult} {world final : World} {trace : List Event} {code : UInt64}
    (run : Exec host (manifestNext s got) world trace (.exited code) final) : False := by
  unfold manifestNext at run
  split at run
  · cases run
  · split at run <;> cases run

theorem manifestNext_failed (s : ManifestState) {errno : UInt64} (nonzero : errno ≠ 0)
    (count : UInt64) (buffer : Bytes) :
    manifestNext s ⟨errno, count, buffer⟩ = .pure (buffer, s.2.1, errno) := by
  simp [manifestNext, nonzero]

theorem manifestNext_eof (s : ManifestState) (buffer : Bytes) :
    manifestNext s ⟨0, 0, buffer⟩ = .pure (buffer, s.2.1, 1) := by
  simp [manifestNext]

theorem manifestNext_more (s : ManifestState) {count : UInt64} (nonzero : count ≠ 0)
    (buffer : Bytes) :
    manifestNext s ⟨0, count, buffer⟩ = .pure (buffer, s.2.1 + count, 0) := by
  simp [manifestNext, nonzero]

/-- The window of a read of the manifest: the bytes of its buffer after those already read. -/
theorem manifest_window {m : Bytes} {held size : UInt64} (hm : m.data.size = size.toNat)
    (hlt : held.toNat < size.toNat) :
    m.windowLength held (size - held) = UInt64.ofNat (size.toNat - held.toNat) ∧
      (m.window held (size - held)).1 = held.toNat ∧
      (m.window held (size - held)).2 = size.toNat - held.toNat := by
  have hc : (size - held).toNat = size.toNat - held.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  refine ⟨?_, ?_, ?_⟩
  · unfold Bytes.windowLength
    rw [Bytes.window_snd, hc, hm]
    congr 1
    omega
  · rw [Bytes.window_fst, hm]
    omega
  · rw [Bytes.window_snd, hc, hm]
    omega

/-- The loop of `readManifest` on `fd` for a manifest of `size` bytes, from a buffer of that size
whose first bytes are those already read, `got`, with a pass for each byte that remains, never
exits, and when it returns it made the reads of `ManifestReads`, records their status, an errno or
at most 76, and, with status 0, holds the bytes that they returned. -/
theorem manifest_loop {World : Type} {host : Host World} {fd size : UInt64}
    {test : UInt64 → ManifestState → Bool} {step : UInt64 → ManifestState → Action ManifestState}
    (tested : ∀ i s, test i s = (s.2.2 == 0 && decide (s.2.1 < size)))
    (stepped : ManifestStep fd size step) (hfd : fd.toNat < 2 ^ 32)
    (hsize : size.toNat < 2 ^ 32) :
    ∀ (remaining index : Nat) (m : Bytes) (held : UInt64) (got : List UInt8)
      {world : World} {trace : List Event} {outcome : Outcome ManifestState} {final : World},
      m.data.size = size.toNat → held.toNat = got.length → got.length ≤ size.toNat →
      m.data.data.toList.take held.toNat = got → size.toNat - got.length ≤ remaining →
      LoopExec host remaining index (m, held, 0) test step .pure world trace outcome final →
      (∀ c, outcome ≠ .exited c) ∧ ∀ s, outcome = .returned s → ∃ bytes,
        ManifestReads fd size.toNat got trace bytes s.2.2 ∧ s.2.2.toNat ≤ 76 ∧
        (s.2.2 = 0 → s.1.data.data.toList = bytes)
  | 0, _, m, held, got, _, _, _, _, hm, hheld, hle, htake, hrem, run => by
    cases run with
    | zero next =>
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
      cases e
      refine ⟨got, .full (by omega), Nat.zero_le _, fun _ => ?_⟩
      rw [← htake, List.take_of_length_le (by simp; omega)]
  | remaining + 1, index, m, held, got, _, _, _, _, hm, hheld, hle, htake, hrem, run => by
    cases run with
    | stop test next =>
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      have hge : size ≤ held := by simpa [tested] using test
      have hge' := UInt64.le_iff_toNat_le.mp hge
      refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
      cases e
      refine ⟨got, .full (by omega), Nat.zero_le _, fun _ => ?_⟩
      rw [← htake, List.take_of_length_le (by simp; omega)]
    | trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
    | exit test step =>
      have hlt : held < size := by simpa [tested] using test
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      obtain ⟨hL, -, -⟩ := manifest_window hm hlt'
      rw [stepped] at step
      cases step with
      | sys_reject fits =>
        exact absurd (fdRead_accepted fd _ hfd (by rw [hL, toNat_ofNat (by omega)]; omega)) fits
      | sys_return _ _ next => exact (manifestNext_not_exited next).elim
    | next test step rest =>
      have hlt : held < size := by simpa [tested] using test
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      obtain ⟨hL, hfirst, hsecond⟩ := manifest_window hm hlt'
      rw [stepped] at step
      cases step with
      | sys_reject fits =>
        exact absurd (fdRead_accepted fd _ hfd (by rw [hL, toNat_ofNat (by omega)]; omega)) fits
      | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
        beta_reduce at next
        obtain ⟨valid, bytes, count, rfl, hbytes⟩ := read_reply permitted
        rw [hL, toNat_ofNat (by omega)] at hbytes
        rw [hL, hheld]
        have hleft : got.length < size.toNat := by omega
        by_cases zero : errno = 0
        · subst zero
          rw [sysReply_zero] at next
          dsimp only at next
          rw [fill_ok, hfirst, hL, reply_bytes, hheld] at next
          generalize hused : Min.min ((⟨0, [bytes, count]⟩ : Reply).word 1)
            (UInt64.ofNat (size.toNat - got.length)) = used at next
          have hret : returned (UInt64.ofNat (size.toNat - got.length)) [bytes, count] =
              bytes.data.data.toList.take used.toNat := by
            rw [returned_eq, hused]
          have husedle : used.toNat ≤ size.toNat - got.length := by
            have := min_toNat_le ((⟨0, [bytes, count]⟩ : Reply).word 1)
              (UInt64.ofNat (size.toNat - got.length))
            rw [hused, toNat_ofNat (by omega)] at this
            exact this
          have hfit : got.length + bytes.data.size ≤ m.data.size := by rw [hbytes, hm]; omega
          by_cases empty : used = 0
          · subst empty
            rw [manifestNext_eof] at next
            obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
            have hs'' := Outcome.returned.inj hs'
            subst hs''
            obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
            refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
            cases e
            exact ⟨got, .short hleft (by rw [hret]; simp), by simp, fun h => absurd h (by simp)⟩
          · have hpos : 0 < used.toNat := by
              rcases Nat.eq_zero_or_pos used.toNat with h0 | h0
              · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) empty
              · exact h0
            have hc : used.toNat ≤ bytes.data.size := by omega
            have hne : returned (UInt64.ofNat (size.toNat - got.length)) [bytes, count] ≠ [] := by
              rw [hret]
              exact List.ne_nil_of_length_pos (by rw [List.length_take, toList_length]; omega)
            rw [manifestNext_more _ empty] at next
            obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
            have hs'' := Outcome.returned.inj hs'
            subst hs''
            have hsum : (held + used).toNat = got.length + used.toNat := by
              rw [UInt64.toNat_add, hheld]
              omega
            obtain ⟨noExit, results⟩ := manifest_loop tested stepped hfd hsize remaining
              (index + 1) (m.splice got.length bytes) (held + used)
              (got ++ bytes.data.data.toList.take used.toNat)
              ((Bytes.splice_size hfit).trans hm) (by rw [hsum]; simp; omega) (by simp; omega)
              (by rw [hsum, splice_take hfit hc, ← hheld, htake]) (by simp; omega) rest
            refine ⟨noExit, fun s e => ?_⟩
            obtain ⟨bytes', reads, small, held'⟩ := results s e
            refine ⟨bytes', ?_, small, held'⟩
            exact .more hleft hne (by rw [hret]; exact reads)
        · rw [sysReply_errno, fill_failed zero, manifestNext_failed _ zero] at next
          obtain ⟨rfl, hs', -⟩ := Verified.Wasi.exec_pure_shape next
          have hs'' := Outcome.returned.inj hs'
          subst hs''
          obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested, zero]) rest
          refine ⟨(fun _ e => nomatch e), fun s e => ?_⟩
          cases e
          exact ⟨got, .failed hleft zero, valid, fun h => absurd h zero⟩

/-- Reads that end with status 0 fill the buffer. -/
theorem ManifestReads.full_length {fd : UInt64} {size : Nat} {held : List UInt8}
    {events : List Event} {bytes : List UInt8} {status : UInt64}
    (h : ManifestReads fd size held events bytes status) : status = 0 → bytes.length = size := by
  induction h with
  | full filled => exact fun _ => filled
  | short => exact fun e => absurd e (by decide)
  | failed _ nonzero => exact fun e => absurd e nonzero
  | more _ _ _ ih => exact ih

/-- The window of the last read of the manifest, the whole read buffer. -/
theorem probe_window (buffer : Bytes) (hsize : buffer.data.size = 65536) :
    buffer.windowLength 0 chunk = 65536 ∧ (buffer.window 0 chunk).1 = 0 ∧
      (buffer.window 0 chunk).2 = 65536 := by
  have hc : chunk.toNat = 65536 := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold Bytes.windowLength
    rw [Bytes.window_snd, hc, hsize]
    rfl
  · rw [Bytes.window_fst, hsize]
    rfl
  · rw [Bytes.window_snd, hc, hsize]
    rfl

/-- A run of `readBytes` on `fd` for a manifest of the size `size` that a reply of
`fd_filestat_get` reported, below `2^32`, with a read buffer of 65,536 bytes, never exits, and when
it returns, the call of `fd_filestat_get` followed by its events are those of `ManifestBody`, its
status is that of `ManifestBody`, at most 76, with status 0 its bytes are the manifest's, and its
read buffer holds 65,536 bytes. -/
theorem readBytes_run {World : Type} {host : Host World} {fd size : UInt64}
    (hfd : fd.toNat < 2 ^ 32) (hsize : size.toNat < 2 ^ 32) {outputs : List Bytes}
    (hstat : statSize outputs = size) {buffer : Bytes} (hbuffer : buffer.data.size = 65536)
    {world final : World} {trace : List Event} {outcome : Outcome (UInt64 × Bytes × Bytes)}
    (run : Exec host (readBytes ⟨fd⟩ size buffer) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → ∃ bytes,
      ManifestBody fd (statEvent fd 0 outputs :: trace) r.1 bytes ∧ r.1.toNat ≤ 76 ∧
      (r.1 = 0 → r.2.1.data.data.toList = bytes ∧ bytes.length < 2 ^ 32) ∧
      r.2.2.data.size = 65536 := by
  subst hstat
  unfold readBytes at run
  obtain ⟨after, first, middle, rest, loopRun, cont, rfl⟩ := Exec.unbind _ run
  cases loopRun with
  | loop loopRun =>
  obtain ⟨noExit, results⟩ := manifest_loop (fd := fd) (size := statSize outputs)
    (fun _ _ => rfl) (fun _ _ => rfl) hfd hsize _ 0 _ 0 [] (by rw [build_size]) rfl
    (by simp) (by simp) (by simp) loopRun
  cases middle with
  | exited c => exact absurd rfl (noExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | returned s =>
    obtain ⟨bytes, reads, svalid, sbytes⟩ := results s rfl
    change Exec host (if s.2.2 != 0 then _ else _) after rest outcome final at cont
    split at cont
    · rename_i stopped
      have hne : s.2.2 ≠ 0 := by simpa using stopped
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape cont
      refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
      cases e
      rw [List.append_nil]
      exact ⟨[], .stopped hsize reads hne, svalid, fun h => absurd h hne, hbuffer⟩
    · rename_i full
      have hz : s.2.2 = 0 := by simpa using full
      have hfull := sbytes hz
      rw [hz] at reads
      have hlen : bytes.length = (statSize outputs).toNat := reads.full_length rfl
      obtain ⟨hL, hfirst, hsecond⟩ := probe_window _ hbuffer
      cases cont with
      | sys_reject fits =>
        exact absurd (fdRead_accepted fd _ hfd (by rw [hL]; decide)) fits
      | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
      | @sys_return _ _ _ _ _ _ _ _ _ errno' committed' _ permitted' next' =>
        beta_reduce at next'
        simp only [Action.bind] at next'
        obtain ⟨valid', pb, pc, rfl, hpb⟩ := read_reply permitted'
        rw [hL] at hpb
        simp only [UInt64.reduceToNat] at hpb
        by_cases zero' : errno' = 0
        · subst zero'
          rw [sysReply_zero] at next'
          dsimp only at next'
          rw [fill_ok, hfirst, hL, reply_bytes] at next'
          generalize hused : Min.min ((⟨0, [pb, pc]⟩ : Reply).word 1) 65536 = used at next'
          have hret : returned 65536 [pb, pc] = pb.data.data.toList.take used.toNat := by
            rw [returned_eq, hused]
          have hspliced : (buffer.splice 0 pb).data.size = 65536 :=
            (Bytes.splice_size (by rw [hpb, hbuffer])).trans hbuffer
          rw [hL]
          split at next'
          · rename_i bad
            simp at bad
          · split at next'
            · rename_i more
              have hu : used ≠ 0 := by simpa using more
              obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next'
              refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
              cases e
              have hpos : 0 < used.toNat := by
                rcases Nat.eq_zero_or_pos used.toNat with h0 | h0
                · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hu
                · exact h0
              have husedle : used.toNat ≤ 65536 := by
                have := min_toNat_le ((⟨0, [pb, pc]⟩ : Reply).word 1) 65536
                rw [hused] at this
                exact this
              have hret' : returned 65536 [pb, pc] ≠ [] := by
                rw [hret]
                exact List.ne_nil_of_length_pos
                  (by rw [List.length_take, toList_length, hpb]; omega)
              have hp := ManifestBody.probed (fd := fd) (errno := 0) (last := [pb, pc])
                hsize reads
              rw [ite_eq_right (by decide), ite_eq_left hret'] at hp
              exact ⟨bytes, hp, by simp, fun h => absurd h (by simp), hspliced⟩
            · rename_i none
              have hu : used = 0 := by simpa using none
              obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next'
              refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
              cases e
              have hret' : returned 65536 [pb, pc] = [] := by
                rw [hret, hu]
                simp
              have hp := ManifestBody.probed (fd := fd) (errno := 0) (last := [pb, pc])
                hsize reads
              rw [ite_eq_right (by decide), ite_eq_right (by simpa using hret')] at hp
              exact ⟨bytes, hp, by simp, fun _ => ⟨hfull, by omega⟩, hspliced⟩
        · rw [sysReply_errno, fill_failed zero'] at next'
          rw [hL]
          split at next'
          · obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next'
            refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
            cases e
            have hp := ManifestBody.probed (fd := fd) (errno := errno') (last := [pb, pc])
              hsize reads
            rw [ite_eq_left zero'] at hp
            refine ⟨bytes, hp, valid', fun h => absurd h zero', ?_⟩
            rw [hfirst, hsecond]
            exact (Bytes.splice_size (by rw [Bytes.zeros_size, hbuffer])).trans hbuffer
          · rename_i bad
            simp [zero'] at bad

/-- A run of `readManifest` on `fd` with a read buffer of 65,536 bytes never exits, and when it
returns, its events are those of `ManifestBody`, its status is that of `ManifestBody`, at most 76,
with status 0 its bytes are the manifest's, and its read buffer holds 65,536 bytes. -/
theorem readManifest_run {World : Type} {host : Host World} {fd : UInt64}
    (hfd : fd.toNat < 2 ^ 32) {buffer : Bytes} (hbuffer : buffer.data.size = 65536)
    {world final : World} {trace : List Event} {outcome : Outcome (UInt64 × Bytes × Bytes)}
    (run : Exec host (readManifest ⟨fd⟩ buffer) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → ∃ bytes,
      ManifestBody fd trace r.1 bytes ∧ r.1.toNat ≤ 76 ∧
      (r.1 = 0 → r.2.1.data.data.toList = bytes ∧ bytes.length < 2 ^ 32) ∧
      r.2.2.data.size = 65536 := by
  unfold readManifest at run
  cases run with
  | sys_reject fits => exact absurd (fdFilestatGet_accepted fd hfd) fits
  | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
    have valid : errno.toNat ≤ 76 := (host.sys_bound permitted).2
    beta_reduce at next
    simp only [Action.bind] at next
    split at next
    · rename_i nonzero
      have hne : errno ≠ 0 := by simpa [sysReply] using nonzero
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
      cases e
      exact ⟨[], .statFailed hne, valid, fun h => absurd h hne, hbuffer⟩
    · rename_i zero
      have hz : errno = 0 := by simpa [sysReply] using zero
      subst hz
      split at next
      · rename_i large
        obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
        refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
        cases e
        exact ⟨[], .tooLarge (UInt64.le_iff_toNat_le.mp large), by simp,
          fun h => absurd h (by simp), hbuffer⟩
      · rename_i small
        exact readBytes_run hfd (UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp small)) rfl hbuffer
          next

/-! ## Brackets -/

/-- The events and the result of a run of `withOpen` under descriptor 3 with the flag
`symlink_follow`, the rights `rights`, an error continuation that returns `fallback errno`, and a
body that never exits: the open's event, and, when it returned errno 0, the body's events and the
close's event. -/
theorem withOpen_run {World α : Type} {host : Host World} {name : Bytes} {rights : UInt64}
    (hname : name.data.size < 2 ^ 32) (hr : rights = 2 ∨ rights = 2097154)
    {fallback : UInt64 → α} {body : Handle → Action α} {world final : World}
    {trace : List Event} {outcome : Outcome (α × UInt64)}
    (bodyNoExit : ∀ (fd : UInt64) w t (o : Outcome α) f, fd.toNat < 2 ^ 32 →
      Exec host (body ⟨fd⟩) w t o f → ∀ c, o ≠ .exited c)
    (run : Exec host
      (withOpen .preopened 1 name 0 rights 0 0 (fun errno => pure (fallback errno)) body)
      world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → ∃ errno outputs,
      (errno ≠ 0 ∧ errno.toNat ≤ 76 ∧ trace = [.sys .pathOpen [.word 3, .word 1, .bytes name,
        .word 0, .word rights, .word 0, .word 0] (.returned errno outputs)] ∧
        r = (fallback errno, 0)) ∨
      (errno = 0 ∧ (openedDescriptor outputs).toNat < 2 ^ 32 ∧ ∃ events after closing closeErrno
          committed, closeErrno.toNat ≤ 76 ∧ trace = .sys .pathOpen [.word 3, .word 1, .bytes name, .word 0, .word rights,
            .word 0, .word 0] (.returned 0 outputs) :: events ++
            [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)] ∧
        Exec host (body ⟨openedDescriptor outputs⟩) after events (.returned r.1) closing ∧
        r.2 = closeErrno) := by
  unfold withOpen at run
  cases run with
  | sys_reject fits => exact absurd (pathOpen_accepted name hname rights hr) fits
  | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | @sys_return _ _ _ _ _ _ _ _ _ errno committed _ permitted next =>
    by_cases zero : errno = 0
    · subst zero
      have small := Verified.Wasi.openedDescriptor_lt rfl ⟨_, (host.sys_bound permitted).1⟩
      have hReply : sysReply 0 committed = ⟨0, committed⟩ := rfl
      simp only [hReply, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at next
      obtain ⟨closing, first, middle, rest, bodyRun, closeRun, rfl⟩ := Exec.unbind _ next
      have noExit := bodyNoExit _ _ _ _ _ small bodyRun
      cases middle with
      | exited c => exact absurd rfl (noExit c)
      | trapped m =>
        obtain ⟨-, rfl, -⟩ := closeRun
        exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
      | returned value =>
        simp only [Continue] at closeRun
        cases closeRun with
        | sys_reject fits => exact absurd (fdClose_accepted _ small) fits
        | sys_trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
        | @sys_return _ _ _ _ _ _ _ _ _ closeErrno closeCommitted _ closePermitted last =>
          obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape last
          refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
          cases e
          exact ⟨0, committed, .inr ⟨rfl, small, first, _, _, closeErrno, closeCommitted,
            (host.sys_bound closePermitted).2, rfl, bodyRun, rfl⟩⟩
    · have hReply : sysReply errno committed = ⟨errno, []⟩ := by simp [sysReply, zero]
      have off : ((errno != 0) = true) = True := eq_true (bne_iff_ne.mpr zero)
      simp only [hReply, off, ↓reduceIte] at next
      have hpure : Action.bind (pure (fallback errno))
          (fun result => Action.pure (result, (0 : UInt64))) = Action.pure (fallback errno, 0) :=
        rfl
      rw [hpure] at next
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      refine ⟨(fun _ e => nomatch e), fun r e => ?_⟩
      cases e
      exact ⟨errno, committed, .inl ⟨zero, (host.sys_bound permitted).2, rfl, rfl⟩⟩


/-! ## Checks of lines -/

theorem openArgs_bytes (rights : UInt64) (name : Bytes) :
    openArgs rights name.data.data.toList =
      [.word 3, .word 1, .bytes name, .word 0, .word rights, .word 0, .word 0] := by
  rw [openArgs, bytesOf_toList]

/-- A run of the check of one file, `withOpen` around `hashFile` with a read buffer of 65,536
bytes, never exits, and when it returns, its read buffer holds 65,536 bytes, and it made the
open's event and, after an open that returned errno 0, the reads of `FileReads` and the close's
event, with the digest and the ending of `hashFile_run`. -/
theorem checkFile_run {World : Type} {host : Host World} {name : Bytes}
    (hname : name.data.size < 2 ^ 32) {buffer : Bytes} (hsize : buffer.data.size = 65536)
    {world final : World} {trace : List Event}
    {outcome : Outcome ((Words4 × UInt64 × Bytes) × UInt64)}
    (run : Exec host (withOpen .preopened 1 name 0 2 0 0
      (fun _ => pure ((⟨0, 0, 0, 0⟩ : Words4), (0 : UInt64), buffer))
      fun file => hashFile file buffer) world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → r.1.2.2.data.size = 65536 ∧
      ∃ errno outputs,
      (errno ≠ 0 ∧ trace = [.sys .pathOpen (openArgs fileRights name.data.data.toList)
        (.returned errno outputs)] ∧ r.1.2.1 = 0) ∨
      (errno = 0 ∧ ∃ events bytes ending closeErrno committed,
        trace = .sys .pathOpen (openArgs fileRights name.data.data.toList) (.returned 0 outputs) ::
          events ++
            [.sys .fdClose [.word (openedDescriptor outputs)] (.returned closeErrno committed)] ∧
        FileReads (openedDescriptor outputs) 35184372088831 [] events bytes ending ∧
        bytes.length < 2 ^ 61 ∧ r.1.1.bytes 32 = SHS.SHA256.Impl.sha256 (bytesOf bytes).data ∧
        r.1.2.1 = endCode ending ∧ r.2 = closeErrno) := by
  simp only [openArgs_bytes, fileRights]
  obtain ⟨noExit, results⟩ := withOpen_run (rights := 2)
    (fallback := fun _ => ((⟨0, 0, 0, 0⟩ : Words4), (0 : UInt64), buffer))
    (body := fun file => hashFile file buffer) hname (.inl rfl)
    (fun fd _ _ _ _ hfd bodyRun => (hashFile_run hfd hsize bodyRun).1) run
  refine ⟨noExit, fun r e => ?_⟩
  obtain ⟨errno, outputs, failed | opened⟩ := results r e
  · obtain ⟨hne, -, htrace, rfl⟩ := failed
    exact ⟨hsize, errno, outputs, .inl ⟨hne, htrace, rfl⟩⟩
  · obtain ⟨rfl, small, events, after, closing, closeErrno, committed, -, htrace, bodyRun,
      hclose⟩ := opened
    obtain ⟨-, hashed⟩ := hashFile_run small hsize bodyRun
    obtain ⟨bytes, ending, reads, hsmall, hdigest, hcode, hbuf⟩ := hashed r.1 rfl
    exact ⟨hbuf, 0, outputs, .inr ⟨rfl, events, bytes, ending, closeErrno, committed, htrace,
      reads, hsmall, hdigest, hcode, hclose⟩⟩

theorem getD_take_drop (l : List UInt8) (start len j : Nat) (hj : j < len) :
    ((l.drop start).take len).getD j 0 = l.getD (start + j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj,
    List.getElem?_drop]

/-- `hexMatchesSpec` from a position states that the line from that position has the hex digits of
the digest's bytes. -/
theorem hexMatchesSpec_iff (m : Bytes) (start len : Nat) (hlen : 64 ≤ len) (hs : start < 2 ^ 64)
    (d : Words4) :
    hexMatchesSpec (m, UInt64.ofNat start, d) = true ↔
      HexDigits ((m.data.data.toList.drop start).take len) (d.bytes 32) := by
  unfold hexMatchesSpec HexDigits
  dsimp only
  rw [List.all_eq_true, toNat_ofNat hs]
  constructor
  · intro h k hk
    have := h k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    rw [getD_take_drop _ _ _ _ (by omega), getD_take_drop _ _ _ _ (by omega),
      ← getElem!_pos (d.bytes 32) k hk]
    exact this
  · intro h k hk
    have hk' := List.mem_range.mp hk
    obtain ⟨h1, h2⟩ := h k hk'
    rw [getD_take_drop _ _ _ _ (by omega)] at h1
    rw [getD_take_drop _ _ _ _ (by omega), ← Nat.add_assoc] at h2
    rw [getElem!_pos (d.bytes 32) k hk']
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨h1, h2⟩

/-- The hex digits give the digest of FIPS 180-4 of the bytes exactly when they give the
implementation's digest bytes, since distinct digests have distinct bits. -/
theorem digestOf_iff (line bytes : List UInt8) (hsmall : bytes.length < 2 ^ 61) :
    DigestOf line bytes ↔ HexDigits line (SHS.SHA256.Impl.sha256 (bytesOf bytes).data) := by
  constructor
  · rintro ⟨d, small, hd, hbits⟩
    rw [← SHS.Equiv.SHA256.sha256_correct _ small] at hbits
    rwa [digestBitVec_inj _ _ hbits] at hd
  · intro h
    exact ⟨_, hsmall, h, SHS.Equiv.SHA256.sha256_correct (bytesOf bytes).data hsmall⟩

theorem endCode_eof (ending : Ending) : (endCode ending == 1) = decide (ending = .eof) := by
  cases ending <;> simp [endCode]

/-- The name that the check of the line of `m` from position `start` to position `stop`, a line in
the format, copies with `slice`: the line's bytes after its first 66, fewer than `2^32` of them. -/
theorem entry_name (m : Bytes) (hm : m.data.size < 2 ^ 32) (start stop : Nat) (hss : start ≤ stop)
    (hstop : stop ≤ m.data.size)
    (hline : WellFormed ((m.data.data.toList.drop start).take (stop - start))) :
    (slice m (UInt64.ofNat start + 66)
        (UInt64.ofNat stop - UInt64.ofNat start - 66)).data.data.toList =
      ((m.data.data.toList.drop start).take (stop - start)).drop 66 ∧
    (slice m (UInt64.ofNat start + 66)
        (UInt64.ofNat stop - UInt64.ofNat start - 66)).data.size < 2 ^ 32 := by
  have hlen : 67 ≤ stop - start := by
    have := hline.1
    simp only [List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data] at this
    omega
  have hs66 : UInt64.ofNat start + 66 = UInt64.ofNat (start + 66) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, toNat_ofNat (by omega), toNat_ofNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have hcount : UInt64.ofNat stop - UInt64.ofNat start - 66 =
      UInt64.ofNat (stop - start - 66) := by
    apply UInt64.toNat_inj.mp
    have h1 : (UInt64.ofNat stop - UInt64.ofNat start).toNat = stop - start := by
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_ofNat (by omega), toNat_ofNat (by omega)]; omega),
        toNat_ofNat (by omega), toNat_ofNat (by omega)]
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1]; simp; omega), h1,
      toNat_ofNat (by omega)]
    simp
  rw [hs66, hcount]
  have hname : (slice m (UInt64.ofNat (start + 66))
      (UInt64.ofNat (stop - start - 66))).data.data.toList =
      ((m.data.data.toList.drop start).take (stop - start)).drop 66 := by
    rw [slice_toList m _ _ (by omega) (by omega), List.drop_take, List.drop_drop]
  refine ⟨hname, ?_⟩
  have := congrArg List.length hname
  simp only [Array.length_toList, ByteArray.size_data, List.length_drop, List.length_take]
    at this
  omega

/-- The check of the line of `m` from position `start` to position `stop`, a line in the format:
`withOpen` of the line's name around `hashFile` makes the events of `FileCheck` for the line, and
its verdict is the program's test of the reads, the close, and the digits. -/
theorem entry_check {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (start stop : Nat) (hss : start ≤ stop) (hstop : stop ≤ m.data.size)
    (hline : WellFormed ((m.data.data.toList.drop start).take (stop - start)))
    {buffer : Bytes} (hsize : buffer.data.size = 65536) {world final : World}
    {trace : List Event} {outcome : Outcome ((Words4 × UInt64 × Bytes) × UInt64)}
    (run : Exec host (withOpen .preopened 1
      (slice m (UInt64.ofNat start + 66) (UInt64.ofNat stop - UInt64.ofNat start - 66)) 0 2 0 0
      (fun _ => pure ((⟨0, 0, 0, 0⟩ : Words4), (0 : UInt64), buffer))
      fun file => hashFile file buffer) world trace outcome final) :
    (slice m (UInt64.ofNat start + 66)
        (UInt64.ofNat stop - UInt64.ofNat start - 66)).data.data.toList =
      ((m.data.data.toList.drop start).take (stop - start)).drop 66 ∧
    (∀ c, outcome ≠ .exited c) ∧ ∀ r, outcome = .returned r → r.1.2.2.data.size = 65536 ∧
      FileCheck (((m.data.data.toList.drop start).take (stop - start)).drop 66)
        ((m.data.data.toList.drop start).take (stop - start)) trace
        (r.1.2.1 == 1 && r.2 == 0 && hexMatches m (UInt64.ofNat start) r.1.1) := by
  have hlen : 67 ≤ stop - start := by
    have := hline.1
    simp only [List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data] at this
    omega
  obtain ⟨hname, hnsize⟩ := entry_name m hm start stop hss hstop hline
  obtain ⟨noExit, results⟩ := checkFile_run hnsize hsize run
  refine ⟨hname, noExit, fun r e => ?_⟩
  obtain ⟨hbuf, errno, outputs, failed | opened⟩ := results r e
  · obtain ⟨hne, htrace, hcode⟩ := failed
    refine ⟨hbuf, ?_⟩
    have hok : (r.1.2.1 == 1 && r.2 == 0 && hexMatches m (UInt64.ofNat start) r.1.1) = false := by
      rw [hcode]
      simp
    rw [htrace, hname, hok]
    exact .refused hne
  · obtain ⟨-, events, bytes, ending, closeErrno, committed, htrace, reads, hsmall, hdigest, hcode,
      hclose⟩ := opened
    refine ⟨hbuf, ?_⟩
    rw [htrace, hname]
    refine .opened reads ?_
    rw [Bool.and_eq_true, Bool.and_eq_true, hcode, endCode_eof, hclose,
      hexMatches_eq m _ _ (by omega),
      hexMatchesSpec_iff m start (stop - start) (by omega) (by omega), hdigest,
      digestOf_iff _ _ hsmall]
    simp only [decide_eq_true_eq, beq_iff_eq, and_assoc]

/-! ## The writes -/

/-- The writes of a run of the loop of `writeAll` offer at least one byte each and number at most
its passes, and a run that exits ends with the exit after them. -/
theorem WriteAllRun.shape {World : Type} {host : Host World} {bytes : List UInt8}
    {written : UInt64} {passes : Nat} {events : List Event} {outcome : Outcome UInt64}
    (run : WriteAllRun host bytes written passes events outcome) :
    (∀ v, outcome = .returned v → events.length ≤ passes ∧ ∀ e ∈ events, WroteSome e) ∧
    (∀ code, outcome = .exited code → ∃ writes, events = writes ++ [.exit code] ∧
      writes.length ≤ passes ∧ ∀ e ∈ writes, WroteSome e) := by
  induction run with
  | done _ => exact ⟨fun _ _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩, fun _ e => nomatch e⟩
  | spent _ => exact ⟨fun _ _ => ⟨Nat.zero_le _, fun _ h => nomatch h⟩, fun _ e => nomatch e⟩
  | @wrote written count passes offered events outcome left offers within rest ih =>
    have some : WroteSome (.write .stdout offered (.returned 0 count)) := by
      refine ⟨offered, _, rfl, fun e => ?_⟩
      have := congrArg List.length offers
      simp [e] at this
      omega
    refine ⟨fun v e => ?_, fun code e => ?_⟩
    · obtain ⟨hlen, hall⟩ := ih.1 v e
      refine ⟨by simp; omega, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact some
      · exact hall x hx
    · obtain ⟨writes, rfl, hlen, hall⟩ := ih.2 code e
      refine ⟨_ :: writes, rfl, by simp; omega, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact some
      · exact hall x hx
  | @failed written errno count passes offered events outcome left offers nonzero valid ended =>
    obtain ⟨_, _, ended⟩ := ended
    have some : WroteSome (.write .stdout offered (.returned errno count)) := by
      refine ⟨offered, _, rfl, fun e => ?_⟩
      have := congrArg List.length offers
      simp [e] at this
      omega
    refine ⟨fun v e => ?_, fun code e => ?_⟩
    · subst e
      cases ended
    · subst e
      cases ended with
      | exit _ =>
        refine ⟨[.write .stdout offered (.returned errno count)], rfl, by simp, fun x hx => ?_⟩
        rw [List.mem_singleton.mp hx]
        exact some
  | trapped _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩

/-- A run of `writeAll text 0 text.size` makes the writes of `LineWrites`: when it returns `v`,
those of `stalled` when `v` falls short of the text and of `all` otherwise, and when it exits,
those of `failed` with its status, followed by the exit. -/
theorem line_writes {World : Type} {host : Host World} {text : Bytes}
    (small : text.data.size < 2 ^ 32) {world final : World} {trace : List Event}
    {outcome : Outcome UInt64}
    (run : Exec host (writeAll text 0 text.size) world trace outcome final) :
    (∀ v, outcome = .returned v →
      LineWrites text.data.data.toList trace (if v < text.size then .stalled else .all)) ∧
    (∀ code, outcome = .exited code → ∃ writes, trace = writes ++ [.exit code] ∧
      LineWrites text.data.data.toList writes (.failed code)) := by
  have length : text.data.data.toList.length = text.data.size := by simp
  have wide : text.size.toNat = text.data.size := Bytes.size_toNat text (by omega)
  have wrun := writeAll_run_whole (by omega) run
  have facts := wrun.taken (by rw [length]; omega) (by simp)
  have shape := WriteAllRun.shape wrun
  refine ⟨fun v e => ?_, fun code e => ?_⟩
  · obtain ⟨all, -, high, taken, offered, counted⟩ := facts.1 v e
    obtain ⟨hlen, some⟩ := shape.1 v e
    simp only [UInt64.toNat_zero, List.drop_zero, Nat.sub_zero] at taken offered
    by_cases short : v < text.size
    · rw [ite_eq_left short]
      have below : v.toNat < text.data.size := by
        rw [UInt64.lt_iff_toNat_lt, wide] at short
        exact short
      refine ⟨offered, by omega, some, all, by rw [counted (by omega), length], ?_, ?_⟩
      · rw [taken]
        exact List.take_prefix _ _
      · rw [taken, List.length_take]
        omega
    · rw [ite_eq_right short]
      have above : text.data.size ≤ v.toNat := by
        rw [UInt64.lt_iff_toNat_lt, wide] at short
        omega
      refine ⟨offered, by omega, some, all, ?_⟩
      rw [taken, List.take_of_length_le (by omega)]
  · obtain ⟨nonzero, valid, ⟨before, offered, count, shapeEq, earlier, offeredBefore⟩, prefix_,
      bound⟩ := facts.2 code e
    obtain ⟨writes, hwrites, hlen, some⟩ := shape.2 code e
    have hw : writes = before ++ [.write .stdout offered (.returned code count)] := by
      rw [shapeEq] at hwrites
      have h2 : (before ++ [.write .stdout offered (.returned code count)]) ++ [.exit code] =
          writes ++ [.exit code] := by
        rw [List.append_assoc]
        exact hwrites
      exact (List.append_cancel_right h2).symm
    subst hw
    have dropped : stdoutTaken (before ++ [.write .stdout offered (.returned code count)]) =
        stdoutTaken trace := by
      rw [shapeEq]
      simp [stdoutTaken_append, Event.stdoutTaken, nonzero]
    simp only [UInt64.toNat_zero] at offeredBefore
    refine ⟨_, hwrites, offeredBefore, by omega, some, nonzero, valid,
      ⟨before, offered, count, rfl, earlier⟩, ?_, ?_⟩
    · rw [dropped]
      simpa using prefix_
    · rw [dropped]
      simp only [UInt64.toNat_zero, Nat.zero_add] at bound
      omega

/-! ## The lines -/

/-- Each line of `linesFrom s ps` lies in `m` at its position, when the pieces `ps` joined by
newlines are the bytes of `m` from `s`. -/
theorem linesFrom_pos (m : List UInt8) : ∀ (ps : List (List UInt8)) (s : Nat),
    m.drop s = [10].intercalate ps → ∀ l ∈ linesFrom s ps,
      (m.drop l.1).take l.2.length = l.2 ∧ l.1 + l.2.length ≤ m.length
  | [], _, _ => by simp [linesFrom]
  | p :: ps, s, hm => by
    intro l hl
    have hsplit : ∃ rest, m.drop s = p ++ rest := by
      cases ps with
      | nil => exact ⟨[], by simpa using hm⟩
      | cons q qs => exact ⟨_, by rw [hm, List.intercalate_cons_cons, List.append_assoc]⟩
    obtain ⟨rest, hrest⟩ := hsplit
    simp only [linesFrom, List.mem_append] at hl
    rcases hl with hl | hl
    · split at hl
      · simp at hl
      · rename_i hp
        simp only [List.mem_singleton] at hl
        subst hl
        have hlen : s + p.length ≤ m.length := by
          have := congrArg List.length hrest
          have hpos : 0 < p.length := List.length_pos_iff.mpr hp
          simp at this
          omega
        exact ⟨by rw [hrest, List.take_left' rfl], hlen⟩
    · cases ps with
      | nil => simp [linesFrom] at hl
      | cons q qs =>
        have hm' : m.drop (s + p.length + 1) = [10].intercalate (q :: qs) := by
          have hm2 := hm
          rw [List.intercalate_cons_cons] at hm2
          have key : (m.drop s).drop (p.length + 1) = m.drop (s + p.length + 1) := by
            rw [List.drop_drop]
            exact congrArg (List.drop · m) (by omega)
          rw [← key, hm2, List.drop_left' (by simp)]
        exact linesFrom_pos m (q :: qs) _ hm' l hl

theorem lines_pos (m : List UInt8) :
    ∀ l ∈ lines m, (m.drop l.1).take l.2.length = l.2 ∧ l.1 + l.2.length ≤ m.length :=
  linesFrom_pos m _ 0 (by rw [List.drop_zero, List.intercalate_splitOn])

theorem linesFrom_length (s : Nat) :
    ∀ ps : List (List UInt8), (linesFrom s ps).length ≤ ps.length
  | [] => by simp [linesFrom]
  | p :: ps => by
    have := linesFrom_length (s + p.length + 1) ps
    simp only [linesFrom, List.length_append, List.length_cons]
    split <;> simp <;> omega

theorem intercalate_length (ps : List (List UInt8)) :
    ps.length ≤ ([10].intercalate ps).length + 1 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    cases ps with
    | nil => simp
    | cons q qs =>
      rw [List.intercalate_cons_cons]
      simp only [List.length_append, List.length_cons] at ih ⊢
      omega

/-- A byte string has at most one line more than bytes. -/
theorem lines_length (m : List UInt8) : (lines m).length ≤ m.length + 1 := by
  have h1 := linesFrom_length 0 (m.splitOn 10)
  have h2 := intercalate_length (m.splitOn 10)
  rw [List.intercalate_splitOn] at h2
  unfold lines
  omega

theorem spanWords_get (ls : List (Nat × List UInt8)) :
    ∀ j (hj : j < ls.length),
      (spanWords ls)[2 * j]? = some (UInt64.ofNat ls[j].1) ∧
      (spanWords ls)[2 * j + 1]? = some (UInt64.ofNat (ls[j].1 + ls[j].2.length)) := by
  induction ls with
  | nil => intro j hj; simp at hj
  | cons l ls ih =>
    intro j hj
    cases j with
    | zero => simp [spanWords]
    | succ j =>
      obtain ⟨h1, h2⟩ := ih j (by simp at hj; omega)
      simp only [spanWords] at h1 h2 ⊢
      rw [List.flatMap_cons]
      simp only [show 2 * (j + 1) = 2 * j + 2 by omega,
        show 2 * j + 2 + 1 = 2 * j + 1 + 2 by omega, List.getElem?_cons_succ, List.cons_append,
        List.nil_append, List.getElem_cons_succ]
      exact ⟨h1, h2⟩

/-- A manifest that the pure core accepts gives the positions of its lines. -/
theorem parse_accepted (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2) :
    parse m = (spanWords (lines m.data.data.toList)).toArray := by
  rw [parse_eq m (by omega)]
  unfold parseSpec
  exact ite_eq_left accepted

/-- A manifest that the pure core refuses gives no position. -/
theorem parse_refused (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (refused : ¬ (lines m.data.data.toList ≠ [] ∧
      ∀ l ∈ lines m.data.data.toList, WellFormed l.2)) :
    parse m = #[] := by
  rw [parse_eq m (by omega)]
  unfold parseSpec
  exact ite_eq_right refused

/-- The positions of line `j` among the positions that `parse` gives. -/
theorem entry_get (ls : List (Nat × List UInt8)) (j : Nat) (hj : j < ls.length)
    (hsmall : ls.length ≤ 2 ^ 32) :
    (spanWords ls).toArray[(2 * UInt64.ofNat j).toNat]! = UInt64.ofNat ls[j].1 ∧
      (spanWords ls).toArray[(2 * UInt64.ofNat j + 1).toNat]! =
        UInt64.ofNat (ls[j].1 + ls[j].2.length) := by
  have h2 : (2 * UInt64.ofNat j).toNat = 2 * j := by
    rw [UInt64.toNat_mul, toNat_ofNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have h3 : (2 * UInt64.ofNat j + 1).toNat = 2 * j + 1 := by
    rw [UInt64.toNat_add, h2]
    simp only [UInt64.reduceToNat]
    omega
  have hs := spanWords_length ls
  obtain ⟨g1, g2⟩ := spanWords_get ls j hj
  obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.mp g1
  obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.mp g2
  refine ⟨?_, ?_⟩
  · rw [h2, getElem!_pos _ _ (by simp; omega), List.getElem_toArray]
    exact e1
  · rw [h3, getElem!_pos _ _ (by simp; omega), List.getElem_toArray]
    exact e2

/-! ## The loop of the checks -/

/-- The state of `checkLines`'s loop: the read buffer, 1 once a verdict was FAILED, and 1 once the
writes of an output line stalled. -/
abbrev CheckState := Bytes × UInt64 × UInt64

/-- The step of `checkLines`'s loop on the manifest `m` with the positions `entries`. -/
def checkStep (m : Bytes) (entries : Array UInt64) (j : UInt64) (s : CheckState) :
    Action CheckState := do
  let start := entries[(2 * j).toNat]!
  let stop := entries[(2 * j + 1).toNat]!
  let name := slice m (start + 66) (stop - start - 66)
  let checked ← withOpen .preopened 1 name 0 2 0 0
    (fun _ => pure ((⟨0, 0, 0, 0⟩ : Words4), (0 : UInt64), s.1)) fun file => hashFile file s.1
  let ok := checked.1.2.1 == 1 && checked.2 == 0 && hexMatches m start checked.1.1
  let line := render name ok
  let written ← writeAll line 0 line.size
  pure (checked.1.2.2, (if ok then s.2.1 else 1), (if written < line.size then 1 else 0))

/-- A step of `checkLines`'s loop on line `j` of a manifest that the pure core accepts: when it
returns, it made the events of `FileCheck` and the writes of the output line, its read buffer holds
65,536 bytes, and it records the verdict and whether the writes stalled; when it exits, the writes
of the output line failed. -/
theorem check_step {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    (j : Nat) (hj : j < (lines m.data.data.toList).length) {buffer : Bytes}
    (hsize : buffer.data.size = 65536) (failed : UInt64) {world final : World}
    {trace : List Event} {outcome : Outcome CheckState}
    (run : Exec host (checkStep m (parse m) (UInt64.ofNat j) (buffer, failed, 0)) world trace
      outcome final) :
    (∀ s, outcome = .returned s → ∃ ok fileEvents writes buffer' stalled,
      trace = fileEvents ++ writes ∧ s = (buffer', (if ok then failed else 1), stalled) ∧
      FileCheck ((lines m.data.data.toList)[j].2.drop 66) (lines m.data.data.toList)[j].2
        fileEvents ok ∧ buffer'.data.size = 65536 ∧
      ((stalled = 0 ∧ LineWrites (lineText ((lines m.data.data.toList)[j].2.drop 66) ok) writes
          .all) ∨
        (stalled = 1 ∧ LineWrites (lineText ((lines m.data.data.toList)[j].2.drop 66) ok) writes
          .stalled))) ∧
    (∀ code, outcome = .exited code → ∃ ok fileEvents writes,
      trace = fileEvents ++ writes ++ [.exit code] ∧
      FileCheck ((lines m.data.data.toList)[j].2.drop 66) (lines m.data.data.toList)[j].2
        fileEvents ok ∧
      LineWrites (lineText ((lines m.data.data.toList)[j].2.drop 66) ok) writes (.failed code)) := by
  have hlsmall := lines_length m.data.data.toList
  have hlenm : m.data.data.toList.length = m.data.size := by simp
  have hparse := parse_accepted m hm accepted
  generalize hls : lines m.data.data.toList = ls at accepted hj hlsmall hparse ⊢
  have hlmem : ls[j] ∈ ls := List.getElem_mem hj
  have hpos := lines_pos m.data.data.toList ls[j] (by rw [hls]; exact hlmem)
  obtain ⟨hstart, hstop⟩ := entry_get ls j hj (by omega)
  have hl : (m.data.data.toList.drop ls[j].1).take (ls[j].1 + ls[j].2.length - ls[j].1) =
      ls[j].2 := by
    rw [Nat.add_sub_cancel_left]
    exact hpos.1
  unfold checkStep at run
  rw [hparse, hstart, hstop] at run
  dsimp only at run
  obtain ⟨after, first, middle, rest, checkRun, cont, rfl⟩ := Exec.unbind _ run
  obtain ⟨hname, noExit, results⟩ := entry_check m hm ls[j].1 (ls[j].1 + ls[j].2.length)
    (by omega) (by omega) (by rw [hl]; exact accepted.2 _ hlmem) hsize checkRun
  rw [hl] at hname results
  generalize hn : slice m (UInt64.ofNat ls[j].1 + 66)
    (UInt64.ofNat (ls[j].1 + ls[j].2.length) - UInt64.ofNat ls[j].1 - 66) = name at hname cont
  have hnlen : name.data.size + 66 ≤ m.data.size := by
    have h1 : name.data.size = ls[j].2.length - 66 := by
      have := congrArg List.length hname
      rw [toList_length, List.length_drop] at this
      exact this
    have h2 := (accepted.2 _ hlmem).1
    have h3 := hpos.2
    omega
  cases middle with
  | exited c => exact absurd rfl (noExit c)
  | trapped msg =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | returned r =>
    obtain ⟨hbuf, check⟩ := results r rfl
    simp only [Continue] at cont
    generalize hok : (r.1.2.1 == 1 && r.2 == 0 && hexMatches m (UInt64.ofNat ls[j].1) r.1.1) = ok
      at check cont
    obtain ⟨after2, writes, wmid, rest2, writeRun, cont2, rfl⟩ := Exec.unbind _ cont
    have htext : (render name ok).data.data.toList = lineText (ls[j].2.drop 66) ok := by
      rw [render_eq name ok (by omega), lineText, ← hname, bytesOf_toList]
    have hrs : (render name ok).data.size < 2 ^ 32 := by
      have h1 : (render name ok).data.size = (name.size + if ok then 5 else 9).toNat := by
        unfold render
        exact build_size _ _
      have h2 : name.size.toNat = name.data.size := Bytes.size_toNat name (by omega)
      rw [h1, UInt64.toNat_add, h2]
      cases ok <;> simp <;> omega
    obtain ⟨wret, wexit⟩ := line_writes hrs writeRun
    rw [htext] at wret wexit
    cases wmid with
    | returned v =>
      have lw := wret v rfl
      simp only [Continue] at cont2
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape cont2
      refine ⟨fun s e => ?_, fun _ e => nomatch e⟩
      cases e
      refine ⟨ok, first, writes, r.1.2.2, _, by simp, rfl, check, hbuf, ?_⟩
      by_cases short : v < (render name ok).size
      · rw [ite_eq_left short] at lw
        exact .inr ⟨by simp [short], lw⟩
      · rw [ite_eq_right short] at lw
        exact .inl ⟨by simp [short], lw⟩
    | exited code =>
      simp only [Continue] at cont2
      obtain ⟨rfl, rfl, -⟩ := cont2
      refine ⟨(fun _ e => nomatch e), fun c e => ?_⟩
      cases e
      obtain ⟨ws, hws, lw⟩ := wexit code rfl
      exact ⟨ok, first, ws, by rw [hws]; simp, check, lw⟩
    | trapped msg =>
      simp only [Continue] at cont2
      obtain ⟨rfl, rfl, -⟩ := cont2
      exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩

/-- The loop of `checkLines` on a manifest that the pure core accepts, from line `j` with the
passes for the lines that remain, makes the events of `Checks` for those lines: when it returns,
with the status that `checkLines` computes from its state, and when it exits, followed by the
exit. -/
theorem checks_loop {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {test : UInt64 → CheckState → Bool} {step : UInt64 → CheckState → Action CheckState}
    (tested : ∀ i s, test i s = (s.2.2 == 0))
    (stepped : ∀ i s, step i s = checkStep m (parse m) i s) :
    ∀ (remaining j : Nat) (buffer : Bytes) (failed : UInt64) {world : World}
      {trace : List Event} {outcome : Outcome CheckState} {final : World},
      j + remaining = (lines m.data.data.toList).length → buffer.data.size = 65536 →
      (failed = 0 ∨ failed = 1) →
      LoopExec host remaining j (buffer, failed, 0) test step .pure world trace outcome final →
      (∀ s, outcome = .returned s →
        Checks (((lines m.data.data.toList).drop j).map (·.2)) (failed == 0) trace
          (if s.2.2 != 0 then 77 else s.2.1)) ∧
      (∀ code, outcome = .exited code → ∃ events, trace = events ++ [.exit code] ∧
        code.toNat ≤ 76 ∧
        Checks (((lines m.data.data.toList).drop j).map (·.2)) (failed == 0) events code)
  | 0, j, buffer, failed, _, _, _, _, hj, _, hf, run => by
    cases run with
    | zero next =>
      obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape next
      refine ⟨fun s e => ?_, fun _ e => nomatch e⟩
      cases e
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil]
      rcases hf with rfl | rfl <;> exact .done
  | remaining + 1, j, buffer, failed, _, _, _, _, hj, hsize, hf, run => by
    have hjl : j < (lines m.data.data.toList).length := by omega
    have hcons : ((lines m.data.data.toList).drop j).map (·.2) =
        (lines m.data.data.toList)[j].2 :: ((lines m.data.data.toList).drop (j + 1)).map (·.2) := by
      rw [List.drop_eq_getElem_cons hjl, List.map_cons]
    cases run with
    | stop test _ => simp [tested] at test
    | trap _ _ => exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
    | exit _ step =>
      rw [stepped] at step
      obtain ⟨-, exits⟩ := check_step m hm accepted j hjl hsize failed step
      refine ⟨(fun _ e => nomatch e), fun code e => ?_⟩
      obtain ⟨ok, fileEvents, writes, rfl, check, lw⟩ := exits code e
      exact ⟨fileEvents ++ writes, rfl, lw.2.2.2.2.1, by rw [hcons]; exact .failed check lw⟩
    | next _ step rest =>
      rw [stepped] at step
      obtain ⟨returns, -⟩ := check_step m hm accepted j hjl hsize failed step
      obtain ⟨ok, fileEvents, writes, buffer', stalled, rfl, hs, check, hbuf, ending⟩ :=
        returns _ rfl
      subst hs
      have hf' : (if ok then failed else 1) = 0 ∨ (if ok then failed else 1) = 1 := by
        cases ok <;> simp [hf]
      have hallok : ((failed == 0) && ok) = ((if ok then failed else 1) == 0) := by
        cases ok <;> rcases hf with rfl | rfl <;> rfl
      rcases ending with ⟨rfl, lw⟩ | ⟨rfl, lw⟩
      · obtain ⟨returned, exited⟩ := checks_loop m hm accepted tested stepped remaining (j + 1)
          buffer' _ (by omega) hbuf hf' rest
        refine ⟨fun s e => ?_, fun code e => ?_⟩
        · rw [hcons]
          exact .line check lw (by rw [hallok]; exact returned s e)
        · obtain ⟨events, rfl, hle, chk⟩ := exited code e
          refine ⟨fileEvents ++ writes ++ events, by simp, hle, ?_⟩
          rw [hcons]
          exact .line check lw (by rw [hallok]; exact chk)
      · obtain ⟨rfl, rfl⟩ := loop_done (fun i => by simp [tested]) rest
        refine ⟨fun s e => ?_, fun _ e => nomatch e⟩
        cases e
        rw [hcons, List.append_nil]
        exact .stalled check lw

/-- The loop of `checkLines` on a manifest that the pure core accepts makes a pass for each of its
lines. -/
theorem parse_passes (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2) :
    ((parse m).size.toUInt64 >>> 1).toNat = (lines m.data.data.toList).length := by
  have hlsmall := lines_length m.data.data.toList
  have hlenm : m.data.data.toList.length = m.data.size := by simp
  rw [parse_accepted m hm accepted, List.size_toArray, spanWords_length]
  show (UInt64.ofNat (2 * (lines m.data.data.toList).length) >>> 1).toNat = _
  rw [UInt64.toNat_shiftRight, toNat_ofNat (by omega)]
  simp [Nat.shiftRight_eq_div_pow]

/-- A manifest that the pure core accepts gives at least one position. -/
theorem parse_size_ne (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2) :
    (parse m).size.toUInt64 ≠ 0 := by
  have hlenm := lines_length m.data.data.toList
  have hml : m.data.data.toList.length = m.data.size := by simp
  intro zero
  have h0 := congrArg UInt64.toNat zero
  rw [parse_accepted m hm accepted, List.size_toArray, spanWords_length] at h0
  have : (2 * (lines m.data.data.toList).length).toUInt64.toNat =
      2 * (lines m.data.data.toList).length := toNat_ofNat (by omega)
  rw [this] at h0
  have hpos := List.length_pos_iff.mpr accepted.1
  rw [UInt64.toNat_zero] at h0
  omega

/-- A run of `checkLines` on a manifest that the pure core accepts makes the events of `Checks` for
its lines, from no verdict: when it returns, with the status that it returns, and when it exits,
followed by the exit. -/
theorem checkLines_run {World : Type} {host : Host World} (m : Bytes) (hm : m.data.size < 2 ^ 32)
    (accepted : lines m.data.data.toList ≠ [] ∧ ∀ l ∈ lines m.data.data.toList, WellFormed l.2)
    {buffer : Bytes} (hsize : buffer.data.size = 65536) {world final : World}
    {trace : List Event} {outcome : Outcome UInt64}
    (run : Exec host (checkLines m (parse m) buffer) world trace outcome final) :
    (∀ v, outcome = .returned v → Checks ((lines m.data.data.toList).map (·.2)) true trace v) ∧
    (∀ code, outcome = .exited code → ∃ events, trace = events ++ [.exit code] ∧
      code.toNat ≤ 76 ∧ Checks ((lines m.data.data.toList).map (·.2)) true events code) := by
  unfold checkLines at run
  obtain ⟨after, first, middle, rest, loopRun, cont, rfl⟩ := Exec.unbind _ run
  cases loopRun with
  | loop loopRun =>
  rw [parse_passes m hm accepted] at loopRun
  obtain ⟨returned, exited⟩ := checks_loop m hm accepted (fun _ _ => rfl) (fun _ _ => rfl) _ 0
    buffer 0 (by simp) hsize (.inl rfl) loopRun
  cases middle with
  | exited c =>
    obtain ⟨rfl, rfl, -⟩ := cont
    refine ⟨(fun _ e => nomatch e), fun code e => ?_⟩
    cases e
    obtain ⟨events, rfl, hle, chk⟩ := exited c rfl
    exact ⟨events, by simp, hle, by simpa using chk⟩
  | trapped msg =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ e => nomatch e), fun _ e => nomatch e⟩
  | returned s =>
    have chk := returned s rfl
    change Exec host (if s.2.2 != 0 then pure 77 else pure s.2.1) after rest outcome final at cont
    refine ⟨fun v e => ?_, fun _ e => ?_⟩
    · split at cont
      · rename_i h
        obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape cont
        cases e
        rw [ite_eq_left h] at chk
        simpa using chk
      · rename_i h
        obtain ⟨rfl, rfl, -⟩ := Verified.Wasi.exec_pure_shape cont
        cases e
        rw [ite_eq_right h] at chk
        simpa using chk
    · split at cont <;>
        (obtain ⟨-, h, -⟩ := Verified.Wasi.exec_pure_shape cont
         rw [e] at h
         cases h)


/-! ## Descriptors and opens -/

theorem sys_ne {c d : Call} {a b : List Arg} {r s : Transfer (List Bytes)} (h : c.name ≠ d.name) :
    Event.sys c a r ≠ Event.sys d b s :=
  fun e => h (congrArg Call.name (Event.sys.inj e).1)

theorem OnDescriptor.not_open {fd : UInt64} {e : Event} (h : OnDescriptor fd e) (args : List Arg)
    (reply : Transfer (List Bytes)) : e ≠ .sys .pathOpen args reply := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact sys_ne (by decide)
  · exact sys_ne (by decide)

theorem Handled.append {a b : List Event} (ha : Handled a) (hb : Handled b) :
    Handled (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | write _ ih => exact .write ih
  | argsCall named _ ih => exact .argsCall named ih
  | refused nonzero _ ih => exact .refused nonzero ih
  | bracket calls _ ih =>
    simp only [List.cons_append, List.append_assoc]
    exact .bracket calls ih

theorem Handled.writes : ∀ {ws : List Event}, (∀ e ∈ ws, WroteSome e) → Handled ws
  | [], _ => .nil
  | e :: ws, h => by
    obtain ⟨o, r, rfl, -⟩ := h e (List.mem_cons_self ..)
    exact .write (Handled.writes fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem FileReads.calls {fd : UInt64} {r : Nat} {done : List UInt8} {events : List Event}
    {bytes : List UInt8} {ending : Ending} (h : FileReads fd r done events bytes ending) :
    ∀ e ∈ events, OnDescriptor fd e := by
  induction h with
  | cut => intro e he; nomatch he
  | eof _ => intro e he; rw [List.mem_singleton.mp he]; exact .inl ⟨_, _, rfl⟩
  | failed _ => intro e he; rw [List.mem_singleton.mp he]; exact .inl ⟨_, _, rfl⟩
  | more _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl ⟨_, _, rfl⟩
    · exact ih e he

theorem ManifestReads.calls {fd : UInt64} {size : Nat} {held : List UInt8} {events : List Event}
    {bytes : List UInt8} {status : UInt64} (h : ManifestReads fd size held events bytes status) :
    ∀ e ∈ events, OnDescriptor fd e := by
  induction h with
  | full _ => intro e he; nomatch he
  | short _ _ => intro e he; rw [List.mem_singleton.mp he]; exact .inl ⟨_, _, rfl⟩
  | failed _ _ => intro e he; rw [List.mem_singleton.mp he]; exact .inl ⟨_, _, rfl⟩
  | more _ _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl ⟨_, _, rfl⟩
    · exact ih e he

theorem ManifestBody.calls {fd : UInt64} {events : List Event} {status : UInt64}
    {bytes : List UInt8} (h : ManifestBody fd events status bytes) :
    ∀ e ∈ events, OnDescriptor fd e := by
  cases h with
  | statFailed _ => intro e he; rw [List.mem_singleton.mp he]; exact .inr ⟨_, rfl⟩
  | tooLarge _ => intro e he; rw [List.mem_singleton.mp he]; exact .inr ⟨_, rfl⟩
  | stopped _ reads _ =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .inr ⟨_, rfl⟩
    · exact reads.calls e he
  | probed _ reads =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_cons.mp he with rfl | he
      · exact .inr ⟨_, rfl⟩
      · exact reads.calls e he
    · rw [List.mem_singleton.mp he]
      exact .inl ⟨_, _, rfl⟩

theorem FileCheck.handled {name line : List UInt8} {events : List Event} {ok : Bool}
    (h : FileCheck name line events ok) : Handled events := by
  cases h with
  | refused nonzero => exact .refused nonzero .nil
  | opened reads _ => exact .bracket reads.calls .nil

theorem FileCheck.opens {name line : List UInt8} {events : List Event} {ok : Bool}
    (h : FileCheck name line events ok) :
    ∀ args reply, Event.sys .pathOpen args reply ∈ events → args = openArgs fileRights name := by
  intro args reply he
  cases h with
  | refused _ =>
    exact (Event.sys.inj (List.mem_singleton.mp he)).2.1
  | opened reads _ =>
    rw [List.mem_append, List.mem_cons, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact (Event.sys.inj he).2.1
    · exact absurd rfl ((reads.calls _ he).not_open args reply)
    · exact absurd he (sys_ne (by decide))

theorem ManifestRun.handled {name : List UInt8} {events : List Event} {status : UInt64}
    {bytes : List UInt8} (h : ManifestRun name events status bytes) : Handled events := by
  cases h with
  | refused nonzero => exact .refused nonzero .nil
  | opened reading => exact .bracket reading.calls .nil

theorem ManifestRun.opens {name : List UInt8} {events : List Event} {status : UInt64}
    {bytes : List UInt8} (h : ManifestRun name events status bytes) :
    ∀ args reply, Event.sys .pathOpen args reply ∈ events → args = openArgs manifestRights name := by
  intro args reply he
  cases h with
  | refused _ =>
    exact (Event.sys.inj (List.mem_singleton.mp he)).2.1
  | opened reading =>
    rw [List.mem_append, List.mem_cons, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact (Event.sys.inj he).2.1
    · exact absurd rfl ((reading.calls _ he).not_open args reply)
    · exact absurd he (sys_ne (by decide))

theorem LineWrites.no_open {text : List UInt8} {writes : List Event} {ending : WriteEnd}
    (h : LineWrites text writes ending) (args : List Arg) (reply : Transfer (List Bytes)) :
    Event.sys .pathOpen args reply ∉ writes := by
  intro he
  obtain ⟨_, _, heq, -⟩ := h.2.2.1 _ he
  cases heq

theorem Checks.handled {ls : List (List UInt8)} {allOk : Bool} {events : List Event}
    {code : UInt64} (h : Checks ls allOk events code) : Handled events := by
  induction h with
  | done => exact .nil
  | line check wrote _ ih => exact (check.handled.append (Handled.writes wrote.2.2.1)).append ih
  | stalled check wrote => exact check.handled.append (Handled.writes wrote.2.2.1)
  | failed check wrote => exact check.handled.append (Handled.writes wrote.2.2.1)

theorem Checks.opens {ls : List (List UInt8)} {allOk : Bool} {events : List Event}
    {code : UInt64} (h : Checks ls allOk events code) :
    ∀ args reply, Event.sys .pathOpen args reply ∈ events →
      ∃ l ∈ ls, args = openArgs fileRights (l.drop 66) := by
  induction h with
  | done => intro _ _ he; nomatch he
  | line check wrote _ ih =>
    intro args reply he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact ⟨_, List.mem_cons_self .., check.opens args reply he⟩
      · exact absurd he (wrote.no_open args reply)
    · obtain ⟨l, hl, e⟩ := ih args reply he
      exact ⟨l, List.mem_cons_of_mem _ hl, e⟩
  | stalled check wrote =>
    intro args reply he
    rcases List.mem_append.mp he with he | he
    · exact ⟨_, List.mem_cons_self .., check.opens args reply he⟩
    · exact absurd he (wrote.no_open args reply)
  | failed check wrote =>
    intro args reply he
    rcases List.mem_append.mp he with he | he
    · exact ⟨_, List.mem_cons_self .., check.opens args reply he⟩
    · exact absurd he (wrote.no_open args reply)

/-- The status of the checks is at most 77. -/
theorem Checks.code_le {ls : List (List UInt8)} {allOk : Bool} {events : List Event}
    {code : UInt64} (h : Checks ls allOk events code) : code.toNat ≤ 77 := by
  induction h with
  | done => cases ‹Bool› <;> decide
  | line _ _ _ ih => exact ih
  | stalled _ _ => decide
  | failed _ wrote => have := wrote.2.2.2.2.1; omega

/-! ## The arguments -/

theorem exec_pure {World α : Type} {host : Host World} {value : α} {world final : World}
    {trace : List Event} {outcome : Outcome α}
    (run : Exec host (.pure value) world trace outcome final) :
    trace = [] ∧ outcome = .returned value := by
  cases run
  exact ⟨rfl, rfl⟩

/-- `args` never exits, and a returned result has an errno of at most 76 and a buffer of fewer
than `2^32` bytes: the size that the reporter's four-byte word gives. -/
theorem args_returned {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {outcome : Outcome ArgsResult}
    (run : Exec host args world trace outcome final) :
    (∀ c, outcome ≠ .exited c) ∧
      ∀ a, outcome = .returned a → a.errno.toNat ≤ 76 ∧ a.bytes.data.size < 2 ^ 32 := by
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | @sys_return _ _ _ _ _ _ _ _ _ errno sizes _ reporter next =>
    have errnoValid : errno.toNat ≤ 76 := (host.sys_bound reporter).2
    beta_reduce at next
    split at next
    · obtain ⟨-, rfl⟩ := exec_pure next
      refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
      cases h
      exact ⟨by simpa [sysReply] using errnoValid, by simp [Bytes.empty]⟩
    · split at next
      · obtain ⟨-, rfl⟩ := exec_pure next
        refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
        cases h
        exact ⟨by decide, by simp [Bytes.empty]⟩
      · rename_i nonzero _
        have zero : errno = 0 := by simpa [sysReply] using nonzero
        subst zero
        cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap => exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
        | @sys_return _ _ _ _ _ _ _ _ _ errno got _ getter next =>
          have gotValid : errno.toNat ≤ 76 := (host.sys_bound getter).2
          beta_reduce at next
          split at next
          · obtain ⟨-, rfl⟩ := exec_pure next
            refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
            cases h
            exact ⟨by simpa [sysReply] using gotValid, by simp [Bytes.empty]⟩
          · rename_i gotNonzero
            have gotZero : errno = 0 := by simpa [sysReply] using gotNonzero
            subst gotZero
            obtain ⟨-, rfl⟩ := exec_pure next
            refine ⟨fun _ h => (nomatch h), fun a h => ?_⟩
            cases h
            have shape : sizes.map (·.data.size) = [4, 4] := (host.sys_bound reporter).1
            rcases sizes with _ | ⟨count, _ | ⟨size, _ | ⟨_, _⟩⟩⟩ <;> simp at shape
            have sizeSmall := Verified.Wasi.littleEndian_four_lt shape.2
            have gotShape : got.map (·.data.size) = [1 * (littleEndian size).toNat] := by
              have permitted := (host.sys_bound getter).1
              rw [host.sys_reports (call := Call.argsGet) reporter rfl] at permitted
              exact permitted
            rcases got with _ | ⟨shown, _ | ⟨_, _⟩⟩ <;> simp at gotShape
            refine ⟨Nat.zero_le _, ?_⟩
            simp only [sysReply, ↓reduceIte, Reply.bytes, List.getElem?_cons_zero,
              Option.getD_some]
            omega

/-- The events of a run of `args` are calls of `args_sizes_get` and `args_get`. -/
theorem args_events {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {outcome : Outcome ArgsResult}
    (run : Exec host args world trace outcome final) :
    ∀ e ∈ trace, ∃ call ar rep, e = .sys call ar rep ∧
      (call = .argsSizesGet ∨ call = .argsGet) := by
  unfold args at run
  cases run with
  | sys_reject fits => exact absurd (by decide) fits
  | sys_trap =>
    intro e he
    rw [List.mem_singleton.mp he]
    exact ⟨_, _, _, rfl, .inl rfl⟩
  | sys_return _ _ next =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, _, _, rfl, .inl rfl⟩
    beta_reduce at next
    split at next
    · obtain ⟨rfl, -⟩ := exec_pure next
      nomatch he
    · split at next
      · obtain ⟨rfl, -⟩ := exec_pure next
        nomatch he
      · cases next with
        | sys_reject fits => exact absurd (by decide) fits
        | sys_trap =>
          rw [List.mem_singleton.mp he]
          exact ⟨_, _, _, rfl, .inr rfl⟩
        | sys_return _ _ next =>
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨_, _, _, rfl, .inr rfl⟩
          beta_reduce at next
          split at next <;> (obtain ⟨rfl, -⟩ := exec_pure next; nomatch he)

theorem handled_of_args : ∀ {trace : List Event}, (∀ e ∈ trace, ∃ call ar rep,
    e = .sys call ar rep ∧ (call = .argsSizesGet ∨ call = .argsGet)) → Handled trace
  | [], _ => .nil
  | e :: t, h => by
    obtain ⟨call, ar, rep, rfl, named⟩ := h e (List.mem_cons_self ..)
    exact .argsCall named (handled_of_args fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem no_open_of_args {trace : List Event} (h : ∀ e ∈ trace, ∃ call ar rep,
    e = .sys call ar rep ∧ (call = .argsSizesGet ∨ call = .argsGet)) :
    ∀ args reply, Event.sys .pathOpen args reply ∉ trace := by
  intro args reply he
  obtain ⟨call, ar, rep, heq, named⟩ := h _ he
  have hc := (Event.sys.inj heq).1
  rcases named with rfl | rfl
  · exact absurd (congrArg Call.name hc) (by decide)
  · exact absurd (congrArg Call.name hc) (by decide)

theorem oneArgument_unique {l n n' : List UInt8} (h : OneArgument l n) (h' : OneArgument l n') :
    n = n' := by
  rw [(oneArgument_shape h).2.2.2, (oneArgument_shape h').2.2.2]

/-! ## `main` -/

/-- `Meets` of a run whose argument buffer holds one argument, the name of the manifest, from the
events of `args`, those of `ManifestRun`, and those that follow, as `Run` states them. -/
theorem meets_of {World : Type} {host : Host World} {world after : World} {a : ArgsResult}
    {pre opening post : List Event} {name manifest : List UInt8} {status code : UInt64}
    (argsRun : Exec host args world pre (.returned a) after) (hz : a.errno = 0)
    (hone : OneArgument a.bytes.data.data.toList name)
    (mrun : ManifestRun name opening status manifest)
    (rest : (status ≠ 0 → code = status ∧ post = []) ∧
      (status = 0 → (lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2) →
        code = 1 ∧ post = []) ∧
      (status = 0 → lines manifest ≠ [] → (∀ l ∈ lines manifest, WellFormed l.2) →
        Checks ((lines manifest).map (·.2)) true post code)) :
    Meets host world (pre ++ (opening ++ post)) code := by
  have preEvents := args_events argsRun
  have hpost : post = [] ∨ Checks ((lines manifest).map (·.2)) true post code := by
    by_cases hs : status = 0
    · by_cases acc : lines manifest ≠ [] ∧ ∀ l ∈ lines manifest, WellFormed l.2
      · exact .inr (rest.2.2 hs acc.1 acc.2)
      · have hr : lines manifest = [] ∨ ∃ l ∈ lines manifest, ¬ WellFormed l.2 := by
          by_cases e : lines manifest = []
          · exact .inl e
          · right
            by_contra hall
            exact acc ⟨e, fun l hl => by_contra fun hn => hall ⟨l, hl, hn⟩⟩
        exact .inl (rest.2.1 hs hr).2
    · exact .inl (rest.1 hs).2
  refine ⟨a, manifest, ⟨pre, opening ++ post, after, rfl, argsRun, fun h => absurd hz h,
    fun _ h => absurd hone (h name), fun _ name' hone' => ?_⟩, ?_, ?_⟩
  · obtain rfl := oneArgument_unique hone' hone
    exact ⟨opening, post, status, rfl, mrun, rest⟩
  · intro args reply he
    rcases List.mem_append.mp he with he | he
    · exact absurd he (no_open_of_args preEvents args reply)
    rcases List.mem_append.mp he with he | he
    · exact ⟨name, .inl ⟨mrun.opens args reply he, hone⟩⟩
    · rcases hpost with rfl | chk
      · nomatch he
      · obtain ⟨l, hl, e⟩ := chk.opens args reply he
        obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
        exact ⟨l'.2.drop 66, .inr ⟨e, l', hl', rfl⟩⟩
  · refine (handled_of_args preEvents).append (mrun.handled.append ?_)
    rcases hpost with rfl | chk
    · exact .nil
    · exact chk.handled

/-- Every run of `main` that returns a status has a status of at most 77 and events that meet
`Meets`, and every run that exits does so with a status of at most 76 and events that meet `Meets`
followed by the exit. -/
theorem main_runs {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {outcome : Outcome UInt64} (run : Exec host main world trace outcome final) :
    (∀ status, outcome = .returned status → status.toNat ≤ 77 ∧ Meets host world trace status) ∧
    (∀ code, outcome = .exited code → code.toNat ≤ 76 ∧
      ∃ events, trace = events ++ [.exit code] ∧ Meets host world events code) := by
  obtain ⟨after, pre, middle, rest, argsRun, cont, rfl⟩ := Exec.unbind args run
  obtain ⟨argsNoExit, argsFacts⟩ := args_returned argsRun
  have preEvents := args_events argsRun
  cases middle with
  | exited c => exact absurd rfl (argsNoExit c)
  | trapped m =>
    obtain ⟨-, rfl, -⟩ := cont
    exact ⟨(fun _ h => nomatch h), fun _ h => nomatch h⟩
  | returned a =>
    obtain ⟨aValid, aSize⟩ := argsFacts a rfl
    change Exec host (if a.errno != 0 then Action.pure a.errno else _) after rest outcome final
      at cont
    split at cont
    · rename_i nonzero
      have hne : a.errno ≠ 0 := by simpa using nonzero
      obtain ⟨rfl, rfl⟩ := exec_pure cont
      refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
      cases h
      refine ⟨by omega, a, [], ⟨pre, [], after, rfl, argsRun, fun _ => ⟨rfl, rfl⟩,
        fun e => absurd e hne, fun e => absurd e hne⟩, ?_, ?_⟩
      · intro args reply he
        exact absurd (by simpa using he) (no_open_of_args preEvents args reply)
      · simpa using handled_of_args preEvents
    · rename_i zero
      have hz : a.errno = 0 := by simpa using zero
      have hcases := argument_cases a.bytes (by omega)
      dsimp only at cont
      split at cont
      · rename_i refuse
        obtain ⟨rfl, rfl⟩ := exec_pure cont
        refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
        cases h
        refine ⟨by decide, a, [], ⟨pre, [], after, rfl, argsRun, fun e => absurd hz e,
          fun _ _ => ⟨rfl, rfl⟩, fun _ name hone => absurd hone (hcases.1 refuse name)⟩, ?_, ?_⟩
        · intro args reply he
          exact absurd (by simpa using he) (no_open_of_args preEvents args reply)
        · simpa using handled_of_args preEvents
      · rename_i accept
        have hone := hcases.2 (by simpa using accept)
        generalize slice a.bytes ((argScan a.bytes).2.1 + 1)
          (a.bytes.size - (argScan a.bytes).2.1 - 2) = name at hone cont
        have hnsize : name.data.size < 2 ^ 32 := by
          obtain ⟨program, hprog, -, -⟩ := hone
          have := congrArg List.length hprog
          simp at this
          omega
        have hargs : openArgs manifestRights name.data.data.toList =
            [.word 3, .word 1, .bytes name, .word 0, .word 2097154, .word 0, .word 0] := by
          rw [openArgs_bytes]
          rfl
        generalize hbuf : (Bytes.build chunk fun _ => 0) = buffer at cont
        have hbsize : buffer.data.size = 65536 := by
          rw [← hbuf, build_size]
          rfl
        obtain ⟨after2, opening, gotMid, post, openRun, cont2, rfl⟩ := Exec.unbind _ cont
        obtain ⟨openNoExit, openResults⟩ := withOpen_run (rights := 2097154)
          (fallback := fun errno => (errno, Bytes.build 0 fun _ => 0, Bytes.build 0 fun _ => 0))
          (body := fun file => readManifest file buffer) hnsize (.inr rfl)
          (fun fd _ _ _ _ hfd bodyRun => (readManifest_run hfd hbsize bodyRun).1) openRun
        cases gotMid with
        | exited c => exact absurd rfl (openNoExit c)
        | trapped m =>
          obtain ⟨-, rfl, -⟩ := cont2
          exact ⟨(fun _ h => nomatch h), fun _ h => nomatch h⟩
        | returned got =>
          simp only [Continue] at cont2
          obtain ⟨errno, outputs, failed | opened⟩ := openResults got rfl
          · obtain ⟨hne, hvalid, htrace, rfl⟩ := failed
            rw [← hargs] at htrace
            subst htrace
            have mrun := ManifestRun.refused (name := name.data.data.toList) (outputs := outputs) hne
            dsimp only at cont2
            split at cont2
            · obtain ⟨rfl, rfl⟩ := exec_pure cont2
              refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
              cases h
              exact ⟨by omega, meets_of argsRun hz hone mrun
                ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h hne, fun h => absurd h hne⟩⟩
            · rename_i bad
              exact absurd (by simpa using hne) bad
          · obtain ⟨rfl, small, events, after3, closing, closeErrno, committed, cvalid, htrace,
              bodyRun, hclose⟩ := opened
            obtain ⟨-, bodyFacts⟩ := readManifest_run small hbsize bodyRun
            obtain ⟨bytes, body, svalid, sbytes, rbuf⟩ := bodyFacts got.1 rfl
            rw [← hargs] at htrace
            subst htrace
            have mrun := ManifestRun.opened (name := name.data.data.toList)
              (closeErrno := closeErrno) (committed := committed) body
            change Exec host (if got.1.1 != 0 then pure got.1.1 else _) after2 post outcome final
              at cont2
            split at cont2
            · rename_i nonzero
              have hne : got.1.1 ≠ 0 := by simpa using nonzero
              rw [ite_eq_left hne] at mrun
              obtain ⟨rfl, rfl⟩ := exec_pure cont2
              refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
              cases h
              exact ⟨by omega, meets_of argsRun hz hone mrun
                ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h hne, fun h => absurd h hne⟩⟩
            · rename_i zero1
              have hz1 : got.1.1 = 0 := by simpa using zero1
              rw [ite_eq_right (by simpa using hz1)] at mrun
              have hbytes := sbytes hz1
              change Exec host (if got.2 != 0 then pure got.2 else _) after2 post outcome final
                at cont2
              split at cont2
              · rename_i nonzero
                have hne : closeErrno ≠ 0 := by rw [← hclose]; simpa using nonzero
                obtain ⟨rfl, rfl⟩ := exec_pure cont2
                refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
                cases h
                rw [hclose]
                exact ⟨by omega, meets_of argsRun hz hone mrun
                  ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h hne, fun h => absurd h hne⟩⟩
              · rename_i zero2
                have hz2 : closeErrno = 0 := by rw [← hclose]; simpa using zero2
                obtain ⟨hmb, hmsmall⟩ := hbytes
                generalize got.1.2.1 = m at cont2 hmb
                generalize got.1.2.2 = buffer' at cont2 rbuf
                subst hmb
                have hm : m.data.size < 2 ^ 32 := by simpa using hmsmall
                by_cases acc : lines m.data.data.toList ≠ [] ∧
                    ∀ l ∈ lines m.data.data.toList, WellFormed l.2
                · split at cont2
                  · rename_i hsz
                    exact absurd (eq_of_beq hsz) (parse_size_ne m hm acc)
                  · obtain ⟨creturns, cexits⟩ := checkLines_run m hm acc rbuf cont2
                    have refusedNot : (lines m.data.data.toList = [] ∨
                        ∃ l ∈ lines m.data.data.toList, ¬ WellFormed l.2) → False := by
                      intro hr
                      rcases hr with e | ⟨l, hl, hn⟩
                      · exact acc.1 e
                      · exact hn (acc.2 l hl)
                    refine ⟨fun status h => ?_, fun code h => ?_⟩
                    · have chk := creturns status h
                      exact ⟨chk.code_le, meets_of argsRun hz hone mrun
                        ⟨fun h => absurd hz2 h, fun _ hr => (refusedNot hr).elim,
                          fun _ _ _ => chk⟩⟩
                    · obtain ⟨events, rfl, hle, chk⟩ := cexits code h
                      exact ⟨hle, pre ++ (_ ++ events), by simp, meets_of argsRun hz hone mrun
                        ⟨fun h => absurd hz2 h, fun _ hr => (refusedNot hr).elim,
                          fun _ _ _ => chk⟩⟩
                · split at cont2
                  · obtain ⟨rfl, rfl⟩ := exec_pure cont2
                    refine ⟨fun status h => ?_, fun _ h => nomatch h⟩
                    cases h
                    exact ⟨by decide, meets_of argsRun hz hone mrun
                      ⟨fun h => absurd hz2 h, fun _ _ => ⟨rfl, rfl⟩,
                        fun _ h1 h2 => absurd ⟨h1, h2⟩ acc⟩⟩
                  · rename_i hsz
                    rw [parse_refused m hm acc] at hsz
                    simp at hsz

/-- Every run of the command's `main` followed by its exit, under every host, that ends with the
exit status `code` has the events of `Meets` followed by the exit, and the status is at most 77. -/
theorem exec_main {World : Type} {host : Host World} {world final : World} {trace : List Event}
    {code : UInt64}
    (execution : Exec host (main.bind fun status => Action.exit (α := Unit) status) world trace
      (.exited code) final) :
    ∃ events, trace = events ++ [.exit code] ∧ code.toNat ≤ 77 ∧ Meets host world events code := by
  obtain ⟨after, events, middle, rest, mainRun, cont, rfl⟩ := Exec.unbind main execution
  obtain ⟨returned, exited⟩ := main_runs mainRun
  cases middle with
  | exited c =>
    obtain ⟨rfl, same, -⟩ := cont
    obtain ⟨small, steps, rfl, meets⟩ := exited c rfl
    cases same
    exact ⟨steps, by rw [List.append_nil], by omega, meets⟩
  | trapped m =>
    obtain ⟨-, h, -⟩ := cont
    cases h
  | returned status =>
    obtain ⟨small, hm⟩ := returned status rfl
    change Exec host (Action.exit status) after rest (.exited code) final at cont
    cases cont with
    | exit _ =>
      rw [exitStatus_of_lt (by omega)]
      exact ⟨events, rfl, small, hm⟩

end Demos.ManifestCheck
