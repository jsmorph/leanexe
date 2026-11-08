import TestSupport.M7.Hist
import TestSupport.M7.CrcReplies

/-!
What the histogram step writes, in terms of the bytes that it reads.  For a register map `u` whose
receive and status registers differ, `histTick u` is `histPhases` of
`tests/TestSupport/M7/Hist.lean` with the map's registers, and `hist_replies` states for every bus, every sequence `σ` of the values
read, and every number `N` of windows from `histInit`: the values that the windows write to the
transmit register begin `histReplies` of the bytes that they read from the receive register, for
each byte the low byte of the number of times it occurs among the bytes read up to it, and at most
one byte read has no reply yet.

The proof carries `HistAt` over the windows.  The state's array has 256 elements, and element `i`
holds the number of times the byte `i` occurs among the bytes counted, `Counts`.  In phases 0 and
3 every byte read is counted and has its reply; in phase 1 the last byte read, the value of the last
request, waits for its count; and in phase 2 every byte is counted, the reply to the last byte lies
in the word's second byte, and the next write sends it.  `histUsart3_replies` and
`histCmsdk_replies` instantiate the theorem for the two steps' maps.
-/

namespace TestSupport.M7.Hist

open LeanExe.Requests TestSupport.M7.Crc
open LeanExe.Native (readReq writeReq)

/-- USART3's registers in `histUsart3`. -/
def histUsart3Map : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

/-- UART0's registers in `histCmsdk`. -/
def histCmsdkMap : Uart := ⟨0x1000, 0x1000, 0x1001, 2, 1, 0⟩

/-- The histogram step for the register map `u`. -/
def histTick (u : Uart) (g : HistState) (v : UInt64) : HistState × UInt64 :=
  histPhases u.rx u.tx u.status u.rxFull u.txMask u.txRoom g.1 g.2 v

/-- The reply to the bytes `bs` that end in the byte just read: the low byte of the number of times
that byte occurs in them. -/
def histReply (bs : List UInt64) : UInt64 := UInt64.ofNat (bs.count (bs.getLastD 0) % 256)

/-- The replies to the bytes `bs`: the reply to each nonempty prefix. -/
def histReplies (bs : List UInt64) : List UInt64 :=
  (List.range bs.length).map fun i => histReply (bs.take (i + 1))

/-- The array `h` counts the bytes `bs`: it has 256 elements, and element `i` is the number of
times the byte `i` occurs in `bs`. -/
def Counts (h : Array UInt64) (bs : List UInt64) : Prop :=
  h.size = 256 ∧ ∀ i (hi : i < h.size), h[i] = UInt64.ofNat (bs.count (UInt64.ofNat i))

/-! ## Counts and replies -/

theorem length_histReplies (bs : List UInt64) : (histReplies bs).length = bs.length := by
  simp [histReplies]

theorem histReplies_snoc (bs : List UInt64) (b : UInt64) :
    histReplies (bs ++ [b]) = histReplies bs ++ [histReply (bs ++ [b])] := by
  unfold histReplies
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton,
    List.take_of_length_le (show (bs ++ [b]).length ≤ bs.length + 1 by simp)]
  refine congrArg (· ++ [histReply (bs ++ [b])]) (List.map_congr_left fun i hi => ?_)
  rw [List.mem_range] at hi
  rw [List.take_append_of_le_length (l₂ := [b]) (show i + 1 ≤ bs.length by omega)]

theorem histReply_snoc (bs : List UInt64) (b : UInt64) :
    histReply (bs ++ [b]) = UInt64.ofNat ((bs.count b + 1) % 256) := by
  simp [histReply, List.count_append]

/-- Counting the byte `b`: the count after it is the old one plus 1, and the array with that count
written at `b` counts the bytes with `b` appended. -/
theorem counts_snoc {h : Array UInt64} {bs : List UInt64} (hc : Counts h bs) {b : UInt64}
    (hb : b.toNat < 256) :
    h[b.toNat]! + 1 = UInt64.ofNat (bs.count b + 1) ∧
      Counts (h.set! b.toNat (h[b.toNat]! + 1)) (bs ++ [b]) := by
  obtain ⟨hsz, hel⟩ := hc
  have hbi : b.toNat < h.size := by omega
  have hget : h[b.toNat]! = UInt64.ofNat (bs.count b) := by
    rw [getElem!_pos h b.toNat hbi, hel _ hbi, UInt64.ofNat_toNat]
  have hc1 : h[b.toNat]! + 1 = UInt64.ofNat (bs.count b + 1) := by
    rw [hget]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_one]
    omega
  refine ⟨hc1, ?_, fun i hi => ?_⟩
  · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz]
  · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hi
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds hi, List.count_append, List.count_singleton]
    by_cases hib : b.toNat = i
    · subst hib
      rw [ite_eq_left rfl, hc1, UInt64.ofNat_toNat]
      simp
    · rw [ite_eq_right hib, hel i hi]
      have hne : (b == UInt64.ofNat i) = false := by
        apply beq_false_of_ne
        intro he
        apply hib
        rw [he, UInt64.toNat_ofNat']
        omega
      rw [hne]
      simp

/-- The word of phase 2 with the reply `x`. -/
theorem phase2_word {x : UInt64} (hx : x.toNat < 256) :
    ((2 : UInt64) ||| (x <<< 8)) &&& 255 = 2 ∧
      (((2 : UInt64) ||| (x <<< 8)) >>> 8) &&& 255 = x := by
  obtain ⟨-, e2⟩ := reply_phase (r := 0) hx
  constructor
  · apply UInt64.toNat_inj.mp
    rw [toNat_low, e2]
    show _ = 2
    omega
  · apply UInt64.toNat_inj.mp
    rw [toNat_second, e2]
    omega

theorem phase_one : (1 : UInt64) &&& 255 = 1 := by decide
theorem phase_zero : (0 : UInt64) &&& 255 = 0 := by decide
theorem phase_three : (3 : UInt64) &&& 255 = 3 := by decide

theorem low_ofNat (n : Nat) : UInt64.ofNat n &&& 255 = UInt64.ofNat (n % 256) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_low, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  omega

/-! ## The steps of the phases -/

section

variable (u : Uart) (g : HistState) (v : UInt64)

theorem tick_phase0 (hp : g.2 &&& 255 = 0) :
    histTick u g v = if (v &&& u.rxFull != 0) = true then ((g.1, (1 : UInt64)), readReq u.rx)
      else ((g.1, (0 : UInt64)), readReq u.status) := by
  dsimp only [histTick, histPhases]
  rw [hp]
  rfl

theorem tick_phase1 (hp : g.2 &&& 255 = 1) :
    histTick u g v = ((g.1.set! (v &&& 255).toNat (g.1[(v &&& 255).toNat]! + 1),
      (2 : UInt64) ||| (((g.1[(v &&& 255).toNat]! + 1) &&& 255) <<< 8)), readReq u.status) := by
  dsimp only [histTick, histPhases]
  rw [hp]
  rfl

theorem tick_phase2 (hp : g.2 &&& 255 = 2) :
    histTick u g v = if (v &&& u.txMask == u.txRoom) = true then
        ((g.1, (3 : UInt64)), writeReq u.tx ((g.2 >>> 8) &&& 255))
      else (g, readReq u.status) := by
  dsimp only [histTick, histPhases]
  rw [hp]
  rfl

theorem tick_phase3 (hp : g.2 &&& 255 = 3) :
    histTick u g v = ((g.1, (0 : UInt64)), readReq u.status) := by
  dsimp only [histTick, histPhases]
  rw [hp]
  rfl

end

/-! ## The invariant -/

/-- The step's state `g` with the last value read `v`, after the bytes `ins` read and the values
`outs` written: in phase 0 or 3 every byte is counted and has its reply; in phase 1 the last byte,
the low byte of `v`, waits; in phase 2 every byte is counted and the word's second byte holds the
reply to the last, which waits. -/
def HistAt (g : HistState) (v : UInt64) (ins outs : List UInt64) : Prop :=
  ((g.2 &&& 255 = 0 ∨ g.2 &&& 255 = 3) ∧ Counts g.1 ins ∧ outs = histReplies ins) ∨
  (g.2 &&& 255 = 1 ∧ ∃ ins0, ins = ins0 ++ [v &&& 255] ∧ Counts g.1 ins0 ∧
    outs = histReplies ins0) ∨
  (g.2 &&& 255 = 2 ∧ Counts g.1 ins ∧ (g.2 >>> 8) &&& 255 = histReply ins ∧
    histReplies ins = outs ++ [histReply ins])

section

variable {α : Type} (B : Bus α) (u : Uart) (hrx : u.rx.toNat < 65536)
  (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536) (hrs : u.rx ≠ u.status)
  (σ : Nat → UInt32) (g : HistState) (v : UInt64) (k : Nat) {ins outs : List UInt64}

/-- The invariant after the window from the state `g`, the last value `v`, and `k` reads. -/
def HistNext (ins outs : List UInt64) : Prop :=
  HistAt (reqNext (histTick u) σ ⟨g, v, k⟩).state (reqNext (histTick u) σ ⟨g, v, k⟩).last
    (ins ++ dataIn B u [reqEvent B (histTick u) σ ⟨g, v, k⟩])
    (outs ++ dataOut B u [reqEvent B (histTick u) σ ⟨g, v, k⟩])

include hrx hs hrs in
/-- After a window whose request reads the status, the invariant needs only the new state. -/
theorem histNext_status {g' : HistState} (ht : histTick u g v = (g', readReq u.status))
    (h : ∀ x, HistAt g' x ins outs) : HistNext B u σ g v k ins outs := by
  obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨g, v, k⟩) ht (reqWrite_readReq hs)
  unfold HistNext
  rw [h1, h2, h3, reqReg_readReq hs, dataIn_status B u hrx hs hrs, dataOut_read B u,
    List.append_nil, List.append_nil]
  exact h _

include hrx hs hrs in
theorem histNext_phase0 (hp : g.2 &&& 255 = 0) (hc : Counts g.1 ins)
    (ho : outs = histReplies ins) : HistNext B u σ g v k ins outs := by
  by_cases hx : (v &&& u.rxFull != 0) = true
  · have ht : histTick u g v = ((g.1, (1 : UInt64)), readReq u.rx) := by
      rw [tick_phase0 u g v hp, ite_eq_left_of_eq_true _ _ (eq_true hx)]
    obtain ⟨h1, h2, h3⟩ := next_read (B := B) (σ := σ) (r := ⟨g, v, k⟩) ht (reqWrite_readReq hrx)
    unfold HistNext
    rw [h1, h2, h3, reqReg_readReq hrx, dataIn_data B u, dataOut_read B u, List.append_nil]
    exact Or.inr (Or.inl ⟨phase_one, ins, rfl, hc, ho⟩)
  · exact histNext_status B u hrx hs hrs σ g v k (g' := (g.1, 0))
      (by rw [tick_phase0 u g v hp, ite_eq_right_of_eq_false _ _ (eq_false hx)])
      (fun _ => Or.inl ⟨Or.inl phase_zero, hc, ho⟩)

include hrx hs hrs in
theorem histNext_phase3 (hp : g.2 &&& 255 = 3) (hc : Counts g.1 ins)
    (ho : outs = histReplies ins) : HistNext B u σ g v k ins outs :=
  histNext_status B u hrx hs hrs σ g v k (g' := (g.1, 0)) (tick_phase3 u g v hp)
    (fun _ => Or.inl ⟨Or.inl phase_zero, hc, ho⟩)

include hrx hs hrs in
theorem histNext_phase1 {ins0 : List UInt64} (hp : g.2 &&& 255 = 1)
    (hin : ins = ins0 ++ [v &&& 255]) (hc : Counts g.1 ins0) (ho : outs = histReplies ins0) :
    HistNext B u σ g v k ins outs := by
  have hb : (v &&& 255).toNat < 256 := by rw [toNat_low]; omega
  obtain ⟨hc1, hc'⟩ := counts_snoc hc hb
  have hx : ((g.1[(v &&& 255).toNat]! + 1) &&& 255).toNat < 256 := by rw [toNat_low]; omega
  obtain ⟨w1, w2⟩ := phase2_word hx
  refine histNext_status B u hrx hs hrs σ g v k (tick_phase1 u g v hp) (fun _ => ?_)
  refine Or.inr (Or.inr ⟨w1, by rw [hin]; exact hc', ?_, ?_⟩)
  · rw [w2, hin, histReply_snoc, hc1, low_ofNat]
  · rw [hin, histReplies_snoc, ho]

include hrx htx hs hrs in
theorem histNext_phase2 (hp : g.2 &&& 255 = 2) (hc : Counts g.1 ins)
    (hy : (g.2 >>> 8) &&& 255 = histReply ins) (ho : histReplies ins = outs ++ [histReply ins]) :
    HistNext B u σ g v k ins outs := by
  by_cases hx : (v &&& u.txMask == u.txRoom) = true
  · have ht : histTick u g v = ((g.1, (3 : UInt64)), writeReq u.tx ((g.2 >>> 8) &&& 255)) := by
      rw [tick_phase2 u g v hp, ite_eq_left_of_eq_true _ _ (eq_true hx)]
    obtain ⟨h1, h2, h3⟩ :=
      next_write (B := B) (σ := σ) (r := ⟨g, v, k⟩) ht (reqWrite_writeReq _ htx)
    have hb : ((g.2 >>> 8) &&& 255).toNat < 256 := by rw [toNat_second]; omega
    unfold HistNext
    rw [h1, h2, h3, reqReg_writeReq _ htx, dataIn_write B u, dataOut_write B u htx hb,
      List.append_nil]
    exact Or.inl ⟨Or.inr phase_three, hc, by rw [ho, hy]⟩
  · exact histNext_status B u hrx hs hrs σ g v k
      (by rw [tick_phase2 u g v hp, ite_eq_right_of_eq_false _ _ (eq_false hx)])
      (fun _ => Or.inr (Or.inr ⟨hp, hc, hy, ho⟩))

include hrx htx hs hrs in
/-- One window keeps the invariant. -/
theorem histAt_next (r : ReqState HistState) (h : HistAt r.state r.last ins outs) :
    HistAt (reqNext (histTick u) σ r).state (reqNext (histTick u) σ r).last
      (ins ++ dataIn B u [reqEvent B (histTick u) σ r])
      (outs ++ dataOut B u [reqEvent B (histTick u) σ r]) := by
  obtain ⟨g, v, k⟩ := r
  change HistAt g v ins outs at h
  change HistNext B u σ g v k ins outs
  rcases h with ⟨hp | hp, hc, ho⟩ | ⟨hp, ins0, hin, hc, ho⟩ | ⟨hp, hc, hy, ho⟩
  · exact histNext_phase0 B u hrx hs hrs σ g v k hp hc ho
  · exact histNext_phase3 B u hrx hs hrs σ g v k hp hc ho
  · exact histNext_phase1 B u hrx hs hrs σ g v k hp hin hc ho
  · exact histNext_phase2 B u hrx htx hs hrs σ g v k hp hc hy ho

theorem counts_init : Counts histInit.1 [] :=
  ⟨Array.size_replicate, fun _ _ => by
    simp only [histInit, Array.getElem_replicate, List.count_nil]
    rfl⟩

include hrx htx hs hrs in
/-- The invariant holds before every window from `histInit`. -/
theorem histAt_run : ∀ n,
    HistAt (reqRun (histTick u) histInit σ n).state (reqRun (histTick u) histInit σ n).last
      (dataIn B u (windows (reqTrace B (histTick u) histInit σ) n))
      (dataOut B u (windows (reqTrace B (histTick u) histInit σ) n))
  | 0 => Or.inl ⟨Or.inr phase_three, counts_init, rfl⟩
  | n + 1 => by
      rw [windows, dataIn_append, dataOut_append]
      exact histAt_next B u hrx htx hs hrs σ _ (histAt_run n)

include hrx htx hs hrs in
/-- For every sequence `σ` of the values read and every number `N` of windows from `histInit`, the
values that the windows write to the transmit register begin the replies to the bytes that they
read from the receive register, for each byte the low byte of the number of times it occurs among
the bytes read up to it, and at most one byte read waits for its reply. -/
theorem hist_replies (N : Nat) :
    dataOut B u (windows (reqTrace B (histTick u) histInit σ) N) <+:
        histReplies (dataIn B u (windows (reqTrace B (histTick u) histInit σ) N)) ∧
      (dataIn B u (windows (reqTrace B (histTick u) histInit σ) N)).length ≤
        (dataOut B u (windows (reqTrace B (histTick u) histInit σ) N)).length + 1 := by
  rcases histAt_run B u hrx htx hs hrs σ N with ⟨-, -, ho⟩ | ⟨-, ins0, hin, -, ho⟩ | ⟨-, -, -, ho⟩
  · rw [ho, length_histReplies]
    exact ⟨⟨[], List.append_nil _⟩, Nat.le_succ _⟩
  · rw [hin, ho, histReplies_snoc, length_histReplies, List.length_append, List.length_singleton]
    exact ⟨⟨_, rfl⟩, Nat.le_refl _⟩
  · rw [ho]
    refine ⟨⟨_, rfl⟩, ?_⟩
    have := congrArg List.length ho
    rw [length_histReplies, List.length_append, List.length_singleton] at this
    omega

end

/-- `hist_replies` for `histUsart3Tick` over USART3's registers. -/
theorem histUsart3_replies {α : Type} (B : Bus α) (σ : Nat → UInt32) (N : Nat) :
    dataOut B histUsart3Map (windows (reqTrace B histUsart3Tick histInit σ) N) <+:
        histReplies (dataIn B histUsart3Map (windows (reqTrace B histUsart3Tick histInit σ) N)) ∧
      (dataIn B histUsart3Map (windows (reqTrace B histUsart3Tick histInit σ) N)).length ≤
        (dataOut B histUsart3Map (windows (reqTrace B histUsart3Tick histInit σ) N)).length + 1 :=
  hist_replies B histUsart3Map (by decide) (by decide) (by decide) (by decide) σ N

/-- `hist_replies` for `histCmsdkTick` over UART0's registers. -/
theorem histCmsdk_replies {α : Type} (B : Bus α) (σ : Nat → UInt32) (N : Nat) :
    dataOut B histCmsdkMap (windows (reqTrace B histCmsdkTick histInit σ) N) <+:
        histReplies (dataIn B histCmsdkMap (windows (reqTrace B histCmsdkTick histInit σ) N)) ∧
      (dataIn B histCmsdkMap (windows (reqTrace B histCmsdkTick histInit σ) N)).length ≤
        (dataOut B histCmsdkMap (windows (reqTrace B histCmsdkTick histInit σ) N)).length + 1 :=
  hist_replies B histCmsdkMap (by decide) (by decide) (by decide) (by decide) σ N

end TestSupport.M7.Hist
