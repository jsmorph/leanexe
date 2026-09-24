import Mathlib.Data.List.TakeDrop
import Init.Omega

/-!
The byte-I/O protocol, with nondeterministic syscall and clock observations.
`writeStep` follows one iteration of the emitted write loop. A successful
partial syscall commits its prefix even if the following clock call fails.
Clock readings are observations, not a bound on host scheduling latency.
-/
namespace Project.ByteIO.Protocol

abbrev Bytes := List UInt8

def maxTime : Nat := 2 ^ 64 - 1

def deadline (now timeout : Nat) : Nat := min (now + timeout) maxTime

theorem deadline_bounded (now timeout : Nat) : deadline now timeout ≤ maxTime :=
  Nat.min_le_right _ _

theorem deadline_no_wrap (now timeout : Nat) (h : now ≤ maxTime) :
    now ≤ deadline now timeout := by
  simp only [deadline, Nat.le_min]
  omega

structure WriteState where
  sent : Bytes
  pending : Bytes
  now : Nat
  limit : Nat
  result : Option UInt32
  deriving DecidableEq, Repr

def initial (bytes : Bytes) (now timeout : Nat) : WriteState :=
  { sent := [], pending := bytes, now, limit := deadline now timeout,
    result := if bytes.isEmpty then some 0 else none }

/-- `transferred` is a successful fd_write followed, when needed, by a clock
observation. `retry` represents AGAIN/INTR followed by wait. Other errors
return immediately. An already completed state is absorbing. -/
inductive WriteEvent where
  | transferred (count : Nat) (clock : Except UInt32 Nat)
  | retry (wait : Except UInt32 Nat)
  | error (errno : UInt32)
  deriving DecidableEq, Repr

def observe (s : WriteState) (clock : Except UInt32 Nat) : WriteState :=
  match clock with
  | .error errno => { s with result := some errno }
  | .ok now =>
      { s with
        now := max s.now now
        result := if s.limit ≤ max s.now now then some 73 else none }

def writeStep (s : WriteState) (event : WriteEvent) : WriteState :=
  if s.result.isSome then s else
  match event with
  | .error errno => { s with result := some errno }
  | .retry wait => observe s wait
  | .transferred n clock =>
      if n = 0 ∨ s.pending.length < n then { s with result := some 29 }
      else
        let next := { s with
          sent := s.sent ++ s.pending.take n
          pending := s.pending.drop n }
        if next.pending.isEmpty then { next with result := some 0 }
        else observe next clock

def run (s : WriteState) (events : List WriteEvent) : WriteState :=
  events.foldl writeStep s

/-- The bytes committed by successful writes, followed by the unconsumed
suffix, are exactly the caller's original bytes. -/
def Conserves (bytes : Bytes) (s : WriteState) : Prop :=
  s.sent ++ s.pending = bytes

theorem initial_conserves (bytes : Bytes) (now timeout : Nat) :
    Conserves bytes (initial bytes now timeout) := by
  simp [Conserves, initial]

theorem observe_conserves (bytes : Bytes) (s : WriteState) (clock : Except UInt32 Nat)
    (h : Conserves bytes s) : Conserves bytes (observe s clock) := by
  cases clock <;> exact h

theorem writeStep_conserves (bytes : Bytes) (s : WriteState) (event : WriteEvent)
    (h : Conserves bytes s) : Conserves bytes (writeStep s event) := by
  unfold writeStep
  split
  · exact h
  · cases event with
    | error errno => exact h
    | retry wait => exact observe_conserves bytes s wait h
    | transferred n clock =>
      dsimp only
      split
      · exact h
      · have hn : Conserves bytes
            { s with sent := s.sent ++ s.pending.take n, pending := s.pending.drop n } := by
          simpa [Conserves, List.append_assoc] using h
        split
        · exact hn
        · exact observe_conserves _ _ _ hn

theorem run_conserves (bytes : Bytes) (s : WriteState) (events : List WriteEvent)
    (h : Conserves bytes s) : Conserves bytes (run s events) := by
  induction events generalizing s with
  | nil => exact h
  | cons event events ih =>
    exact ih _ (writeStep_conserves bytes s event h)

theorem emitted_prefix (bytes : Bytes) (now timeout : Nat) (events : List WriteEvent) :
    (run (initial bytes now timeout) events).sent <+: bytes := by
  exact ⟨_, run_conserves bytes _ events (initial_conserves bytes now timeout)⟩

/-- Error observations cannot claim success. This is a host-contract
obligation: an errno passed as an error is nonzero. -/
def ValidEvent : WriteEvent → Prop
  | .error errno => errno ≠ 0
  | .retry (.error errno) => errno ≠ 0
  | .transferred _ (.error errno) => errno ≠ 0
  | _ => True

def SuccessComplete (s : WriteState) : Prop := s.result = some 0 → s.pending = []

theorem observe_success (s : WriteState) (clock : Except UInt32 Nat)
    (h : ∀ errno, clock = .error errno → errno ≠ 0) :
    SuccessComplete (observe s clock) := by
  cases clock with
  | error errno => simp [SuccessComplete, observe, h errno rfl]
  | ok now => simp [SuccessComplete, observe]

theorem writeStep_success (s : WriteState) (event : WriteEvent)
    (hs : SuccessComplete s) (he : ValidEvent event) :
    SuccessComplete (writeStep s event) := by
  unfold writeStep
  split
  · exact hs
  · cases event with
    | error errno => simp [SuccessComplete, show errno ≠ 0 from he]
    | retry wait =>
      apply observe_success
      intro errno h; subst h; exact he
    | transferred n clock =>
      dsimp only
      split
      · simp [SuccessComplete]
      · split
        · intro _
          exact List.isEmpty_iff.mp ‹_›
        · apply observe_success
          intro errno h; subst h; exact he

theorem initial_success (bytes : Bytes) (now timeout : Nat) :
    SuccessComplete (initial bytes now timeout) := by
  simp only [SuccessComplete, initial]
  split <;> simp_all

theorem run_success (s : WriteState) (events : List WriteEvent)
    (hs : SuccessComplete s) (he : ∀ e ∈ events, ValidEvent e) :
    SuccessComplete (run s events) := by
  induction events generalizing s with
  | nil => exact hs
  | cons event events ih =>
    apply ih _ (writeStep_success s event hs (he event (by simp)))
    intro e hm; exact he e (by simp [hm])

theorem successful_write_exact (bytes : Bytes) (now timeout : Nat) (events : List WriteEvent)
    (he : ∀ e ∈ events, ValidEvent e)
    (h : (run (initial bytes now timeout) events).result = some 0) :
    (run (initial bytes now timeout) events).sent = bytes := by
  have hc := run_conserves bytes _ events (initial_conserves bytes now timeout)
  have hs := run_success _ events (initial_success bytes now timeout) he h
  simpa [Conserves, hs] using hc

theorem writeStep_deadline (s : WriteState) (event : WriteEvent) :
    (writeStep s event).limit = s.limit := by
  cases event <;> simp [writeStep, observe]
  all_goals repeat first | split | (solve | simp_all [observe])

theorem observe_continues_before_deadline (s : WriteState) (clock : Except UInt32 Nat)
    (h : (observe s clock).result = none) :
    (observe s clock).now < s.limit := by
  cases clock with
  | error errno => simp [observe] at h
  | ok now =>
    simp only [observe] at h ⊢
    split at h <;> simp_all <;> omega

/-- A retry that observes a strictly later clock has a decreasing budget.
Together with the strictly shorter suffix on a positive write, this is the
well-founded measure for termination under clock progress. -/
def rank (s : WriteState) : Nat := s.pending.length + (s.limit - s.now)

theorem retry_progress (s : WriteState) (now : Nat)
    (hprogress : s.now < now) (hbefore : now < s.limit) :
    rank (observe s (.ok now)) < rank s := by
  simp [rank, observe, Nat.max_eq_right (Nat.le_of_lt hprogress)]
  omega

/-- The only environmental liveness assumption is that a retry which
continues observes a strictly later clock. Successful transfers already
make progress by shortening the pending suffix. Errors terminate. -/
def ProgressEvent (s : WriteState) : WriteEvent → Prop
  | .retry (.ok now) => s.now < now
  | _ => True

theorem observe_rank_le (s : WriteState) (clock : Except UInt32 Nat) :
    rank (observe s clock) ≤ rank s := by
  cases clock <;> simp [rank, observe]
  omega

theorem writeStep_progress (s : WriteState) (event : WriteEvent)
    (hs : s.result = none) (he : ProgressEvent s event)
    (hc : (writeStep s event).result = none) :
    rank (writeStep s event) < rank s := by
  cases event with
  | error errno => simp [writeStep, hs] at hc
  | retry wait =>
    cases wait with
    | error errno => simp [writeStep, hs, observe] at hc
    | ok now =>
      simp only [writeStep, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      apply retry_progress s now he
      have hb := observe_continues_before_deadline s (.ok now) hc
      simp only [observe] at hb
      omega
  | transferred n clock =>
    simp only [writeStep, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hc ⊢
    split at hc
    · simp at hc
    · rename_i hn
      rw [if_neg hn]
      split at hc
      · simp at hc
      · rename_i hnonempty
        rw [if_neg hnonempty]
        have hle := observe_rank_le
          { s with sent := s.sent ++ s.pending.take n, pending := s.pending.drop n } clock
        simp only [rank, List.length_drop, hs] at hle ⊢
        omega

/-- A trace supplies environmental progress at each state, including after
an earlier event has completed. The latter observations are ignored. -/
def ProgressTrace : WriteState → List WriteEvent → Prop
  | _, [] => True
  | s, e :: es => ProgressEvent s e ∧ ProgressTrace (writeStep s e) es

theorem completed_absorbing (s : WriteState) (events : List WriteEvent)
    (hs : s.result ≠ none) : (run s events).result = s.result := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    have he : writeStep s e = s := by simp [writeStep, Option.isSome_iff_ne_none.mpr hs]
    simpa only [run, List.foldl_cons, he] using ih

theorem continuing_trace_bounded (s : WriteState) (events : List WriteEvent)
    (hp : ProgressTrace s events) (hc : (run s events).result = none) :
    events.length ≤ rank s := by
  induction events generalizing s with
  | nil => simp
  | cons e es ih =>
    have hs : s.result = none := by
      by_contra hn
      exact hn ((completed_absorbing s (e :: es) hn).symm.trans hc)
    have hn : (writeStep s e).result = none := by
      by_contra hn
      exact hn ((completed_absorbing (writeStep s e) es hn).symm.trans hc)
    have hlt := writeStep_progress s e hs hp.1 hn
    have hle := ih (writeStep s e) hp.2 hc
    simp only [List.length_cons]
    omega

/-- Every trace longer than the finite byte/deadline budget has completed
under the stated progress assumption. Host calls themselves must return. -/
theorem write_terminates (s : WriteState) (events : List WriteEvent)
    (hp : ProgressTrace s events) (hl : rank s < events.length) :
    (run s events).result ≠ none := by
  intro hc
  have := continuing_trace_bounded s events hp hc
  omega

#print axioms writeStep_progress
#print axioms write_terminates

#print axioms emitted_prefix
#print axioms successful_write_exact
#print axioms retry_progress

end Project.ByteIO.Protocol
