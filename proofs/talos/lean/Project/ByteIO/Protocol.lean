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

#print axioms emitted_prefix
#print axioms successful_write_exact
#print axioms retry_progress

end Project.ByteIO.Protocol
