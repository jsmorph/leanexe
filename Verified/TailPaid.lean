import Verified.TailBound

namespace Verified

def TailBody.paidResult (flags : Flags S) (modes : List Mode) (paid : List Bool) :
    {Γ : List Ty} → TailBody S params result Γ → Bool
  | _, .ret value => value.paid flags modes paid (fun _ => false)
  | _, .next _ => true
  | _, .ite _ yes no => yes.paidResult flags modes paid && no.paidResult flags modes paid
  | _, .letE value body =>
    body.paidResult flags (value.mode modes :: modes)
      (value.paid flags modes paid (fun i => body.uses (i + 1)) :: paid)
  | _, .letPair value body =>
    body.paidResult flags (value.mode modes :: value.mode modes :: modes) (false :: false :: paid)

def TailFunc.paidResult (func : TailFunc S) (flags : Flags S) : Bool :=
  !func.result.scalar && func.body.paidResult flags (entryModes func.params func.modes)
    (func.paidParams flags)

def TailFunc.flags (func : TailFunc S) (flags : Flags S) : Flags (func.sig :: S) :=
  .cons (func.paidParams flags) (func.paidResult flags) flags

end Verified
