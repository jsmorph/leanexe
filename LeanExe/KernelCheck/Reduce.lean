import LeanExe.KernelCheck.Substitution

namespace LeanExe.KernelCheck

/-- Tail-recursive weak-head machine. The work counter is shared with
instantiation, while the first Nat makes the Lean recursion structural. -/
def whnfLoop : Nat → Result → UInt64 → Array UInt64 → Bool → Result
  | 0, s, current, args, rebuilding =>
      if rebuilding && args.isEmpty then { s with root := current }
      else { s with status := 5 }
  | fuel + 1, s, current, args, rebuilding =>
      if rebuilding && args.isEmpty then { s with root := current }
      else if s.fuel == 0 then { s with status := 5 }
      else
        let s := { s with fuel := s.fuel - 1 }
        if rebuilding then
          let next := addNode s 4 current (args.getD (args.size - 1) 0)
          whnfLoop fuel next next.root args.pop true
        else
          let tag := nodeTag s.graph current
          if tag == 4 then
            whnfLoop fuel s (nodeA s.graph current) (args.push (nodeB s.graph current)) false
          else if tag == 3 && !args.isEmpty then
            let next := instantiateCore s (nodeB s.graph current) (args.getD (args.size - 1) 0)
            if next.status != 0 then next
            else whnfLoop fuel next next.root args.pop false
          else if args.isEmpty then { s with root := current }
          else whnfLoop fuel s current args true

/-- Weak-head beta reduction, not a typing judgment. -/
def whnfCore (initial : Result) (root : UInt64) : Result :=
  whnfLoop initial.fuel initial root #[] false

def reduceHead (g : Array UInt64) (root fuel : UInt64) : Array UInt64 :=
  if validateGraph g root != 0 then #[4]
  else packResult (whnfCore ⟨g, root, 0, fuel.toNat⟩ root)

end LeanExe.KernelCheck
