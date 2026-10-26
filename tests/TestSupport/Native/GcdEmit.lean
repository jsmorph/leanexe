import TestSupport.Native.Gcd
import LeanExe.Native.ClightCheck

/-!
The executable of the translator's end-to-end test on GCD (`tests/native/gcd.sh`).
`native-gcd emit DIR` writes, for each of the two GCD modules, the C text of its translation as
`DIR/NAME.c`, a host program `DIR/NAME_host.c` that calls the translated functions on fixed
arguments and prints each result and `lx_status`, and the lines that Talos's `run` gives for the
same calls as `DIR/NAME.expected`.  A call that traps prints the result 0, which the translated
function returns after a trap, and the trap's code.  `native-gcd check DIR` compares each
translation with the Clight that `clightgen` wrote for it as `DIR/NAME.v`.
-/

open LeanExe.Native TestSupport.Native.Gcd

/-- A call of the function `k` of a module under the C name `cname`, with its arguments in
declaration order. -/
structure Call where
  k : Nat
  cname : String
  args : List UInt64

def pairs : List (UInt64 × UInt64) :=
  [(0, 0), (0, 7), (7, 0), (12, 18), (18, 12), (1, 1), (17, 5), (1071, 462),
   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
   (12200160415121876738, 7540113804746346429), (2 ^ 63, 2 ^ 62), (2 ^ 32 * 3, 2 ^ 32 * 9)]

def loopCalls : List Call := pairs.map fun (a, b) => { k := 2, cname := "lxf_gcd", args := [a, b] }

/-- The entry `lxf_gcd` and, called directly, the recursion `lxf_2` that takes the call depth
first: from depth 998 the third frame traps at `unreachable`. -/
def recCalls : List Call :=
  pairs.map (fun (a, b) => { k := 3, cname := "lxf_gcd", args := [a, b] }) ++
  [{ k := 2, cname := "lxf_2", args := [998, 12, 18] },
   { k := 2, cname := "lxf_2", args := [999, 12, 18] },
   { k := 2, cname := "lxf_2", args := [1000, 12, 18] },
   { k := 2, cname := "lxf_2", args := [997, 1071, 462] }]

def argText (c : Call) : String := " ".intercalate (c.args.map toString)

def line (c : Call) (r : UInt64) (status : Nat) : String :=
  s!"{c.cname} {argText c} {r} {status}"

/-- What Talos's `run` gives for the call, as a line of the host's output. -/
def expected (m : Wasm.Module) (c : Call) : Except String String :=
  let args := (c.args.map Wasm.Value.i64).reverse
  match Wasm.run 100000 m c.k (m.initialStore : Wasm.Store Unit) args with
  | .Success [.i64 r] _ => pure (line c r 0)
  | .Trap _ msg => pure (line c 0 (trapCode msg))
  | _ => throw s!"{c.cname}: the run does not return one i64 or trap"

def host (calls : List Call) (protos : List String) : String :=
  let callLines := calls.map fun c =>
    let args := ", ".intercalate (c.args.map fun a => s!"{a}ULL")
    s!"  lx_status = 0U;\n  r = {c.cname}({args});\n" ++
      s!"  printf(\"{c.cname} {argText c} %llu %u\\n\", r, lx_status);\n"
  "int printf(const char *, ...);\nextern unsigned int lx_status;\n" ++ String.join protos ++
    "int main(void) {\n  unsigned long long r;\n" ++ String.join callLines ++ "  return 0;\n}\n"

def modules : List (String × Wasm.Module × List Call × List String) :=
  [("gcd_loop", loopCompiled.module, loopCalls,
     ["unsigned long long lxf_gcd(unsigned long long, unsigned long long);\n"]),
   ("gcd_rec", recCompiled.module, recCalls,
     ["unsigned long long lxf_gcd(unsigned long long, unsigned long long);\n",
      "unsigned long long lxf_2(unsigned long long, unsigned long long, unsigned long long);\n"])]

def translation (name : String) (m : Wasm.Module) : IO Translation := do
  match translate m with
  | some t => pure t
  | none => throw <| IO.userError s!"native-gcd: {name}: the module does not translate"

def emit (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, m, calls, protos) in modules do
    let t ← translation name m
    match t.text with
    | .error e => throw <| IO.userError s!"native-gcd: {name}: {e}"
    | .ok text => IO.FS.writeFile s!"{dir}/{name}.c" text
    IO.FS.writeFile s!"{dir}/{name}_host.c" (host calls protos)
    match calls.mapM (expected m) with
    | .error e => throw <| IO.userError s!"native-gcd: {name}: {e}"
    | .ok lines => IO.FS.writeFile s!"{dir}/{name}.expected" (String.join (lines.map (· ++ "\n")))
    IO.println s!"native-gcd: {name}: functions {t.funcs}"

def check (dir : String) : IO UInt32 := do
  let mut failed := false
  for (name, m, _, _) in modules do
    let t ← translation name m
    let text ← IO.FS.readFile s!"{dir}/{name}.v"
    match ClightCheck.check t text with
    | .error e =>
        IO.eprintln s!"native-gcd: {name}: {e}"
        failed := true
    | .ok [] => IO.println s!"native-gcd: {name}: the clightgen program matches the translation"
    | .ok errors =>
        for e in errors do IO.eprintln s!"native-gcd: {name}: {e}"
        failed := true
  pure (if failed then 1 else 0)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir; pure 0
  | ["check", dir] => check dir
  | _ => throw <| IO.userError "usage: native-gcd emit|check DIR"
