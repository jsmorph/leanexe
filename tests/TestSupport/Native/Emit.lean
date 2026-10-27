import TestSupport.Native.Gcd
import Verified.Examples.Arrays
import Library.Arrays.Filter.Compiled
import Library.Arrays.Range.Compiled
import Library.Arrays.Repeat.Compiled
import Library.Arrays.Search.Compiled
import Library.Arrays.Word.Compiled
import Library.Hashing.Crc.Compiled
import Library.Lists.Word.Compiled
import Library.Sorting.Insertion.Compiled
import LeanExe.Native.ClightCheck

/-!
The executable of the translator's end-to-end test (`tests/native/run.sh`).  `native-emit emit
DIR` writes, for each module of `cases`, the C text of its translation with `lx_mem` of `cap`
pages as `DIR/NAME.c`, a host program `DIR/NAME_host.c`, and the lines that Talos's `run` gives
for the host's calls as `DIR/NAME.expected`.  `native-emit check DIR` compares each translation
with the Clight that `clightgen` wrote for it as `DIR/NAME.v`.

The host calls `lx_init`, then makes each call of the case in order, in the same memory.  An
argument in memory is allocated with the module's `alloc` and written byte by byte: an array as
its length and words, a list as a chain of records of two slots, and bytes as themselves, passed
as their address and length.  After each call the host prints the export's name, `lx_status`,
the result, the four globals, and a 64-bit FNV-1a checksum of the memory below global 0, the
allocator's bump pointer.  Talos runs the same allocations, writes, and calls from the module's
initial store with its memory cap set to `cap`, and the expected line of a call that traps has
the result 0, which the translated function returns after a trap, and the trap's code.
-/

open LeanExe.Native Wasm

/-- The pages of `lx_mem` in the test. -/
def cap : Nat := 256

inductive Arg where
  | word (n : UInt64)
  | array (ws : List UInt64)
  | chain (ws : List UInt64)
  | bytes (bs : List UInt8)

structure Call where
  name : String
  args : List Arg

structure Case where
  name : String
  module : Module
  calls : List Call

/-- The state of the test: Talos's store, the host's statements, and the number of pointer
variables the host has used. -/
structure Sim where
  store : Store Unit
  lines : Array String := #[]
  vars : Nat := 0

abbrev SimM := StateT Sim (Except String)

def fuel : Nat := 100000000

def exportIndex (m : Module) (name : String) : Except String Nat :=
  match m.exports.find? (·.name == name) with
  | some e => pure e.funcIdx
  | none => throw s!"no export {name}"

def emitLine (s : String) : SimM Unit :=
  modify fun st => { st with lines := st.lines.push s }

/-- Allocates `len` bytes with the module's `alloc` in Talos and in the host, and returns the
address and the host's variable that holds it. -/
def alloc (m : Module) (len : Nat) : SimM (UInt64 × String) := do
  let k ← exportIndex m "alloc"
  let st ← get
  match run fuel m k st.store [.i64 (UInt64.ofNat len)] with
  | .Success [.i64 p] store' =>
      let v := s!"p{st.vars}"
      set { st with store := store', vars := st.vars + 1 }
      emitLine s!"  {v} = alloc({len}ULL);"
      pure (p, v)
  | _ => throw s!"alloc {len} does not return an address"

/-- Writes the word `w`, which the host computes as `wText`, at `a + off`. -/
def write64 (a : UInt64) (aText : String) (off : Nat) (w : UInt64) (wText : String := s!"{w}ULL") :
    SimM Unit := do
  modify fun st =>
    { st with store := { st.store with mem := st.store.mem.write64 (a.toUInt32 + UInt32.ofNat off) w } }
  emitLine s!"  put64({aText} + {off}ULL, {wText});"

def write8 (a : UInt64) (aText : String) (off : Nat) (b : UInt8) : SimM Unit := do
  modify fun st =>
    { st with store := { st.store with mem := st.store.mem.write8 (a.toUInt32 + UInt32.ofNat off) b } }
  emitLine s!"  put8({aText} + {off}ULL, {b}U);"

/-- The values of an argument, as Talos's values and as the host's C expressions. -/
def argValues (m : Module) : Arg → SimM (List (UInt64 × String))
  | .word n => pure [(n, s!"{n}ULL")]
  | .array ws => do
      let (p, v) ← alloc m (8 + 8 * ws.length)
      write64 p v 0 (UInt64.ofNat ws.length)
      for (w, i) in ws.zipIdx do write64 p v (8 + 8 * i) w
      pure [(p, v)]
  | .chain ws => do
      let mut next : UInt64 × String := (0, "0ULL")
      for w in ws.reverse do
        let (p, v) ← alloc m 16
        write64 (p - 24) s!"{v} - 24ULL" 0 1
        write64 (p - 16) s!"{v} - 16ULL" 0 2
        write64 (p - 8) s!"{v} - 8ULL" 0 2
        write64 p v 0 w
        write64 p v 8 next.1 next.2
        next := (p, v)
      pure [next]
  | .bytes bs => do
      let (p, v) ← alloc m bs.length
      for (b, i) in bs.zipIdx do write8 p v i b
      pure [(p, v), (UInt64.ofNat bs.length, s!"{bs.length}ULL")]

def fnv (mem : Mem) (stop : Nat) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for a in [0:stop] do
    h := (h ^^^ (mem.bytes a).toUInt64) * 1099511628211
  pure h

def globalWords (st : Store Unit) : List UInt64 :=
  st.globals.globals.map fun
    | .i64 n => n
    | _ => 0

def resultLine (name : String) (status : Nat) (r : UInt64) (st : Store Unit) : String :=
  let gs := globalWords st
  let top := (gs.headD 0).toNat
  s!"{name} {status} {r} " ++ " ".intercalate (gs.map toString) ++ s!" {fnv st.mem top}"

/-- Runs the call in Talos, writes the host's statements for it, and returns the expected
line. -/
def simCall (m : Module) (c : Call) : SimM String := do
  let k ← exportIndex m c.name
  let vals := (← c.args.mapM (argValues m)).flatten
  let args := vals.map fun (n, _) => Value.i64 n
  let cargs := ", ".intercalate (vals.map (·.2))
  let f := functionName m k
  let rs := (m.funcs[k]?.map (·.results)).getD []
  let callText := if rs.isEmpty then s!"  lx_status = 0U; {f}({cargs}); r = 0ULL;"
    else s!"  lx_status = 0U; r = {f}({cargs});"
  emitLine callText
  emitLine s!"  report(\"{c.name}\", r);"
  match run fuel m k (← get).store args.reverse with
  | .Success [.i64 r] store' =>
      modify fun st => { st with store := store' }
      pure (resultLine c.name 0 r store')
  | .Success [] store' =>
      modify fun st => { st with store := store' }
      pure (resultLine c.name 0 0 store')
  | .Trap store' msg =>
      modify fun st => { st with store := store' }
      pure (resultLine c.name (trapCode msg) 0 store')
  | _ => throw s!"{c.name}: the run does not return at most one i64 or trap"

def initialStore (m : Module) : Store Unit :=
  { (m.initialStore : Store Unit) with memoryCaps := [cap] }

def hostText (t : Translation) (m : Module) (body : Array String) (vars : Nat) : String :=
  let globals := (List.range m.globals.length).map fun i => s!"lx_g{i}"
  let protos := t.cprogram.prog_defs.filterMap fun (id, g) =>
    match g with
    | .Gfun (.Internal f) =>
        match cprototype t.gname tempName id f with
        | .ok s => some s
        | .error _ => none
    | _ => none
  let gfmt := " ".intercalate (globals.map fun _ => "%llu")
  let gargs := String.join (globals.map fun g => s!", {g}")
  let decls := if vars = 0 then "" else
    "  unsigned long long " ++ ", ".intercalate ((List.range vars).map fun i => s!"p{i}") ++ ";\n"
  "int printf(const char *, ...);\n" ++
  "extern unsigned int lx_status;\n" ++
  "extern unsigned long long lx_mem[];\n" ++
  String.join (globals.map fun g => s!"extern unsigned long long {g};\n") ++
  String.join protos ++
  "static void put8(unsigned long long a, unsigned int b) {\n" ++
  "  ((unsigned char *) lx_mem)[a] = (unsigned char) b;\n}\n" ++
  "static void put64(unsigned long long a, unsigned long long w) {\n" ++
  "  int i;\n  for (i = 0; i < 8; i++) put8(a + i, (unsigned int) (w >> (8 * i)) & 255U);\n}\n" ++
  "static unsigned long long fnv(void) {\n" ++
  "  unsigned long long h = 14695981039346656037ULL, a;\n" ++
  "  for (a = 0; a < lx_g0; a++) h = (h ^ ((unsigned char *) lx_mem)[a]) * 1099511628211ULL;\n" ++
  "  return h;\n}\n" ++
  "static void report(const char *name, unsigned long long r) {\n" ++
  s!"  printf(\"%s %u %llu {gfmt} %llu\\n\", name, lx_status, r{gargs}, fnv());\n}\n" ++
  (if vars = 0 then "" else
    "static unsigned long long alloc(unsigned long long n) {\n" ++
    "  unsigned long long p;\n  lx_status = 0U;\n  p = lxf_alloc(n);\n" ++
    "  if (lx_status != 0U) printf(\"alloc %llu: trap %u\\n\", n, lx_status);\n  return p;\n}\n") ++
  "int main(void) {\n" ++ decls ++ "  unsigned long long r;\n  lx_init();\n" ++
  String.join (body.toList.map (· ++ "\n")) ++ "  return 0;\n}\n"

def emitCase (dir : String) (c : Case) : IO Unit := do
  let some t := translate cap c.module
    | throw <| IO.userError s!"native-emit: {c.name}: the module does not translate"
  match t.text with
  | .error e => throw <| IO.userError s!"native-emit: {c.name}: {e}"
  | .ok text => IO.FS.writeFile s!"{dir}/{c.name}.c" text
  let run : SimM (List String) := c.calls.mapM (simCall c.module)
  match run.run { store := initialStore c.module } with
  | .error e => throw <| IO.userError s!"native-emit: {c.name}: {e}"
  | .ok (lines, st) =>
      IO.FS.writeFile s!"{dir}/{c.name}.expected" (String.join (lines.map (· ++ "\n")))
      IO.FS.writeFile s!"{dir}/{c.name}_host.c" (hostText t c.module st.lines st.vars)
  IO.println s!"native-emit: {c.name}: functions {t.funcs}"

/-! ## The cases -/

def words (n : Nat) (f : Nat → UInt64) : List UInt64 := (List.range n).map f

def pairs : List (UInt64 × UInt64) :=
  [(0, 0), (0, 7), (7, 0), (12, 18), (1071, 462), (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE),
   (12200160415121876738, 7540113804746346429), (2 ^ 63, 2 ^ 62)]

def big : List UInt64 := words 300 fun i => UInt64.ofNat ((i * 7919 + 13) % 1000)

/-- A module of memory operations: loads and stores at offsets 0, 5, and 3, `memory.size`, and
`memory.grow`, with two pages, data segments that begin and end off a word boundary, and global 0
at 128, so that the checksum covers the first 128 bytes. -/
def memops : Module :=
  { funcs := [
      { params := [.i64], results := [.i64], body := [.localGet 0, .wrapI64, .load64 0] },
      { params := [.i64], results := [.i64], body := [.localGet 0, .wrapI64, .load64 5] },
      { params := [.i64, .i64], body := [.localGet 0, .wrapI64, .localGet 1, .store64 0] },
      { params := [.i64, .i64], body := [.localGet 0, .wrapI64, .localGet 1, .store64 3] },
      { results := [.i64], body := [.memorySize, .extendUI32] },
      { params := [.i64], results := [.i64], body := [.localGet 0, .wrapI64, .memoryGrow, .extendUI32] }]
    exports := [⟨"load", 0⟩, ⟨"load5", 1⟩, ⟨"store", 2⟩, ⟨"store3", 3⟩, ⟨"size", 4⟩, ⟨"grow", 5⟩]
    memory := some { pagesMin := 2
                     data := [{ offset := some 13, bytes := (List.range 20).map fun i => UInt8.ofNat (i + 1) },
                              { offset := some 64, bytes := (List.range 24).map fun i => UInt8.ofNat (200 + i) },
                              { offset := some 70, bytes := [0xAA, 0xBB] }] }
    globals := [{ init := .i64 128 }, { init := .i64 0 }, { init := .i64 0 }, { init := .i64 0 }] }

def cases : List Case :=
  [{ name := "memops", module := memops
     calls := [
       { name := "load", args := [.word 8] },
       { name := "load", args := [.word 13] },
       { name := "load5", args := [.word 60] },
       { name := "store3", args := [.word 0, .word 0x0102030405060708] },
       { name := "load", args := [.word 0] },
       { name := "load", args := [.word 3] },
       { name := "store", args := [.word 40, .word 0xFFEEDDCCBBAA9988] },
       { name := "load5", args := [.word 37] },
       { name := "load", args := [.word 131064] },
       { name := "load", args := [.word 131065] },
       { name := "load5", args := [.word 131060] },
       { name := "store3", args := [.word 131061, .word 7] },
       { name := "store3", args := [.word 131062, .word 7] },
       { name := "load", args := [.word 0xFFFFFFF8] },
       { name := "size", args := [] },
       { name := "grow", args := [.word 3] },
       { name := "size", args := [] },
       { name := "store3", args := [.word 327666, .word 0x1122334455667788] },
       { name := "load5", args := [.word 327664] },
       { name := "load", args := [.word 327672] },
       { name := "load", args := [.word 327673] },
       { name := "grow", args := [.word (UInt64.ofNat (cap - 5))] },
       { name := "grow", args := [.word 1] },
       { name := "grow", args := [.word 0] },
       { name := "grow", args := [.word 0xFFFFFFFF] },
       { name := "size", args := [] },
       { name := "load", args := [.word (UInt64.ofNat (cap * 65536 - 8))] },
       { name := "load", args := [.word (UInt64.ofNat (cap * 65536 - 7))] }] },
   { name := "gcd_loop", module := TestSupport.Native.Gcd.loopCompiled.module
     calls := pairs.map fun (a, b) => { name := "gcd", args := [.word a, .word b] } },
   { name := "gcd_rec", module := TestSupport.Native.Gcd.recCompiled.module
     calls := pairs.map fun (a, b) => { name := "gcd", args := [.word a, .word b] } },
   { name := "arrays", module := Verified.Examples.Arrays.compiled.module
     calls := [
       { name := "sum", args := [.array []] },
       { name := "sum", args := [.array [1, 2, 3, 0xFFFFFFFFFFFFFFFF]] },
       { name := "sum", args := [.array big] },
       { name := "dot", args := [.array [1, 2, 3], .array [4, 5, 6]] },
       { name := "dot", args := [.array [1, 2, 3], .array [4]] },
       { name := "count", args := [.array [5, 1, 5, 5, 2], .word 5] },
       { name := "at3", args := [.array [10, 20, 30, 40], .word 2] },
       { name := "at3", args := [.array [10, 20, 30, 40], .word 3] },
       { name := "at3", args := [.array [10, 20, 30, 40], .word 0xFFFFFFFFFFFFFFFF] },
       { name := "sumBoth", args := [.array [1, 2], .array [30, 40, 50]] },
       { name := "larger", args := [.array [1, 2], .array [30, 40, 50]] },
       { name := "larger", args := [.array [1, 2, 3, 4], .array [30]] }] },
   { name := "liblists", module := Library.Lists.Word.compiled.module
     calls := [
       { name := "listSum", args := [.chain []] },
       { name := "listSum", args := [.chain [1, 2, 3, 4]] },
       { name := "range", args := [.word 0] },
       { name := "range", args := [.word 12] },
       { name := "sum", args := [.chain [5, 6, 7], .word 100] },
       { name := "reverse", args := [.chain [1, 2, 3], .chain [9]] },
       { name := "increment", args := [.chain [1, 2, 0xFFFFFFFFFFFFFFFF]] },
       { name := "increment", args := [.chain (words 999 UInt64.ofNat)] },
       { name := "increment", args := [.chain (words 1001 UInt64.ofNat)] }] },
   { name := "libsort", module := Library.Sorting.Insertion.compiled.module
     calls := [
       { name := "sortInsert", args := [.array []] },
       { name := "sortInsert", args := [.array [3, 1, 2]] },
       { name := "sortInsert", args := [.array big] }] },
   { name := "libsearch", module := Library.Arrays.Search.compiled.module
     calls := [
       { name := "count", args := [.array [1, 7, 7, 3], .word 7] },
       { name := "firstZero", args := [.array [4, 5, 0, 6], .word 4] }] },
   { name := "libfilter", module := Library.Arrays.Filter.compiled.module
     calls := [
       { name := "removeAll", args := [.array [1, 2, 1, 3, 1], .word 1] },
       { name := "below", args := [.array [9, 1, 8, 2, 7, 3], .word 5, .word 2] },
       { name := "clearUntil", args := [.array [1, 2, 3, 4], .word 3] }] },
   { name := "librepeat", module := Library.Arrays.Repeat.compiled.module
     calls := [{ name := "repeated", args := [.array [1, 2, 3], .word 4] }] },
   { name := "librange", module := Library.Arrays.Range.compiled.module
     calls := [{ name := "evens", args := [.word 0] }, { name := "evens", args := [.word 9] }] },
   { name := "libwordarray", module := Library.Arrays.Word.compiled.module
     calls := [{ name := "scaled", args := [.array [1, 2, 3], .word 0x100000001] }] },
   { name := "crc", module := Library.Hashing.Crc.compiled.module
     calls := [
       { name := "crc32", args := [.array [], .word 0] },
       { name := "crc32", args := [.array [0x3837363534333231, 0x39], .word 9] },
       { name := "crc32c", args := [.array [0x3837363534333231, 0x39], .word 9] },
       { name := "crc32Update", args := [.word 0xCBF43926, .array [0x61], .word 1] },
       { name := "crc32", args := [.array (words 40 fun i => UInt64.ofNat (i * 0x0101010101010101)), .word 317] }] }]

def emit (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for c in cases do emitCase dir c

def check (dir : String) : IO UInt32 := do
  let mut failed := false
  for c in cases do
    let some t := translate cap c.module
      | throw <| IO.userError s!"native-emit: {c.name}: the module does not translate"
    let text ← IO.FS.readFile s!"{dir}/{c.name}.v"
    match ClightCheck.check t text with
    | .error e =>
        IO.eprintln s!"native-emit: {c.name}: {e}"
        failed := true
    | .ok [] => IO.println s!"native-emit: {c.name}: the clightgen program matches the translation"
    | .ok errors =>
        for e in errors do IO.eprintln s!"native-emit: {c.name}: {e}"
        failed := true
  pure (if failed then 1 else 0)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir; pure 0
  | ["check", dir] => check dir
  | ["names"] => do
      for c in cases do IO.println c.name
      pure 0
  | _ => throw <| IO.userError "usage: native-emit emit|check DIR, or native-emit names"
