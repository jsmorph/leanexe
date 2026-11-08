import Lean

open Lean

/-- An entry as its two files give it. -/
structure Entry where
  id : String
  dir : System.FilePath
  modules : Array Name
  /-- The names of `declarations` and `examples`. -/
  listed : Array Name
  /-- The files of `unimported` with the names that the README cites from each. -/
  unimported : Array (String × Array Name)
  readme : String

/-- The inline code spans of a Markdown text, outside its fenced blocks. -/
def codeSpans (text : String) : Array String := Id.run do
  let mut prose : Array String := #[]
  let mut fenced := false
  for line in text.splitOn "\n" do
    if (line.dropWhile Char.isWhitespace).startsWith "```" then
      fenced := !fenced
    else if !fenced then
      prose := prose.push line
  let pieces := ("\n".intercalate prose.toList).splitOn "`"
  return (pieces.zipIdx.filterMap fun (piece, i) => if i % 2 == 1 then some piece else none).toArray

/-- The name that a code span writes when it has the form of a qualified name: identifiers
separated by dots, the first of which starts with an upper-case letter.  Paths, which contain `/`,
and expressions over local names, such as `p.f.implements`, do not have that form. -/
def qualified? (code : String) : Option Name :=
  let parts := code.splitOn "."
  let identifier (part : String) : Bool :=
    !part.isEmpty && !part.front.isDigit &&
      part.all fun c => c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  if parts.length ≥ 2 && code.front.isUpper && parts.all identifier then
    some (parts.foldl Name.mkStr .anonymous)
  else none

/-- Reads the entries under `entries`, in the order of their directories' names.  The second
component holds a message for each entry whose `id` differs from its directory's name.  An entry
without a `README.md` and an `entry.json` that does not parse raise an error. -/
def readEntries (entries : System.FilePath) : IO (Array Entry × Array String) := do
  let mut read : Array Entry := #[]
  let mut found : Array String := #[]
  let dirs := (← entries.readDir).qsort fun a b => a.fileName < b.fileName
  for dir in dirs do
    unless ← (dir.path / "README.md").pathExists do
      throw <| IO.userError s!"{dir.path}: missing README.md"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dir.path / "entry.json"))
    let id ← IO.ofExcept <| json.getObjValAs? String "id"
    unless id == dir.fileName do
      found := found.push s!"{dir.fileName}: id {id} differs from the directory name"
    let names (field : String) : IO (Array Name) := do
      return (← IO.ofExcept <| json.getObjValAs? (Array String) field).map String.toName
    let unimported ← match json.getObjVal? "unimported" with
      | .error _ => pure #[]
      | .ok value => do
        let files ← IO.ofExcept value.getObj?
        files.toList.toArray.mapM fun (file, names) => do
          return (file, (← IO.ofExcept <| fromJson? (α := Array String) names).map String.toName)
    read := read.push {
      id, dir := dir.path, modules := ← names "modules",
      listed := (← names "declarations") ++ (← names "examples"), unimported,
      readme := ← IO.FS.readFile (dir.path / "README.md") }
  return (read, found)

/-- Imports the modules that the entries list. -/
def importEntries (entries : Array Entry) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (entries.flatMap (·.modules) |>.map fun module =>
    { module, importAll := false, isExported := true, isMeta := false }) {}

/-- The indices of the modules that `roots` import, directly or transitively, with the roots. -/
partial def closure (env : Environment) (roots : Array Name) : Std.HashSet Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := roots.filterMap fun root => (env.getModuleIdx? root).map (·.toNat)
  while !todo.isEmpty do
    let idx := todo.back!
    todo := todo.pop
    unless seen.contains idx do
      seen := seen.insert idx
      for i in env.header.moduleData[idx]!.imports do
        if let some j := env.getModuleIdx? i.module then
          todo := todo.push j.toNat
  return seen

/-- The namespaces that hold the constants of `env`: every proper prefix of a constant's name.
`importModules` without `loadExts` leaves the extension that `Environment.isNamespace` reads at its
initial state. -/
def namespaces (env : Environment) : Std.HashSet Name :=
  env.constants.fold (init := {}) fun set name _ => Id.run do
    let mut set := set
    let mut pre := name.getPrefix
    while !pre.isAnonymous && !set.contains pre do
      set := set.insert pre
      pre := pre.getPrefix
    return set

/-- Whether `name` is a declaration, a module, or a namespace of `env`, or the path of a file
from the working directory, the repository's root. -/
def resolves (env : Environment) (spaces : Std.HashSet Name) (name : Name) (code : String) :
    IO Bool := do
  if env.contains name || (env.getModuleIdx? name).isSome || spaces.contains name then
    return true
  System.FilePath.pathExists code

/-- One message for each listed declaration or example that the imported environment lacks or that
the entry's own modules do not import, for each qualified name in a README's code spans that does
not resolve and that `unimported` does not list, for each name of `unimported` that the
environment declares, for each file of `unimported` that does not exist, and for each entry whose
`id` differs from its directory's name. -/
def problems (entries : System.FilePath) : IO (Array String) := do
  let (read, found) ← readEntries entries
  let env ← importEntries read
  let spaces := namespaces env
  let mut found := found
  for entry in read do
    let own := closure env entry.modules
    for decl in entry.listed do
      match env.getModuleIdxFor? decl with
      | none =>
        found := found.push s!"{entry.id}: {decl} does not exist"
      | some idx =>
        unless own.contains idx.toNat do
          found := found.push s!"{entry.id}: the entry's modules do not import {decl}"
    let exempt := entry.unimported.flatMap (·.2)
    for (file, names) in entry.unimported do
      unless ← System.FilePath.pathExists file do
        found := found.push s!"{entry.id}: the file {file} of unimported does not exist"
      for name in names do
        if env.contains name then
          found := found.push s!"{entry.id}: {name} of unimported is declared by an imported module"
    for code in codeSpans entry.readme do
      if let some name := qualified? code then
        unless exempt.contains name || (← resolves env spaces name code) do
          found := found.push s!"{entry.id}: `{code}` in README.md does not resolve"
  return found

/-- Runs `git` with `args` in the working directory and returns its standard output. -/
def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"git {" ".intercalate args.toList}: {out.stderr}"
  return out.stdout

/-- For each entry, the files of the repository that hold the declarations it names, in its JSON
or its README, and the files of its `unimported`, which differ in the working tree from the last
commit that changed the entry.  The report concerns guidance that may be stale and fails only when
an entry or `git` does. -/
def changed (entries : System.FilePath) : IO (Array String) := do
  let (read, _) ← readEntries entries
  let env ← importEntries read
  let sources ← getSrcSearchPath
  let root ← IO.FS.realPath "."
  let mut report : Array String := #[]
  for entry in read do
    let named := entry.listed ++ (codeSpans entry.readme).filterMap qualified?
    let mut files : Array String := entry.unimported.map (·.1)
    for name in named do
      let module? := match env.getModuleIdxFor? name with
        | some idx => env.header.moduleNames[idx.toNat]?
        | none => if (env.getModuleIdx? name).isSome then some name else none
      let some module := module? | continue
      let some path ← sources.findModuleWithExt "lean" module | continue
      let path ← IO.FS.realPath path
      let some relative := path.toString.dropPrefix? (root.toString ++ "/") | continue
      let relative := relative.toString
      unless relative.startsWith ".lake/" || files.contains relative do
        files := files.push relative
    let base := (← git #["log", "-1", "--format=%h", "--", entry.dir.toString]).trimAscii.toString
    if base.isEmpty then
      report := report.push s!"{entry.id}: no commit changes the entry"
      continue
    let diff ← git (#["diff", "--name-only", base, "--"] ++ files.qsort (· < ·))
    let paths := (diff.splitOn "\n").filter (!·.isEmpty)
    unless paths.isEmpty do
      report := report.push s!"{entry.id}: changed since {base}: {", ".intercalate paths}"
  return report

/-- `lean --run VKB/Check.lean [ENTRIES]` reports the problems of `problems` and exits with status 1
when there is one.  `lean --run VKB/Check.lean --changed [ENTRIES]` prints the report of `changed`
and exits with status 0.  `ENTRIES` is `VKB/entries` unless given. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--changed" :: rest =>
    for line in ← changed (rest.headD "VKB/entries") do
      IO.println line
    return 0
  | _ =>
    let found ← problems (args.headD "VKB/entries")
    for message in found do
      IO.eprintln message
    return if found.isEmpty then 0 else 1
