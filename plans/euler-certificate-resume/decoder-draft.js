"use strict";
const fs = require("node:fs");
const crypto = require("node:crypto");
const root = "proofs/talos/lean/Project/EulerCertificate/";
const previous = "proofs/talos/lean/Project/EulerReconstructed/";
const ns = "Project.EulerCertificate.Artifact";
const size = 45644;
const digest = "22696951ce81106990843e19494430292bdde35183058a34ff30133cc47bd981";
const bytes = fs.readFileSync(`proofs/artifacts/euler_certificate/${digest}/program.wasm`);
if (bytes.length !== size || crypto.createHash("sha256").update(bytes).digest("hex") !== digest) throw Error("artifact mismatch");
const rows = (name, old = false) => fs.readFileSync(`tmp/euler-${old ? "reconstructed" : "certificate"}-${name}-${old ? "20260915" : "20260916"}.csv`, "utf8").trim().split("\n").map(x => x.split(","));
const sequences = new Map(), codes = new Map(), sections = new Map();
for (const row of rows("nested")) {
  if (row[0] === "seq") {
    const [, path, start, fuel, allowElse, finish, ending, limit] = row;
    sequences.set(path, { path, start: +start, fuel: +fuel, allowElse, finish: +finish, ending, limit: +limit, offsets: [] });
  } else if (row[0] === "at") sequences.get(row[1]).offsets.push({ index: +row[2], fuel: +row[3], pos: +row[4] });
  else if (row[1] === "code") codes.set(+row[0], { start: +row[2], stop: +row[3], body: +row[4], payload: +row[5] });
}
for (const row of rows("sections")) {
  if (row[0] === "section") {
    const [, id, start, payload, items, count, end] = row.map((x, i) => i ? +x : x);
    sections.set(id, { start, payload, items, count, end, entries: [] });
  } else if (row[0] === "item") sections.get(+row[1]).entries.push({ index: +row[2], start: +row[3], end: +row[4] });
}
if (codes.size !== 195 || sections.size !== 6 || sections.get(10).end !== size || sections.get(7).count !== 11) throw Error("unexpected artifact shape");
const cur = (pos, limit = size) => `{ bytes := artifactBytes, pos := ${pos}, limit := ${limit} }`;
const header = (imports = []) => `import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
${imports.map(x => `import ${x}`).join("\n")}

namespace ${ns}
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

`;
const outputs = new Map(), targets = [];
const save = (name, source) => {
  outputs.set(root + name + ".lean", source + `\nend ${ns}\n`);
  targets.push(`Project.EulerCertificate.${name}`);
};
function group(name, declarations, imports = []) {
  if (declarations.length <= 16) return save(name, header(imports) + declarations.join("\n"));
  let prior;
  for (let first = 0, part = 0; first < declarations.length; first += 16, part++) {
    const partName = `${name}Part${part}`;
    save(partName, header(prior ? [prior] : imports) + declarations.slice(first, first + 16).join("\n"));
    prior = `Project.EulerCertificate.${partName}`;
  }
  outputs.set(root + name + ".lean", `import ${prior}\n`);
  targets.push(`Project.EulerCertificate.${name}`);
}
const seqName = (index, path, offset) => `code${index}_seq_${path.replaceAll(".", "_")}_tail${offset}_decoded`;
function body(path) {
  const parts = path.split(".");
  let result = `(Cache.raw.codes[${parts[0]}]!).body`;
  for (let i = 1; i < parts.length; i += 2) result = `((${result})[${parts[i]}]!).childBody ${parts[i + 1] === "e"}`;
  return result;
}
const groups = [];
let certificates = 0;
for (let first = 0; first < codes.size; first += 8) {
  const last = Math.min(first + 7, codes.size - 1), name = `ArtifactCodes${first}To${last}`, declarations = [];
  groups.push(`Project.EulerCertificate.${name}`);
  for (let index = first; index <= last; index++) {
    const code = codes.get(index), text = String(index);
    const selected = [...sequences.values()].filter(s => s.path.split(".")[0] === text && (s.path === text || s.finish - s.start >= 128));
    selected.sort((a, b) => b.path.split(".").length - a.path.split(".").length);
    for (const s of selected) {
      let end = s.finish;
      for (const offset of [...s.offsets].reverse()) {
        if (end - offset.pos < 128 && offset.index !== 0) continue;
        declarations.push(`@[cbv_eval] theorem ${seqName(index, s.path, offset.index)} :
    instructionSequenceAt ${offset.fuel} ${s.allowElse} ${cur(offset.pos, s.limit)} =
      .ok (((${body(s.path)}).drop ${offset.index}, .${s.ending}), ${cur(s.finish, s.limit)}) := by
  cbv
`);
        end = offset.pos;
        certificates++;
      }
    }
    declarations.push(`theorem code${index}_decoded :
    code ${cur(code.start)} =
      .ok (Cache.raw.codes[${index}]!, ${cur(code.stop)}) := by
  refine code_eq_of_parts (size := ${code.stop - code.payload})
    (payload := ${cur(code.payload)})
    (bodyStart := ${cur(code.body, code.stop)})
    (bodyFinish := ${cur(code.stop, code.stop)})
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact ${seqName(index, text, 0)}
  · rfl

#print axioms code${index}_decoded
`);
  }
  group(name, declarations);
}
function vector(name, id, field, parser, singular, imports = [], items = true) {
  const s = sections.get(id), declarations = [];
  if (items) {
    const entries = s.entries.map(e => `theorem ${singular}${e.index}_decoded :
    ${parser} ${cur(e.start, s.end)} =
      .ok (Cache.raw.${field}[${e.index}]!, ${cur(e.end, s.end)}) := by cbv

#print axioms ${singular}${e.index}_decoded
`);
    group(`${name}Items`, entries);
    imports = [...imports, `Project.EulerCertificate.${name}Items`];
  }
  declarations.push(`theorem ${field}_tail${s.count}_decoded :
    Internal.vectorLoop ${parser} 0 ${cur(s.end, s.end)} =
      .ok (Cache.raw.${field}.drop ${s.count}, ${cur(s.end, s.end)}) := by rfl
`);
  for (let i = s.count - 1; i >= 0; i--) declarations.push(`theorem ${field}_tail${i}_decoded :
    Internal.vectorLoop ${parser} ${s.count - i} ${cur(s.entries[i].start, s.end)} =
      .ok (Cache.raw.${field}.drop ${i}, ${cur(s.end, s.end)}) := by
  exact vectorLoop_eq_cons ${singular}${i}_decoded ${field}_tail${i + 1}_decoded
`);
  declarations.push(`theorem ${field}_vector_decoded :
    vector ${parser} ${cur(s.payload, s.end)} =
      .ok (Cache.raw.${field}, ${cur(s.end, s.end)}) := by
  refine vector_eq_of_parts (length := ${s.count})
    (itemsStart := ${cur(s.items, s.end)}) ?_ ?_ ?_
  · cbv
  · decide
  · exact ${field}_tail0_decoded

#print axioms ${field}_vector_decoded
`);
  declarations.push(`theorem ${field}_section_decoded :
    sized (vector ${parser}) ${cur(s.start)} =
      .ok (Cache.raw.${field}, ${cur(s.end)}) := by
  refine sized_eq_of_parts (size := ${s.end - s.payload})
    (payload := ${cur(s.payload)}) (finish := ${cur(s.end, s.end)})
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact ${field}_vector_decoded
  · rfl

#print axioms ${field}_section_decoded
`);
  save(name, header(imports) + declarations.join("\n"));
}
vector("ArtifactTypeSection", 1, "types", "funcType", "type");
vector("ArtifactFunctionSection", 3, "functionTypeIndices", "Leb.u32", "functionIndex");
vector("ArtifactMemorySection", 5, "memories", "memoryType", "memory");
vector("ArtifactGlobalSection", 6, "globals", "global", "global");
vector("ArtifactExportSection", 7, "exports", "exportEntry", "export");
vector("ArtifactCodeVector", 10, "codes", "code", "code", groups, false);
outputs.set(root + "ArtifactMetadata.lean", ["Type", "Function", "Memory", "Global", "Export"].map(x => `import Project.EulerCertificate.Artifact${x}Section`).join("\n") + "\n");
targets.push("Project.EulerCertificate.ArtifactMetadata");
const rename = s => s.replaceAll("EulerReconstructed", "EulerCertificate");
const offsets = new Map();
for (let i = 0; i <= 14; i++) offsets.set(30726 - i, size - i);
for (const row of rows("sections", true)) if (row[0] === "section") {
  const s = sections.get(+row[1]);
  offsets.set(+row[2] - 1, s.start - 1);
  offsets.set(+row[2], s.start);
  offsets.set(+row[6], s.end);
}
const replaceOffsets = s => s.replace(/\b[0-9]+\b/g, x => offsets.get(+x) ?? x);
for (const name of ["ArtifactParsedStates", "ArtifactParsedCode", "ArtifactParsedSections", "ArtifactParsed"]) {
  outputs.set(root + name + ".lean", replaceOffsets(rename(fs.readFileSync(previous + name + ".lean", "utf8"))));
  targets.push(`Project.EulerCertificate.${name}`);
}
for (const name of ["ArtifactDecoded", "ArtifactRawCache", "ArtifactValidation", "ArtifactValidationMetadata", "ArtifactValidationExports"]) {
  outputs.set(root + name + ".lean", rename(fs.readFileSync(previous + name + ".lean", "utf8")));
}
let translation = fs.readFileSync(root + "ArtifactTranslation.lean", "utf8").replace("import Project.EulerCertificate.Program", "import Project.EulerCertificate.Spec\nimport Project.EulerCertificate.Program");
const behavior = [["exact", "ExactSpecFor"], ["enclosure", "EnclosedSpecFor"]].map(([name, predicate]) => `theorem artifact_solve_${name} :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      Project.EulerCertificate.Spec.${predicate} validated.toTalos := by
  exact artifact_correct_of Project.EulerCertificate.Spec.${predicate}
    Project.EulerCertificate.Spec.solve_${name}

#print axioms artifact_solve_${name}
`).join("\n");
translation = translation.replace(`end ${ns}`, `#print axioms translation_cache_eq\n#print axioms artifact_module_eq_cache\n\n${behavior}\nend ${ns}`);
outputs.set(root + "ArtifactTranslation.lean", translation);
outputs.set(root + "HostInitial.lean", rename(fs.readFileSync(previous + "HostInitial.lean", "utf8")).replaceAll("150", "192"));
let byteSource = `import Project.Artifact.Binary.Translate\n\nset_option maxRecDepth 1048576\n\nnamespace ${ns}\n\ndef sha256 : String :=\n  "${digest}"\n\n`;
const chunks = [];
for (let start = 0; start < size; start += 8192) {
  const name = `bytesChunk${chunks.length}`, values = [...bytes.subarray(start, start + 8192)], lines = [];
  chunks.push(name);
  for (let i = 0; i < values.length; i += 20) lines.push("    " + values.slice(i, i + 20).join(", "));
  byteSource += `def ${name} : List UInt8 :=\n  [\n${lines.join(",\n")}\n  ]\n\n`;
}
byteSource += `def artifactData : Array UInt8 :=\n  ⟨${chunks.join(" ++ ")}⟩\n\ndef artifactBytes : ByteArray :=\n  ⟨artifactData⟩\n\ntheorem artifactBytes_data : artifactBytes.data = artifactData := rfl\n\ntheorem artifactBytes_size : artifactBytes.size = ${size} := by rfl\n\nend ${ns}\n`;
outputs.set(root + "ArtifactBytes.lean", byteSource);
const editable = new Set(["ArtifactBytes", "ArtifactDecoded", "ArtifactRawCache", "ArtifactValidation", "ArtifactTranslation"].map(x => root + x + ".lean"));
for (const file of outputs.keys()) if (fs.existsSync(file) && !editable.has(file)) throw Error(`pre-existing output: ${file}`);
for (const [file, content] of outputs) fs.writeFileSync(file, content, { flag: editable.has(file) ? "w" : "wx" });
fs.writeFileSync("tmp/euler-certificate-decoder-targets-20260916.json", JSON.stringify(targets, null, 2) + "\n", { flag: "wx" });
console.log(JSON.stringify({ files: outputs.size, functions: codes.size, certificates, targets: targets.length }));
