"use strict";

function decoderCertificates(leanModule, size, nestedText, sectionsText) {
  const namespace = `Project.${leanModule}.Artifact`;
  const prefix = `Project.${leanModule}`;
  const outputs = new Map();
  const sequences = new Map(), codes = new Map(), sections = new Map();
  for (const row of nestedText.trim().split("\n").map(line => line.split(","))) {
    if (row[0] === "seq") {
      const [, path, start, fuel, allowElse, finish, ending, limit] = row;
      sequences.set(path, { path, start: +start, fuel: +fuel, allowElse,
        finish: +finish, ending, limit: +limit, offsets: [] });
    } else if (row[0] === "at") {
      sequences.get(row[1]).offsets.push({ index: +row[2], fuel: +row[3], pos: +row[4] });
    } else if (row[1] === "code") {
      codes.set(+row[0], { start: +row[2], stop: +row[3], body: +row[4], payload: +row[5] });
    }
  }
  for (const row of sectionsText.trim().split("\n").map(line => line.split(","))) {
    if (row[0] === "section") {
      const [, id, start, payload, items, count, end] = row.map((value, i) => i ? +value : value);
      sections.set(id, { start, payload, items, count, end, entries: [] });
    } else if (row[0] === "item") {
      sections.get(+row[1]).entries.push({ index: +row[2], start: +row[3], end: +row[4] });
    } else throw Error(`unexpected section metadata: ${row.join(",")}`);
  }
  if (codes.size === 0 || sections.get(10)?.end !== size) throw Error("incomplete code metadata");
  const cursor = (pos, limit = size) => `{ bytes := artifactBytes, pos := ${pos}, limit := ${limit} }`;
  const header = (imports = []) => `import ${prefix}.ArtifactByteLookup
import ${prefix}.ArtifactCache
import Project.Artifact.Binary.CodeParts
${imports.map(name => `import ${name}`).join("\n")}

namespace ${namespace}
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

`;
  const save = (name, source) => outputs.set(name, source + `\nend ${namespace}\n`);
  const seqName = (path, offset) => `sequence_${path.replaceAll(".", "_")}_tail${offset}`;
  function body(path) {
    const parts = path.split(".");
    let result = `(Cache.raw.codes[${parts[0]}]!).body`;
    for (let i = 1; i < parts.length; i += 2) {
      result = `((${result})[${parts[i]}]!).childBody ${parts[i + 1] === "e"}`;
    }
    return result;
  }
  const groups = [];
  for (let index = 0; index < codes.size; index++) {
    const code = codes.get(index);
    if (!code) throw Error(`missing function ${index}`);
    const name = `ArtifactCode${index}`;
    groups.push(`${prefix}.${name}`);
    let source = header();
    const selected = [...sequences.values()].filter(sequence =>
      sequence.path.split(".")[0] === String(index) &&
      (sequence.path === String(index) || sequence.finish - sequence.start >= 128));
    selected.sort((a, b) => b.path.split(".").length - a.path.split(".").length);
    for (const sequence of selected) {
      let end = sequence.finish;
      for (const offset of [...sequence.offsets].reverse()) {
        if (end - offset.pos < 128 && offset.index !== 0) continue;
        source += `@[cbv_eval] theorem ${seqName(sequence.path, offset.index)} :
    instructionSequenceAt ${offset.fuel} ${sequence.allowElse} ${cursor(offset.pos, sequence.limit)} =
      .ok (((${body(sequence.path)}).drop ${offset.index}, .${sequence.ending}), ${cursor(sequence.finish, sequence.limit)}) := by
  cbv

`;
        end = offset.pos;
      }
    }
    source += `theorem code${index}_decoded :
    code ${cursor(code.start)} = .ok (Cache.raw.codes[${index}]!, ${cursor(code.stop)}) := by
  refine code_eq_of_parts (size := ${code.stop - code.payload})
    (payload := ${cursor(code.payload)})
    (bodyStart := ${cursor(code.body, code.stop)})
    (bodyFinish := ${cursor(code.stop, code.stop)})
    ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact ${seqName(String(index), 0)}
  · rfl

#print axioms code${index}_decoded
`;
    save(name, source);
  }
  const kinds = new Map([
    [1, ["type", "types", "funcType"]], [3, ["function", "functionTypeIndices", "Leb.u32"]],
    [5, ["memory", "memories", "memoryType"]], [6, ["global", "globals", "global"]],
    [7, ["export", "exports", "exportEntry"]], [10, ["code", "codes", "code"]],
  ]);
  const sectionImports = [];
  for (const [id, section] of sections) {
    const kind = kinds.get(id);
    if (!kind || section.entries.length !== section.count) throw Error(`invalid section metadata: ${id}`);
    const [tag, field, parser] = kind;
    const name = `ArtifactSection${id}`;
    sectionImports.push(`${prefix}.${name}`);
    let source = header(id === 10 ? groups : []);
    if (id !== 10) for (const entry of section.entries) source += `theorem ${tag}${entry.index}_decoded :
    ${parser} ${cursor(entry.start, section.end)} =
      .ok (Cache.raw.${field}[${entry.index}]!, ${cursor(entry.end, section.end)}) := by cbv

`;
    source += `theorem ${field}_tail${section.count} :
    Internal.vectorLoop ${parser} 0 ${cursor(section.end, section.end)} =
      .ok (Cache.raw.${field}.drop ${section.count}, ${cursor(section.end, section.end)}) := by rfl

`;
    for (let i = section.count - 1; i >= 0; i--) source += `theorem ${field}_tail${i} :
    Internal.vectorLoop ${parser} ${section.count - i} ${cursor(section.entries[i].start, section.end)} =
      .ok (Cache.raw.${field}.drop ${i}, ${cursor(section.end, section.end)}) := by
  exact vectorLoop_eq_cons ${tag}${i}_decoded ${field}_tail${i + 1}

`;
    source += `theorem ${field}_vector_decoded :
    vector ${parser} ${cursor(section.payload, section.end)} =
      .ok (Cache.raw.${field}, ${cursor(section.end, section.end)}) := by
  refine vector_eq_of_parts (length := ${section.count})
    (itemsStart := ${cursor(section.items, section.end)}) ?_ ?_ ?_
  · cbv
  · decide
  · exact ${field}_tail0

theorem ${field}_section_decoded :
    sized (vector ${parser}) ${cursor(section.start)} = .ok (Cache.raw.${field}, ${cursor(section.end)}) := by
  refine sized_eq_of_parts (size := ${section.end - section.payload})
    (payload := ${cursor(section.payload)}) (finish := ${cursor(section.end, section.end)})
    ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · exact ${field}_vector_decoded
  · rfl

#print axioms ${field}_section_decoded
`;
    save(name, source);
  }
  let source = header([...sectionImports, "Project.Artifact.Binary.SectionParts"]);
  const ordered = [...sections];
  source += "def state0 : RawModule := default\n\n";
  for (let i = 0; i < ordered.length; i++) {
    const [id] = ordered[i], [, field] = kinds.get(id);
    const tags = ordered.slice(0, i + 1).map(([key]) => `.${kinds.get(key)[0]}`).join(", ");
    source += `def state${i + 1} : RawModule :=
  { state${i} with ${field} := Cache.raw.${field}, sections := [${tags}] }\n\n`;
  }
  const rank = id => [...kinds.keys()].indexOf(id) + 1;
  source += `theorem sections_from${ordered.length} :
    sectionLoop ${size - 8 - ordered.length} ${rank(ordered.at(-1)[0])} state${ordered.length} ${cursor(size)} =
      .ok (Cache.raw, ${cursor(size)}) := by rfl\n\n`;
  for (let i = ordered.length - 1; i >= 0; i--) {
    const [id, section] = ordered[i], [tag, field] = kinds.get(id);
    source += `theorem sections_from${i} :
    sectionLoop ${size - 8 - i} ${i === 0 ? 0 : rank(ordered[i - 1][0])} state${i} ${cursor(section.start - 1)} =
      .ok (Cache.raw, ${cursor(size)}) := by
  refine sectionLoop_eq_step (fuel := ${size - 9 - i}) (rawId := ${id}) (id := .${tag}) (rank := ${rank(id)})
    (payload := ${cursor(section.start)}) (next := ${cursor(section.end)})
    (parsed := { state${i} with ${field} := Cache.raw.${field} }) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · cbv
  · rfl
  · decide
  · decide
  · exact parseSection_${tag}_eq ${field}_section_decoded
  · exact sections_from${i + 1}

`;
  }
  source += `theorem decode_eq_cache_parts : decode artifactBytes = .ok Cache.raw := by
  refine decode_eq_of_parts (versionStart := ${cursor(4)})
    (sectionsStart := ${cursor(8)}) (finish := ${cursor(size)}) ?_ ?_ ?_ ?_
  · cbv
  · cbv
  · exact sections_from0
  · rfl

#print axioms decode_eq_cache_parts
`;
  save("ArtifactParsed", source);
  const validationHeader = `import ${prefix}.ArtifactCache
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace ${namespace}
open Wasm.Binary

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

`;
  source = validationHeader;
  source += `theorem validation_export_names : Validator.duplicateName? Cache.raw.exports = none := by cbv\n\n`;
  const exports = sections.get(7)?.count || 0;
  for (let i = 0; i < exports; i++) source += `theorem validation_export${i} :
    Validator.validateExportEntry Cache.raw Cache.raw.exports[${i}]! = .ok () := by
  have hname : Cache.raw.exports[${i}]!.name.text.toByteArray.data.toList =
      Cache.raw.exports[${i}]!.name.bytes := by rfl
  simp only [Validator.validateExportEntry, hname, ite_true]
  cbv

`;
  source += `theorem validation_exports : Validator.validateExports Cache.raw = .ok () := by
  unfold Validator.validateExports
  rw [validation_export_names]
  change Validator.validateExportEntries Cache.raw
    [${Array.from({length: exports}, (_, i) => `Cache.raw.exports[${i}]!`).join(", ")}] = .ok ()
  simp only [Validator.validateExportEntries, Bind.bind, Pure.pure, Except.pure, Except.bind${Array.from({length: exports}, (_, i) => `, validation_export${i}`).join("")}]

#print axioms validation_exports
`;
  save("ArtifactValidationExports", source);
  source = `import ${prefix}.ArtifactValidationExports\n` + validationHeader;
  source += `def resolvedTypes : List FuncType :=
  Cache.raw.functionTypeIndices.map (fun index => Cache.raw.types[index.toNat]!)

theorem validation_sections : Validator.validateSections Cache.raw = .ok () := by cbv
theorem validation_memory : Cache.raw.memories.length = 1 := by rfl
theorem validation_limits : Validator.validateLimits Cache.raw.memories.head!.limits = .ok () := by cbv
theorem validation_globals : Validator.validateGlobals Cache.raw.globals = .ok () := by cbv
theorem validation_types : Validator.resolveFunctionTypes Cache.raw = .ok resolvedTypes := by cbv
`;
  save("ArtifactValidationMetadata", source);
  source = `import ${prefix}.ArtifactValidationMetadata
import ${prefix}.ArtifactDecode
import Project.Artifact.Binary.Evidence
` + validationHeader;
  source += `theorem validation_functions : Validator.validateFunctions Cache.raw resolvedTypes = .ok () := by cbv

def cacheValidationSucceeded : Bool := (validate Cache.raw).toOption.isSome

theorem cache_validation_test : cacheValidationSucceeded = true := by
  have hraw := validateRaw_eq_of_parts validation_sections validation_memory
    validation_limits validation_globals validation_exports validation_types validation_functions
  unfold cacheValidationSucceeded validate
  rw [hraw]
  rfl

theorem cache_validation_exists : ∃ validated, validate Cache.raw = .ok validated :=
  ok_exists_of_toOption_isSome cache_validation_test

#print axioms validation_functions
#print axioms cache_validation_exists
`;
  save("ArtifactValidation", source);
  return outputs;
}

module.exports = { decoderCertificates };
