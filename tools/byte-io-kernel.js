"use strict";
const { decoderCertificates } = require("./artifact-kernel");

// Untrusted proof generation. Every emitted cursor, cache item, and section
// equality is checked by Lean; this scanner is outside the trusted decoder.
function sectionMetadata(bytes) {
  let pos = 8;
  function u32() {
    let value = 0, shift = 0;
    for (let i = 0; i < 5; i++) {
      if (pos >= bytes.length) throw Error("truncated section size");
      const byte = bytes[pos++];
      value += (byte & 127) * 2 ** shift;
      if (!(byte & 128)) return value;
      shift += 7;
    }
    throw Error("overlong section size");
  }
  const result = [];
  while (pos < bytes.length) {
    const id = bytes[pos++], start = pos, size = u32(), payload = pos, end = pos + size;
    if (end > bytes.length) throw Error("section exceeds input");
    const count = u32(), items = pos, entries = [];
    if (id === 10) {
      for (let index = 0; index < count; index++) {
        const start = pos, size = u32();
        pos += size;
        entries.push({ index, start, end: pos });
      }
      if (pos !== end) throw Error("code section size mismatch");
    }
    if (id === 2) {
      for (let index = 0; index < count; index++) {
        const start = pos;
        const moduleSize = u32(); pos += moduleSize;
        const fieldSize = u32(); pos += fieldSize;
        if (bytes[pos++] !== 0) throw Error("unsupported import kind");
        u32();
        if (pos > end) throw Error("import exceeds section");
        entries.push({ index, start, end: pos });
      }
      if (pos !== end) throw Error("import section size mismatch");
    }
    result.push({ id, start, payload, items, end, count, entries });
    pos = end;
  }
  if (result.map(x => x.id).join(",") !== "1,2,3,5,6,7,10") throw Error("unexpected byte-I/O section profile");
  return result;
}

function certificates(bytes, nestedText) {
  const sections = sectionMetadata(bytes), code = sections.at(-1), outputs = new Map();
  const rows = [`section,10,${code.start},${code.payload},${code.items},${code.count},${code.end}`,
    ...code.entries.map(e => `item,10,${e.index},${e.start},${e.end}`)];
  for (const [name, source] of decoderCertificates("ByteIO", bytes.length, nestedText, rows.join("\n"))) {
    if (!/^ArtifactCode\d+$/.test(name) && name !== "ArtifactSection10") continue;
    outputs.set(name, source
      .replaceAll("artifactBytes_data", "ByteLookup.bytes_data")
      .replaceAll("artifactBytes_size", "ByteLookup.bytes_size")
      .replaceAll("artifactData", "ByteLookup.data")
      .replaceAll("artifactBytes", "bytes")
      .replaceAll("Cache.raw", "raw.core"));
  }
  const fields = new Map([
    [1, ["types", "funcType", "raw.core.types"]],
    [2, ["imports", "Binary.importEntry", "raw.imports"]],
    [3, ["functions", "Leb.u32", "raw.core.functionTypeIndices"]],
    [5, ["memories", "memoryType", "raw.core.memories"]],
    [6, ["globals", "global", "raw.core.globals"]],
    [7, ["exports", "exportEntry", "raw.core.exports"]],
  ]);
  let header = `import Project.ByteIO.ArtifactCache
import Project.ByteIO.ArtifactByteLookup
import Project.ByteIO.BinaryParts

namespace Project.ByteIO.Artifact
open Wasm.Binary
attribute [local cbv_opaque] bytes
set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

`;
  for (const sec of sections.slice(0, -1)) {
    const [name, parser, field] = fields.get(sec.id);
    if (sec.id === 2) {
      const cursor = (pos, limit = bytes.length) => `{ bytes, pos := ${pos}, limit := ${limit} }`;
      for (const e of sec.entries) header += `theorem import${e.index}_parsed :
    Binary.importEntry ${cursor(e.start, sec.end)} =
      .ok (raw.imports[${e.index}]!, ${cursor(e.end, sec.end)}) := by cbv

`;
      header += `theorem imports_tail${sec.count} :
    Internal.vectorLoop Binary.importEntry 0 ${cursor(sec.end, sec.end)} =
      .ok (raw.imports.drop ${sec.count}, ${cursor(sec.end, sec.end)}) := rfl

`;
      for (let i = sec.count - 1; i >= 0; i--) header += `theorem imports_tail${i} :
    Internal.vectorLoop Binary.importEntry ${sec.count - i} ${cursor(sec.entries[i].start, sec.end)} =
      .ok (raw.imports.drop ${i}, ${cursor(sec.end, sec.end)}) :=
  vectorLoop_eq_cons import${i}_parsed imports_tail${i + 1}

`;
      header += `theorem imports_vector :
    vector Binary.importEntry ${cursor(sec.payload, sec.end)} =
      .ok (raw.imports, ${cursor(sec.end, sec.end)}) := by
  refine vector_eq_of_parts (length := ${sec.count}) (itemsStart := ${cursor(sec.items, sec.end)}) ?_ ?_ imports_tail0
  · cbv
  · decide

theorem imports_sized :
    sized (vector Binary.importEntry) ${cursor(sec.start)} =
      .ok (raw.imports, ${cursor(sec.end)}) := by
  refine sized_eq_of_parts (size := ${sec.end - sec.payload})
    (payload := ${cursor(sec.payload)}) (finish := ${cursor(sec.end, sec.end)}) ?_ ?_ ?_ imports_vector ?_
  · cbv
  · decide
  · cbv
  · rfl

theorem imports_parsed :
    Binary.parseSection 2 Binary.importEntry ${cursor(sec.start - 1)} =
      .ok (raw.imports, ${cursor(sec.end)}) := by
  refine Binary.parseSection_eq_of_parts (payload := ${cursor(sec.start)}) ?_ imports_sized
  cbv

#print axioms imports_parsed

`;
      continue;
    }
    header += `theorem ${name}_parsed :
    Binary.parseSection ${sec.id} ${parser} { bytes, pos := ${sec.start - 1}, limit := ${bytes.length} } =
      .ok (${field}, { bytes, pos := ${sec.end}, limit := ${bytes.length} }) := by cbv

#print axioms ${name}_parsed

`;
  }
  outputs.set("ArtifactSections", header + "end Project.ByteIO.Artifact\n");
  outputs.set("ArtifactDecode", `import Project.ByteIO.ArtifactSections
import Project.ByteIO.ArtifactSection10
import Project.ByteIO.BinaryParts

namespace Project.ByteIO.Artifact
open Wasm.Binary

attribute [local cbv_opaque] bytes
set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem codes_parsed :
    Binary.parseSection 10 code { bytes, pos := ${code.start - 1}, limit := ${bytes.length} } =
      .ok (raw.core.codes, { bytes, pos := ${bytes.length}, limit := ${bytes.length} }) := by
  refine Binary.parseSection_eq_of_parts
    (payload := { bytes, pos := ${code.start}, limit := ${bytes.length} }) ?_ codes_section_decoded
  cbv

attribute [local cbv_eval] types_parsed imports_parsed functions_parsed
  memories_parsed globals_parsed exports_parsed codes_parsed
attribute [local cbv_opaque] Binary.parseSection

theorem decoded : Binary.decode bytes = .ok raw := by cbv

theorem encoded : Binary.Grammar.ModuleBytes bytes.data.toList raw :=
  Binary.decode_sound decoded

#print axioms decoded
#print axioms encoded

end Project.ByteIO.Artifact
`);
  return outputs;
}
module.exports = { sectionMetadata, certificates };
