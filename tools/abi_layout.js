function pointer(value) {
  return Number(BigInt.asUintN(64, BigInt(value)));
}

class SparseMemory {
  constructor(chunks) {
    this.chunks = chunks.map((chunk) => ({
      start: pointer(chunk.start),
      bytes: chunk.bytes,
    }));
  }

  range(ptr, len) {
    const start = pointer(ptr);
    const length = Number(BigInt.asUintN(64, BigInt(len)));
    const chunk = this.chunks.find((item) => start >= item.start && start + length <= item.start + item.bytes.length);
    if (!chunk) {
      throw new Error(`missing memory range ${start}+${length}`);
    }
    return chunk.bytes.slice(start - chunk.start, start - chunk.start + length);
  }

  u64(ptr) {
    const bytes = this.range(ptr, 8n);
    let value = 0n;
    for (let index = 0; index < 8; index += 1) {
      value |= BigInt(bytes[index]) << BigInt(index * 8);
    }
    return value;
  }
}

function normalizeU64(value) {
  if (typeof value === "bigint") {
    return BigInt.asUintN(64, value);
  }
  if (typeof value === "number") {
    if (!Number.isInteger(value) || value < 0) {
      throw new Error(`invalid UInt64 value: ${value}`);
    }
    return BigInt(value);
  }
  if (typeof value === "string" && /^[0-9]+$/.test(value)) {
    return BigInt.asUintN(64, BigInt(value));
  }
  throw new Error(`invalid UInt64 value: ${JSON.stringify(value)}`);
}

function normalizeByte(value) {
  const byte = Number(normalizeU64(value));
  if (byte < 0 || byte > 255) {
    throw new Error(`invalid byte value: ${value}`);
  }
  return byte;
}

function scalarLayout(name) {
  return {
    name,
    publicSlots: 1,
    elementSlots: 1,
    normalize: normalizeU64,
    writePublicPlan(_plan, value) {
      return [{ kind: "u64", value: normalizeU64(value) }];
    },
    writeElementPlan(_plan, value) {
      return [{ kind: "u64", value: normalizeU64(value) }];
    },
    readPublicPlan() {},
    readElementPlan() {},
    readPublicSlots(_memory, slots) {
      return BigInt.asUintN(64, slots[0]);
    },
    readElementSlots(_memory, slots) {
      return BigInt.asUintN(64, slots[0]);
    },
  };
}

function makeByteArrayLayout() {
  return {
    name: "ByteArray",
    publicSlots: 2,
    elementSlots: 3,
    normalize(value) {
      if (!Array.isArray(value)) {
        throw new Error(`ByteArray value must be an array: ${JSON.stringify(value)}`);
      }
      return value.map(normalizeByte);
    },
    writePublicPlan(plan, value) {
      const bytes = this.normalize(value);
      const id = plan.bytes(bytes);
      return [{ kind: "ptr", id }, { kind: "u64", value: BigInt(bytes.length) }];
    },
    writeElementPlan(plan, value) {
      const bytes = this.normalize(value);
      const id = plan.bytes(bytes);
      return [
        { kind: "u64", value: 0n },
        { kind: "ptr", id },
        { kind: "u64", value: BigInt(bytes.length) },
      ];
    },
    readPublicPlan(plan, slots) {
      plan.readMemory(slots[0], slots[1]);
    },
    readElementPlan(plan, slots) {
      plan.readMemory(slots[1], slots[2]);
    },
    readPublicSlots(memory, slots) {
      return readBytes(memory, slots[0], slots[1]);
    },
    readElementSlots(memory, slots) {
      return readBytes(memory, slots[1], slots[2]);
    },
  };
}

function arrayLayout(itemLayout) {
  return {
    name: `Array ${itemLayout.name}`,
    publicSlots: 1,
    elementSlots: 2,
    normalize(value) {
      if (!Array.isArray(value)) {
        throw new Error(`Array value must be an array: ${JSON.stringify(value)}`);
      }
      return value.map((item) => itemLayout.normalize(item));
    },
    writePublicPlan(plan, value) {
      return [{ kind: "ptr", id: writeArrayRootPlan(plan, itemLayout, this.normalize(value)) }];
    },
    writeElementPlan(plan, value) {
      return [
        { kind: "u64", value: 0n },
        { kind: "ptr", id: writeArrayRootPlan(plan, itemLayout, this.normalize(value)) },
      ];
    },
    readPublicPlan(plan, slots, value) {
      readArrayRootPlan(plan, itemLayout, slots[0], this.normalize(value));
    },
    readElementPlan(plan, slots, value) {
      readArrayRootPlan(plan, itemLayout, slots[1], this.normalize(value));
    },
    readPublicSlots(memory, slots) {
      return readArrayRoot(memory, itemLayout, slots[0]);
    },
    readElementSlots(memory, slots) {
      return readArrayRoot(memory, itemLayout, slots[1]);
    },
  };
}

function structLayout(fields) {
  const publicSlots = fields.reduce((total, field) => total + field[1].publicSlots, 0);
  const elementSlots = fields.reduce((total, field) => total + field[1].elementSlots, 0);
  return {
    name: "structure",
    publicSlots,
    elementSlots,
    normalize(value) {
      if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`structure value must be an object: ${JSON.stringify(value)}`);
      }
      const normalized = {};
      for (const [name, layout] of fields) {
        normalized[name] = layout.normalize(value[name]);
      }
      return normalized;
    },
    writePublicPlan(plan, value) {
      const normalized = this.normalize(value);
      return fields.flatMap((field) => field[1].writePublicPlan(plan, normalized[field[0]]));
    },
    writeElementPlan(plan, value) {
      const normalized = this.normalize(value);
      return fields.flatMap((field) => field[1].writeElementPlan(plan, normalized[field[0]]));
    },
    readPublicPlan(plan, slots, value) {
      readStructPlan(plan, fields, slots, this.normalize(value), "publicSlots", "readPublicPlan");
    },
    readElementPlan(plan, slots, value) {
      readStructPlan(plan, fields, slots, this.normalize(value), "elementSlots", "readElementPlan");
    },
    readPublicSlots(memory, slots) {
      return readStructSlots(memory, fields, slots, "publicSlots", "readPublicSlots");
    },
    readElementSlots(memory, slots) {
      return readStructSlots(memory, fields, slots, "elementSlots", "readElementSlots");
    },
  };
}

function variantLayout(ctors) {
  const publicSlots = 1 + ctors.flat().reduce((total, layout) => total + layout.publicSlots, 0);
  const elementSlots = 1 + ctors.flat().reduce((total, layout) => total + layout.elementSlots, 0);
  return {
    name: "tagged",
    publicSlots,
    elementSlots,
    normalize(value) {
      if (!value || typeof value !== "object" || Array.isArray(value)) {
        throw new Error(`tagged value must be an object: ${JSON.stringify(value)}`);
      }
      const tag = Number(normalizeU64(value.tag));
      if (tag < 0 || tag >= ctors.length) {
        throw new Error(`variant tag ${tag} is outside constructor range`);
      }
      const fields = value.fields || [];
      if (fields.length !== ctors[tag].length) {
        throw new Error(`variant tag ${tag} expected ${ctors[tag].length} fields`);
      }
      return {
        tag,
        fields: fields.map((field, index) => ctors[tag][index].normalize(field)),
      };
    },
    writePublicPlan(plan, value) {
      return writeVariantPlan(plan, ctors, this.normalize(value), "publicSlots", "writePublicPlan");
    },
    writeElementPlan(plan, value) {
      return writeVariantPlan(plan, ctors, this.normalize(value), "elementSlots", "writeElementPlan");
    },
    readPublicPlan(plan, slots, value) {
      readVariantPlan(plan, ctors, slots, this.normalize(value), "publicSlots", "readPublicPlan");
    },
    readElementPlan(plan, slots, value) {
      readVariantPlan(plan, ctors, slots, this.normalize(value), "elementSlots", "readElementPlan");
    },
    readPublicSlots(memory, slots) {
      return readVariantSlots(memory, ctors, slots, "publicSlots", "readPublicSlots");
    },
    readElementSlots(memory, slots) {
      return readVariantSlots(memory, ctors, slots, "elementSlots", "readElementSlots");
    },
  };
}

function defaultPlanSlots(count) {
  return Array.from({ length: count }, () => ({ kind: "u64", value: 0n }));
}

function writeVariantPlan(plan, ctors, value, widthKey, writeKey) {
  const slots = [{ kind: "u64", value: BigInt(value.tag) }];
  for (let ctorIndex = 0; ctorIndex < ctors.length; ctorIndex += 1) {
    const fields = ctors[ctorIndex];
    if (ctorIndex === value.tag) {
      fields.forEach((layout, fieldIndex) => {
        slots.push(...layout[writeKey](plan, value.fields[fieldIndex]));
      });
    } else {
      fields.forEach((layout) => {
        slots.push(...defaultPlanSlots(layout[widthKey]));
      });
    }
  }
  return slots;
}

function readStructPlan(plan, fields, slots, value, widthKey, readKey) {
  let offset = 0;
  for (const [name, layout] of fields) {
    const width = layout[widthKey];
    layout[readKey](plan, slots.slice(offset, offset + width), value[name]);
    offset += width;
  }
}

function readVariantPlan(plan, ctors, slots, value, widthKey, readKey) {
  let offset = 1;
  for (let ctorIndex = 0; ctorIndex < ctors.length; ctorIndex += 1) {
    const fields = ctors[ctorIndex];
    for (let fieldIndex = 0; fieldIndex < fields.length; fieldIndex += 1) {
      const layout = fields[fieldIndex];
      const width = layout[widthKey];
      if (ctorIndex === value.tag) {
        layout[readKey](plan, slots.slice(offset, offset + width), value.fields[fieldIndex]);
      }
      offset += width;
    }
  }
}

function readStructSlots(memory, fields, slots, widthKey, readKey) {
  const value = {};
  let offset = 0;
  for (const [name, layout] of fields) {
    const width = layout[widthKey];
    value[name] = layout[readKey](memory, slots.slice(offset, offset + width));
    offset += width;
  }
  return value;
}

function readVariantSlots(memory, ctors, slots, widthKey, readKey) {
  const tag = Number(BigInt.asUintN(64, slots[0]));
  const fields = [];
  let offset = 1;
  for (let ctorIndex = 0; ctorIndex < ctors.length; ctorIndex += 1) {
    for (const layout of ctors[ctorIndex]) {
      const width = layout[widthKey];
      if (ctorIndex === tag) {
        fields.push(layout[readKey](memory, slots.slice(offset, offset + width)));
      }
      offset += width;
    }
  }
  return { tag, fields };
}

class HostPlan {
  constructor() {
    this.commands = [];
    this.nextId = 1;
  }

  alloc(size) {
    const id = this.nextId;
    this.nextId += 1;
    this.commands.push(`alloc ${id} ${size}`);
    return id;
  }

  bytes(values) {
    const id = this.nextId;
    this.nextId += 1;
    const hex = values.map((byte) => byte.toString(16).padStart(2, "0")).join("");
    this.commands.push(`bytes ${id} ${hex}`);
    return id;
  }

  writeSlot(blockId, offset, slot) {
    if (slot.kind === "ptr") {
      this.commands.push(`write-ptr ${blockId} ${offset} ${slot.id}`);
      return;
    }
    this.commands.push(`write-u64 ${blockId} ${offset} ${BigInt(slot.value).toString()}`);
  }

  argSlot(slot) {
    if (slot.kind === "ptr") {
      this.commands.push(`arg-ptr ${slot.id}`);
      return;
    }
    this.commands.push(`arg-u64 ${BigInt(slot.value).toString()}`);
  }
}

class ReadPlan {
  constructor() {
    this.commands = [];
    this.nextId = 1;
  }

  result(index) {
    return `result:${index}`;
  }

  readU64(ptrExpr, offset) {
    const id = this.nextId;
    this.nextId += 1;
    this.commands.push(`read-u64 ${id} ${ptrExpr} ${offset}`);
    return `u64:${id}`;
  }

  readMemory(ptrExpr, lenExpr) {
    this.commands.push(`read-memory ${ptrExpr} ${lenExpr}`);
  }
}

function writeArrayRootPlan(plan, itemLayout, values) {
  const width = itemLayout.elementSlots;
  const root = plan.alloc(8 + values.length * width * 8);
  plan.writeSlot(root, 0, { kind: "u64", value: BigInt(values.length) });
  values.forEach((value, index) => {
    const slots = itemLayout.writeElementPlan(plan, value);
    if (slots.length !== width) {
      throw new Error(`${itemLayout.name}: wrote ${slots.length} slots, expected ${width}`);
    }
    const base = 8 + index * width * 8;
    slots.forEach((slot, slotIndex) => {
      plan.writeSlot(root, base + slotIndex * 8, slot);
    });
  });
  return root;
}

function readArrayRootPlan(plan, itemLayout, ptrExpr, values) {
  const width = itemLayout.elementSlots;
  plan.readMemory(ptrExpr, 8 + values.length * width * 8);
  values.forEach((value, index) => {
    const slots = [];
    const base = 8 + index * width * 8;
    for (let slot = 0; slot < width; slot += 1) {
      slots.push(plan.readU64(ptrExpr, base + slot * 8));
    }
    itemLayout.readElementPlan(plan, slots, value);
  });
}

function readArrayRoot(memory, itemLayout, ptr) {
  const length = Number(memory.u64(ptr));
  const values = [];
  for (let index = 0; index < length; index += 1) {
    const slots = [];
    for (let slot = 0; slot < itemLayout.elementSlots; slot += 1) {
      slots.push(memory.u64(ptr + BigInt(8 * (1 + index * itemLayout.elementSlots + slot))));
    }
    values.push(itemLayout.readElementSlots(memory, slots));
  }
  return values;
}

function readBytes(memory, ptr, len) {
  const length = Number(BigInt.asUintN(64, BigInt(len)));
  return Array.from(memory.range(ptr, length));
}

function materializeArgPlan(plan, arg) {
  if (typeof arg === "bigint" || typeof arg === "number" || typeof arg === "string") {
    plan.argSlot({ kind: "u64", value: normalizeU64(arg) });
    return;
  }
  if (arg && arg.layout) {
    for (const slot of arg.layout.writePublicPlan(plan, arg.value)) {
      plan.argSlot(slot);
    }
    return;
  }
  throw new Error(`unknown ABI argument shape: ${JSON.stringify(arg)}`);
}

function resultReadCommands(layout, value, resultIndex = 0) {
  const plan = new ReadPlan();
  const normalized = layout.normalize(value);
  const slots = Array.from({ length: layout.publicSlots }, (_item, index) => plan.result(resultIndex + index));
  layout.readPublicPlan(plan, slots, normalized);
  return plan.commands;
}

function decodePublicValue(layout, chunks, slots, resultIndex = 0) {
  const memory = new SparseMemory(chunks);
  const publicSlots = slots
    .slice(resultIndex, resultIndex + layout.publicSlots)
    .map((slot) => BigInt.asUintN(64, slot));
  return layout.readPublicSlots(memory, publicSlots);
}

function formatAbiValue(value) {
  return JSON.stringify(value, (_key, item) => (typeof item === "bigint" ? item.toString() : item));
}

function assertAbiEqual(testName, path, actual, expected) {
  if (typeof expected === "bigint" || typeof actual === "bigint") {
    if (BigInt(actual) !== BigInt(expected)) {
      throw new Error(`${testName}: expected ${path} ${formatAbiValue(expected)}, got ${formatAbiValue(actual)}`);
    }
    return;
  }
  if (Array.isArray(expected)) {
    if (!Array.isArray(actual) || actual.length !== expected.length) {
      throw new Error(`${testName}: expected ${path} ${formatAbiValue(expected)}, got ${formatAbiValue(actual)}`);
    }
    expected.forEach((item, index) => assertAbiEqual(testName, `${path}[${index}]`, actual[index], item));
    return;
  }
  if (expected && typeof expected === "object") {
    if (!actual || typeof actual !== "object") {
      throw new Error(`${testName}: expected ${path} ${formatAbiValue(expected)}, got ${formatAbiValue(actual)}`);
    }
    for (const key of Object.keys(expected)) {
      assertAbiEqual(testName, `${path}.${key}`, actual[key], expected[key]);
    }
    return;
  }
  if (actual !== expected) {
    throw new Error(`${testName}: expected ${path} ${formatAbiValue(expected)}, got ${formatAbiValue(actual)}`);
  }
}

function memoryReadCommands(testCase) {
  const plan = new ReadPlan();
  for (const memoryArray of testCase.memoryArrays || []) {
    const ptr = plan.result(memoryArray.resultIndex);
    plan.readMemory(ptr, 8 + memoryArray.values.length * 8);
  }
  for (const memoryBytes of testCase.memoryBytes || []) {
    plan.readMemory(plan.result(memoryBytes.resultIndex), plan.result(memoryBytes.lengthIndex));
  }
  for (const memoryValue of testCase.memoryValues || []) {
    const slots = Array.from({ length: memoryValue.layout.publicSlots }, (_item, index) =>
      plan.result(memoryValue.resultIndex + index),
    );
    memoryValue.layout.readPublicPlan(plan, slots, memoryValue.value);
  }
  return plan.commands;
}

function checkMemoryExpectations(testCase, memory, actualSlots) {
  for (const memoryArray of testCase.memoryArrays || []) {
    const ptr = actualSlots[memoryArray.resultIndex];
    const len = memory.u64(ptr);
    const expectedLength = memoryArray.length ?? memoryArray.values.length;
    if (len !== BigInt(expectedLength)) {
      throw new Error(`${testCase.name}: expected array length ${expectedLength}, got ${len}`);
    }
    for (let index = 0; index < memoryArray.values.length; index += 1) {
      const cell = memory.u64(ptr + BigInt(8 * (index + 1)));
      if (cell !== memoryArray.values[index]) {
        throw new Error(`${testCase.name}: expected array[${index}] ${memoryArray.values[index]}, got ${cell}`);
      }
    }
  }
  for (const memoryBytes of testCase.memoryBytes || []) {
    const ptr = actualSlots[memoryBytes.resultIndex];
    const len = actualSlots[memoryBytes.lengthIndex];
    const expectedLength = BigInt(memoryBytes.values.length);
    if (len !== expectedLength) {
      throw new Error(`${testCase.name}: expected byte length ${expectedLength}, got ${len}`);
    }
    const bytes = memory.range(ptr, len);
    for (let index = 0; index < memoryBytes.values.length; index += 1) {
      if (bytes[index] !== memoryBytes.values[index]) {
        throw new Error(`${testCase.name}: expected byte[${index}] ${memoryBytes.values[index]}, got ${bytes[index]}`);
      }
    }
  }
  for (const memoryValue of testCase.memoryValues || []) {
    const slots = actualSlots.slice(
      memoryValue.resultIndex,
      memoryValue.resultIndex + memoryValue.layout.publicSlots,
    );
    const actual = memoryValue.layout.readPublicSlots(memory, slots);
    assertAbiEqual(testCase.name, `result[${memoryValue.resultIndex}]`, actual, memoryValue.value);
  }
}

function layoutFromDescriptor(desc) {
  if (desc === "u64" || desc === "UInt64" || desc === "Nat" || desc === "Bool" ||
      desc === "UInt8" || desc === "UInt32") {
    return scalarLayout(desc);
  }
  if (desc === "bytes" || desc === "ByteArray") {
    return byteArrayLayout;
  }
  if (desc && typeof desc === "object" && !Array.isArray(desc)) {
    if (desc.array) {
      return arrayLayout(layoutFromDescriptor(desc.array));
    }
    if (desc.struct) {
      return structLayout(desc.struct.map((field) => [field[0], layoutFromDescriptor(field[1])]));
    }
    if (desc.tagged) {
      return variantLayout(desc.tagged.map((ctor) => ctor.map(layoutFromDescriptor)));
    }
  }
  throw new Error(`unsupported ABI layout descriptor: ${JSON.stringify(desc)}`);
}

const byteArrayLayout = makeByteArrayLayout();

module.exports = {
  HostPlan,
  ReadPlan,
  SparseMemory,
  arrayLayout,
  assertAbiEqual,
  byteArrayLayout,
  checkMemoryExpectations,
  decodePublicValue,
  layoutFromDescriptor,
  materializeArgPlan,
  memoryReadCommands,
  resultReadCommands,
  scalarLayout,
  structLayout,
  variantLayout,
};
