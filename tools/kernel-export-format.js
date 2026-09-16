"use strict";

// Narrow syntax adapter. No inference, reduction, equality, or verdicts here.
const leanHash = "6a10ac8c22beadecabdbb0919c2b50214762f91d";
const maxWord = (1n << 64n) - 1n;
function fields(value, keys, label) {
  if (!value || typeof value !== "object" || Array.isArray(value) ||
      Object.keys(value).sort().join(",") !== [...keys].sort().join(",")) {
    throw new Error(`unsupported or malformed ${label} fields`);
  }
}
function nat(n, label) {
  if (!Number.isSafeInteger(n) || n < 0) throw new Error(`invalid ${label}: expected a safe natural-number index`);
  return n;
}
function prior(n, table, label) {
  nat(n,label);
  if (n >= table.length) throw new Error(`missing/forward ${label} reference ${n}`);
  return table[n];
}
function decodeExport(text) {
  const lines = text.split(/\r?\n/).filter(l => l.trim() !== "");
  if (!lines.length) throw new Error("empty export");
  const records = lines.map((l,i) => {
    try { return JSON.parse(l); } catch { throw new Error(`invalid JSON on line ${i+1}`); }
  });
  fields(records[0],["meta"],"header");
  const meta = records[0].meta;
  fields(meta,["exporter","format","lean"],"metadata");
  fields(meta.exporter,["name","version"],"exporter");
  fields(meta.format,["version"],"format");
  fields(meta.lean,["githash","version"],"Lean version");
  if (meta.format.version !== "3.1.0" || meta.exporter.name !== "lean4export" ||
      meta.exporter.version !== "3.1.0" || meta.lean.githash !== leanHash || meta.lean.version !== "4.34.0-rc2") {
    throw new Error("unsupported export/Lean version");
  }
  const names=[""], levels=[0n], exprs=[], graph=[];
  let theorem;
  for (const r of records.slice(1)) {
    if (theorem) throw new Error("the single theorem must be the last record");
    if (Object.hasOwn(r,"in")) {
      if (r.in !== names.length) throw new Error("nonsequential name index");
      const kind=Object.hasOwn(r,"str")?"str":"num";
      fields(r,["in",kind],"name record");
      fields(r[kind],kind === "str"?["pre","str"]:["pre","i"],"name");
      const prefix=prior(r[kind].pre,names,"name");
      let suffix;
      if (kind === "str") {
        if (typeof r.str.str !== "string") throw new Error("invalid name string");
        suffix=r.str.str;
      } else suffix=String(nat(r.num.i,"name numeral"));
      names.push(prefix?`${prefix}.${suffix}`:suffix);
    } else if (Object.hasOwn(r,"il")) {
      fields(r,["il","succ"],"concrete successor level");
      if (r.il !== levels.length) throw new Error("nonsequential level index");
      const level=prior(r.succ,levels,"level")+1n;
      if(level>maxWord)throw new Error("unsupported universe representation overflow");
      levels.push(level);
    } else if (Object.hasOwn(r,"ie")) {
      if(r.ie !== exprs.length)throw new Error("nonsequential expression index");
      const keys=Object.keys(r).filter(k=>k!=="ie");
      if(keys.length!==1)throw new Error("malformed expression record");
      const kind=keys[0], value=r[kind];
      let tag,a,b=0;
      if(kind==="sort"){tag=0;a=prior(value,levels,"level");}
      else if(kind==="bvar"){tag=1;a=nat(value,"bound variable");}
      else if(kind==="app"){
        fields(value,["fn","arg"],"application");
        tag=4;a=prior(value.fn,exprs,"function");b=prior(value.arg,exprs,"argument");
      }
      else if(kind==="lam"||kind==="forallE"){
        fields(value,["binderInfo","body","name","type"],"binder");
        prior(value.name,names,"binder name");
        if(!["default","implicit","strictImplicit","instImplicit"].includes(value.binderInfo))throw new Error("unsupported binder info");
        tag=kind==="lam"?3:2;
        a=prior(value.type,exprs,"domain");b=prior(value.body,exprs,"body");
      } else throw new Error(`unsupported expression ${kind}; no constants or hidden dependencies are admitted`);
      exprs.push(graph.length/3);
      graph.push(String(tag),String(a),String(b));
    } else if (Object.hasOwn(r,"thm")) {
      fields(r,["thm"],"declaration record");
      const t=r.thm;
      fields(t,["all","levelParams","name","type","value"],"theorem");
      if(!Array.isArray(t.levelParams)||t.levelParams.length!==0)throw new Error("unsupported universe parameters");
      if(!Array.isArray(t.all)||t.all.length!==1||t.all[0]!==t.name)throw new Error("unsupported theorem block");
      const name=prior(t.name,names,"theorem name");
      if(!name)throw new Error("anonymous theorem");
      theorem={name,graph,term:prior(t.value,exprs,"theorem value"),claimed:prior(t.type,exprs,"theorem type")};
    } else throw new Error("unsupported record/dependency: only one closed theorem is admitted");
  }
  if(!theorem)throw new Error("missing theorem");
  return theorem;
}
module.exports={decodeExport,leanHash};
