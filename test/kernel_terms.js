// Test syntax builder only: resolves names to de Bruijn indices and serializes.
// It does not infer types, normalize terms, or supply verdicts.
const S = level => ({ tag: 0, level });
const V = name => ({ tag: 1, name });
const P = (name, domain, body) => ({ tag: 2, name, domain, body });
const L = (name, domain, body) => ({ tag: 3, name, domain, body });
const A = (fn, arg) => ({ tag: 4, fn, arg });
const E = (name, domain, value, body) => ({ tag: 5, name, domain, value, body });
const arrow = (domain, body) => P("_", domain, body);
function encode(...terms) {
  const graph = [];
  function go(t, ctx) {
    let a, b = 0;
    if (t.tag === 0) a = t.level;
    else if (t.tag === 1) {
      const i = ctx.lastIndexOf(t.name);
      if (i < 0) throw new Error(`unbound fixture variable ${t.name}`);
      a = ctx.length - 1 - i;
    } else if (t.tag === 2 || t.tag === 3) {
      a = go(t.domain,ctx); b = go(t.body,[...ctx,t.name]);
    } else if (t.tag === 4) { a = go(t.fn,ctx); b = go(t.arg,ctx); }
    else if (t.tag === 5) { a = go(t.value,ctx); b = go(L(t.name,t.domain,t.body),ctx); }
    else throw new Error(`unsupported fixture tag ${t.tag}`);
    const root = graph.length / 3;
    graph.push(t.tag,a,b);
    return root;
  }
  const roots = terms.map(t => go(t,[]));
  return { graph, roots };
}
module.exports = { S,V,P,L,A,E,arrow,encode };
