import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {Host,cell} from '../../tools/smalltalk-host.mjs';
const [path='build/smalltalk/smalltalk.wasm',nativePath='build/smalltalk/native.json']=process.argv.slice(2);
const bytes=readFileSync(path),module=new WebAssembly.Module(bytes);
assert.deepEqual(WebAssembly.Module.imports(module),[]);
const x=new WebAssembly.Instance(module).exports,h=new Host(x);
const cases=JSON.parse(readFileSync('build/smalltalk/corpus.json'));
const native=new Map(JSON.parse(readFileSync(nativePath)).map(r=>[`${r.name}:${r.stress}`,r.state]));
let checks=0;
for(const test of cases) for(const stress of [0,1]) {
  const code=h.array(test.code); let state=x.init(BigInt(test.capacity),BigInt(stress));
  const pointer=state;
  state=x.boot(code,state); state=x.run(code,state,BigInt(test.fuel));
  let words=h.words(state);
  assert.equal(words[15],BigInt(test.error),`${test.name}: error`);
  if(!test.error) {
    assert.equal(words[0],3n,`${test.name}: did not finish`);
    assert.equal(cell(words,words[7])[0],BigInt(test.kind));
    assert.equal(x.resultWord(state),BigInt(test.expected));
  }
  state=x.collect(state); words=h.words(state);
  assert.equal(state,pointer,`${test.name}: arena moved`);
  assert.deepEqual(words.map(String),native.get(`${test.name}:${stress}`),`${test.name}: native/WASM heap differs`);
  if(test.error || words[0]===3n) {
    state=x.step(code,state); assert.deepEqual(h.words(state),words,'finished/error state changed');
  }
  h.release(state); h.release(code); assert.equal(h.outstanding(),0n,'leaked host arrays'); checks++;
}
// Independent reachability oracle for mixed object graphs, including dead cycles.
let random=123456789;
const rand=()=>{random=(Math.imul(random,1664525)+1013904223)>>>0;return random;};
for(let trial=0;trial<25;trial++) {
  let state=x.init(48n,0n); const nodes=[];
  for(let i=0;i<30;i++) {state=x.allocate(state,1n,BigInt(i),0n,0n,0n,0n,0n); nodes.push(Number(h.words(state)[10]));}
  const edges=new Map(),tags=[1,2,4,5,6,7,8];
  for(const id of nodes) {
    const tag=tags[rand()%tags.length],payload=Array(6).fill(0n),refs=[];
    const indices=tag===4||tag===6?[1]:tag===5?[2,3,4,5]:tag===7?[0,1]:[];
    for(const index of indices) {const child=rand()%5===0?0:nodes[rand()%nodes.length];payload[index]=BigInt(child);if(child)refs.push(child);}
    state=x.write(state,BigInt(24+8*(id-1)),BigInt(tag));
    for(let j=0;j<6;j++) state=x.write(state,BigInt(26+8*(id-1)+j),payload[j]);
    edges.set(id,refs);
  }
  const root=nodes[rand()%nodes.length];state=x.write(state,16n,BigInt(root));
  const reachable=new Set([1,2,3]),todo=[root];
  while(todo.length) {const id=todo.pop();if(reachable.has(id))continue;reachable.add(id);todo.push(...edges.get(id));}
  const before=h.words(state);state=x.collect(state);const after=h.words(state);
  assert.equal(after[15],0n);
  for(const id of nodes) {
    const a=cell(after,id),b=cell(before,id);
    if(reachable.has(id)) {assert.equal(a[0],b[0]);assert.deepEqual(a.slice(2),b.slice(2));}
    else assert.equal(a[0],0n);
  }
  assert.equal(after[9],48n-BigInt(reachable.size));
  const allocated=x.allocCount.value,buffer=x.memory.buffer;state=x.collect(state);
  assert.equal(x.allocCount.value,allocated,'collector allocated'); assert.equal(x.memory.buffer,buffer,'collector grew memory');
  h.release(state);assert.equal(h.outstanding(),0n);checks++;
}
console.log(`WASM: ${checks} checks; ${cases.length*2} exact native comparisons; ${bytes.length} bytes`);
