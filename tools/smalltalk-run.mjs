import {readFileSync} from 'node:fs';
import {compile} from './smalltalk-compile.mjs';
import {Host,cell} from './smalltalk-host.mjs';
const [modulePath,sourcePath,...flags]=process.argv.slice(2);
if(!modulePath||!sourcePath) throw Error('usage: smalltalk-run.mjs MODULE.wasm INPUT.st [--stress] [--capacity N] [--fuel N]');
let capacity=128n,fuel=200000n,stress=0n;
for(let i=0;i<flags.length;i++) {
  const flag=flags[i];
  if(flag==='--stress') {stress=1n;continue;}
  if(flag!=='--capacity'&&flag!=='--fuel') throw Error(`unknown option ${flag}`);
  const value=flags[++i];
  if(!/^[0-9]+$/.test(value??'')||BigInt(value)>=(1n<<64n))
    throw Error(`${flag} requires an unsigned 64-bit integer`);
  if(flag==='--capacity') capacity=BigInt(value);else fuel=BigInt(value);
}
const x=new WebAssembly.Instance(new WebAssembly.Module(readFileSync(modulePath))).exports;
const h=new Host(x),code=h.array(compile(readFileSync(sourcePath,'utf8')));
let state;
try {
  state=x.init(capacity,stress);
  state=x.boot(code,state);state=x.run(code,state,fuel);
  const words=h.words(state);
  if(words[0]===4n) throw Error(`Smalltalk VM error ${words[15]}`);
  if(words[0]!==3n) throw Error('instruction fuel exhausted');
  const result=cell(words,words[7]);
  console.log(result[0]===1n?BigInt.asIntN(64,result[2]).toString():
    result[0]===2n?['nil','false','true'][Number(result[2])]:`object ${words[7]}`);
} finally {if(state!==undefined)h.release(state);h.release(code);}
