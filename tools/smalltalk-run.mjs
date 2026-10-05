import {readFileSync} from 'node:fs';
import {compile} from './smalltalk-compile.mjs';
import {Host,cell} from './smalltalk-host.mjs';
const args=process.argv.slice(2),[modulePath,sourcePath]=args;
if(!modulePath||!sourcePath) throw Error('usage: smalltalk-run.mjs MODULE.wasm INPUT.st [--stress] [--capacity N] [--fuel N]');
const option=(name,fallback)=>{const i=args.indexOf(name);return i<0?fallback:BigInt(args[i+1]);};
const x=new WebAssembly.Instance(new WebAssembly.Module(readFileSync(modulePath))).exports;
const h=new Host(x),code=h.array(compile(readFileSync(sourcePath,'utf8')));
let state=x.init(option('--capacity',128n),args.includes('--stress')?1n:0n);
try {
  state=x.boot(code,state);state=x.run(code,state,option('--fuel',200000n));
  const words=h.words(state);
  if(words[0]===4n) throw Error(`Smalltalk VM error ${words[15]}`);
  if(words[0]!==3n) throw Error('instruction fuel exhausted');
  const result=cell(words,words[7]);
  console.log(result[0]===1n?BigInt.asIntN(64,result[2]).toString():
    result[0]===2n?['nil','false','true'][Number(result[2])]:`object ${words[7]}`);
} finally {h.release(state);h.release(code);}
