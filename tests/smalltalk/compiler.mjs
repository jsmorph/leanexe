import assert from 'node:assert/strict';
import {compile} from '../../tools/smalltalk-compile.mjs';
const rejected=["'string'",'#symbol','1.2','self; foo','| x x | x','| self | self',
  '[ :x :x | x ]','missingVariable','self := 1','[1','(1','1 )','9223372036854775808',
  '-9223372036854775809','"unfinished comment','| x | x :='];
for(const source of rejected) assert.throws(()=>compile(source),source);
console.log(`compiler: ${rejected.length} rejected inputs`);
