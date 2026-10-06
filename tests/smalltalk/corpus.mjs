import {Program,core,SELECTORS as S,jsonWords} from '../../tools/smalltalk-program.mjs';
import {compile} from '../../tools/smalltalk-compile.mjs';
import {mkdirSync,writeFileSync} from 'node:fs';
const cases=[];
function source(name,text,expected,options={}) {
  cases.push({name,code:jsonWords(compile(text)),capacity:128,fuel:200000,expected:String(BigInt.asUintN(64,BigInt(expected))),kind:1,error:0,...options});
}
function fixture(name,build,expected,options={}) {
  const p=core(new Program()),main=p.method(7,p.selector('run'));
  p.code(main,build(p,main));
  cases.push({name,code:jsonWords(p.wire(main)),capacity:128,fuel:200000,expected:String(BigInt.asUintN(64,BigInt(expected))),kind:1,error:0,...options});
}
source('literal','42',42); source('negative','-42',-42);
source('arithmetic','40 + 2',42); source('subtraction','50 - 8',42);
source('precedence','1 + 2 + 3',6);
source('binary-associativity','10 - 3 - 2',5);
source('unary-before-binary','[40] value + 2',42);
source('binary-before-keyword','[:x | x + x] value: 10 - 3',14);
source('assignment','| a b | a := b := 42. a + b',84);
source('assignment-value','| x | (x := 40) + 2',42);
source('capture-mutate','| x b | x := 40. b := [x := x + 1]. b value. b value. x',42);
source('nested-capture','| x | x := 40. [[x := x + 2] value] value. x',42);
source('block-argument','[:x | x + 2] value: 40',42);
source('argument-capture','[:x | [x + 2] value] value: 40',42);
source('block-temporary','[| x | x := 40. x + 2] value',42);
source('shadowing','| x | x := 40. [| x | x := 999] value. x + 2',42);
source('nonlocal','[ ^42 ] value. 999',42);
source('nested-nonlocal','[[^42] value. 999] value. 998',42);
source('nonlocal-through-control','true ifTrue: [^42]. 999',42);
source('ifTrue','true ifTrue: [42]',42);
source('ifFalse','false ifFalse: [42]',42);
source('ifTrue-skipped','false ifTrue: [999]',0,{kind:2});
source('while','| x | x := 0. [x < 1000] whileTrue: [x := x + 1]. x',1000,{capacity:64});
source('int-identity','42 == 42',2,{kind:2});
source('class-identity','Object == Object',2,{kind:2});
source('different-object','Object new == Object new',1,{kind:2});
source('signed-less','-1 < 0',2,{kind:2});
source('equality','40 = 42',1,{kind:2});
source('tight-less','1 < 2',2,{kind:2,capacity:11});
source('tight-equality','1 = 2',1,{kind:2,capacity:11});
source('tight-identity','1 == 2',1,{kind:2,capacity:11});
source('overflow-fallback','9223372036854775807 + 1',0,{kind:2});
source('underflow-fallback','-9223372036854775808 - 1',0,{kind:2});
source('type-fallback','1 + nil',0,{kind:2});
source('collect-capture','| x b | x := 40. b := [x + 2]. self collect. b value',42);
source('out-of-memory','40 + 2',0,{capacity:8,error:9});
source('out-of-memory-call','[42] value',0,{capacity:9,error:9});
source('out-of-memory-boot','| a b c d | 42',0,{capacity:8,error:9});
source('missing-selector','self unknownMessage',0,{error:5});
fixture('direct-loop',()=>[
  ['int',0],['store',1],'loop',['load',1],['int',10000],['send',S['<'],1],['false','done'],
  ['load',1],['int',1],['send',S['+'],1],['store',1],['jump','loop'],'done',['load',1],['return']
],10000,{capacity:24});
// The loop's one local is specified in its method descriptor.
{const c=cases.at(-1),w=c.code.map(BigInt),m=Number(w[3]);w[8+4*Number(w[0])+6*(m-1)+3]=1n;c.code=jsonWords(w);}
for(const escaped of [false,true]) fixture(escaped?'escaped-nonlocal':'escaped-ordinary',(p)=>{
  const make=p.method(7,p.selector('make'),1,1),block=p.method(7,0);
  p.code(block,[['load',1,1],['int',2],['send',S['+'],1],[escaped?'nonlocal':'return']]);
  p.code(make,[['int',40],['store',1],['block',block],['return']]);
  return [['load',0],['send',p.selector('make'),0],['load',0],['send',S.collect,0],['pop'],['send',S.value,0],['return']];
},42,{error:escaped?7:0});
fixture('nonlocal-unwinds-method',(p)=>{
  const invoke=p.method(7,p.selector('invoke:'),2),block=p.method(7,0);
  p.code(invoke,[['load',1],['send',S.value,0],['pop'],['int',999],['return']]);
  p.code(block,[['int',42],['nonlocal']]);
  return [['load',0],['block',block],['send',p.selector('invoke:'),1],['return']];
},42);
fixture('fields-and-inheritance',(p)=>{
  const base=p.addClass(1,1),child=p.addClass(base,2);
  const setter=p.method(base,p.selector('set:'),2),getter=p.method(base,p.selector('get'));
  p.code(setter,[['load',1],['setField',0],['load',0],['return']]);
  p.code(getter,[['field',0],['return']]);
  return [['class',child],['send',S.new,0],['int',42],['send',p.selector('set:'),1],['send',p.selector('get'),0],['return']];
},42);
fixture('out-of-memory-fields',(p)=>{
  const owner=p.addClass(1,2);
  return [['class',owner],['send',S.new,0],['return']];
},0,{capacity:11,error:9});
fixture('super-in-block',(p)=>{
  const base=p.addClass(),child=p.addClass(base),sel=p.selector('answer');
  p.code(p.method(base,sel),[['int',42],['return']]);
  const method=p.method(child,sel),block=p.method(child,0);
  p.code(block,[['load',0],['super',sel,0],['return']]);
  p.code(method,[['block',block],['send',S.value,0],['return']]);
  return [['class',child],['send',S.new,0],['send',sel,0],['return']];
},42);
fixture('class-side-inheritance',(p)=>{
  p.addClass(1,0,9); const baseMeta=p.addClass(6); const child=p.addClass(8,0,11); p.addClass(baseMeta);
  p.code(p.method(baseMeta,p.selector('answer')),[['int',42],['return']]);
  return [['class',child],['send',p.selector('answer'),0],['return']];
},42);
fixture('bad-block-arity',(p)=>{
  const block=p.method(7,0,2);p.code(block,[['load',1],['return']]);
  return [['block',block],['send',S.value,0],['return']];
},0,{error:6});
fixture('bad-boolean',()=>[['int',1],['false','end'],'end',['return']],0,{error:8});
fixture('stack-underflow',()=>[['pop'],['return']],0,{error:4});
fixture('bad-slot',()=>[['load',999],['return']],0,{error:2});
fixture('bad-jump',()=>[['jump',999999]],0,{error:10});
fixture('wrong-block-owner',(p)=>{const b=p.method(6,0);p.code(b,[['constant',0],['return']]);return [['block',b],['return']];},0,{error:10});
cases.push({name:'invalid-wire',code:['0'],capacity:32,fuel:20,expected:'0',kind:1,error:10});
source('nil','nil',0,{kind:2}); source('true','true',2,{kind:2}); source('false','false',1,{kind:2});
source('empty-block','[] value',0,{kind:2}); source('empty-workspace','',0,{kind:2});
source('default-local','| x | x',0,{kind:2});
source('comment','"a workspace comment" 42',42);
source('same-object','| x | x := Object new. x == x',2,{kind:2});
source('different-blocks','[] == []',1,{kind:2});
source('minimum-integer','-9223372036854775808',-(1n<<63n));
source('mutated-argument','[:x | x := x + 2. x] value: 40',42);
source('nonlocal-in-loop','| x | x := 0. [true] whileTrue: [x := x + 1. (x = 42) ifTrue: [^x]]. 0',42,{capacity:80});
fixture('direct-super',(p)=>{
  const base=p.addClass(),child=p.addClass(base),sel=p.selector('answer');
  p.code(p.method(base,sel),[['int',41],['return']]);
  p.code(p.method(child,sel),[['load',0],['super',sel,0],['int',1],['send',S['+'],1],['return']]);
  return [['class',child],['send',S.new,0],['send',sel,0],['return']];
},42);
fixture('two-block-arguments',(p)=>{
  const selector=p.selector('value:value:');p.code(p.method(5,selector,3,0,7),[['constant',0],['return']]);
  const block=p.method(7,0,3);p.code(block,[['load',1],['load',2],['send',S['+'],1],['return']]);
  return [['block',block],['int',40],['int',2],['send',selector,2],['return']];
},42);
mkdirSync('build/smalltalk',{recursive:true});
writeFileSync('build/smalltalk/corpus.json',JSON.stringify(cases));
console.log(`corpus: ${cases.length} programs`);
