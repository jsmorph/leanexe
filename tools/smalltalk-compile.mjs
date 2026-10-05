import {Program,core,CLASSES,jsonWords} from './smalltalk-program.mjs';
import {readFileSync,writeFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';

function tokenize(source) {
  const tokens=[]; let i=0;
  while(i<source.length) {
    if(/\s/.test(source[i])) { i++; continue; }
    if(source[i]==='"') {
      const end=source.indexOf('"',i+1); if(end<0) throw Error('unterminated comment');
      i=end+1; continue;
    }
    const m=/^(?::=|[A-Za-z_][A-Za-z_0-9]*:?|[0-9]+|==|[-+<>=*/~@%&,?!]+|[()[\].|^:])/.exec(source.slice(i));
    if(!m) throw Error(`unsupported token at ${i}: ${source[i]}`);
    if(/^[0-9]+$/.test(m[0]) && /^\.[0-9]/.test(source.slice(i+m[0].length))) throw Error('floats unsupported');
    tokens.push(m[0]); i+=m[0].length;
  }
  return tokens;
}
const identifier=x=>typeof x==='string' && /^[A-Za-z_][A-Za-z_0-9]*$/.test(x);
const keyword=x=>typeof x==='string' && /^[A-Za-z_][A-Za-z_0-9]*:$/.test(x);
const binary=x=>typeof x==='string' && /^[-+<>=*/~@%&,?!]+$/.test(x);

export function compile(source) {
  const tokens=tokenize(source), p=core(new Program()); let cursor=0, depth=0;
  const peek=()=>tokens[cursor], take=()=>tokens[cursor++];
  const expect=x=>{if(take()!==x) throw Error(`expected ${x} at token ${cursor-1}`);};
  const resolve=(f,name)=>{
    for(let d=0;f;f=f.outer,d++) if(f.names.has(name)) return [f.names.get(name),d];
    throw Error(`unknown variable ${name}`);
  };
  function frame(outer,args=[],isBlock=false) {
    const names=new Map([['self',0]]);
    for(const a of args) { if(names.has(a)) throw Error(`duplicate binding ${a}`); names.set(a,names.size); }
    if(peek()==='|') {
      take(); while(peek()!=='|') {
        const name=take(); if(!identifier(name)||names.has(name)) throw Error('invalid local declaration');
        names.set(name,names.size);
      } expect('|');
    }
    const method=p.method(7,isBlock?0:p.selector('run'),args.length+1,names.size-args.length-1);
    return {outer,names,method,isBlock,code:[]};
  }
  const emit=(f,...ins)=>f.code.push(ins);
  function atom(f) {
    const t=take();
    if(t==='(') { expression(f); expect(')'); }
    else if(t==='[') {
      if(++depth>128) throw Error('blocks nested too deeply');
      const args=[];
      while(peek()===':') { take(); const a=take(); if(!identifier(a)) throw Error('invalid block argument'); args.push(a); }
      if(args.length) expect('|');
      const child=frame(f,args,true); body(child,']'); expect(']');
      p.code(child.method,child.code); emit(f,'block',child.method); depth--;
    } else if(t==='nil'||t==='false'||t==='true') emit(f,'constant',{nil:0,false:1,true:2}[t]);
    else if(Object.hasOwn(CLASSES,t)) emit(f,'class',CLASSES[t]);
    else if(/^[0-9]+$/.test(t??'') || (t==='-' && /^[0-9]+$/.test(peek()??''))) {
      const value=BigInt(t==='-'?'-'+take():t);
      if(value<-(1n<<63n)||value>=(1n<<63n)) throw Error('integer outside signed 64-bit range');
      emit(f,'int',value);
    } else if(identifier(t)) emit(f,'load',...resolve(f,t));
    else throw Error(`expected expression at token ${cursor-1}`);
  }
  function unary(f) { atom(f); while(identifier(peek())) emit(f,'send',p.selector(take()),0); }
  function binaries(f) { unary(f); while(binary(peek())) { const name=take(); unary(f); emit(f,'send',p.selector(name),1); } }
  function keywords(f) {
    binaries(f); let name='',arity=0;
    while(keyword(peek())) { name+=take(); binaries(f); arity++; }
    if(arity) emit(f,'send',p.selector(name),arity);
  }
  function expression(f) {
    if(identifier(peek()) && tokens[cursor+1]===':=') {
      const name=take(); take(); if(name==='self') throw Error('cannot assign self');
      const slot=resolve(f,name); expression(f); emit(f,'dup'); emit(f,'store',...slot);
    } else keywords(f);
  }
  function body(f,stop) {
    if(peek()===stop) emit(f,'constant',0);
    else while(peek()!==stop) {
      const returns=peek()==='^'; if(returns) take();
      expression(f); if(returns) emit(f,f.isBlock?'nonlocal':'return');
      if(peek()!=='.') break;
      take(); if(peek()===stop) break; emit(f,'pop');
    }
    emit(f,'return');
  }
  const main=frame(null); body(main,undefined);
  if(cursor!==tokens.length) throw Error(`unexpected token ${peek()}`);
  p.code(main.method,main.code);
  return p.wire(main.method);
}
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) {
  const [input,output]=process.argv.slice(2);
  if(!input) throw Error('usage: smalltalk-compile.mjs INPUT.st [OUTPUT.json]');
  const text=JSON.stringify(jsonWords(compile(readFileSync(input,'utf8'))))+'\n';
  if(output) writeFileSync(output,text); else process.stdout.write(text);
}
