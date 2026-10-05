// Immutable wordcode builder and a minimal library. The Lean VM performs execution.
export const OP = Object.freeze({int:0,constant:1,load:2,store:3,field:4,setField:5,
  block:6,class:7,dup:8,pop:9,send:10,super:11,return:12,nonlocal:13,jump:14,false:15});
export const SELECTORS = Object.freeze({new:1,'+':2,'-':3,'<':4,'=':5,'==':6,
  value:7,'value:':8,collect:9,'ifTrue:':10,'ifFalse:':11,'whileTrue:':12});
export const CLASSES = Object.freeze({Object:1,Nil:2,Boolean:3,Integer:4,Block:5,Class:6,Main:7});
export class Program {
  constructor() {
    this.classes = Array.from({length:7},(_,i)=>[i===0?0:1,6,0,0]);
    this.methods=[]; this.selectors=new Map(Object.entries(SELECTORS)); this.nextSelector=40;
  }
  selector(name) {
    if (!this.selectors.has(name)) this.selectors.set(name,this.nextSelector++);
    return this.selectors.get(name);
  }
  addClass(parent=1,fields=0,meta=6) {
    this.classes.push([parent,meta,fields,0]); return this.classes.length;
  }
  method(owner,selector,arity=1,locals=0,primitive=0) {
    this.methods.push({owner,selector,arity,locals,primitive,body:[]}); return this.methods.length;
  }
  code(id,body) { this.methods[id-1].body=body; return id; }
  wire(entry) {
    const instructions=[], descriptors=[];
    for(const m of this.methods) {
      const start=instructions.length, labels=new Map(); let count=0;
      for(const ins of m.body) { if(typeof ins==='string') labels.set(ins,count); else count++; }
      descriptors.push(m.owner,m.selector,m.arity,m.locals,start,m.primitive);
      for(const ins of m.body) {
        if(typeof ins==='string') continue;
        const [name,a=0,b=0]=ins, op=typeof name==='number'?name:OP[name];
        if(op===undefined) throw Error(`unknown instruction ${name}`);
        const target=typeof a==='string'?start+labels.get(a):a;
        if(target===undefined || Number.isNaN(target)) throw Error(`missing label ${a}`);
        instructions.push([op,target,b,0]);
      }
    }
    return [this.classes.length,this.methods.length,instructions.length,entry,2,3,4,5,
      ...this.classes.flat(),...descriptors,...instructions.flat()].map(x=>BigInt.asUintN(64,BigInt(x)));
  }
}
export function core(p) {
  const primitive=(owner,sel,arity,prim)=>p.code(p.method(owner,SELECTORS[sel],arity,0,prim),
    [['constant',0],['return']]);
  primitive(6,'new',1,1); primitive(1,'==',2,6); primitive(1,'collect',1,8);
  for(const [sel,prim] of [['+',2],['-',3],['<',4],['=',5]]) primitive(4,sel,2,prim);
  primitive(5,'value',1,7); primitive(5,'value:',2,7);
  p.code(p.method(3,SELECTORS['ifTrue:'],2),[
    ['load',0],['false','no'],['load',1],['send',7,0],['return'],'no',['constant',0],['return']]);
  p.code(p.method(3,SELECTORS['ifFalse:'],2),[
    ['load',0],['false','yes'],['constant',0],['return'],'yes',['load',1],['send',7,0],['return']]);
  p.code(p.method(5,SELECTORS['whileTrue:'],2),[
    'loop',['load',0],['send',7,0],['false','done'],['load',1],['send',7,0],['pop'],
    ['jump','loop'],'done',['constant',0],['return']]);
  return p;
}
export const jsonWords=words=>words.map(String);
