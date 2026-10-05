// ABI bridge only. All VM execution and collection run inside the emitted WASM.
export class Host {
  constructor(exports) { this.x=exports; }
  array(words) {
    const ptr=this.x.alloc(BigInt(8*(words.length+1)));
    const view=new DataView(this.x.memory.buffer), base=Number(ptr);
    view.setBigUint64(base-24,2n,true);
    view.setBigUint64(base-16,1n,true);
    view.setBigUint64(base-8,0n,true);
    view.setBigUint64(base,BigInt(words.length),true);
    words.forEach((word,i)=>view.setBigUint64(base+8*(i+1),BigInt.asUintN(64,BigInt(word)),true));
    return ptr;
  }
  words(ptr) {
    const view=new DataView(this.x.memory.buffer),base=Number(ptr);
    return Array.from({length:Number(view.getBigUint64(base,true))},(_,i)=>view.getBigUint64(base+8*(i+1),true));
  }
  release(ptr) { this.x.release(ptr); }
  outstanding() { return this.x.allocCount.value-this.x.freeCount.value; }
}
export const cell=(state,handle)=>state.slice(24+8*(Number(handle)-1),24+8*Number(handle));
