// Wasm host bindings. No floating-point model, tokenization, or sampling math.
const need=(ok,message)=>{if(!ok)throw Error(message);};
const INPUT=64,OUTPUT=16384,LOGITS=201028,WEIGHTS=497759232;
const temperatures={"0":0n,"0.7":0x3fe6666666666666n,"0.8":0x3fe999999999999an,"1":0x3ff0000000000000n};
const bytes=values=>{
  const data=new Uint8Array(values.length*8),view=new DataView(data.buffer);
  values.forEach((v,i)=>view.setBigUint64(i*8,BigInt(v),true));return data;
};
const words=data=>Array.from({length:data.byteLength/8},(_,i)=>new DataView(data.buffer,data.byteOffset,data.byteLength).getBigUint64(i*8,true));
async function artifact(name) {
  const response=await fetch(`/bundle/${name}`);need(response.ok,`Cannot load ${name}`);return response.arrayBuffer();
}
class Wasm {
  constructor(w){this.w=w;}
  region(pointer,size){
    const p=Number(pointer);need(Number.isSafeInteger(p)&&p>=0&&p+size<=this.w.memory.buffer.byteLength,"Wasm byte range");
    return new Uint8Array(this.w.memory.buffer,p,size);
  }
  array(data){
    need(data.byteLength%8===0,"Wasm word array alignment");
    const pointer=this.w.alloc(BigInt(data.byteLength+8));
    new DataView(this.w.memory.buffer).setBigUint64(Number(pointer),BigInt(data.byteLength/8),true);
    this.region(pointer+8n,data.byteLength).set(data);return pointer;
  }
  result(pointer,max){
    const n=Number(new DataView(this.region(pointer,8).buffer).getBigUint64(Number(pointer),true));
    need(n<=max,"Wasm result length");return this.region(pointer+8n,n*8).slice();
  }
}
let started=false;
self.onmessage=async ({data:options})=>{
  if(started)return;started=true;
  try {
    const count=options.generate,settings=[temperatures[options.temperature],40n,BigInt(options.seed)];
    need(Number.isInteger(count)&&count>0&&count<128,"Generation count must be 1–127");
    need(settings[0]!==undefined&&settings[2]>0n&&settings[2]<2n**64n,"Invalid sampler settings");
    const prompt=new TextEncoder().encode(options.prompt);need(prompt.length>0&&prompt.length<=16384,"Prompt byte length");
    const shared=options.shared,control=new Int32Array(shared,0,1);let model,weightsPtr;
    const invoke=(kind,args)=>{
      need(args[1]===weightsPtr&&args[2]===BigInt(WEIGHTS),"Unexpected weight allocation");
      const size=kind==="linear"?Number(args[8])*4:3072;
      need(size<=12288&&args[5]>=BigInt(size),"Matrix input length");
      new Uint8Array(shared,INPUT,size).set(model.region(args[4],size));
      const request=kind==="linear"?{kind,weightOffset:Number(args[6]),biasOffset:Number(args[7]),inner:Number(args[8]),cols:Number(args[9])}:{kind};
      if(kind==="linear")need(args[10]===1n,"Only one-row products are supported");
      Atomics.store(control,0,0);self.postMessage({type:"dispatch",request});
      need(Atomics.wait(control,0,0,60000)!=="timed-out","WebGPU dispatch timed out");
      need(Atomics.load(control,0)===1,"WebGPU dispatch failed");
      const outputSize=kind==="linear"?request.cols*4:LOGITS;
      model.region(args.at(-1),outputSize).set(new Uint8Array(shared,OUTPUT,outputSize));
    };
    const instantiate=async(name,imports={})=>new Wasm((await WebAssembly.instantiate(await artifact(name),imports)).instance.exports);
    self.postMessage({type:"status",text:"Loading Wasm and tokenizer"});
    model=await instantiate("model.wasm",{wgsl:{linear:(...args)=>invoke("linear",args),vocabulary:(...args)=>invoke("vocabulary",args)}});
    const tokenizer=await instantiate("tokenizer.wasm"),sampler=await instantiate("sampler.wasm"),transfer=await instantiate("transfer.wasm");
    const table=new Uint8Array(await artifact("tokenizer.bin"));
    const tokens=(op,input)=>{
      tokenizer.w.reset();return tokenizer.result(tokenizer.w.tokens(BigInt(op),tokenizer.array(table),tokenizer.array(input)),65536);
    };
    const encoded=words(tokens(0,bytes(Array.from(prompt))));
    need(encoded.length>0&&encoded.every(t=>t<50257n),"Tokenizer rejected prompt");
    need(encoded.length+count<=128,"Prompt and requested completion exceed 128 tokens");
    self.postMessage({type:"status",text:"Loading 124M checkpoint"});
    const weightBytes=await artifact("weights.bin");need(weightBytes.byteLength===WEIGHTS,"Checkpoint byte length");
    model.w.reset();weightsPtr=model.w.alloc(BigInt(WEIGHTS));model.region(weightsPtr,WEIGHTS).set(new Uint8Array(weightBytes));
    // The GPU host receives the same immutable source bytes just written to Wasm.
    self.postMessage({type:"weights",bytes:weightBytes},[weightBytes]);
    let cache=0n,cacheSize=0n,logits;
    const forward=(token,position)=>{
      const result=model.w.cachedStep(weightsPtr,BigInt(WEIGHTS),cache,cacheSize,token,BigInt(position));
      need(result[1]===BigInt((position+1)*73728)&&result[3]===BigInt(LOGITS),"Wasm output lengths");
      const output=model.region(result[2],LOGITS).slice();
      if(cache)model.w.release(cache);model.w.release(result[2]);[cache,cacheSize]=result;return output;
    };
    for(let i=0;i<encoded.length;i++){
      self.postMessage({type:"status",text:`Prompt token ${i+1}/${encoded.length}`});logits=forward(encoded[i],i);
    }
    let reason="count",produced=0;
    for(let i=0;i<count;i++){
      transfer.region(161000000n,LOGITS).set(logits);transfer.w.convert(1n,50257n);sampler.w.reset();
      const result=words(sampler.result(sampler.w.compute(5n,sampler.array(transfer.region(160000000n,50257*8)),
        sampler.array(new Uint8Array()),sampler.array(bytes(settings)),0n),2));
      need(result.length===2&&result[0]<50257n,"Wasm sampler rejected logits");
      const [token,seed]=result;settings[2]=seed;
      if(options.trace){const copy=logits.slice();self.postMessage({type:"trace",token:Number(token),logits:copy.buffer},[copy.buffer]);}
      if(token===50256n){reason="eos";break;}
      const decoded=words(tokens(1,bytes([token])));need(decoded.every(b=>b<256n),"Decoded byte range");
      const output=new Uint8Array(decoded.map(Number));self.postMessage({type:"token",token:Number(token),bytes:output.buffer},[output.buffer]);produced++;
      if(i+1<count)logits=forward(token,encoded.length+i);
    }
    if(cache)model.w.release(cache);model.w.release(weightsPtr);
    self.postMessage({type:"done",reason,produced,promptTokens:encoded.length});
  } catch(error){self.postMessage({type:"error",message:error.message});}
};
