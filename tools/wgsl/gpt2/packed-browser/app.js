import {runPacked} from './host.js';
const $=id=>document.getElementById(id),runs={wasm:null,wgsl:null};
let controller,running=false,renderQueued=false;
window.runPacked=runPacked;
const seconds=ms=>ms==null?'—':`${(ms/1000).toFixed(3)} s`;
const mib=bytes=>bytes==null?'—':`${(bytes/1048576).toFixed(1)} MiB`;
const rate=(n,ms)=>n>0&&ms>0?`${(n*1000/ms).toFixed(2)} tok/s`:'—';
const metrics=[
  ['Setup',s=>seconds(s.setupMs)],['Prompt tokens processed',s=>`${s.prefillCompleted} / ${s.promptTokens}`],
  ['Prefill time',s=>seconds(s.prefillMs)],['Prefill throughput',s=>rate(s.prefillCompleted,s.prefillMs)],
  ['First token · after setup',s=>seconds(s.timeToFirstTokenMs)],['Generated tokens',s=>String(s.produced)],
  ['Decode model steps',s=>String(s.decodeSteps)],['Decode time',s=>seconds(s.decodeMs)],
  ['Decode throughput',s=>rate(s.decodeSteps,s.decodeMs)],['Sampling time',s=>seconds(s.samplingMs)],
  ['Text decoding time',s=>seconds(s.detokenizeMs)],['Generation elapsed',s=>seconds(s.generationMs)],
  ['Total elapsed · including setup',s=>seconds(s.totalMs)],['Model Wasm memory · peak',s=>mib(s.memory.modelWasmBytes)],
  ['Auxiliary Wasm memory · peak',s=>mib(s.memory.auxiliaryWasmBytes)],['KV cache payload · peak',s=>mib(s.memory.cacheBytes)],
  ['WebGPU buffers · peak',s=>mib(s.memory.gpuBufferBytes)],['Extra host weight copy',s=>mib(s.memory.hostWeightBytes)],
  ['Shared transfer staging',s=>mib(s.memory.sharedStagingBytes)],['WGSL dispatches',s=>String(s.dispatches)]
];
const cells=metrics.map(([name])=>{
  const row=document.createElement('tr'),label=document.createElement('th');label.scope='row';label.textContent=name;row.append(label);
  const values=['wasm','wgsl'].map(()=>{const td=document.createElement('td');td.textContent='—';row.append(td);return td;});
  $('metrics').append(row);return values;
});
function render(){
  renderQueued=false;
  metrics.forEach(([,format],i)=>['wasm','wgsl'].forEach((backend,j)=>{cells[i][j].textContent=runs[backend]?.stats?format(runs[backend].stats):'—';}));
  const a=runs.wasm,b=runs.wgsl;
  if(!a?.done||!b?.done){$('comparison').textContent=running?'Running. Live measurements appear below.':'Complete both runs to compare their outputs and speed.';return;}
  if(a.key!==b.key){$('comparison').textContent='These runs used different prompts or generation settings. Use Compare both for matching inputs.';return;}
  const equal=a.tokens.length===b.tokens.length&&a.tokens.every((token,i)=>token===b.tokens[i])&&a.result.reason===b.result.reason;
  const identity=equal?`All ${a.tokens.length} generated token IDs and the stopping reason match.`:'The completions differ. Decode timings follow each implementation’s own generated token sequence.';
  const x=a.stats,y=b.stats;
  let speed='';
  if(x.decodeSteps&&y.decodeSteps&&x.decodeMs>0&&y.decodeMs>0){
    const ratio=(x.decodeMs/x.decodeSteps)/(y.decodeMs/y.decodeSteps);
    speed=ratio>=1?` WGSL decode throughput is ${ratio.toFixed(2)}× CPU Wasm.`:` CPU Wasm decode throughput is ${(1/ratio).toFixed(2)}× WGSL.`;
  }
  $('comparison').textContent=identity+speed;
}
function scheduleRender(){if(!renderQueued){renderQueued=true;requestAnimationFrame(render);}}
function deviceLabel(cpu){return cpu?'CPU WebGPU':'Available GPU';}
function adapterLabel(info){return `${info.isFallbackAdapter?'CPU fallback':'GPU adapter'} · ${[info.description,info.vendor,info.architecture,info.device].filter(Boolean).join(' · ')||'name unavailable'}`;}
function setBusy(value){
  running=value;$('settings').disabled=value;$('run').disabled=value;$('compare').disabled=value;$('stop').disabled=!value;
  if(!value)$('device').disabled=$('backend').value==='wasm';
}
async function execute(compare){
  if(running)return;
  const options={prompt:$('prompt').value,generate:Number($('count').value),temperature:$('temperature').value,seed:$('seed').value,cpu:$('device').value==='cpu'};
  const key=JSON.stringify([options.prompt,options.generate,options.temperature,options.seed]);
  const order=compare?['wasm','wgsl']:[$('backend').value];
  if(compare)for(const backend of order){
    runs[backend]=null;$(`${backend}-output`).textContent='Waiting to run…';
    $(`${backend}-status`).textContent='Queued';$(`${backend}-settings`).textContent='';
    $(`${backend}-status`).classList.remove('error');
  }
  controller=new AbortController();setBusy(true);let failed=false;
  try{
    for(const backend of order){
      if(controller.signal.aborted)break;
      const decoder=new TextDecoder(),entry={key,tokens:[],stats:null,done:false};runs[backend]=entry;
      const output=$(`${backend}-output`);output.replaceChildren();
      const echo=document.createElement('span');echo.className='echo';echo.textContent=options.prompt;output.append(echo);
      const continuation=document.createTextNode('');output.append(continuation);
      $(`${backend}-card`).classList.add('active');$(`${backend}-status`).classList.remove('error');
      $(`${backend}-settings`).textContent=`Requested ${options.generate} tokens · temperature ${options.temperature} · seed ${options.seed}${backend==='wgsl'?` · ${deviceLabel(options.cpu)}`:''}`;
      if(backend==='wgsl')$('wgsl-adapter').textContent=`Requesting ${deviceLabel(options.cpu)}…`;
      const status=text=>{$('status').textContent=`${backend==='wasm'?'CPU Wasm':'Wasm + WGSL'}: ${text}`;$(`${backend}-status`).textContent=text;};
      status('Starting…');scheduleRender();
      try{
        entry.result=await runPacked({...options,backend,signal:controller.signal},event=>{
          if(event.type==='status')status(event.text);
          if(event.type==='adapter')$('wgsl-adapter').textContent=adapterLabel(event.info);
          if(event.type==='token'){entry.tokens.push(event.token);continuation.textContent+=decoder.decode(event.bytes,{stream:true});}
          if(event.stats){entry.stats=event.stats;scheduleRender();}
        });
        entry.done=true;entry.stats=entry.result.stats;
        status(`Finished · ${entry.result.produced} tokens · ${entry.result.reason==='eos'?'end-of-text token':'requested count reached'}`);
      }catch(error){
        failed=true;status(error.name==='AbortError'?'Stopped. Measurements are partial.':error.message);
        $(`${backend}-status`).classList.toggle('error',error.name!=='AbortError');
      }finally{continuation.textContent+=decoder.decode();$(`${backend}-card`).classList.remove('active');render();}
    }
  }finally{
    setBusy(false);$('status').textContent=controller.signal.aborted?'Stopped.':failed?'One or more runs did not finish. See each result for details.':'Finished. Results and measurements are retained below.';render();
  }
}
$('run').onclick=()=>execute(false);$('compare').onclick=()=>execute(true);$('stop').onclick=()=>controller?.abort();
$('backend').onchange=()=>{$('device').disabled=$('backend').value==='wasm';};
if(!navigator.gpu){$('backend').value='wasm';$('device').disabled=true;$('status').textContent='WebGPU is unavailable here. CPU-only Wasm is available.';}
