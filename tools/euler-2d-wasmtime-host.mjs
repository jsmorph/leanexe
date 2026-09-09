import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
const root=fileURLToPath(new URL('../',import.meta.url));
const source=path.join(root,'tools/euler-2d-wasmtime-host.c');
const hash=bytes=>crypto.createHash('sha256').update(bytes).digest('hex');
const flags=['-std=c11','-O2','-Wall','-Wextra','-Werror','-fno-fast-math','-ffp-contract=off'];
export function ensure2DHost(){
 const api=process.env.WASMTIME_C_API;
 assert.ok(api&&path.basename(api).startsWith('wasmtime-v44.0.0-'),'source the pinned Wasmtime44 environment');
 assert.ok(fs.existsSync(path.join(api,'include/wasmtime.h')));
 const input={sourceSha256:hash(fs.readFileSync(source)),flags,api,platform:process.platform,arch:process.arch};
 const digest=hash(JSON.stringify(input)),executable=path.join(root,'build/tools/euler-2d-wasmtime-host-'+digest),receipt=executable+'.json';
 if(fs.existsSync(executable)||fs.existsSync(receipt)){
  assert.ok(fs.existsSync(executable)&&fs.existsSync(receipt),'preserve incomplete build; refuse reuse');
  const record=JSON.parse(fs.readFileSync(receipt));assert.deepEqual(record.input,input);assert.equal(hash(fs.readFileSync(executable)),record.executableSha256);
 }else{
  execFileSync('cc',[...flags,'-I'+path.join(api,'include'),source,'-L'+path.join(api,'lib'),'-lwasmtime','-Wl,-rpath,'+path.join(api,'lib'),'-o',executable],{cwd:root,timeout:120000,stdio:'pipe'});
  fs.writeFileSync(receipt,JSON.stringify({input,executableSha256:hash(fs.readFileSync(executable))},null,2)+'\n',{flag:'wx'});
 }
 return executable;
}
export function run2DHost(side,flux,cell,n,frames,scenario){
 const executable=ensure2DHost(),directory=fs.mkdtempSync(path.join(root,'tmp/euler-2d-run-'));
 const outPath=path.join(directory,'run.ndjson'),errPath=path.join(directory,'stderr.log');
 const output=fs.openSync(outPath,'wx'),error=fs.openSync(errPath,'wx');
 try{execFileSync(executable,[scenario,side,flux,cell,String(n),String(frames)],{cwd:root,timeout:600000,stdio:['ignore',output,error]});}
 finally{fs.closeSync(output);fs.closeSync(error);}
 const events=fs.readFileSync(outPath,'utf8').trim().split('\n').map(line=>JSON.parse(line));
 return {events,evidenceDirectory:path.relative(root,directory)};
}
