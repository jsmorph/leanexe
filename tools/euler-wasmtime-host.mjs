import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
const root=fileURLToPath(new URL('../',import.meta.url));
const source=path.join(root,'tools/euler-wasmtime-host.c');
const flags=['-std=c11','-O2','-Wall','-Wextra','-Werror','-fno-fast-math','-ffp-contract=off'];
export function ensureEulerHost(){
 const api=process.env.WASMTIME_C_API;
 assert.ok(api&&path.basename(api).startsWith('wasmtime-v44.0.0-'),'source the pinned runtime environment');
 assert.ok(fs.existsSync(path.join(api,'include/wasmtime.h')));
 const digest=crypto.createHash('sha256').update(fs.readFileSync(source)).update(JSON.stringify({flags,api,platform:process.platform,arch:process.arch})).digest('hex');
 const executable=path.join(root,'build/tools/euler-wasmtime-host-'+digest);
 if(!fs.existsSync(executable)){
  execFileSync('cc',[...flags,'-I'+path.join(api,'include'),source,'-L'+path.join(api,'lib'),'-lwasmtime','-Wl,-rpath,'+path.join(api,'lib'),'-o',executable],{cwd:root,timeout:120000,stdio:'pipe'});
 }
 return executable;
}
export function runSodHost(scan,step,n,capture){
 const text=execFileSync(ensureEulerHost(),['sod',scan,step,String(n),capture?'1':'0'],{cwd:root,encoding:'utf8',timeout:600000,maxBuffer:128*1024*1024});
 return text.trim().split('\n').map(line=>JSON.parse(line));
}
