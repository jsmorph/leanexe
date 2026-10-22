#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

const files = execFileSync('git', ['ls-files', '--cached', '--others', '--exclude-standard'],
  { encoding: 'utf8' }).trim().split('\n').filter(p => p.endsWith('.md'));
const cache = new Map();
const problems = [];
let links = 0;

function content(file) {
  if (!cache.has(file)) cache.set(file, fs.readFileSync(file, 'utf8'));
  return cache.get(file);
}

function anchors(file) {
  const text = content(file).replace(/^```[^\n]*\n[\s\S]*?^```[^\n]*$/gm, '');
  const result = new Set();
  const counts = new Map();
  for (const match of text.matchAll(/^#{1,6}\s+(.+?)\s*#*$/gm)) {
    const base = match[1].replace(/<[^>]+>/g, '').toLowerCase()
      .replace(/[^\p{L}\p{N}_\-\s]/gu, '').replace(/ /g, '-');
    const count = counts.get(base) || 0;
    result.add(base + (count ? '-' + count : ''));
    counts.set(base, count + 1);
  }
  for (const match of text.matchAll(/<(?:a|h[1-6])\b[^>]*(?:id|name)=["']([^"']+)["']/g))
    result.add(match[1]);
  return result;
}

for (const file of files) {
  const text = content(file).replace(/^```[^\n]*\n[\s\S]*?^```[^\n]*$/gm, '');
  const targets = [...text.matchAll(/\[[^\]]*\]\(([^)\n]+)\)/g)].map(m => m[1]);
  targets.push(...[...text.matchAll(/^\[[^\]\n]+\]:\s*(\S+)/gm)].map(m => m[1]));
  for (let target of targets) {
    links++;
    target = target.replace(/^<([^>]+)>.*$/, '$1').replace(/\s+["'][\s\S]*$/, '');
    if (/^[a-z][a-z0-9+.-]*:/i.test(target) || target.startsWith('//')) continue;
    const [destination, fragment] = target.split('#', 2).map(s => decodeURIComponent(s));
    const resolved = destination ? path.resolve(path.dirname(file), destination) : path.resolve(file);
    if (!fs.existsSync(resolved)) {
      problems.push(`${file}: missing ${target}`);
      continue;
    }
    if (fragment && resolved.endsWith('.md') && !anchors(resolved).has(fragment))
      problems.push(`${file}: missing anchor ${target}`);
  }
}

console.log(JSON.stringify({ files: files.length, links, problems }, null, 2));
if (problems.length) process.exitCode = 1;
