#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

function prose(file) {
  return /\.(md|markdown|mdx)$/i.test(file) || /^readme(?:\.txt)?$/i.test(path.basename(file));
}

function withoutCode(text) {
  let fence;
  return text.split('\n').map(line => {
    const match = line.match(/^ {0,3}(`{3,}|~{3,})/);
    if (fence) {
      if (match && match[1][0] === fence[0] && match[1].length >= fence.length &&
          line.slice(match[0].length).trim() === '') fence = undefined;
      return ' '.repeat(line.length);
    }
    if (match) { fence = match[1]; return ' '.repeat(line.length); }
    return line;
  }).join('\n').replace(/<!--[\s\S]*?-->/g, m => m.replace(/[^\n]/g, ' '));
}

function anchors(text) {
  const result = new Set();
  function add(heading) {
    const base = heading.replace(/\[([^\]]+)\]\([^)]*\)/g, '$1').replace(/<[^>]+>/g, '')
      .toLowerCase().replace(/[^\p{L}\p{N}_\-\s]/gu, '').replace(/ /g, '-');
    let id = base;
    for (let n = 1; result.has(id); n++) id = `${base}-${n}`;
    result.add(id);
  }
  const lines = text.split('\n');
  for (let i = 0; i < lines.length; i++) {
    const match = lines[i].match(/^ {0,3}#{1,6}\s+(.+?)\s*#*$/);
    if (match) add(match[1]);
    else if (lines[i].trim() && /^ {0,3}(?:=+|-+)\s*$/.test(lines[i + 1] ?? '')) add(lines[i]);
  }
  for (const match of text.matchAll(/<\w+\b[^>]*\b(?:id|name)=["']([^"']+)["']/gi))
    result.add(match[1]);
  return result;
}

function destination(text) {
  text = text.trim();
  if (text.startsWith('<')) return text.slice(1, text.indexOf('>'));
  return text.replace(/\s+["'][\s\S]*$/, '').replace(/\\([\\`*{}\[\]()#+.!_> -])/g, '$1');
}

function closing(text, start, open, close) {
  let depth = 1;
  let angle = false;
  let quote;
  for (let i = start + 1; i < text.length; i++) {
    if (text[i] === '\\') { i++; continue; }
    if (quote) {
      if (text[i] === quote) quote = undefined;
      continue;
    }
    if (open === '(' && !angle && /["']/.test(text[i]) && /\s/.test(text[i - 1])) {
      quote = text[i];
      continue;
    }
    if (open === '(' && text[i] === '<') angle = true;
    if (open === '(' && text[i] === '>') angle = false;
    if (angle) continue;
    if (text[i] === open) depth++;
    if (text[i] === close && --depth === 0) return i;
  }
  return -1;
}

function links(text) {
  const found = [];
  const refs = new Map();
  const normalize = text => text.replace(/\s+/g, ' ').trim().toLowerCase();
  const definitions = /^ {0,3}\[([^\]\n]+)\]:[ \t]*(?:\n[ \t]*)?(<[^>\n]+>|\S+)/gm;
  for (const match of text.matchAll(definitions)) {
    const target = destination(match[2]);
    refs.set(normalize(match[1]), target);
    found.push({ offset: match.index, target, definition: true });
  }
  const masked = text.replace(/(`+)([\s\S]*?)\1/g, m => m.replace(/[^\n]/g, ' '));
  const destinations = new Map();
  for (let i = 0; i < masked.length; i++) {
    if (destinations.has(i)) { i = destinations.get(i); continue; }
    if (masked[i] !== '[' || masked[i - 1] === '\\') continue;
    const end = closing(masked, i, '[', ']');
    if (end < 0) continue;
    const label = text.slice(i + 1, end);
    let target;
    let last = end;
    if (masked[end + 1] === '(') {
      last = closing(masked, end + 1, '(', ')');
      if (last < 0) continue;
      target = destination(text.slice(end + 2, last));
    } else if (masked[end + 1] === '[') {
      last = masked.indexOf(']', end + 2);
      if (last < 0) continue;
      target = refs.get(normalize(text.slice(end + 2, last) || label));
    } else if (masked[end + 1] !== ':') target = refs.get(normalize(label));
    if (target !== undefined) {
      found.push({ offset: i, target, image: masked[i - 1] === '!' });
      destinations.set(end, last);
    }
  }
  for (const match of masked.matchAll(/<(a|img)\b[^>]*?\b(href|src)=["']([^"']+)["'][^>]*>/gi))
    found.push({ offset: match.index, target: match[3], image: match[1].toLowerCase() === 'img' });
  found.sort((a, b) => a.offset - b.offset);
  let line = 1;
  let previous = 0;
  for (const link of found) {
    line += text.slice(previous, link.offset).split('\n').length - 1;
    link.line = line;
    previous = link.offset;
  }
  return found;
}

export function checkDocuments(root, files) {
  const known = new Set(files);
  const documents = files.filter(prose).sort();
  const content = new Map(documents.map(file => [file,
    withoutCode(fs.readFileSync(path.join(root, file), 'utf8'))]));
  const headings = new Map(documents.map(file => [file, anchors(content.get(file))]));
  const edges = new Map(documents.map(file => [file, new Set()]));
  const directories = new Set();
  const readmes = new Map();
  for (const file of files) {
    for (let dir = path.posix.dirname(file); dir !== '.'; dir = path.posix.dirname(dir))
      directories.add(dir);
    if (/^readme(?:\.md|\.txt)?$/i.test(path.basename(file)))
      readmes.set(path.posix.dirname(file), file);
  }
  const problems = [];
  let count = 0;
  for (const file of documents) {
    for (const link of links(content.get(file))) {
      count++;
      if (/^[a-z][a-z0-9+.-]*:/i.test(link.target) || link.target.startsWith('//')) continue;
      const at = `${file}:${link.line}`;
      let destinationPath;
      let fragment;
      try {
        const hash = link.target.indexOf('#');
        destinationPath = decodeURIComponent((hash < 0 ? link.target : link.target.slice(0, hash)).split('?')[0]);
        fragment = hash < 0 ? '' : decodeURIComponent(link.target.slice(hash + 1));
      } catch {
        problems.push(`${at}: invalid URL encoding ${link.target}`);
        continue;
      }
      let target = destinationPath ? path.posix.normalize(path.posix.join(path.posix.dirname(file), destinationPath)) : file;
      target = target.replace(/\/$/, '') || '.';
      if (path.posix.isAbsolute(destinationPath) || target === '..' || target.startsWith('../')) {
        problems.push(`${at}: path outside repository ${link.target}`);
        continue;
      }
      if (directories.has(target) || target === '.') target = readmes.get(target) ?? target;
      if ((!known.has(target) && !directories.has(target) && target !== '.') ||
          !fs.existsSync(path.join(root, target))) {
        problems.push(`${at}: missing repository path ${link.target}`);
        continue;
      }
      if (headings.has(target)) {
        if (fragment && !headings.get(target).has(fragment))
          problems.push(`${at}: missing anchor ${link.target}`);
        if (!link.image && !link.definition) edges.get(file).add(target);
      }
    }
  }
  const reached = new Set();
  const queue = ['README.md'];
  for (let i = 0; i < queue.length; i++) {
    const file = queue[i];
    if (reached.has(file) || !edges.has(file)) continue;
    reached.add(file);
    queue.push(...edges.get(file));
  }
  for (const file of documents) if (!reached.has(file)) problems.push(`${file}: unreachable from README.md`);
  return { files: documents.length, links: count, reachable: reached.size, problems };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const files = [...new Set(execFileSync('git', ['ls-files', '-z', '--cached', '--others', '--exclude-standard'],
    { encoding: 'utf8' }).split('\0').filter(Boolean))];
  const result = checkDocuments(process.cwd(), files);
  console.log(JSON.stringify(result, null, 2));
  if (result.problems.length) process.exitCode = 1;
}
