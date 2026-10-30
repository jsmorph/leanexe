import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import test from 'node:test';
import { checkDocuments } from './check-doc-links.mjs';

function check(t, contents, extra = {}) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'leanexe-doc-links-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  for (const [file, text] of Object.entries({ ...contents, ...extra })) {
    fs.mkdirSync(path.dirname(path.join(root, file)), { recursive: true });
    fs.writeFileSync(path.join(root, file), text);
  }
  return checkDocuments(root, Object.keys(contents));
}

test('follows inline, reference, HTML, directory, and plain-text README links', t => {
  const result = check(t, {
    'README.md': '[Guide](guide/README.md#use)\n[Archive][record]\n[record]:\n <record.md>\n<a href="extra.md">Details</a>\n',
    'guide/README.md': '# Guide\n## Use\n[Vectors](../vectors/)\n',
    'vectors/Readme.txt': 'Vector file formats.\n',
    'record.md': '# Record\n',
    'extra.md': '# Details\n',
  });
  assert.equal(result.reachable, 5);
  assert.deepEqual(result.problems, []);
});

test('reports missing paths, local artifacts, and missing anchors with lines', t => {
  const result = check(t, {
    'README.md': '# Start\n[Missing](gone.md)\n[Artifact](build/local.pdf)\n[Section](#gone)\n',
  }, { 'build/local.pdf': 'local output' });
  assert.deepEqual(result.problems, [
    'README.md:2: missing repository path gone.md',
    'README.md:3: missing repository path build/local.pdf',
    'README.md:4: missing anchor #gone',
  ]);
});

test('directory browsing, images, and unused definitions leave prose unreachable', t => {
  const result = check(t, {
    'README.md': '[Directory](notes)\n![Image](image.md)\n[unused]: unused.md\n',
    'notes/page.md': '# Notes\n',
    'image.md': '# Image target\n',
    'unused.md': '# Unused definition\n',
  });
  assert.equal(result.reachable, 1);
  assert.equal(result.problems.filter(p => p.includes('unreachable')).length, 3);
});

test('detects an isolated cycle and follows an incoming link into it', t => {
  const contents = {
    'README.md': '# Start\n',
    'a.md': '[B](b.md)\n',
    'b.md': '[A](a.md)\n',
  };
  assert.equal(check(t, contents).problems.length, 2);
  assert.deepEqual(check(t, { ...contents, 'README.md': '[A](a.md)\n' }).problems, []);
});

test('ignores fenced code, inline code, and comments and checks nested destinations', t => {
  const result = check(t, {
    'README.md': '# Start\n```md\n[Example](absent.md)\n```\n~~~\n[Example](absent.md)\n~~~\n`[Example](absent.md)`\n<!-- [Example](absent.md) -->\n[Guide](guide(1).md "Guide")\n',
    'guide(1).md': '# Guide\n',
  });
  assert.deepEqual(result.problems, []);
});

test('checks duplicate headings, setext headings, encoded paths, and explicit IDs', t => {
  const result = check(t, {
    'README.md': '[One](guide%20name.md#use)\n[Two](guide%20name.md#use-1)\n[Three](guide%20name.md#details)\n[Four](guide%20name.md#special)\n',
    'guide name.md': '# Guide\n## Use\n## Use\nDetails\n-------\n<a id="special"></a>\n',
  });
  assert.deepEqual(result.problems, []);
});

test('checks linked images and accepts parentheses in quoted link titles', t => {
  const contents = {
    'README.md': '[![Diagram](diagram.svg)](guide.md "A (title")\n',
    'guide.md': '# Guide\n',
  };
  const missing = check(t, contents);
  assert.equal(missing.reachable, 2);
  assert.deepEqual(missing.problems, ['README.md:1: missing repository path diagram.svg']);
  assert.deepEqual(check(t, { ...contents, 'diagram.svg': '<svg/>' }).problems, []);
});

test('reports malformed encoding and paths outside the repository', t => {
  assert.deepEqual(check(t, { 'README.md': '[Bad](bad%ZZ.md)\n[Outside](../other.md)\n' }).problems, [
    'README.md:1: invalid URL encoding bad%ZZ.md',
    'README.md:2: path outside repository ../other.md',
  ]);
});
