# /// script
# requires-python = ">=3.12"
# dependencies = ["transformers==5.18.0"]
# ///
"""Serves the two WebGPU pages from one server: /kernels/, which runs the cases of
tests/wgsl/Cases.lean on the browser's WebGPU, and /gpt2/, which runs GPT-2 124M in binary32 with
each kernel on WebGPU or in gpt32.wasm on the CPU.

Run with `uv run tests/web/serve.py [--host H] [--port P]` (default 127.0.0.1:8000).  The kernel
page needs the kernels and cases that tests/wgsl/run.sh writes to build/wgsl.  The GPT-2 page needs
the weight files that tests/gpt32/generate.py writes to build/gpt2-32; the server emits the GPT-2
kernels, gpt32.wasm, and the sampler's module gpt.wasm, and builds the program printer
`gpt32-lines`, when they are missing.  The GPT-2 page gets each step's host commands from
`gpt32-lines`, which prints the programs of Project/Gpt32/Program.lean, and the server tokenizes
and decodes with the pinned GPT-2 tokenizer.  Browsers expose WebGPU only to secure contexts,
which include http://127.0.0.1 and http://localhost; a browser on another machine needs an SSH
tunnel (`ssh -L 8000:127.0.0.1:8000 THIS-HOST`) or, in Chrome, the address in
chrome://flags/#unsafely-treat-insecure-origin-as-secure."""
import argparse
import http.server
import json
import os
import pathlib
import re
import subprocess
import threading
import urllib.parse

from transformers import GPT2TokenizerFast

ROOT = pathlib.Path(__file__).resolve().parents[2]
INDEX = ROOT / 'tests/web/index.html'
KERNEL_PAGE = ROOT / 'tests/wgsl/browser'
GPT_PAGE = ROOT / 'tests/gpt32/browser'
WEIGHTS = ROOT / 'build/gpt2-32'
WGSL = ROOT / 'build/wgsl'
WASM = ROOT / 'build/gpt32/gpt32.wasm'
SAMPLER = ROOT / 'build/gpt/gpt.wasm'
LINES = ROOT / '.lake/build/bin/gpt32-lines'
REPO = 'openai-community/gpt2'
REVISION = '607a30d783dfa663caf39e06633721c8d4cfcd7e'
SHAPE = ['12', '3072', '12565', '50257', '12']
KERNELS = ['embed', 'layerNorm', 'linear', 'append', 'scores', 'headMax', 'headSum', 'probs',
           'mix', 'add', 'gelu', 'logits']
TYPES = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
         '.wgsl': 'text/plain; charset=utf-8', '.txt': 'text/plain; charset=utf-8',
         '.wasm': 'application/wasm', '.bin': 'application/octet-stream',
         '.json': 'application/json'}


def leanrun(*args):
    subprocess.run([str(ROOT / 'tools/leanrun'), '--timeout', '30m', *args], cwd=ROOT, check=True)


def prepare():
    for k in KERNELS:
        if not (WGSL / f'{k}.wgsl').is_file():
            WGSL.mkdir(parents=True, exist_ok=True)
            leanrun('lake', 'env', 'lean', '--run', 'Project/WGSL/Emit.lean', 'Project.Gpt32.Specs',
                    f'Project.Gpt32.{k}Kernel', str(WGSL / f'{k}.wgsl'))
    for path, module in [(WASM, 'Project.Gpt32.Module:Project.Gpt32.gpt32.module'),
                         (SAMPLER, 'Project.Gpt.Module:Project.Gpt.gpt.module')]:
        if not path.is_file():
            path.parent.mkdir(parents=True, exist_ok=True)
            leanrun('lake', 'env', 'lean', '--run', 'Project/Pipeline/Emit.lean',
                    *module.split(':'), str(path))
    if not LINES.is_file():
        leanrun('lake', 'build', 'gpt32-lines')
    if not (WGSL / 'cases.txt').is_file():
        print(f'{WGSL}/cases.txt is missing; the kernel page needs tests/wgsl/run.sh', flush=True)
    if not (WEIGHTS / 'revision').is_file():
        print(f'{WEIGHTS} has no weights; the GPT-2 page needs '
              '`uv run tests/gpt32/generate.py --tokens 1`', flush=True)


class Lines:
    """The `gpt32-lines` process, one request at a time."""

    def __init__(self):
        self.proc = subprocess.Popen([str(LINES), *SHAPE], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True)
        self.lock = threading.Lock()

    def ask(self, request):
        with self.lock:
            self.proc.stdin.write(request + '\n')
            self.proc.stdin.flush()
            lines = []
            while True:
                line = self.proc.stdout.readline()
                if line == '':
                    raise RuntimeError('gpt32-lines exited')
                line = line.rstrip('\n')
                if line == 'end':
                    return lines
                if line.startswith('error '):
                    raise ValueError(line[6:])
                lines.append(line)


def handler(lines, tokenizer):
    class Handler(http.server.BaseHTTPRequestHandler):
        def send(self, status, body, content_type):
            self.send_response(status)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            self.wfile.write(body)

        def send_json(self, value):
            self.send(200, json.dumps(value).encode(), TYPES['.json'])

        def send_file(self, file):
            if not file.is_file():
                self.send_error(404)
                return
            self.send_response(200)
            self.send_header('Content-Type', TYPES[file.suffix])
            self.send_header('Content-Length', str(file.stat().st_size))
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            with file.open('rb') as f:
                while chunk := f.read(1 << 20):
                    self.wfile.write(chunk)

        def redirect(self, location):
            self.send_response(301)
            self.send_header('Location', location)
            self.send_header('Content-Length', '0')
            self.end_headers()

        def kernels(self, path):
            if path in ('', 'index.html'):
                self.send_file(KERNEL_PAGE / 'index.html')
            elif path == 'app.js':
                self.send_file(KERNEL_PAGE / 'app.js')
            elif m := re.fullmatch(r'wgsl/([A-Za-z0-9]+\.wgsl|cases\.txt)', path):
                self.send_file(WGSL / m.group(1))
            else:
                self.send_error(404)

        def gpt2(self, path, query):
            if path in ('', 'index.html'):
                self.send_file(GPT_PAGE / 'index.html')
            elif path in ('app.js', 'hosts.js'):
                self.send_file(GPT_PAGE / path)
            elif m := re.fullmatch(r'wgsl/([A-Za-z0-9]+)\.wgsl', path):
                self.send_file(WGSL / f'{m.group(1)}.wgsl')
            elif path == 'gpt32.wasm':
                self.send_file(WASM)
            elif path == 'sampler.wasm':
                self.send_file(SAMPLER)
            elif m := re.fullmatch(r'weights/([A-Za-z0-9_]+)\.bin', path):
                self.send_file(WEIGHTS / f'{m.group(1)}.bin')
            elif path == 'api/tokenize':
                self.send_json(tokenizer(query.get('text', [''])[0])['input_ids'])
            elif path == 'api/decode':
                text = query.get('ids', [''])[0]
                self.send_json(tokenizer.decode([int(t) for t in text.split(',')] if text else []))
            elif path == 'api/setup':
                self.send_json(lines.ask('setup weights'))
            elif path == 'api/step':
                self.send_json(lines.ask(f'step {int(query["token"][0])} {int(query["p"][0])}'))
            else:
                self.send_error(404)

        def do_GET(self):
            url = urllib.parse.urlsplit(self.path)
            query = urllib.parse.parse_qs(url.query)
            path = url.path
            try:
                if path in ('/', '/index.html'):
                    self.send_file(INDEX)
                elif path in ('/kernels', '/gpt2'):
                    self.redirect(path + '/')
                elif path.startswith('/kernels/'):
                    self.kernels(path[len('/kernels/'):])
                elif path.startswith('/gpt2/'):
                    self.gpt2(path[len('/gpt2/'):], query)
                else:
                    self.send_error(404)
            except (KeyError, ValueError) as e:
                self.send(400, str(e).encode(), 'text/plain; charset=utf-8')

        def log_message(self, format, *args):
            if not self.path.startswith('/gpt2/api/step'):
                super().log_message(format, *args)

    return Handler


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--host', default='127.0.0.1')
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args()
    prepare()
    tokenizer = GPT2TokenizerFast.from_pretrained(REPO, revision=REVISION)
    server = http.server.ThreadingHTTPServer((args.host, args.port), handler(Lines(), tokenizer))
    print(f'WebGPU pages: http://{args.host}:{server.server_address[1]}/', flush=True)
    server.serve_forever()


if __name__ == '__main__':
    os.environ.setdefault('TOKENIZERS_PARALLELISM', 'false')
    main()
