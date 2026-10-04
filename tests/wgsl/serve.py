# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Serves the WebGPU test page of tests/wgsl/browser with the kernels and cases that
tests/wgsl/run.sh writes to build/wgsl.

Run tests/wgsl/run.sh once, then `uv run tests/wgsl/serve.py [--host H] [--port P] [--build DIR]`
and open http://127.0.0.1:8000/ in a browser with WebGPU.  Browsers expose WebGPU only to secure
contexts, which include http://127.0.0.1 and http://localhost.  To use a browser on another
machine, forward the port with `ssh -L 8000:127.0.0.1:8000 THIS-HOST` and open the same address
there."""
import argparse
import http.server
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
PAGE = ROOT / 'tests/wgsl/browser'
TYPES = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
         '.wgsl': 'text/plain; charset=utf-8', '.txt': 'text/plain; charset=utf-8'}


def handler(wgsl):
    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            path = self.path.split('?', 1)[0]
            if path in ('/', '/index.html'):
                file = PAGE / 'index.html'
            elif path == '/app.js':
                file = PAGE / 'app.js'
            elif m := re.fullmatch(r'/wgsl/([A-Za-z0-9]+\.wgsl|cases\.txt)', path):
                file = wgsl / m.group(1)
            else:
                file = None
            if file is None or not file.is_file():
                self.send_error(404)
                return
            body = file.read_bytes()
            self.send_response(200)
            self.send_header('Content-Type', TYPES[file.suffix])
            self.send_header('Content-Length', str(len(body)))
            self.send_header('Cache-Control', 'no-store')
            self.end_headers()
            self.wfile.write(body)

    return Handler


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--host', default='127.0.0.1')
    parser.add_argument('--port', type=int, default=8000)
    parser.add_argument('--build', default=str(ROOT / 'build'))
    args = parser.parse_args()
    wgsl = pathlib.Path(args.build) / 'wgsl'
    if not (wgsl / 'cases.txt').is_file():
        sys.exit(f'{wgsl}/cases.txt is missing; run tests/wgsl/run.sh first')
    server = http.server.ThreadingHTTPServer((args.host, args.port), handler(wgsl))
    print(f'WebGPU kernel tests: http://{args.host}:{server.server_address[1]}/', flush=True)
    server.serve_forever()


if __name__ == '__main__':
    main()
