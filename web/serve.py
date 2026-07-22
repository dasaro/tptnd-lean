#!/usr/bin/env python3
"""Minimal local server for the TPTND-Lean certificate checker UI.

Serves the static files in this directory and bridges POST /check to the
Lean `tptnd_check` binary, so the browser talks to the *real* checker.

Usage:  python3 web/serve.py   (from the repo root, after `lake build tptnd_check`)
Then open http://127.0.0.1:8787
"""
import http.server
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(ROOT, "..", ".lake", "build", "bin", "tptnd_check")
PORT = 8787


class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=ROOT, **kwargs)

    def do_POST(self):
        if self.path != "/check":
            self.send_error(404)
            return
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length)
        try:
            r = subprocess.run([BIN], input=body, capture_output=True, timeout=60)
            out = r.stdout.strip()
            if not out:
                out = json.dumps(
                    {"ok": False, "error": "checker produced no output: "
                     + r.stderr.decode(errors="replace")[:400]}
                ).encode()
        except FileNotFoundError:
            out = json.dumps(
                {"ok": False, "error": "tptnd_check binary not found — run "
                 "`lake build tptnd_check` first"}).encode()
        except Exception as e:  # timeout etc.
            out = json.dumps({"ok": False, "error": str(e)}).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(out)))
        self.end_headers()
        self.wfile.write(out)

    def log_message(self, fmt, *args):  # keep the console quiet
        pass


if __name__ == "__main__":
    if not os.path.exists(BIN):
        print(f"warning: {BIN} not found — build it with `lake build tptnd_check`",
              file=sys.stderr)
    print(f"TPTND-Lean checker UI: http://127.0.0.1:{PORT}")
    http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Handler).serve_forever()
