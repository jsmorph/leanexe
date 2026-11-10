# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Downloads the Maine RCV corpus that `manifest.json` lists and verifies every file.

The files are the Maine Secretary of State's RCV summary reports, first-choice results, and cast
vote record spreadsheets, and the 2026 primary candidate and withdrawal lists.  Each goes to its
manifest path under the data directory, `tmp/rcv-maine-data` by default.  A file already present
with the manifest's size and SHA-256 is kept.  Any other file is downloaded again, one request at a
time with a pause between requests, and replaces the old file only if its size and SHA-256 match.  A
mismatched download stays beside its target with the suffix `.mismatch`, and the script prints the
expected and the received size and digest.  On 2026-11-10 www.maine.gov answered this script's
requests with HTTP 403, while a web browser received the files.  A file saved from a browser at its
manifest path passes the check like a downloaded one.  The script exits with status 1 if any file is
missing or mismatched.
"""

import argparse
import hashlib
import json
import os
import sys
import time
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
USER_AGENT = "leanexe tests/rcv/maine/fetch.py (Python urllib)"
PAUSE = 2.0


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while chunk := f.read(1 << 20):
            h.update(chunk)
    return os.path.getsize(path), h.hexdigest()


def download(url, path):
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=300) as response, open(path, "wb") as f:
        while chunk := response.read(1 << 20):
            f.write(chunk)


def entries(manifest):
    for contest in manifest["contests"]:
        for part in ("report", "first_choice"):
            if part in contest:
                yield contest["key"], contest[part]
        for cvr in contest.get("cvr", []):
            yield contest["key"], cvr
    for doc in manifest["documents"]:
        yield doc["title"], doc


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("data", nargs="?", default="tmp/rcv-maine-data",
                    help="data directory (default tmp/rcv-maine-data)")
    args = ap.parse_args()
    data = Path(args.data)
    manifest = json.loads((HERE / "manifest.json").read_text())
    kept = fetched = 0
    failures = []
    for label, entry in entries(manifest):
        target = data / entry["path"]
        expected = (entry["size"], entry["sha256"])
        if target.exists() and digest(target) == expected:
            kept += 1
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        partial = target.with_name(target.name + ".part")
        try:
            download(entry["url"], partial)
        except OSError as e:
            failures.append(f"{entry['path']} ({label}): {entry['url']}: {e}")
            partial.unlink(missing_ok=True)
            time.sleep(PAUSE)
            continue
        time.sleep(PAUSE)
        received = digest(partial)
        if received != expected:
            partial.replace(target.with_name(target.name + ".mismatch"))
            failures.append(f"{entry['path']} ({label}): expected size {expected[0]} sha256 {expected[1]}, "
                            f"received size {received[0]} sha256 {received[1]}")
            continue
        partial.replace(target)
        fetched += 1
    for failure in failures:
        print(failure, file=sys.stderr)
    print(f"{kept} files kept, {fetched} downloaded, {len(failures)} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
