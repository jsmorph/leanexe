# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Downloads the Oakland RCV corpus that `manifest.json` lists and verifies every file.

The files are Alameda County's RCV detailed reports, D. Otis's standardized CVRs from Harvard
Dataverse, and the Registrar's 2022 presentation on the District 4 error.  Each goes to its
manifest path under the data directory, `tmp/rcv-data` by default.  A file already present with the
manifest's size and SHA-256 is kept.  Any other file is downloaded again, one request at a time with
a pause between requests, and replaces the old file only if its size and SHA-256 match.  A mismatched
download stays beside its target with the suffix `.mismatch`, and the script prints the expected and
the received size and digest.  The script exits with status 1 if any file is missing or mismatched.
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
USER_AGENT = "leanexe tests/rcv/fetch.py (Python urllib)"
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


def entries(manifest, cvr):
    for contest in manifest["contests"]:
        yield contest["key"], contest["report"]
        if cvr and "cvr" in contest:
            yield contest["key"], contest["cvr"]
    for doc in manifest["documents"]:
        yield doc["title"], doc


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("data", nargs="?", default="tmp/rcv-data", help="data directory (default tmp/rcv-data)")
    ap.add_argument("--no-cvr", action="store_true", help="skip the CVR files")
    args = ap.parse_args()
    data = Path(args.data)
    manifest = json.loads((HERE / "manifest.json").read_text())
    kept = fetched = 0
    failures = []
    for label, entry in entries(manifest, not args.no_cvr):
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
            note = " (preliminary report)" if entry.get("preliminary") else ""
            failures.append(f"{entry['path']} ({label}){note}: expected size {expected[0]} sha256 {expected[1]}, "
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
