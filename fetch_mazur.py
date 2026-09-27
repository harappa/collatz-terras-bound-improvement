#!/usr/bin/env python3
"""Fetch Mazur's natural-density formalization (ProofAtlas, Apache-2.0) and unpack it into vendor/mazur.

L. Mazur, "Natural-density Collatz descent in logarithmic time" (ProofAtlas project
natural-density-log-time-collatz, commit ca3dd0d63920411213403092aecc6946619eb082, Lean v4.30.0-rc2).
Mathlib is not bundled with it (135 files import Mathlib); the lakefile requires Mathlib tag v4.30.0-rc2.
The sources are not redistributed with this bundle.

Verification: the SHA-256 of the whole ZIP, and the SHA-256 of every file listed in the bundled
proofatlas-source-manifest.json. Unpacking uses only the standard library and rejects absolute paths
and parent-directory references.
"""
import hashlib
import json
import sys
import urllib.request
import zipfile
from pathlib import Path

URL = ("https://www.proofatlas.ai/sources/natural-density-log-time-collatz/commits/"
       "ca3dd0d63920411213403092aecc6946619eb082/"
       "natural-density-log-time-collatz-checked-source-ca3dd0d63920.zip")
SHA256 = "5761e6bdad1284275f3a19aa51d8278a68b19cb569c516c20df956e6fac91864"

HERE = Path(__file__).resolve().parent
DEST = HERE / "vendor" / "mazur"
ZIP = HERE / "vendor" / "mazur-ca3dd0d.zip"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    ZIP.parent.mkdir(parents=True, exist_ok=True)
    if not ZIP.exists():
        # ProofAtlas returns HTTP 400 for Python's default User-Agent (Python-urllib/...), so set one explicitly.
        req = urllib.request.Request(URL, headers={"User-Agent": "tao-star-fetch_mazur/1.0"})
        with urllib.request.urlopen(req) as r:
            ZIP.write_bytes(r.read())
    data = ZIP.read_bytes()
    if sha256(data) != SHA256:
        print(f"SHA-256 mismatch: {sha256(data)}", file=sys.stderr)
        return 1
    with zipfile.ZipFile(ZIP) as z:
        for name in z.namelist():
            p = Path(name)
            if p.is_absolute() or ".." in p.parts:
                print(f"illegal path: {name}", file=sys.stderr)
                return 1
        z.extractall(DEST)
    manifest = json.loads((DEST / "proofatlas-source-manifest.json").read_text())
    bad = 0
    for f in manifest["files"]:
        got = "sha256:" + sha256((DEST / f["path"]).read_bytes())
        if got != f["sha256"]:
            print(f"file SHA-256 mismatch: {f['path']}", file=sys.stderr)
            bad += 1
    if bad:
        return 1
    print(f"verified: ZIP and {len(manifest['files'])} files -> {DEST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
