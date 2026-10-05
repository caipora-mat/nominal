#!/usr/bin/env python3
"""Build a source snapshot with fresh project artifacts and cached dependencies."""

from pathlib import Path
import hashlib
import shutil
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parent.parent
    dependencies = root / ".lake/packages"
    if not dependencies.is_dir():
        raise SystemExit("Missing .lake/packages; first follow docs/validation.md setup.")
    snapshot = Path(tempfile.mkdtemp(prefix="nominal-fresh-"))
    for directory in ("Nominal", "Instances", "Examples"):
        shutil.copytree(root / directory, snapshot / directory)
    for filename in ("Nominal.lean", "Instances.lean", "Examples.lean", "lakefile.toml",
                     "lake-manifest.json", "lean-toolchain"):
        shutil.copy2(root / filename, snapshot / filename)
    fingerprint = hashlib.sha256()
    for source in sorted(path for path in snapshot.rglob("*") if path.is_file()):
        fingerprint.update(str(source.relative_to(snapshot)).encode() + b"\0")
        fingerprint.update(source.read_bytes() + b"\0")
    (snapshot / ".lake").mkdir()
    (snapshot / ".lake/packages").symlink_to(dependencies, target_is_directory=True)
    print(f"Source snapshot: {snapshot}", flush=True)
    print(f"Source/config SHA-256: {fingerprint.hexdigest()}", flush=True)
    print("Fresh project artifacts; reusing pinned dependency artifacts.", flush=True)
    print("Includes current working-tree sources, including uncommitted examples.", flush=True)
    subprocess.run(["lake", "build", "Nominal", "Instances", "Examples"],
                   cwd=snapshot, check=True)
    subprocess.run(["lake", "env", "lean", "Examples/AxiomAudit.lean"],
                   cwd=snapshot, check=True)


if __name__ == "__main__":
    main()
