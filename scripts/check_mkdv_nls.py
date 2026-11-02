#!/usr/bin/env python3
"""Compile article changes using read-only cached imports and private outputs.

Pass --imports-from the pinned canonical checkout. This never invokes lake or
writes a dependency artifact. It is a focused check, not a fresh full build.
"""
from pathlib import Path
import argparse
from contextlib import nullcontext
import fcntl
import os
import shutil
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--imports-from", type=Path, required=True)
parser.add_argument("--lean", default=shutil.which("lean"))
parser.add_argument("--full-audit", action="store_true")
parser.add_argument("--module-only", action="append", metavar="PATH",
                    help="Check only this module, without aggregate compilation or audit (repeatable).")
args = parser.parse_args()
if not args.lean:
    parser.error("Set PATH to the pinned toolchain or pass --lean.")
root = Path(__file__).resolve().parent.parent
canonical = args.imports_from.resolve()
build = root / ".lake/build"
lib = build / "lib/lean"
logs = build / "article-logs/mkdv-nls-hierarchies"
logs.mkdir(parents=True, exist_ok=True)
version = subprocess.check_output([args.lean, "--version"], text=True).strip()
if not version.startswith("Lean (version 4.33.1,"):
    parser.error(f"Expected pinned Lean 4.33.1, got {version}")
modules = [
    "NLS/ZakharovShabat/SobolevHierarchySymmetries.lean",
    "NLS/MKdV/HierarchyRestriction.lean",
    "NLS/Articles/MKdVNLSHierarchies/InitialChecks.lean",
    "NLS.lean",
]
if args.module_only:
    if args.full_audit:
        parser.error("--module-only cannot be combined with --full-audit")
    modules = args.module_only
targets = {Path(module).with_suffix(".olean") for module in modules}

def overlay(source, target, prefix=Path()):
    if target.is_symlink():
        target.unlink()
    target.mkdir(parents=True, exist_ok=True)
    for item in source.iterdir():
        relative = prefix / item.name
        destination = target / item.name
        if relative in targets:
            if destination.is_symlink():
                destination.unlink()
            continue
        if item.is_dir() and any(relative in module.parents for module in targets):
            overlay(item, destination, relative)
        elif not destination.exists() and not destination.is_symlink():
            destination.symlink_to(item, target_is_directory=item.is_dir())

overlay(canonical / ".lake/build/lib/lean", lib)
paths = [lib]
paths.extend(sorted((canonical / ".lake/packages").glob("*/.lake/build/lib/lean")))
env = dict(os.environ, LEAN_PATH=":".join(map(str, paths)))

def run(source, output=None):
    command = [args.lean, "-DautoImplicit=false", "-DwarningAsError=true", "--root", str(root)]
    if output:
        if output.is_symlink() or not output.resolve().is_relative_to(build.resolve()):
            raise RuntimeError(f"Refusing to write through cached dependency link: {output}")
        output.parent.mkdir(parents=True, exist_ok=True)
        command.extend(["-o", str(output)])
    command.append(str(root / source))
    print(f"Checking {source}", flush=True)
    result = subprocess.run(command, cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (Path(source).stem + ".log")).write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode:
        sys.exit(result.returncode)

# Serialize aggregate compilation and larger validation with the article lock.
with (nullcontext(None) if args.module_only else
      open("/tmp/diss-lean-article-build.lock", "a")) as lock:
    if lock is not None:
        print("Waiting for shared article build lock", flush=True)
        fcntl.flock(lock, fcntl.LOCK_EX)
    for module in modules:
        run(module, lib / Path(module).with_suffix(".olean"))
    if not args.module_only:
        run("scripts/CheckMKdVNLSHierarchiesAxioms.lean")
    if args.full_audit:
        run("scripts/CheckAxioms.lean")
    print("Requested compilation and axiom checks passed.", flush=True)
