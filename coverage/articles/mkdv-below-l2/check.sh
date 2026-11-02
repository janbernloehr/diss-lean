#!/usr/bin/env bash
# Focused direct-Lean checks using read-only canonical compiled dependencies.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
project_dir="$(cd -- "$script_dir/../../.." && pwd)"
canonical="${CANONICAL_NLS_ROOT:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls}"
export ELAN_HOME="${ELAN_HOME:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/tooling/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/cache/mathlib}"
lean_bin="${LEAN_BIN:-$ELAN_HOME/toolchains/leanprover--lean4---v4.33.1/bin/lean}"
build_root="${MKDV_BUILD_ROOT:-$project_dir/.lake/mkdv-below-l2/lib/lean}"
mkdir -p "$build_root/NLS/Articles/MKdVBelowL2"
# Symlink established namespaces for imports only; all new outputs stay local.
for entry in "$canonical"/.lake/build/lib/lean/NLS/*; do
  name="${entry##*/}"
  if [[ "$name" != Articles && ! -e "$build_root/NLS/$name" ]]; then
    ln -s "$entry" "$build_root/NLS/$name"
  fi
done
export LEAN_PATH="$build_root:$canonical/.lake/build/lib/lean"
for pkg in "$canonical"/.lake/packages/*; do
  if [[ -d "$pkg/.lake/build/lib/lean" ]]; then
    export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
  fi
done
cd "$project_dir"
"$lean_bin" --version
for module in SmoothRenormalization TranslationFourier PhysicalBirkhoff FourthMomentSummability; do
  "$lean_bin" -o "$build_root/NLS/Articles/MKdVBelowL2/$module.olean" \
    "NLS/Articles/MKdVBelowL2/$module.lean"
  printf '%s: checked\n' "$module"
done
"$lean_bin" NLS/Articles/MKdVBelowL2/AxiomAudit.lean
