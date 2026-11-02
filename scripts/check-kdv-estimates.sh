#!/usr/bin/env bash
# Focused checks using immutable compiled dependencies from a pinned reference.
# Set ELAN_HOME/PATH to the repository's Lean 4.33.1 installation first.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
reference="${DISS_LEAN_REFERENCE_CHECKOUT:?Set DISS_LEAN_REFERENCE_CHECKOUT to the pinned, prebuilt reference checkout}"
build_root="$project_dir/.lake/build/lib/lean"
mkdir -p "$build_root/NLS/KdV" "$build_root/NLS/Articles/KdVEstimates"
for imported_entry in "$reference"/.lake/build/lib/lean/NLS/*; do
  target="$build_root/NLS/${imported_entry##*/}"
  if [[ ! -e "$target" && ! -L "$target" ]]; then
    ln -s "$imported_entry" "$target"
  fi
done
export LEAN_PATH="$build_root:$reference/.lake/build/lib/lean"
for package_lib in "$reference"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$package_lib"
done
cd "$project_dir"
lean --version
modules=(NLS/KdV/FreeHill NLS/Articles/KdVEstimates/EstimateAdapter)
for module in "${modules[@]}"; do
  lean -DautoImplicit=false -o "$build_root/$module.olean" "$module.lean"
done
lean -DautoImplicit=false coverage/articles/kdv-estimates/CheckPrivateAxioms.lean
