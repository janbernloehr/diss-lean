#!/usr/bin/env bash
# Focused checks using immutable compiled dependencies from a pinned reference.
# Set ELAN_HOME/PATH to the repository's Lean 4.33.1 installation first.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
reference="${DISS_LEAN_REFERENCE_CHECKOUT:?Set DISS_LEAN_REFERENCE_CHECKOUT to the pinned, prebuilt reference checkout}"
build_root="$project_dir/.lake/build/lib/lean"
# Replace a directory symlink by a private directory of read-only imports
# before compiling a new shared module into that namespace.
ensure_private_dir() {
  local target="$build_root/$1"
  if [[ -L "$target" ]]; then
    local backing
    backing="$(readlink -f -- "$target")"
    rm -- "$target"
    mkdir -p "$target"
    for imported_entry in "$backing"/*; do
      ln -s "$imported_entry" "$target/${imported_entry##*/}"
    done
  else
    mkdir -p "$target"
  fi
}
ensure_private_dir NLS/KdV
ensure_private_dir NLS/Articles/KdVEstimates
ensure_private_dir NLS/FunctionalAnalysis
ensure_private_dir NLS/SequenceSpaces
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
modules=(NLS/FunctionalAnalysis/TwoDimensionalDeterminant NLS/SequenceSpaces/WeightedInsertion NLS/SequenceSpaces/PositiveFourierTail NLS/SequenceSpaces/ReciprocalSquareTail NLS/KdV/FreeHill NLS/KdV/HillComplement NLS/KdV/HillReduction NLS/KdV/HillSobolev NLS/KdV/HillPhysical NLS/KdV/HillAnalytic NLS/KdV/HillLocalization NLS/KdV/HillZeroCount NLS/KdV/HillWeightedCoefficients NLS/KdV/HillBilinearSymmetry NLS/KdV/HillSpectralLipschitz NLS/KdV/HillRootSeparation NLS/KdV/HillPeriodOnePotential NLS/KdV/HillGapTail NLS/Articles/KdVEstimates/EstimateAdapter)
for module in "${modules[@]}"; do
  for suffix in olean olean.private olean.server; do
    if [[ -L "$build_root/$module.$suffix" ]]; then
      rm -- "$build_root/$module.$suffix"
    fi
  done
  lean -DautoImplicit=false -DwarningAsError=true -o "$build_root/$module.olean" "$module.lean"
done
lean -DautoImplicit=false -DwarningAsError=true coverage/articles/kdv-estimates/CheckPrivateAxioms.lean
