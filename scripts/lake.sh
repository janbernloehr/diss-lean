#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
local_elan="$project_dir/../../work/tooling/elan"
if [[ -x "$local_elan/bin/lake" ]]; then
  export ELAN_HOME="$local_elan"
  export PATH="$ELAN_HOME/bin:$PATH"
  export MATHLIB_CACHE_DIR="$project_dir/../../work/cache/mathlib"
fi
cd -- "$project_dir"
exec lake "$@"
