# Indexed real bands at original and mapped contour crossings

This step proves the band geometry needed for normalized period transfer.
It does not yet prove the contour homotopy or equality of its integrals.

`sourceRealBand_of_between_canonicalCriticalPoints` identifies a real
cut-free point between consecutive canonical critical frequencies with the
specific band between their indexed gaps. Gap membership of the two
critical points and exclusion of the two closed cuts suffice; no global
band selection, spectral cutoff, or open-gap assumption is used.

`sourcePeriodCircle_real_crossings_mem_adjacentBands` proves that each
actual normalized NLS period circle crosses exactly the real bands on the
two sides of its indexed gap. The actual circle encloses its own segment
and separates every other segment. Complete real endpoint order fixes both
crossings, including at collapsed gaps.

`HillHminusOneOriginalContourBands.lean` derives quadratic energy bounds
from the existing uniform square-root critical confinement. These separate
the original circle crossings from their own and neighboring actual critical
levels, for every positive index. An actual common rough-open neighborhood
is constructed before all real inputs and indices.

The positive real shifted-square coordinate preserves these inequalities.
Crossings between positive critical energies lie in the specific intervening
NLS band; a crossing below the first critical energy lies in band zero.
The central case uses the actual even real canonical critical frequency zero,
rather than introducing an extra energy critical point.

`hillHminus_original_crossing_mem_adjacentBands` combines the inequalities
with canonical root-domain membership. The left and right original contour
crossings map to bands `k-1` and `k`, respectively.

`exists_hillHminus_original_crossing_bands` applies this to any verified
actual earlier all-contour period data and any applicable real canonical
chart through zero with positive real shift. It constructs one complex open
neighborhood, inside both source domains, before all real rough inputs and
all positive indices. The exact indexed-band conclusions hold for both
original crossings. Critical-label agreement, critical confinement and
canonical root-domain coverage are all supplied by previously proved actual
results. No band identification is assumed.

The next step is to construct the homotopy between the shifted NLS-mapped
loop and the original squared frequency circle inside the canonical root
domain. Their matching adjacent bands and compatible root on the original
loop are now proved. Actual normalized period equality must still be derived
before using the period inverse to identify the coefficient vector with its
normalized column. The physical frequency formula and all main theorem rows
remain open.

Validation uses 419 unchanged previously checked modules, strict incremental
compilation of these two new modules, and a new combined transitive audit of
all 421 selected modules. It does not assert a repeated full 421-module build.
