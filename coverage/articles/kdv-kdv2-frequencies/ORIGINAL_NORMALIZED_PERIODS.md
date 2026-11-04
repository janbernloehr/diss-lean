# Actual normalized periods on the original rough Hill contours

The actual descended Miura numerator now has its proved Kronecker periods on
the original positive frequency circles. One constructed normalized NLS data
set and one norm ball precede all real rough inputs and positive mode pairs.
This is a necessary spectral dependency; no main article row is closed.

`ShiftedSquaredCircleBandHomotopy.lean` proves that the affine homotopy of two
shifted squared positive-frequency circles stays nonreal or in their two
matched real crossing intervals. Its imaginary part is the common sine
factor times a positive convex combination. At the real crossings, convexity
of the matched intervals controls the deformation. The resulting equality
concerns actual smooth loop integrals of any analytic function on that domain.

`HillHminusOneEnergyBands.lean` defines the actual canonical energy bands from
the squared real NLS endpoints and the chart's real energy shift. The central
right frequency endpoint is nonnegative, and complete endpoint order gives
the same property at all nonnegative indices. Every real energy in one of
these bands lies in the actual canonical root domain. Both original and NLS
crossing frequencies map into the appropriate energy intervals by positive
square order.

`hillHminus_original_mapped_energy_integral_eq` applies the homotopy to the
actual canonical energy-root domain. Every nonreal energy belongs to that
domain; the two matched real bands belong to it as well. Thus the proof does
not require the original source continuation domain to contain the whole
homotopy. The previously proved canonical/original root agreement is used
only on the original contour boundary.

`hillHminusMiuraEnergyPsi_original_period` applies this equality to the actual
entire Miura numerator divided by the analytic nonzero canonical energy root.
The actual normalized mapped NLS period, the literal shifted-square integral
pullback with Jacobian `2*z`, and boundary root agreement give the raw original
period `2*pi*(if k=n then 1 else 0)`. No period value or Hilbert-membership
uniqueness premise is assumed.

`exists_hillHminus_actual_original_periods` starts from the actual normalized
NLS data and the same real Miura chart, and constructs a single norm ball
inside both source domains. It retains the positive real shift, real-type
source property, actual `SourceTheorem12_1Data`, source membership and joint
complex energy/source analyticity of the numerator. The literal original
Kronecker periods hold for every physically real input in that ball and every
positive numerator/contour pair. All indices come after the data and the ball.
Finite head, first-mode central geometry and collapsed gaps are included.

The period identities in this theorem are on the physical real slice. Joint
complex analyticity of the numerator is retained, but this theorem does not
assert normalized periods at all complex inputs or source analyticity of the
residue coefficient vector. Identification with the constructed weighted
normalized family still requires applying the verified period inverse to the
previously proved genuine old-basis Hilbert representation. Physical frequency
formula(69), action descent, coherent global charts and all main theorem rows
remain open.

Validation reuses the unchanged 421 previously checked modules, compiles the
three new modules strictly in dependency order, and runs a fresh combined
transitive axiom audit of all 424 selected modules. It does not claim a repeated
full 424-module build. Source hashes, exact ordered selections, private fresh
outputs, seven provenance records and unchanged canonical main are checked.
