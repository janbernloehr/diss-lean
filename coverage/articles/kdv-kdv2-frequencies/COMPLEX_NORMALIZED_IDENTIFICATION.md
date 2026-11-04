# Actual normalized-family identification on a complex rough-input ball

The actual Miura numerator now agrees with the constructed weighted normalized
family for every complex potential in one ball around zero, every positive
index and every complex energy. The ball is the same ball obtained for the
real-input identification. This does not provide a global neighborhood of
all real rough inputs or prove the physical frequency formulas.

`PeriodOneRealFormIdentity.lean` proves the actual physical conjugation is
additive, antilinear and continuous in the rough-potential norm. Its real and
imaginary parts are fixed by physical conjugation and reconstruct every
complex rough potential. Their continuity and zero values satisfy the
hypotheses of the existing connected real-form identity theorem. Agreement
of analytic functions on the physical real slice therefore gives agreement
on any connected open source domain containing zero. The identity principle
is instantiated from proved physical geometry, not assumed for an arbitrary
real subset.

The three generic identity modules `RealLineIdentity.lean`,
`RealFormIdentity.lean` and `ContinuousRealFormIdentity.lean` are reused
unchanged from the canonical dissertation base. They are strictly recompiled
and explicitly included in the selected audit. The check order places these
helpers before their consumers.

`exists_hillHminus_complex_normalized_family_identification` applies physical
real-form uniqueness for each energy and positive numerator index. The actual
Miura numerator and the constructed normalized numerator are both analytic in
the complex rough potential, and their equality on the physical real slice was
already proved using actual periods and genuine Hilbert coefficients. The
result retains the actual normalized NLS data, source membership, joint
complex numerator analyticity and the same common ball before all indices.

`exists_hillHminus_actual_complex_twoWeighted_normalized_identification`
supplies the verified two-weighted construction itself. Both actual charts,
the original period data, normalized NLS data, analytic inverse families,
free inverse values, uniform inverse norm bounds `≤ 2` and exact squared-index
weighted compatibility are retained. The actual numerator equality now holds
for all complex inputs in that ball and all energies, including critical and
central values. This provides an analytic inverse-column representation;
it does not assert a separate unproved global canonical residue labeling.

The next work is to transfer the weighted moment and series results to the
actual family and address the article's global/arbitrary-base source domains,
canonical leading scalar, sharp estimates, physical frequency formula(69),
action descent and Birkhoff/PDE identifications. All main theorem rows remain
open.

Validation reuses 425 unchanged previously checked modules. It strictly
compiles the three unchanged canonical identity helpers and the two new
modules, then runs a fresh combined transitive audit of all 430 selected
modules. This is not a repeated full 430-module build. The shell and audit
selections share the actual dependency order; compilation evidence comprises
the prior 425-module checks and these five incremental checks. Source hashes,
private fresh outputs, seven provenance records and canonical main are verified.
