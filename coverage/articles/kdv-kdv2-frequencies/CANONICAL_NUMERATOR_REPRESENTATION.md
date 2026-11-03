# Full entire canonical Hilbert representation of the actual numerator

Every article main theorem remains OPEN. This milestone proves genuine
Hilbert coefficient membership and a full entire representation of the
actual NLS-derived energy numerator at real-type rough Miura chart inputs.
Identifying its canonical critical coordinates and periods with the earlier
local weighted normalized family is still required.

## Derived exterior decay and actual critical interpolation

`SourcePsiCriticalQuotientExterior.lean` uses the exact complete canonical
critical product for the actual NLS discriminant derivative. The ratio of
two free-normalized products is bounded by four on the large separated
exterior. Restoring the deleted numerator factor gives

    |phi_n(z)/Delta_NLS'(z)| <= 8/|z|.

The threshold may depend on the fixed source and deleted-root vector.
The bound is uniform in the spectral point once it is large and separated
from the free lattice. It also proves that the actual denominator is
nonzero there. Large half-integer circles then have quotient bound 8/R;
the actual outer Cauchy error tends uniformly to zero for bounded families
of evaluation points.

`SourcePsiCriticalInterpolation.lean` selects exactly the actual canonical
critical indices -N,...,N inside sufficiently large half-integer circles.
At a real-type source these critical points are all simple, including the
central finite cluster and all closed-gap inputs. The generic finite-pole
Cauchy theorem gives the exact error formula with actual coefficients

    r_m = phi_n(beta_m)/Delta_NLS''(beta_m).

The derived outer error proves uniform symmetric interpolation limits on
every bounded evaluation set away from derivative zeros. Neither the
residues nor the interpolation formula are assumed.

## Actual residue bounds and absolute summability

`SimplePoleCircleResidue.lean` proves that the literal quotient circle
integral around one simple zero equals 2*pi*i times its derivative-defined
residue. An actual circle bound M implies residue norm <= radius*M.

For every sufficiently distant signed critical index m, its actual root is
the sole derivative zero in the closed free disc of radius pi/4. That
circle is free-lattice separated. The derived quotient bound therefore
gives

    |r_m| <= 4/|m|.

`SourcePsiCriticalResidueBounds.lean` combines this with the finite head
and the verified punctured reciprocal lattice to prove genuine signed
l2 residue membership. `SourcePsiCriticalAbsoluteInterpolation.lean`
proves that the reciprocal critical kernel also belongs to l2 at every
fixed spectral evaluation point. Holder pairing gives absolute
summability of the interpolation terms. The proved symmetric limits then
give the ordinary sum identity

    phi_n(z)/Delta_NLS'(z) = sum_m r_m/(z-beta_m),

at every noncritical z. This applies to every finite-exponent deleted-root
vector and real-type source in the theorem's stated domains.

## The exact energy Hilbert coefficients

`HillHminusOneMiuraResidueHilbert.lean` constructs the actual bounded
positive multiplier beta_j/(pi*j), using the canonical critical-displacement
norm. Acting on the actual signed residue sequence minus its reflection
gives a genuine Coeff 2 vector a. It vanishes at nonpositive indices and
satisfies, for every positive j,

    A_j = 2 beta_j (r_j-r_(-j)),
    a_j = A_j/(2*pi*j).

Here A_j is the actual energy principal coefficient
Psi_n(mu_j)/Delta_H''(mu_j), and mu_j=beta_j^2-C.energyShift. The exact
2*pi*j basis normalization is retained. A norm bound and an actual
normalized-data existence theorem on one common rough-open neighborhood
are proved. There is no sequence-constructor fallback or postulated
coefficient membership.

## Absolutely convergent energy principal series

`HillHminusOneMiuraEnergyPrincipalSeries.lean` combines the actual
interpolations at z and -z through the proved derivative pullback. The
signed series converges absolutely. The exact reflection beta_-j=-beta_j
pairs it into

    Psi_n(lambda)/Delta_H'(lambda) = sum_(j>0) A_j/(lambda-mu_j).

This intermediate quotient identity is stated away from critical poles
and the shifted central energy. Its central signed term cancels exactly.
The next entire representation fills every excluded energy.

## Filled entire Hilbert basis and full numerator identity

`EntireCriticalHilbertBasis.lean` is a reusable scalar result. For an
entire g vanishing at coordinates mu_j with quadratic norm growth, the
filled coordinates

    B_j(lambda) = (2*pi*j)*dslope(g,mu_j,lambda)

have locally uniform reciprocal-index tails. The verified local Hilbert
realization theorem therefore constructs a genuine entire l2-valued
basis. At a critical center its value is the actual derivative, rather
than an unfilled total-division value.

`CanonicalMiuraNumeratorRepresentation.lean` proves the required actual
quadratic critical-energy growth from the canonical critical-displacement
norm and fixed chart shift. With g=Delta_H', the constructed Hilbert
coefficient vector and filled basis give an entire scalar pairing. The
absolute principal-series identity identifies it with the actual
numerator off the critical and central values. The energy i-shift is a
proved noncritical seed: every beta_j is real, so its square cannot equal i.
An entire identity argument then proves, at every energy,

    Psi_n(lambda,q) = dualPairing(a(q), B(lambda,q)).

The pairing is an ordinary absolutely convergent coefficient sum. The
identity includes every simple critical center, every closed-gap input
in scope and the shifted central point. It is not limited to the original
contours, large energies or a punctured domain.

`exists_hillHminus_real_canonical_numerator_representation` constructs the
actual chart, verified normalized NLS Theorem12.1 data and one complex
rough-open neighborhood before every real input, numerator index and
energy. The original joint entire-energy/rough-input candidate analyticity
is retained. For each real input the exact coefficient vector and full
entire canonical Hilbert representation are proved.

## Exact scope and remaining obligations

The Hilbert basis is proved entire in energy for each fixed real-type
chart input. Joint Banach analyticity of this basis or coefficient vector
in the rough input is not asserted. The candidate itself retains its
previously proved joint analyticity on the complex source neighborhood.
The source NLS normalization data remain actual constructed data.

The complete canonical energy labels still need identification with the
earlier local rough critical labels. Actual contour normalization must be
transferred to the earlier period matrix before its inverse identifies
this numerator with the weighted normalized family. The latter's weighted
bounds and moment formulas cannot yet be assigned to the new candidate
merely from the representation.

Full coherent W and numerator chart compatibility, canonical leading
scalar one, sharp source estimate(54), physical Hamiltonian frequency
identity(69), action descent, weighted asymptotic/compact derivative claims
and actual Birkhoff/PDE identification remain open. No source main theorem
inventory row is closed.

## Validation

Nine new proved modules are directly selected. All 403 previously selected
Lean sources remain byte-identical and all seven shared provenance records
remain valid. Checker and audit selections follow the actual transitive
import order. Exact counts and the full permitted transitive axiom audit
are recorded in `VALIDATION.md` and `source.json`.
Pinned Lean4.33.1/mathlibv4.33.1, default heartbeats, warnings as errors,
private fresh outputs and only propext/Classical.choice/Quot.sound are
retained. Canonical main remains unchanged and read only.
