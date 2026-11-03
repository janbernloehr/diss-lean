# Actual canonical-root symmetry and normalized rough energy pullbacks

Every main theorem remains OPEN. This milestone proves the actual NLS
root parity and the signed contour transformation left open by
`REAL_MIURA_ENERGY_PSI.md`. It constructs exact shifted-square pullback
periods near every physically real Hminus1 base potential. A global
chart-independent Hill root and normalized family are still separate
obligations.

## Complete endpoint reflection from the actual discriminant

`EvenDiscriminantPeriodicEndpoints.lean` works at every finite source
exponent p>1 in the period-one source subspace, assuming the actual
canonical discriminant is even in the spectral parameter. The canonical
periodic product is exactly Delta(z)^2-4, and its analytic orders are the
original periodic algebraic multiplicities. Analytic order under z->-z
therefore proves exact spectrum and multiplicity reflection.

The proof reflects a complete endpoint labeling. It retains the entire
finite central multiset, each distant pair's actual spectrum and repeated
multiplicities, and genuine lp displacements. Negation reverses the
complex lexicographic order. Complete ordered-label uniqueness then gives

    left(-n) = -right(n),    right(-n) = -left(n).

This includes central indices, collapsed pairs and arbitrary complex
sources satisfying spectral evenness. No real-type hypothesis or
forward-membership substitute for multiset equality is used.

## The actual canonical root, with its original normalization

`EvenDiscriminantCanonicalRoot.lean` derives odd canonical midpoints,
even oriented gaps, reflected straight segments and invariance of the
actual canonical-root domain. The literal normalized standard-root
formula gives

    standardRoot_n(-z) = -standardRoot_(-n)(z).

In the symmetric finite canonical-root products the nonzero denominators
change sign with the index; the exceptional central denominator stays
one. The central factor is consequently the single remaining minus
sign. Passing to the already proved literal product limit gives

    sourceCanonicalRoot(-z) = -sourceCanonicalRoot(z).

This identifies the actual canonical root, without introducing a new
square root of Delta^2-4 or leaving a sign choice as a hypothesis.

`HillHminusOneMiuraRootSymmetry.lean` applies these reusable results to
the actual even diagonal L2 Miura trace. Actual endpoint reflection,
root oddness and domain symmetry hold at every complex rough chart
input, without restricting the input to the physically real locus.

## Exact positive/negative contour transformation

`NegatedCircleIntegral.lean` proves the literal change of variable

    integral_C(c,R) f(-z) dz = -integral_C(-c,R) f(z) dz.

A half-turn of the periodic circle parameter proves the identity.
Negation preserves the circle's orientation and negates dz.

`EvenPsiAntisymmetricPeriods.lean` reflects an actual original isolating
circle at m to an actual original isolating circle at -m. It uses the
existing verified `SourceTheorem12_1Data`, whose normalized numerator
has exact periods on every original isolating circle. Thus the reflected
circle is covered by the same actual normalized family. Root oddness
cancels the change-of-variable sign, and the antisymmetrized numerator
has raw period

    2*pi*(delta_mn-delta_(-m),n).

Integrability is proved from the actual root domain and nonvanishing,
not assumed. No contour symmetry of an arbitrarily selected family is
assumed. The existing unchanged `SourceTheorem12_1.lean` is now directly
selected and recompiled. Actual spectral isolation also constructs a
simultaneous all-index family of original isolating circles.

## Constructed rough normalized shifted-square pullbacks

`HillHminusOneMiuraEnergyPeriods.lean` retains the previous actual entire
energy candidate, fixed shift s=C.energyShift and literal factor identity

    (2z)*Psi_n(z^2-s,q) = phi_n(z,q)-phi_n(-z,q).

The new signed theorem proves its exact pullback period using the actual
NLS canonical root rho:

    integral_C(c_m,R_m) (2z)*Psi_n(z^2-s,q)/rho(z,q) dz
      = 2*pi*(delta_mn-delta_(-m),n).

For positive m,n the second Kronecker term is zero, giving exactly the
source normalization 2*pi*delta_mn, with no extra factor i.

`exists_hillHminus_real_normalized_energy_pullbacks` constructs C,V,W0,W,s
at every physically real rough q0. One common complex Hminus1-open V,
containing q0 and every real input in C.domain, precedes every numerator
index and circle index. It retains the actual real-preserving Miura
chart, positive real energy shift, full verified NLS Theorem12.1 data,
all-index joint entire-energy analyticity, nonempty simultaneous actual
isolating-circle families, and the exact positive periods on every such
original circle. The source domain is constructed by intersecting the
chart pullback with the actual psi and spectral-isolation domains, both
of which contain the entire real-type locus.

## Source relation and remaining obligations

These are actual normalized pullback periods toward (52)-(53), PDF21,
and the full frequency extensions in Theorems1.2 and1.9, PDF4/6. The
energy path is z->z^2-s and its actual Jacobian 2z is retained. The
root in the proved literal integrals is the actual NLS root evaluated
at the lifted frequency z. The theorem does not yet assert a globally
defined Hill energy-root function, independence of the lift/chart,
lowest-cut continuation, or agreement with the earlier local rough
weighted normalized family. It does not prove the canonical Hill product
leading scalar is one, source root estimate(54), physical Hamiltonian
frequency identity(69), action descent, weighted target spaces, compact
derivatives or actual Birkhoff/PDE flows. All main inventory rows remain
OPEN, and the goal remains incomplete.

## Validation

Six new proved modules and one newly selected existing module are
checked in dependency order. All 378 previously selected Lean sources
remain byte-identical; all seven shared provenance records remain valid.
Exact full-build counts and audit results are in `VALIDATION.md` and
`source.json`. Pinned Lean4.33.1/mathlibv4.33.1, default heartbeats,
warnings as errors and private fresh outputs are retained. Only propext,
Classical.choice and Quot.sound are permitted. Canonical main remains
unchanged and read only.
