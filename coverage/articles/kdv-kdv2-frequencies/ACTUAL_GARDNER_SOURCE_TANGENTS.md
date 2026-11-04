# Actual Hill Gardner source tangents and spectral stationarity

This step supplies actual coefficient-space source directions for the
normalized spectral-differential and Abelian-angle variation needed before
Lemma 3.2 (69), PDF page 26. It does not prove the normalized-differential
or angle identity, a physical frequency theorem, or an article main theorem.

## Complex rough trace involution

`HillL2GardnerTraceInvolution.lean` proves the scalar Gardner pairing of the
actual rough trace gradients vanishes for every complex `q : Coeff 2` and
all complex frequencies, including coincident frequencies. It is available
both with the explicit spatial-gradient curve and with the actual spatial
`deriv` of the gradient representative.

The proof transfers the previously proved actual continuous-potential
identity through finite Fourier synthesis. The physical trace-gradient
curves vary continuously in the source in the norm of continuous curves;
the literal unit-interval integral is a continuous linear map. No presumed
Poisson model or NLS symplectic bracket replaces the scalar Gardner pairing.

The same argument proves that the actual spatial trace-gradient curve has
matching endpoints and zero physical mean at every complex L2 source.
No smoothness, real-type, or endpoint-matching hypothesis on the source is
needed for these statements.

## Actual Fourier coefficient tangent

`HillL2GardnerDirections.lean` constructs
`hillL2DiscriminantGardnerDirection q b : Coeff 2` from the actual unit-period
Fourier integrals of the spatial trace-gradient curve at energy `b`. The
existing coefficient-preserving continuous period-one realization is reused.
It proves that this tangent has even period-two support and exactly zero
zeroth coefficient. Its actual Hilbert synthesis recovers the original
physical spatial gradient almost everywhere on the unit interval.

The actual derivative map from coefficients to physical L2 potentials has
precisely this same representative and sign:

`-(hillPhysicalDirection X_b)₂ = g_b'` almost everywhere.

The actual discriminant derivative formula therefore gives

`D_q Delta(q,a)[X_b] = 0`

for every complex L2 source and every pair of complex energies. These are
source derivatives along a constructed coefficient direction, rather than
only formal integrals of physical densities.

At every actual real period-one base and positive Dirichlet index, every
analytic local branch satisfying the actual Dirichlet equation and agreeing
with the labelled energy has derivative

`D_q nu_n(q)[X_b] = B_n(b)`,

where `B_n` is the previously proved actual normalized Dirichlet/discriminant
Gardner bracket. The reused results prove existence of those labelled local
branches and identify their physical normalized gradients. The exact sheet
quotient and filled diagonal `-r_D/2` from the preceding milestone therefore
apply to these actual source derivatives.

## Actual spectral stationarity

`HillL2GardnerSpectralStationarity.lean` proves that the joint discriminant
differential annihilates `(0,X_b)`. Analytic second-derivative symmetry then
proves the actual source derivative of the spectral derivative vanishes:

`D_q (partial_a Delta(q,a))[X_b] = 0`.

This differentiates the already proved all-energy source identity, using
joint analyticity and symmetry of the second Fréchet derivative; it does not
infer infinitesimal stationarity from equality on an isospectral set.

On the actual open `hillL2ContinuationDomain`, the proved normalized primitive
derivative gives zero source variation of the actual continued primitive.
The actual local identity `2*sinh(F)=R` gives zero source variation of the
sign-normalized continued root as well. Both source-section and joint
statements are provided, on precisely that same continuation domain. No
larger global complex source neighborhood or extension across a branch
point is asserted.

## Validation and remaining work

Validation reuses 569 unchanged previously checked selected sources, strictly
compiles these three new proof modules at the default resource limits, and
runs a fresh combined transitive axiom audit of all 572 selected modules.
No new branch import or change to the ten existing shared provenance records
is made. The canonical helper reuse record is unchanged. Exact selections,
transitive selected dependency order, source hashes, private fresh outputs
and overlay links, reuse hashes and unchanged clean canonical main are
checked before publication. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. No repeated full build is claimed.

Still required are the actual derivative of the normalized entire
numerators and their period equations, the convergent Dirichlet
interpolation and Abelian-angle variation with the correct source
orientation, physical frequency identification, and all full main theorems.
No actual isospectral integral curve is constructed here, and no pointwise
finite-gap energy equality is differentiated in arbitrary source directions.
All main statement inventory rows remain open.
