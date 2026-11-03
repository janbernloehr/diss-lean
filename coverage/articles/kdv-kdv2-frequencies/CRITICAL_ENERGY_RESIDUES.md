# Complete rough Hill critical energies and actual residue transfer

Every article main theorem remains OPEN. This milestone supplies complete
critical-point geometry and genuine principal coefficients for the actual
NLS-derived entire energy numerator. A Hilbert residue sequence and a
numerator representation are still required to identify it with the
earlier weighted normalized rough Hill family.

## Exact reflection of the actual canonical critical labels

`EvenSpectralDerivatives.lean` proves exact derivative parity: the first
derivative of an even scalar complex function is odd and vanishes at zero,
and its second derivative is even. These are identities of the total
derivative and do not require choosing a local spectral branch.

`EvenRealCanonicalCriticalPoints.lean` combines the actual canonical
periodic endpoint reflection with the verified real gap interlacing and
uniqueness theorem. For an even discriminant at a real-type source,

    beta_(-j) = -beta_j,       beta_0 = 0,
    beta_j.re > 0             for every j>0.

This identifies the actual complete canonical sequence, including the
central finite cluster and collapsed gaps. The positive sign follows from
strict canonical order, rather than a high-index approximation.

## All critical energies of the independent rough Hill trace

For an actual Miura chart C, the existing coordinates are

    beta_j(q) = C.frequencyCritical(q,j),
    mu_j(q)   = beta_j(q)^2 - C.energyShift,       j>0.

`HillHminusOneRealCriticalEnergyGeometry.lean` proves, at every chart input
with actual real-type NLS source:

- Each mu_j is a critical energy of the independent rough Hill trace.
- Each critical energy is simple: Delta_H''(q,mu_j) != 0.
- Every zero of Delta_H'(q,lambda), over the entire complex energy plane,
  equals mu_j for some positive index j.
- The real parts of mu_j are strictly increasing. With the real chart
  shift, all mu_j are real. Their values are not asserted positive.
- Each fixed mu_j has a full complex Hminus1-input analytic germ at every
  real-type chart input.

The central frequency is handled explicitly. The actual second-derivative
chain rule gives

    Delta_NLS''(q,0) = 2 Delta_H'(q,-C.energyShift).

The central canonical NLS critical point is zero and is simple. Thus
-C.energyShift is not an energy critical point. In proving completeness,
any Hill critical energy is lifted by sqrt(lambda+C.energyShift); this
frequency cannot be zero. Exhaustive NLS critical labeling and the proved
signed reflection then select an actual positive label. No extra energy
critical point is inserted at the ramification point.

Constructed real-preserving charts yield the unconditional rough result
`hillHminus_critical_real_and_simple`: every critical energy of the actual
Hill trace is real and simple at every physically real Hminus1 potential.
There is no cutoff, L2 or open-gap hypothesis. The theorem
`exists_hillHminus_complete_real_critical_energies` constructs one chart
before all real inputs, all energies and all positive labels on its domain.

## Genuine principal coefficients and the exact 2 beta factor

The energy numerator Psi_n is the previously constructed filled odd square
descent of phi_n(z)-phi_n(-z). Its exact factor identity and the actual
trace derivative chain rule give, for z!=0,

    Psi_n(z^2-c) / Delta_H'(z^2-c)
      = (phi_n(z)-phi_n(-z)) / Delta_NLS'(z).

The identity retains the actual fixed chart shift c. Define the actual
signed canonical principal coefficients

    r_j = phi_n(beta_j) / Delta_NLS''(beta_j)

and the corresponding energy coefficient

    A_j = Psi_n(mu_j) / Delta_H''(mu_j).

All these denominator derivatives are nonzero at the real-type inputs in
the theorem. The actual second-derivative chain rule at beta_j gives
Delta_NLS''(beta_j)=4 beta_j^2 Delta_H''(mu_j). Its evenness identifies the
negative-index denominator. Consequently,

    A_j = 2 beta_j (r_j-r_(-j)),        j>0.

`HillHminusOneMiuraCriticalResidues.lean` proves this as
`hillHminusMiuraEnergyCriticalResidue_eq_signed`, without an assumed
residue transfer or guessed Jacobian.

`SimpleZeroPrincipalCoefficient.lean` supplies a reusable analytic proof
of the principal-coefficient interpretation. For an entire denominator f
with f(a)=0 and f'(a)!=0, the filled function P(z)/dslope(f,a,z) is analytic
near a, equals (z-a)P(z)/f(z) away from a and takes value P(a)/f'(a) at a.
It therefore proves the genuine punctured limit. Applied to the actual
rough Hill derivative, the result is

    (lambda-mu_j) Psi_n(lambda)/Delta_H'(lambda) -> A_j
                              as lambda -> mu_j, lambda!=mu_j.

The quotient may have a removable singularity when A_j=0. The proof covers
this case as well. Each fixed coefficient A_j is analytic in the complex
rough input at every real-type chart input. No sequence norm is asserted.

## Filled central value and actual normalized data

The filled descent has the exact central value

    Psi_n(-c) = phi_n'(0).

Since Delta_H'(-c)!=0, its quotient by the actual Hill derivative is
jointly analytic in a full complex energy/source neighborhood of (-c,q)
at every real-type input where the source root branches are analytic.
There is no remaining artificial central pole.

`exists_hillHminus_real_energy_critical_residues` constructs the actual
real-preserving chart, common complex rough-open V and verified NLS
Theorem12.1 data before all numerator and critical indices, at every
physically real rough base potential. It retains the joint entire energy
numerators, individual analytic residue germs, exact signed transfer,
genuine principal limits and joint central filling. The data retain their
original NLS normalization periods through SourceTheorem12_1Data; they
are constructed rather than assumed.

## What is still needed for the main frequency theorems

Pointwise principal coefficients and individual analytic germs do not yet
supply a genuine Hilbert coefficient sequence or a Mittag-Leffler
representation with vanishing entire remainder. The earlier critical
basis contains the exact factor 2*pi*j, so its coefficient is
A_j/(2*pi*j); that
normalization must be retained when proving sequence bounds. The new
complete real canonical energy labels must also be identified with the
earlier local rough critical labels used by the period operator.

A proved sequence bound, exterior remainder control, the representation
and actual contour-period compatibility are required before invoking the
constructed period inverse to identify the entire numerators. Matching
periods alone does not prove uniqueness of arbitrary entire candidates.
Full coherent W, canonical leading scalar one, sharp source estimate(54),
physical Hamiltonian frequency identity(69), action descent, weighted
asymptotic/compact derivative statements and actual Birkhoff/PDE flows
remain open. No source main-theorem inventory row is closed.

## Validation

Five new proved modules are directly checked. All 398 previously selected
Lean sources remain byte-identical, and all seven shared import provenance
records remain valid. Exact checker/audit/PASS/coverage selections and full
transitive axiom counts are recorded in `VALIDATION.md` and `source.json`.
Pinned Lean4.33.1/mathlibv4.33.1, default heartbeats, warnings as errors,
private fresh outputs and the permitted propext/Classical.choice/Quot.sound
axioms are retained. Canonical main remains unchanged and read only.
