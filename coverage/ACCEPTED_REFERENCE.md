# Accepted Birkhoff-map reference

On 2026-11-02 the user selected the supplied Grébert–Kappeler manuscript,
*The defocusing NLS equation and its normal form*, as the reference for this
formalization. Verifying identity with the published 2014 edition is outside
the agreed scope. Earlier records of that requirement are historical.

The accepted copy has 141 PDF pages and a July 2013 preface. Its SHA-256 is
`eceee60e4bd785605a1404c0449ebb08bcc454bf6e71d0a0c30bc13a27509849`.
The manuscript itself is not distributed in this repository. PDF page numbers
below count from its first page, independently of the printed pagination.

## Construction and proof correspondence

The existing physical construction supplies the map and its inverse through
literal spectral data, contour integrals and angle integrals. The inspected
manuscript uses the following conventions and statements.

| Accepted manuscript | Convention or statement | Existing Lean evidence |
| --- | --- | --- |
| Formula (12.5), PDF p. 68 | Canonical square root: prefactor 2i and symmetric standard-root product divided by pi_m, with pi_0=1. | [Physical canonical product](../NLS/ZakharovShabat/PhysicalCanonicalRoot.lean) |
| Formula (14.1), Theorem 14.1, PDF pp. 77–78 | Deleted psi product with prefactor -2/pi_n, denominator pi_k, real gap placement, and 1/(2*pi) Kronecker periods. | [Physical psi comparison](../NLS/ZakharovShabat/PhysicalPsiComparison.lean), [family identification](../NLS/ZakharovShabat/PhysicalPsiFamily.lean) |
| Section 13, PDF pp. 71–73 | Counterclockwise action integral with factor 1/pi and positive principal amplitude sqrt(4I_n/gamma_n^2). | [Physical actions and coordinates](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsic.lean), [normalized action root](../NLS/ZakharovShabat/SourceBirkhoffRealActionAngle.lean) |
| Section 15, PDF pp. 87–88 | theta=eta+beta; integration from the left periodic endpoint; terminal root sign fixed by the anti-discriminant. | [Physical angular values](../NLS/ZakharovShabat/PhysicalAngularValues.lean) and the detailed [Section 14 comparison](SECTION_14.md) |
| Section 16, PDF p. 95 | x_n=sqrt(2I_n)cos(theta_n), y_n=sqrt(2I_n)sin(theta_n). | [Intrinsic physical map](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsic.lean) |
| Theorem 18.8, PDF p. 106 | Mixed bracket {x_m,y_n}=-delta_mn; both equal-coordinate brackets vanish. | [Physical canonical brackets](../NLS/ZakharovShabat/PhysicalBirkhoffCanonical.lean) |
| Theorem 19.3, PDF pp. 108–109 | Properness, bijectivity and exact Hilbert norm preservation. | [Hilbert properness](../NLS/ZakharovShabat/SourceHilbertProperness.lean) and [intrinsic global inverse](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsicProperties.lean) |
| Theorem 20.2, PDF p. 109 | Global real analytic Sobolev diffeomorphism at every integer order m>=1. | [Native Sobolev inverse](../NLS/ZakharovShabat/NativeWeightedBirkhoff.lean); its proved nonnegative real orders include these integer orders. |

The source comparison is a mathematical reading of the specified passages
against the existing Lean declarations. Lean checks those declarations and
their proofs; it does not certify a PDF transcription or edition identity.

## Closed reference requirements

Under the accepted reference, S14-010 identifies the physical Hilbert map,
S17-007 supplies the Hilbert base case, and S18-003 supplies its Sobolev
canonical extension. These groups are matched with this reference choice
recorded explicitly. The earlier proof evidence remains intact.

The user also accepted the precise smooth-solution interpretation of S7-002.
Its velocity multiplier and smoothness assumptions remain explicit. The
[completion assessment](COMPLETENESS.md) retains all other domain and norm
qualifications and the adopted positive constant corrections.
