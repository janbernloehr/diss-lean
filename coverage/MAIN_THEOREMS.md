# Verification of the three main theorems

The accepted completion criterion is verification of the dissertation's
main theorems. The introduction explicitly identifies these as Theorems
0.1, 0.2 and 0.3, on printed/PDF pages 11, 12 and 13. All three are verified
in Lean under the [accepted manuscript reference](ACCEPTED_REFERENCE.md)
and the recorded definitions and normalizations.

The source statements were compared with the actual Lean data fields and
their existence constructions on 2026-11-02. The conclusions below are
proved properties of constructed objects, rather than hypotheses supplied
by a caller. The [machine-readable verification record](main-theorems-verification.json)
pins the source, inspected modules and validation evidence.

| Main theorem | Verified content | Principal Lean construction |
| --- | --- | --- |
| **0.1 — Uniform tame Sobolev estimates** | One original Birkhoff map works for every integer m>=1. Positive constants c_m and d_m are chosen before the potential. Both estimates retain the highest-order norm linearly and the order-one/order-zero remainders with powers 2m and 4m-3. | [`sourceSection23_original_estimates`](../NLS/ZakharovShabat/SourceSection23Original.lean), with the fields of [`SourceSection23SobolevBounds`](../NLS/ZakharovShabat/SourceSection23Sobolev.lean). |
| **0.2 — Renormalized Hamiltonian** | The same H* is real analytic and nonpositive on nonnegative summable actions, vanishes exactly at zero, extends analytically near zero in ell2, and has real Hessian bounded above by -norm(J)^2 there. Its identity with physical energy retains both the mass-square and weighted linear-action subtractions. | [`sourceSection18_original_hamiltonian`](../NLS/ZakharovShabat/SourceHamiltonianOriginal.lean), including `physical_identity` and `concavity`, and [`real_summable_extension`](../NLS/ZakharovShabat/SourceOriginalActionDomains.lean). |
| **0.3 — Renormalized frequency map** | One frequency on nonnegative summable actions has analytic realizations in every ell^r, r>1. For every finite p>2, its ell^(p/2) extension is analytically invertible between neighborhoods of zero. The same map has correction F(I)+2I in ell^(1+) for 2<p<=3 and ell^(p/3) for p>3. | [`sourceSection18_original_frequencies`](../NLS/ZakharovShabat/SourceFrequencyOriginalHilbert.lean), [`realizations_all`](../NLS/ZakharovShabat/SourceFrequencyOriginalHilbertTop.lean), the [`refined` field and construction](../NLS/ZakharovShabat/SourceFrequencyOriginalAsymptotic.lean), and [`local_open_inverse`](../NLS/ZakharovShabat/SourceFrequencyOpenInverse.lean). |

Theorem 0.2 asserts local concavity; it does not assert concavity on the
entire nonnegative ell2 cone. Theorem 0.3 asserts local invertibility for
finite source exponents p>2; it does not assert global injectivity or an
extension to bounded action inputs. These restrictions match the stated
main theorems. The detailed comparisons are in [the introduction audit](INTRODUCTION.md).

## Validation

The unchanged Lean source and dependency snapshot passed the full build,
7,729 public examples and a transitive axiom audit of 45,245 NLS declarations.
A fresh focused check passed for 16 declarations covering the three
existence constructions, their relevant fields, the local inverse and the
physical Birkhoff-map identification. It confirms that those declarations
have definitions or proofs and permits only `propext`, `Classical.choice`
and `Quot.sound` transitively. Admitted proofs and additional project axioms
are excluded.

The mathematical comparison with the source statements is recorded
separately from Lean's proof checking. The latter verifies the formal
statements; source coverage is not inferred from declaration counts.
No Lean theorem or refutation was added in this verification step.

## Completion scope

The main-theorem verification criterion is satisfied. An exhaustive audit
of every explanatory passage, historical attribution and intermediate
printed formula is not an additional completion requirement. The existing
broader source reviews and accepted corrections remain available.
