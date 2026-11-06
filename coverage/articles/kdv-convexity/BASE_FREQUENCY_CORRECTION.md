# Equation (1.7): the base-domain uniform boundedness claim

The assigned source, arXiv:1502.05857v1, printed p. 3, asserts that the
physical KdV frequencies extend coordinatewise analytically to a complex
neighborhood V0 of the positive ell^(-1,1) action cone, and that their
corrections to 8*pi^3*n^3 are O(1) locally uniformly on V0.

The locally uniform O(1) estimate is incompatible with the physical Taylor
normalization. It must not be included among the hypotheses used to construct
the remaining frequency family. Coordinatewise analyticity and physical
recovery on the original positive ell^(3,1) cone remain meaningful targets.
This correction does not refute the main analytic-extension or local-concavity
assertions of Theorem 1.1.

## Checked obstruction

The raw unit action at n has EXACT base norm 1/(1+n). The proved physical
normalization gives d(omega_n)(0)[e_n]=-6. Therefore every candidate physical
base extension satisfies

    norm(d(omega_n)(0)) >= 6*(1+n).

`BaseFrequencyTaylor.lean` proves both the raw-coordinate derivative and
this full cotangent norm lower bound. The proof uses the actual physical
Hilbert Taylor theorem and the already checked common-domain continuation
bridge; it assumes no bounded sequence realization of the base family.

`UniformScalarDerivativeBound.lean` is the reusable complex-analysis step:
a family of scalar analytic maps, bounded by M on one neighborhood of zero
before the index is chosen, has uniformly bounded cotangent norms at zero.
For a common ball of radius r its proof gives the bound 4*M/r.

`BaseFrequencyBoundObstruction.lean` combines these results. It rules out
ANY N and M for which, on one base-norm neighborhood of zero,

    norm(omega_n(a)-8*pi^3*n^3) <= M for all n >= N.

The index cutoff is allowed: discarding finitely many frequencies does not
avoid the contradiction. Only coordinatewise analyticity is assumed.
All source directions retain raw actions and the weight is exactly (1+n)^(-1).
No corrected upper growth estimate is asserted by this milestone.

## Remaining constructive obligation

`BasePhysicalFrequencyExtension.lean` now states the exact missing record:
one complex-open neighborhood of the entire positive base cone, scalar
analyticity for every coordinate, and equality with the intrinsic derivative
of actual physical KdV energy on the whole original positive ell^(3,1) cone.
The record has NO nonemptiness theorem yet. In particular, this correction
must not be counted as construction of V0 or completion of Theorem 1.1.

Given such a record, `exists_compatible_physicalHstarExtension` constructs one
global physical Hilbert extension, still containing the entire positive cone,
on whose entire domain all frequency identities hold simultaneously. The
already proved Taylor expansion, local analytic inverse, and uniform Hessian
radius then apply to that same extension.

## Source verification

The private assigned PDF was checked both as text and as a rendered page.
Its SHA256 is
`38ee7f287ee8b790b794865accc8ad51d1083e414b82a73c4a543147a7ec4688`.
The displayed date in that file is March 8, 2022; the article inventory records
this separately from its arXiv version identifier.

Independent corroboration appears in Kappeler–Molnar,
*On the wellposedness of the KdV/KdV2 equations and their frequency maps*,
Ann. I. H. Poincare AN 35 (2018), 101–160, Corollary 1.5(ii), printed p. 104:
the O(1) correction fails already for -1<s<-1/2.
[Publisher's full text](https://ems.press/content/serial-article-files/16625#page=4).
That paper's Theorem 3.4 and Remark 3.5(ii) describe a constructive route
through normalized second primitive moments and action descent. These
external statements are NOT imported into Lean as axioms; construction and
physical recovery remain proof obligations in this checkout.
