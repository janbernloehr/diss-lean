# Equation (1.7): reference check and the corrected frequency statement

The assigned source, [arXiv:1502.05857v1](https://arxiv.org/abs/1502.05857v1),
printed p. 3, attributes to [15] both the common analytic extension of the
physical KdV frequencies and the estimate

$$\omega_n(I)-8\pi^3n^3=O(1)$$

locally uniformly on a complex-open neighborhood of the entire nonnegative
$\ell^{-1,1}$ action cone. The estimate is refuted in Lean under exactly
that complex base-norm interpretation. Checking [15] confirms that this
uniform estimate is not the result proved there.

## What reference [15] actually proves

[15] is T. Kappeler and P. Topalov, *Global wellposedness of KdV in
$H^{-1}(\mathbb T,\mathbb R)$*, Duke Mathematical Journal **135**(2)
(2006), 327–360, DOI [10.1215/S0012-7094-06-13524-X](https://doi.org/10.1215/S0012-7094-06-13524-X).
The [author-uploaded full text](https://www.researchgate.net/publication/278194325_Global_wellposedness_of_KdV_in_H-1TR)
was checked on 2026-11-07. Page numbers below are printed journal pages.

- **Theorem 1.9, p. 332:** there is one complex-open neighborhood
  $W\subset H^{-1}_{0,\mathbb C}$ of the entire real $H^{-1}_0$ space such
  that each fixed scalar frequency $\omega_k$ extends analytically to $W$.
  No bound uniform in the frequency index is asserted.
- **Remark 1.10, p. 333:** local boundedness of the imaginary frequency
  sequence on $W$ is explicitly described as unknown. The remark recalls
  an $o(1)$ remainder on a complex neighborhood of $L^2_0$, citing its
  reference [1], Theorem 3.5; the corresponding $o(1)$ question at negative
  Sobolev regularity was described as unknown.
- **Lemma 3.2 and its proof, pp. 345–346; Lemma 3.3, p. 346:** the frequency
  index $k$ is fixed. Uniformity in the auxiliary summation index $l$ in
  the period estimates is not uniformity in $k$.

## The genuine uniform estimate uses the stronger L2 topology

The earlier paper is D. Bättig, T. Kappeler and B. Mityagin,
*On the Korteweg–de Vries equation: Frequencies and initial value problem*,
Pacific Journal of Mathematics **181**(1) (1997), 1–55,
DOI [10.2140/pjm.1997.181.1](https://doi.org/10.2140/pjm.1997.181.1).
Its [publisher PDF](https://msp.org/pjm/1997/181-1/pjm-v181-n1-p01-s.pdf)
states the result in **Theorem 1, p. 2**, with the detailed bound in
**Theorem 3.5, p. 24**; see also **equation (3.41), p. 27**.
For every real $q_0\in L^2_0$, there exists a neighborhood $U_{q_0}$ in
$L^2_{0,\mathbb C}$ such that

$$\sup_{q\in U_{q_0}}|\omega_n(q)-(2\pi n)^3|\longrightarrow0.$$

This is local uniformity in the **L2 norm**, not in the Hminus1 norm.
Through the Birkhoff weights, the corresponding real action regularities are:

| Potential norm | Birkhoff coordinate regularity | Action regularity |
| --- | --- | --- |
| $L^2_0=H^0_0$ | $h^{1/2}$ | $\ell^{1,1}_+$ |
| $H^{-1}_0$ | $h^{-1/2}$ | $\ell^{-1,1}_+$ |

This translation uses $I_n=(x_n^2+y_n^2)/2$ and the regularity shift in
[15], Theorem 1.7, pp. 331–332. An L2 neighborhood gives no Hminus1
neighborhood bound. The stronger action topology cannot be silently replaced
by the weaker base topology used in (1.7).

## Later results confirm the regularity distinction

T. Kappeler and J.-C. Molnar, *On the wellposedness of the KdV/KdV2
equations and their frequency maps*, Ann. I. H. Poincaré – AN **35**
(2018), 101–160, DOI [10.1016/j.anihpc.2017.03.003](https://doi.org/10.1016/j.anihpc.2017.03.003),
**Corollary 1.5(i)–(iii), p. 104**, gives

$$\omega_n(q)-(2\pi n)^3=
\begin{cases}
o(n^{-2s-1}),&-1\le s<0,\\
O(n^{-1}),&s=0,
\end{cases}$$

locally uniformly in the stated Sobolev topology. Part (ii) explicitly rules
out a locally uniform $O(1)$ remainder on real $H^s_0$ for
$-1<s<-1/2$. At $s=-1$, the displayed bound is $o(n)$.
For $s=0$, the $O(n^{-1})$ bound is uniform on bounded L2 sets.
See the [statement, PDF p. 4](https://ems.press/content/serial-article-files/16625#page=4)
and its [proof, printed pp. 128–129 / PDF pp. 28–29](https://ems.press/content/serial-article-files/16625#page=28).
The failure concerns local uniformity on the stated spaces; it does not
assert failure at every individual potential.

## Bibliographic conclusion and precise correction

As printed, (1.7) overstates reference [15]. Its coordinatewise analytic
extension is a legitimate result, but the uniform remainder recalled there
uses L2 topology. No alternate topology convention found in [15] rescues
the printed complex $\ell^{-1,1}$ assertion. Conflation of the Hminus1
extension with the earlier L2 estimate is a possible explanation, not
established authorial intent. Merely restricting to real rough potentials
does not restore a locally uniform O(1) bound in view of the later result.

The corrected Theorem 1.1 retains the displayed main theorem's Hamiltonian
extension, analytic Hilbert-valued gradient, physical frequency identity,
zero gradient, derivative $-6\,\mathrm{Id}$, local analytic inverse, and
one-radius Hessian bound and strict concavity. It also constructs the common
base domain with scalar analytic frequencies and exact physical recovery.
Only the preamble's incompatible uniform base estimate is excluded.

The common base family is now constructed unconditionally by
`nonempty_basePhysicalFrequencyExtension` in
[`BasePhysicalFrequencyConstruction.lean`](../../../NLS/Articles/KdVConvexity/BasePhysicalFrequencyConstruction.lean).
[`MainTheorem11.lean`](../../../NLS/Articles/KdVConvexity/MainTheorem11.lean)
proves `theorem_1_1_corrected : Nonempty Theorem11PhysicalData` and
`Theorem11PhysicalData.printed_uniform_base_estimate_impossible`.
Theorem 1.1 with this correction and Theorems 1.2–1.3 are complete.

## Checked Lean obstruction and validation scope

The raw unit action $e_n$ has exact base norm $1/(1+n)$, while physical
normalization forces $D\omega_n(0)[e_n]=-6$. Thus

$$\|D\omega_n(0)\|\ge6(1+n).$$

[`BaseFrequencyTaylor.lean`](../../../NLS/Articles/KdVConvexity/BaseFrequencyTaylor.lean)
proves the derivative and cotangent norm lower bound using the actual physical
Hilbert Taylor theorem and common-domain continuation. A common local scalar
analytic bound would give uniformly bounded derivative norms by Cauchy's
estimate; the reusable
[`UniformScalarDerivativeBound.lean`](../../../NLS/ComplexAnalysis/UniformScalarDerivativeBound.lean)
gives $4M/r$ for a common ball of radius $r$.
[`BaseFrequencyBoundObstruction.lean`](../../../NLS/Articles/KdVConvexity/BaseFrequencyBoundObstruction.lean)
therefore rules out every $N,M$ and every common base neighborhood of zero
on which $|\omega_n(I)-8\pi^3n^3|\le M$ for all $n\ge N$.
Discarding finitely many indices does not help.

The original source PDF was checked as text and as a rendered page; its
SHA-256 is `38ee7f287ee8b790b794865accc8ad51d1083e414b82a73c4a543147a7ec4688`.
It prints March 8, 2022; the inventory separately records its arXiv version.
This reference check is a documentation update. No Lean source, axiom, or
original physical normalization changes. Stale summary fields are reconciled
with the already completed theorem entries. The external
L2 and later Sobolev estimates are bibliographic evidence, not additional
Lean theorems or imported axioms. Existing strict build and axiom-audit
receipts remain applicable to the unchanged proof sources.
