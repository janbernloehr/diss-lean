# Source discrepancies

## Lemma I.1: missing lower-block invertibility hypothesis

Source: dissertation, printed page 139, checked in the rendered PDF.
The statement asserts that invertibility of Id+T implies invertibility of
both Id+D and the Schur complement. The first of these conclusions is false
without an extra assumption, even for bounded operators on C times C.

Take A=D=-Id and B=C=Id. The full operator Id+T maps (x,y) to (y,x), hence
is its own bounded inverse. Its lower-right block Id+D is zero and is not
invertible. `sourceI1_swap_operator`, `sourceI1_swap_isUnit`, and
`sourceI1_lower_not_isUnit` prove these facts; `sourceLemmaI1_printed_false`
refutes the printed biconditional. This counterexample precedes any use of
the inverse of Id+D and does not depend on defining a singular inverse.

The corrected statement assumes Id+D invertible and then asserts that
Id+T is invertible if and only if S=Id+A-B*(Id+D)^(-1)*C is invertible.
`sourceLemmaI1_corrected` proves this for arbitrary complex Banach blocks;
`sourceLemmaI1_sufficient` retains the valid sufficient direction of the
printed version. The direct-sum transfer theorem applies the result to the
original operator on Z through its bounded linear coordinate equivalence.

Corollary I.2 needs no correction: norm(D)<1 supplies the lower inverse,
and the nonzero finite-dimensional Schur determinant gives invertibility.
`sourceCorollaryI2` and `sourceCorollaryI2_on_decomposition` prove the printed
sufficient condition. The norm bound is strict: with A=B=C=0 and D=-Id,
the Schur expression is Id and has determinant one, but Id+T kills the
second coordinate. `sourceCorollaryI2_boundary_counterexample` formalizes
this boundary example; it is not a counterexample to the printed I.2.

I.4's later displayed Schur formula has not yet been audited in this step.

## Corollary H.2: physical interpretation on the entire H^m source

Source: dissertation, printed page 139. The displayed formula holds at
the stated regularity without a correction. The highest derivative is
represented almost everywhere by the derivative of the penultimate H1
jet; its square is integrable. All lower jets used by the polynomial have
continuous representatives. `sourceCorollaryH2` retains the printed
quantifier order, with one polynomial chosen before every real H^m input,
as well as the stated homogeneity and equal field counts.

`integral_sq_sobolevTopJetPhysical` identifies the leading term with the
actual unit-period integral. The weak-derivative chain is proved using
Mathlib's actual tempered-distribution derivative, and the smooth
comparison recovers the classical mth derivative. The physical Hamiltonian
is the unique continuous extension from the smooth complex hierarchy.
This is an endpoint-regularity verification, not an erratum.

## Lemma H.1: the highest derivative at the printed Sobolev regularity

Source: dissertation, printed page 139, checked in the rendered PDF.
The hypothesis is phi in H^(k-1), while the displayed leading term is
minus the kth derivative of phi_+. Thus at this regularity the leading
derivative is an H^-1 distribution. For k>=2, every remainder jet has
order at most k-2 and a continuous representative; for k=1 the remainder
is zero. This is a weak-derivative interpretation, not a counterexample
or a correction to the printed formula.

`weakSobolevRiccatiDensity` extends the actual derivative-plus-convolution
recurrence to this H^-1 endpoint. Its classical coefficient agreement and
`weakSobolevRiccatiDensity_unique` identify it as the unique continuous
H^-1 extension of the independently defined smooth hierarchy.
`sourceLemmaH1` proves the exact leading-term coefficient formula on all
complex H^(k-1) sources, and `sourceLemmaH1_polynomial` retains the printed
homogeneity, field balance, and derivative bounds.

`sourceLemmaH1_weak` states equality in H^-1.
`sourceLemmaH1_distribution` uses the actual tempered-distribution
derivative after the exact period-one insertion of coefficients. The
remainder's coefficients are the actual Fourier integrals of its
continuous lower-jet polynomial field. The endpoint k=1 and the first
nonlinear case k=2 are both explicitly checked.

## Lemma G.7: an extra pi in the Dirichlet half-wave reference

Source: dissertation, printed page 138, checked in the rendered PDF.
The statement subtracts (e^+_(-2*n*pi)+e^-_(-2*n*pi))/2 from the Dirichlet
eigenvalue gradient. Under the preceding definition
e_alpha(x)=exp(i*pi*alpha*x), the subscripts must instead be -2*n.
The midpoint assertion has no such reference and remains unchanged.

`classicalDirichletNormalizedGradient_free_lattice` proves that the actual
free normalized gradient is (wave(2*n),wave(-2*n))/2, where
wave(m)(s)=exp(i*pi*m*s). The canonical eigenvalues at zero are n*pi,
and `fderiv_canonicalDirichletRoot_zero_eq_free` identifies their actual
derivative with the free functional h |-> (h.fst(-n)+h.snd(n))/2.
The zero H1 source is real and belongs to every complex source neighborhood
used in the corrected result, because each contains the full real locus.

The first component of the printed error is
(exp(2*pi*i*n*s)-exp(2*pi^2*i*n*s))/2. Its Fourier coefficient at mode n
is (1-c_n)/2; G.6's real-frequency integral bound gives |c_n|<=1/2 for
nonzero n. `quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients`
therefore gives a lower bound 1/4 on both signed tails.
`not_eventually_sourceG7PrintedError_majorant` rules out any l2 majorant
even after deleting finitely many spectral indices.
`not_memlp_sourceG7Printed_pair_norms` gives the same failure in the exact
source signed pair norm, regardless of the second component.

`sourceLemmaG7_corrected_with_coefficients` proves both estimates for
finite p>=2 and conjugate q on one common complex neighborhood containing
the real source locus, using the original H1 source. The Dirichlet
Fourier-integral identities explicitly subtract the corrected half waves;
the signed-coordinate isometry and energy identity identify the exact
source norm. The actual corrected derivative error vanishes at zero.
This proves the corrected assertion and does not reinstate its printed
wave normalization.

## Corollary G.6: an extra pi in the anti-discriminant wave index

Source: dissertation, printed page 138, checked in the rendered PDF.
The preceding definition is e_alpha(x)=exp(i*pi*alpha*x), with
e^-_alpha=(e_(-alpha),0) and e^+_alpha=(0,e_alpha).
The second assertion subtracts (-1)^n times
(e^+_(-2*n*pi)-e^-_(-2*n*pi)). Under this definition, its wave frequencies
contain pi twice. The correct subscripts are -2*n.

At zero potential and nu_n=n*pi, the actual i times anti-discriminant
gradient is (-1)^n times (-exp(2*pi*i*n*s),exp(-2*pi*i*n*s)).
The first component of the printed error is therefore (-1)^n times
(exp(2*pi^2*i*n*s)-exp(2*pi*i*n*s)). Its Fourier coefficient at mode n
is (-1)^n times (c_n-1), where c_n is the coefficient of the first
exponential. `sourceG6PrintedWave_diagonal_le_half` bounds |c_n| by 1/2
for every nonzero integer n, using the exact exponential integral and
the frequency-gap bound. Thus the actual inner l2 norm is at least 1/2
at every nonzero n.

`not_memlp_sourceG6PrintedAntiError_norms` and
`not_eventually_sourceG6PrintedError_majorant` prove failure of outer
l2 summability, even after removing any finite spectral head.
`sourceG5_zero_admissible` supplies the original zero H1 source and both
frequency hypotheses. `not_memlp_sourceG6Printed_pair_norms` transfers the
obstruction to the exact source signed pair norm, for any second component.
This refutes the literal second assertion already at p=2.

`sourceCorollaryG6_antiDiscriminant_corrected` proves the estimate after
removing the extra pi. `sourceCorollaryG6_discriminant` proves the first
assertion unchanged. Both hold for every finite 2<=p<infinity with the
printed conjugate exponent, uniformly on exact Chapter 5 H1 source-norm
balls and in the exact finite-exponent output norm of equation (1.2).
The signed Fourier-coordinate and coefficient-energy identities explicitly
identify this output norm. These results do not reinstate the printed
reference. G.7's corresponding wave-index audit is recorded above.

## Lemma G.5: swapped free-reference components and the infinity endpoint

Source: dissertation, printed page 137, checked in the rendered PDF.
Immediately above the lemma, e^-_alpha=(exp(-i*pi*alpha*x),0) and
e^+_alpha=(0,exp(i*pi*alpha*x)). The statement's upper off-diagonal
reference is -e^+_(-2*nu_n/pi), while its lower one is e^-_(-2*nu_n/pi).
However, the proof gives M2 star M2 = e^-_(-2*nu_n/pi) plus errors and
M1 star M1 = e^+_(-2*nu_n/pi) plus errors. Thus the statement swaps the
two superscripts relative to its own proof. The same swap occurs in the
second formula with the lattice reference.

The actual unconjugated potential derivative confirms this discrepancy:
i times the free upper-entry gradient is
(-exp(-i*z)*exp(i*z*s)^2,0), and i times the lower-entry gradient is
(0,exp(i*z)*exp(-i*z*s)^2). `sourceG5_actual_i_free_upper` and
`sourceG5_actual_i_free_lower` prove these identities using the actual
free-gradient representation of the endpoint derivative.

At zero potential and nu_n=n*pi, both source hypotheses hold exactly.
The two printed references coincide, and the first component of the
upper-entry error is -(-1)^n exp(2*pi*i*n*s). Its actual Fourier coefficient
at n has modulus one. `not_memlp_sourceG5PrintedUpperError_norms` proves
failure of the printed outer p=2 assertion; the inner exponent p'=2 is
also exactly the printed conjugate exponent. The majorant and eventual
majorant theorems propagate this obstruction to any full-matrix norm
dominating the component and show that deleting a finite head cannot
help. This is a literal-reference counterexample, not a failure of the
finite-p estimate after exchanging the two superscripts.

There is also a separate failure at p=infinity, p'=1, already established
by `ClassicalGradientInfinityCounterexample.lean`. The smooth period-one
source phi=(1,0) and nu_n=n*pi+i/(2*(abs(n)+1)) satisfy both displacement
conditions. A diagonal gradient component has unequal endpoint traces
and hence is not in Fourier l1, at every spectral index. Its free
reference is zero, so this obstruction survives the off-diagonal
correction. `sourceG5_triangular_coefficients` and
`sourceG5_not_eventually_fourier_l1` explicitly transfer it to the original
period-one H1 source. Multiplication by i does not change Fourier
summability. The proof's strict inequality p'>1+1/p also fails at this
endpoint, where both sides equal one.

The supported correction is upper e^- and lower e^+ in both displayed
references, with the outer range restricted to finite 2<=p<infinity.
`SourceLemmaG5.lean` now proves both corrected finite-p assertions for the
full gradient, uniformly on balls in the exact Chapter 5 source H1 norm.
`classicalHermitianGradientError_eq_correctedReference` identifies the
assembled operator with the actual gradient minus the explicit corrected
reference, and `classicalHermitianCorrectedFreeGradientMatrix_lattice`
checks the (-1)^n phase and signed waves in the second formula. The
Fourier coefficients are actual gradient-valued Bochner integrals, using
the induced operator norm from Hermitian potential directions to Hermitian
matrix operators. This proves the corrected statement; it does not
restore either refuted feature of the printed version.

## Lemma G.3: the epsilon range in the printed exponent

Source: dissertation, printed page 136. The wording "any epsilon > 0"
accompanies 1+epsilon <= q <= 2 and exponent (q-1-epsilon)/(1-epsilon).
For epsilon > 1 the q interval is empty. For epsilon = 1 its only possible
point is q=2, where the displayed exponent is 0/0. Thus the meaningful
nonempty range of the printed formula is 0 < epsilon < 1.

`sourceLemmaG3_fourier_decay` and `sourceLemmaG3_shiftedFree_decay` retain
that formula on this range, including q=1+epsilon and q=2. The theorems
`sourceLemmaG3_l2_decay` and `sourceLemmaG3_shiftedFree_l2_decay` state
O(1/|n|) at q=2 without any epsilon parameter, obtained by choosing the
regular value epsilon=1/2. They do not interpret the source's undefined
0/0 using Lean's totalized division. This is a parameter qualification,
not a counterexample to either decay conclusion.


## Lemma G.2: arbitrary-time first inequality under the integral H1 convention

Source: dissertation, printed page 135. This is a **norm-qualified** failure,
not a refutation of every possible interpretation of the unspecified interval
norm. Define the local H1 norm as the square root of the integral of the
squared magnitudes of both potential components and both derivatives.

For the smooth period-one constant potential phi=(1,0), t=1/4 and z=2*pi,
that norm is 1/2. The actual weighted Hermitian first Born operator norm is
1/(2*pi). The first displayed G.2 right side, using this local norm, equals
5/(16*pi), which is strictly smaller. `lemmaG2_firstBorn_integralNorm_counterexample`
proves the strict inequality, while `g2IntegralNormTestPotential_admissible`
checks smoothness, periodicity, and the nonzero spectral parameter. The exact
original oscillatory kernel is evaluated by
`oscillatoryIntegral_const_quarter_period`; no numerical approximation is used.

Consequently this local integral convention cannot validate the printed
first inequality for all nonnegative times. A different interval norm
convention or a change in the estimate would need separate justification.
We do not select such a correction here. The second, unit-interval remainder
bound **does hold** in this same integral H1 norm: it is independently proved
by `l2HermitianRemainder_le_unit_H1`, using a combined endpoint estimate and
G.1. Its factor 3/(2*abs(z)) and coefficient 1+norm(phi)_2 exp(norm(phi)_2)
are unchanged. The same unit-interval consequence is now also proved in
Chapter 5's exact periodic Fourier norm by `sourceLemmaG2_remainder_unit`,
using a constant-one comparison with the integral norm. That theorem does
not select a norm convention for the arbitrary-time local statement.

## The proof of Lemma F.2: a common-path coefficient and a real majorant

Source: dissertation, printed page 134, visually checked in the PDF.
These issues concern intermediate formulas in the proof. The analyticity
statement of F.2 is proved unchanged by identifying actual endpoint
integrals with the already constructed joint analytic primitive.

In (F.3), the common integral from tau_n to nu has coefficient 1/(2*i).
Both endpoint integrals contain that same common path. Averaging therefore
retains its full coefficient 1/i=-i; only the two short endpoint pieces
are halved. `appendixF_shared_path_normalization` proves the exact splitting
algebra, and `appendixF_half_coefficient_ne` proves that the printed half
coefficient differs whenever the common integral is nonzero. The actual
free endpoint average has value -i*nu+i*pi*n, checked nontrivially at n=0,
nu=i, where its value is 1.

The displayed majorant g_k(t)=sqrt(t+|epsilon_k|)/sqrt(t-|epsilon_k|) is
not a real-valued expression for 0<t<|epsilon_k|. It therefore cannot
justify the claimed estimate on all of [0,1] as written. Under Lean's
totalized real square root and division it is zero on that interval.
`appendixF_printed_majorant_counterexample` uses epsilon=i/2, t=1/4,
and w=sqrt(5/16): w^2=t^2-epsilon^2, the actual normalized quotient t/w
has strictly positive norm, while the printed majorant is zero. Thus no
finite constant repairs that pointwise bound under this interpretation.
The imaginary epsilon also avoids a real-parameter root singularity in
the example. An absolute value in the denominator and a treatment of the
moving singularity would be needed for a real-majorant repair; such a
repair is not used or claimed by the formalization.

The formal route constructs finite polygonal integrals, proves their
improper endpoint limits and agreement with admissible C1 curve integrals,
and identifies both endpoint values with the analytic primitive. This
supplies F.2 directly, including complex collapsed gaps.

## Lemma E.2: the neighborhood must meet the real space

Source: dissertation, printed page 131 (visually checked in the PDF).
E.2 calls U an open connected "neighborhood" without specifying its base
point. The proof begins near u in U intersect X_R, so that intersection
must be nonempty. If "neighborhood" means a neighborhood of a real point,
this is the intended condition, not a change to that interpretation.
Both applications in the dissertation use neighborhoods of real-type
potentials and satisfy it.

The reading as an arbitrary nonempty open connected complex domain is
false. `sourceLemmaE2_realSlice_condition_needed` proves the counterexample
X_R=R, X=C, U the ball of radius 1/2 about i, and f identically one.
U is open and connected and its real slice is empty, so f vanishes there
vacuously, but f(i)=1. Nonemptiness of U alone is insufficient.

`sourceLemmaE2` proves the identity with the necessary nonempty real slice
explicit. `sourceLemmaE2_of_real_point` gives the equivalent real-neighborhood
formulation. Neither theorem adds convexity or a contraction condition on
the real and imaginary projections. The general statement uses continuous
complexification coordinates and includes the source's Banach-space case.

## Lemma E.1: the cardinal product must omit the diagonal index

Source: dissertation, printed pages 130-131. The displayed interpolation
formula on page 130 (visually checked in the PDF) writes the product over
m in Z of (sigma_m-z)/(sigma_m-sigma_n). Its factor at m=n has denominator
zero. The residue calculation on page 131 explicitly uses m != n, and
solving that identity gives the omitted-index cardinal product.

`appendixE_all_index_cutoff_eq_zero` proves that every symmetric cutoff
containing n is zero if the all-index formula is interpreted using Lean's
totalized division. This cannot be treated as the intended cardinal
product. `tendsto_appendixEInterpolationKernel` instead proves convergence
of the literal omitted-index cutoffs. The kernel equals one at its own
root and zero at every other root, with the exact derivative normalization.

`sourceLemmaE1_literal` proves the resulting interpolation formula for
all 1 <= p < infinity, including p=1, with the printed circle-supremum
hypothesis. Both infinite operations are specified as symmetric cutoff
limits, as supplied by the source circle proof; no unconditional sum or
absolute convergence is asserted. A focused nonzero example reconstructs
sinc(0)=1 from the simple lattice with its zero-index root moved to i.

## Remark D.3: the subtracted linear term must be the complex sum

Source: dissertation, printed pages 126–127 (visually checked in the PDF).
D.1 defines `A = |sum_m a_m|`, `B = sum_m |a_m|^2`, and `S = sum_m |a_m|`.
D.3 then writes `|prod_m (1+a_m)-1-A| <= |A|^2 exp(S)/2 + B exp(S+S^2)`.
Literal reuse of D.1's nonnegative A in that subtraction is false.

`ProductEstimateNotation.lean` supplies the admissible integer sequence
`a_0=-1/4`, with all other terms zero. It is absolutely summable and every
coefficient has norm at most 1/2. Its product is 3/4, so the literal left
side is 1/2. The right side is `exp(1/4)/32 + exp(5/16)/16`, less than
9/32 since both exponentials are less than 3. The theorem
`printed_D3_absolute_linear_term_fails` verifies the contradiction in Lean.

Taking A to be the **complex sum** in D.3 gives the valid Taylor refinement.
`norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` in
`SignedProductEstimates.lean` proves that interpretation, retaining the
printed 1/2 and `B exp(S+S^2)` constants. The same module proves D.1 with
its printed absolute sum and both inequalities of D.2. No redefinition is
silently applied to the literal source statement.

## Appendix C.1: ordinary Hilbert transform is not an isomorphism

Source: dissertation, Lemma C.1, printed page 125. The operator is
`(Hx)_n = sum_{m != n} x_m/(m-n)`. The assertion that it is a Banach-space
isomorphism for every 1 < p < infinity is false already at p=2.

`HilbertKernelFactorization.lean` proves h(n)=t(n)+t(n-1), with t in ℓ²
and h(n)=-1/n (zero on the diagonal). For the finitely supported sequence
`a_N(k)=(-1)^k` on 0,...,N, `HilbertNotIsomorphism.lean` proves

```
||a_N||₂² = N+1
H a_N = t + (-1)^N shift_(N+1) t
||H a_N||₂ <= 2 ||t||₂.
```

Consequently `discreteHilbert_not_bounded_below` rules out every nonnegative
constant C satisfying `||a||₂ <= C ||Ha||₂` for all a. The theorem
`hilbertTransform_two_no_left_inverse` rules out any bounded linear left
inverse of the completed transform, and `hilbertTransform_two_ne_equiv`
rules out its equality with any continuous linear equivalence. A generic
version applies to any bounded operator agreeing with the printed formula
on finite inputs, so the obstruction is independent of the construction.

The correction is to assert boundedness, which `HilbertBoundedness.lean`
already proves for every 1 < p < infinity. Neither failure of injectivity
nor the corresponding obstruction at every other exponent is asserted here.
Existing library proofs never used the false invertibility assertion.
The source proof of Lemma C.2 uses only the boundedness part of C.1.
`ModifiedHilbert.lean` now proves C.2 with its full two-lattice hypotheses,
exact normalization, and uniform dependence on the specified norms.

## Theorem 1.1: unresolved printed height above two

The printed central box uses `(1+8‖φ‖ₚ)^p`. The Neumann criterion in
Corollary 3.3 is `(4p/H^(1/p)+1/H)‖φ‖ₚ < 1` at height H.
`PrintedHeight.lean` proves that the printed height satisfies this criterion
for all 1 ≤ p ≤ 2, extending the previous Hilbert-only result.

For p > 2 and M ≥ 1/(4p-8), `printed_height_neumann_bound_fails` proves
that the same criterion is strictly greater than one at H=(1+8M)^p.
Failure of a sufficient condition is not a spectral counterexample.
The literal general-exponent height remains unresolved, not disproved;
`(1+8pM)^p` is a proved alternative but does not complete the printed claim.
See [the spectral overview audit](coverage/SPECTRAL_OVERVIEW.md) for the
source-space counting and projection conclusions now proved for p ≤ 2.

## Lemma 26.2: sign of the higher Hamiltonian

Source: [dissertation, Lemma 26.2](https://janbernloehr.de/Download/fs16/diss.pdf#page=113).
The statement and proof contain the factor `(-1)^(m+1) 2^m H_(2m+1)`.
However, [Theorem 24.1, equation (5.4)](https://janbernloehr.de/Download/fs16/diss.pdf#page=107)
states `sum_n J_(n,k) = H_k / 2^(k-1)`. At `k = 2m+1` this gives

```
8^m sum_n J_(n,2m+1) = 2^m H_(2m+1).
```

The additional sign agrees at odd `m` and disagrees at even `m` unless
`H_(2m+1) = 0`. The repository retains the physical Hamiltonians from
Appendix H; it does not absorb this sign into their definition.

Formal results:

- `eight_pow_mul_tsum_realHigherActions` proves the positive trace equality
  on the real H^m source space.
- `printed_even_trace_identity_iff_zero` proves the precise obstruction
  to the printed equality at every even order.
- `classicalNLSHamiltonian_constant_one_five` independently checks the
  Appendix H recurrence: the constant real-type potential `(1,1)` has
  physical `H_5 = 2`.
- `sourceWeightedAction_summable_and_le_half_mass` proves absolute
  summability and the trace-consistent estimate
  `sum_n ⟨2nπ⟩^(2m) |I_n| ≤ C(P,m) ‖ψ‖²/2 + 2^m H_(2m+1)`, where
  `C(P,m) = (1+16π)^(2m) (1+P)^(4m)` and `P` is the norm of an exact
  π-normalized H¹ realization of the period-one source potential.
- `sourceWeightedAction_le_mass` weakens the half-mass factor to the
  full squared pair norm appearing in the printed remainder.

This establishes the corrected estimate and identifies the error in the
printed proof equality. It does not constitute a formal counterexample
to the entire printed inequality, whose positive remainder must also be
accounted for. The literal signed statement of Lemma 26.2 is not claimed
as a proved result.

## Lemma 27.2: corrected global coefficient and optional endpoint sharpening

Source: [dissertation, Lemma 27.2, page 116](https://janbernloehr.de/Download/fs16/diss.pdf#page=116).
At m=1 the printed conclusion is `H3 ≤ 2S+S²`, where
`S = sum_n ⟨2nπ⟩² I_n`. The final energy estimate used in its proof is
`H3 ≤ S+2M²`, with total action M. Even retaining the stronger available
estimate `H3 ≤ S-M+2M²`, the scalar conditions `0 ≤ M ≤ S` alone do not
imply the conclusion at all sizes.

`Lemma272EndpointArithmetic.lean` proves the precise limitation: the maximum
of `S-M+2M²` over `0 ≤ M ≤ S` is `max(S,2S²)`, and it is at most `2S+S²`
exactly when `S ≤ 2`. The scalar choice M=S=3 permits 18 while the target
is 15. No potential realizing these scalar data and energy is asserted.

`SourceH1EndpointActionBound.lean` proves the literal endpoint for S ≤ 2,
a mass-sensitive sufficient condition, and an unrestricted all-order variant
with twice the printed remainder. `SourceH1EndpointMomentCriterion.lean`
reduces the literal endpoint exactly to a lower bound on the real cubic
moments together with the nonnegative kinetic slack. Thus the missing
spectral input is explicit; the literal unrestricted assertion remains open.

The new `SourcePrimitivePowerCubicLowerBound.lean` proves
`π² I_n³ ≤ 4|γ_n|² R_n` from the actual nonnegative gap profile, with R_n
the cubic moment. Summing gives `H3 ≤ S-M+2M²-D-(π²/3)B`, where
`B = sum_n I_n³/|γ_n|²` is convergent and D is the kinetic slack.
The quotient has the continuous expression `|γ_n|⁴|rho_n|³`, including
closed gaps. This supplies a quantitative sufficient condition using only
actions and gaps, but does not yet prove the comparison needed for all
sources. The unrestricted literal endpoint therefore remains open.

The accepted formalization uses the proved corrected global statement
`sobolevOddHamiltonian_le_twice_weighted_action_remainder`, with twice
the printed remainder for all m ≥ 1. The exact printed bound remains
proved for m ≥ 2; the original unrestricted m=1 coefficient is optional
future work, not a blocker, and has not been disproved.
The downstream proof of Theorem 23.2(ii) treats m=1 directly through
Lemma 27.1 with d=√3. Its higher-order branch absorbs its explicit scalar
constants. Theorem 23.1 and Remark 23.3 inherit that proved bound, so no
exact downstream theorem needs a changed constant.

For comparison, [the cited paper, Lemma 16, page 27](https://arxiv.org/pdf/1403.1369#page=27)
uses the different remainder `(64π)^(2m) (1+M)^(2m-1) S^(2m-1)`.
Its coefficient does not disappear on substituting m=1. This comparison
does not establish a counterexample or justify silently replacing the
constant in the dissertation.

## Lemma 28.1: the final scalar comparison at n=N

Source: [dissertation, proof of Lemma 28.1, page 118](https://janbernloehr.de/Download/fs16/diss.pdf#page=118).
The displayed final comparison is

```
(n+N+2/5)/(n-N+3/10) ≤ 4/3+2N ≤ 2⟨N⟩,
```

under `n ≥ N`, with `⟨N⟩=1+N` for a nonnegative integer cutoff.
At `n=N=1`, the ratio is 8, exceeding `2⟨N⟩=4`.
The subsequent scalar comparison to `2048(1+‖φ‖H¹²)` also fails for
admissible scalar cutoff data: with `n=N=10` and `Q=‖φ‖H¹²=21/16`,
`N < 8Q ≤ N+1` holds, but

```
128 (n+N+2/5)/(n-N+3/10) = 8704 > 4736 = 2048(1+Q).
```

Formal results in `Lemma281BoundaryArithmetic.lean` prove both numerical
counterexamples. They also prove:

- for `n ≥ N+1`, the ratio is at most `2(N+1)`, recovering the scalar
  constant 2048 when `N ≤ 8Q`;
- for `n ≥ N`, the ratio is at most `8(N+1)`, giving an inclusive scalar
  constant 8192 under the same cutoff condition.

This audit concerns the printed scalar implication and supplies no
potential whose actual spectral factor violates the claimed norm bound.
The corrected scalar comparisons alone do not prove the spectral claim.

The actual real-source scalar bound is now proved independently in
`SourceH1ActionGapEstimate.lean`. The central product has squared norm at
most `8(N+1)`, using critical-point membership in ordered real gaps.
Combined with the exterior constant 128, this gives
`‖χ_n‖_gap ≤ 2048(1+P²)` even at the inclusive boundary. Public examples
recover the bound 4736 for the actual real gap factor at n=±10 under the
norm assumption above. This does not validate the false ratio chain.
The real-source version of Proposition 28.2 follows, with the stronger
constant 1536 (and hence the printed 4608).

The complex action estimate of Proposition 28.2 is now proved independently
in `SourceProposition28_2.lean`, on a connected L²-open neighborhood of the
entire real L² locus. It uses the real-type projection and uniform continuity
of the normalized actions; it does not rely on a complex version of the
false ratio chain.

The complex scalar gap-factor bound of Lemma 28.1 is now also proved
independently in `SourceLemma28_1.lean`, including the entire closed gap
and the inclusive cutoff. A sharper real constant 1024 provides room for
a uniform comparison to the real-type projection on finitely many gaps;
a separate uniform complex tail bound of 3 handles all distant gaps.
The neighborhood is connected and L²-open, contains the entire real L²
locus, and can be shared with Proposition 28.2. The actual complex bound
4736 at n=±10 and P²=21/16 is checked publicly. None of these results
validates the printed intermediate scalar comparison disproved above.
