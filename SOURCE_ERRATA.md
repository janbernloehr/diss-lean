# Source discrepancies

## Unnumbered finite-gap regularity sentence: complex sources need a qualification

Source: dissertation, printed p. 21, immediately before Corollary 1.6.
The source defines finite-gap potentials by finitely many nonzero gaps,
then says they are smooth and real analytic. The following density
assertion explicitly concerns real type, but the regularity sentence
itself states no such restriction. The unrestricted complex reading is
false. This audit does not infer that the author intended the unrestricted
reading; it records the qualification needed when formalizing it.

For any finite p>1 take the original period-one source `phi=(u,0)` with

```
u_n = 1/(1+|n|),  n in Z.
```

The formal construction `roughTriangularSource hp hp1` lies in `CoeffPair p`
by the exact reciprocal Sobolev-weight summability theorem. It is not of
real type, since its second component is zero and its first coefficient
at index zero is one.

`TriangularPeriodicSpectrum.lean` works directly with the actual
coefficient-space operator and its original one-derivative domain.
For any triangular potential, `T=V*R_0` satisfies `T^2=0`, so the two-term
expression `R_0*(1+T)` supplies both inverse identities at every point
off the free lattice. The negative signed modes remain eigenvectors at
every point of the free lattice. Thus the entire periodic spectrum is
exactly `pi*Z`, with no smoothness or smallness assumption. Applying the
period-one source embedding gives `roughTriangularSource_spectrum`.
The singleton-strip criterion for the actual canonical endpoint labels
then proves `roughTriangularSource_finite_gap`: the set of nonzero
canonical indexed gaps is finite. Identifying every central label is
unnecessary for this literal finite-gap property.

The same coefficients are not in l1, by the exact harmonic threshold.
The Fourier coefficients of every smooth periodic function are in l1.
`roughTriangularCoefficients_no_smooth_representative` therefore excludes
every smooth period-one representative preserving the original Fourier
coefficients. `roughTriangularCoefficients_no_analytic_representative`
excludes every spatially real-analytic periodic representative as well.
`not_every_complex_finiteGap_source_smooth` explicitly negates the
unrestricted all-source assertion at every finite p>1.

These are complex counterexamples, not counterexamples to real-type
finite-gap regularity. `SourceFiniteGapSmoothRealization.lean` already
proves the coefficient-preserving smooth realization for real-type
finite-gap sources, and Corollary 1.6's real-type density remains valid.
`SourceFiniteGapAnalyticRealization.lean` now proves the real-type spatial
real-analyticity claim as well. Its theorem
`sourceFiniteGap_exists_analytic_representative` preserves period one and
every original Fourier coefficient at every finite p>1. The proof uses
the analytic finite-dimensional reconstruction, the same canonical gap
tail under translation, and bounded Sobolev evaluation of the original
physical Fourier sums. Thus the qualified real-type regularity assertion
is proved, while the unrestricted complex assertion remains refuted.
The free periodic spectrum of this rough complex example gives no height
violation; the separate dyadic construction below refutes the all-exponent
printed periodic height.

## Proposition I.4: reversed signs in the displayed Schur block

Source: dissertation, printed page 140, checked in the rendered PDF.
The proof displays Id-A+B*(Id+D)^(-1)*C. For the decomposition of
Id+T, the correct Schur block is Id+A-B*(Id+D)^(-1)*C, as in I.1.

Take A=D=0 and B=C=Id on C. The printed block is 2*Id and has nonzero
determinant. The full operator sends (x,y) to (x+y,x+y), so it is singular,
even though norm(D)=0<1. `sourceI4_printedSchur_false_positive` proves
this false positive, and `sourceI4_correctSchur_zero` proves that the
corrected block is zero. This is an error in the proof formula, not a
counterexample to Proposition I.4's generic local-invertibility statement.

The source domain is relatively open in the nonnegative sequence cone,
which includes zero and other boundary points. The new density argument
uses that relative topology and local analytic extensions of the original
cone map. Compactness is required only at cone parameters. No global
complex extension or ambient interior assumption has been inserted.
Derivative and local-inverse loci are independent of the extension atlas.

The current theorem supplies ambient complex local inverses on the original
weighted spaces, together with their left-inverse identity on the original
cone map, at all points of a relatively open dense locus. This now covers
every positive weight and every real Sobolev order at finite exponent.
The inverses now restrict to actual weighted real sequence spaces for all
these weights and exponents, with both real analytic inverse identities.
The real inverse locus is relatively open and dense from a real local
inverse seed; a differentiable real left inverse suffices under the
compactness hypothesis. Reality follows from the original cone values,
and the real inverse locus is independent of the extension atlas.

The real-analytic representation bridge is now proved.
`SourcePropositionI4RealAnalytic.lean` constructs local complex extensions
from actual real-analytic germs, identifies their derivatives with the
complexification of the original real derivatives, and proves the real
inverse conclusion for those original germs. The power-series construction
has a 2^n coefficient bound and retains at least half the radius. Thus I.4's
statement is covered with the usual real-neighborhood extension meaning of
analyticity and local diffeomorphism at cone boundary points; the density
conclusion uses the relative cone topology. This interpretation and the
weighting transport are not recorded as source errors. The displayed Schur
sign error above is unchanged.

## Lemma I.3: finite exponents and the cutoff convention

Source: dissertation, printed page 140, checked in the rendered PDF.
The statement is proved without a correction for every finite exponent
1<=p<infinity, including p=1. `Coeff.sourceLemmaI3` uses a symmetric head
|n|<=N and the complementary tail |n|>N, with N>=1. This complement equals
the existing boundary-retaining Fourier tail at N+1; the exact identity
and both signed boundary modes are checked. Enlarging a finite head gives
the required symmetric head, so the quantifier over all positive errors
is preserved.

The formal examples also check the hypotheses. The unit vectors are
pointwise bounded but not totally bounded, so the uniform-tail condition
cannot be dropped. At p=infinity the singleton containing the constant-one
sequence is compact, while every symmetric tail has norm at least one;
thus the finite-exponent restriction cannot be dropped. These are boundary
checks, not counterexamples to the printed statement.

The weighted theorem uses raw coefficients for pointwise boundedness and
the exact weighted norm for tails. The compact-operator consequence gives
small full output tails in operator norm, as needed at the start of I.4.
The relative-cone density argument and the displayed signs are audited above;
real inverse restriction remains open; weighted transport is now proved.

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

I.4's later displayed Schur formula has a separate sign error, audited above.

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

## Lemma G.3 proof: missing remainder hat in the derivative bound

Source: printed page 136, verified in the rendered PDF. After estimates for
`partial_t (M-E)`, the proof displays `||partial_t M||_lambda = O(1)` uniformly
in abs(lambda)>=1 and t in [0,1], on bounded H1 source sets. That displayed
line is false for M itself. At zero potential and time zero,

    partial_t M(0,z) = diag(-i*z, i*z),
    ||partial_t M(0,z)|| = abs(z).

`norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero` proves this
exact Hermitian operator norm for the actual fundamental matrix.
`sourceG3_printed_full_derivative_false` rules out the claimed uniform bound,
even for real spectral parameters and the singleton zero-potential set.
The exponential weight equals one there.

The estimate needed by the surrounding argument is for `M-E`.
`sourceLemmaG3_weighted_remainder_derivative` proves it on the exact original
periodic H1 source ball of radius M, with explicit constant
`4*(8+pi)*(2*M)*exp(4*(2*M))`, for every nonzero complex z and all t in [0,1].
This is a correction to an intermediate proof line. The stated remainder
conclusions of G.3 retain their existing proofs; the separate epsilon
qualification below also remains in force.


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

The new arbitrary-length calculation makes the obstruction quantitative.
For every t>0, the same potential at the real frequency z=pi/(2t) has local
integral norm sqrt(t) and actual weighted first Born norm 2t/pi. Therefore
any estimate B(t)/(2|z|) times this integral norm must have
B(t)>=2/sqrt(t). `lemmaG2_integralNorm_length_necessary` proves this, and
`lemmaG2_integralNorm_no_uniform_numerator` rules out a fixed numerator.

A proved correction candidate is now available:

    ||F(t,z)||_z <= sqrt(1/t+t)/|z| * ||phi||_{H1[0,t]},  t>0.

More generally, the same coefficient with t replaced by T bounds every
intermediate time in [0,T]. The zero-time operator vanishes.
`intervalHermitianFirstBornOperator_weighted_le_local_H1` and
`intervalHermitianFirstBornOperator_weighted_le_interval_H1` prove these
statements for genuine AC/H1 inputs in the Hermitian operator norm.
The sufficient numerator 2*sqrt(1/t+t) divided by the necessary 2/sqrt(t)
is sqrt(1+t^2), with right-hand limit one at zero; both the identity and
limit are proved. No finite-time optimality claim is made.

This correction has not been adopted as the source's intended statement.
The interval norm convention remains unresolved. The publisher's
[2014 reference page](https://ems.press/books/elm/205) requires a subscription;
its accessible metadata supplies no norm definition. The separate verified
unit-interval consequence remains unchanged.

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

## Theorem 1.1: printed height proved through four; all-exponent assertion refuted

Source: dissertation, printed p. 17 (statement), especially clauses (ii)
and (iii), and p. 27 (proof). The central box uses the original source
height `(1+8||phi||_p)^p`, and this box together with the quarter-pi disks
must contain every periodic eigenvalue.

`SourcePeriodicHeightCounterexample.lean` now proves a counterexample
for every integer P>=100000000. The theorem
`sourcePeriodicPrintedHeight_counterexample` supplies a single original
source psi with equal component norms and `||psi||<=1/16`, an actual
periodic spectral point `z=i*2^P`, and nonmembership in the union of the
printed-height box and high disks for **every** cutoff N. Thus no
neighborhood/cutoff pair can satisfy the printed exhaustion at this
source. `not_sourceTheorem1_1_printed_exhaustion` explicitly negates the
all-source exhaustion assertion at the concrete finite exponent 100000000.
This is an operator-spectrum counterexample, not merely failure of a
sufficient resolvent estimate. The threshold is sufficient, not optimized.
The behavior of each individual exponent between four and this threshold
is not determined by this result.

The construction and its proved constants are:

1. At J=2P, the upper real profile U is the sum, for j=2,...,J, of
   `(4*4^j)` times the tent on `[2^(-j),2^(1-j)]` minus its reflection
   across 1/2. `DyadicTentSum.lean` proves that its original lP coefficient
   norm is at most 640 and its weighted interaction
   `A=integral_0^1 U(x) exp(-2H*x) dx` at H=2^P is at least (P-2)/4.
2. `LowerDyadicTent.lean` puts a tent V of area one on `[1-epsilon,1]`,
   epsilon=2^(-2P). Its original mean is one. Uniform and quadratic-tail
   Fourier bounds, after removing the mean, give an lP coefficient norm
   at most nine. Its interaction
   `B=integral_0^1 V(x) exp(2H*x) dx` is at least
   `exp(2H(1-epsilon))`.
3. `OrderedDyadicSource.lean` proves coefficient/physical compatibility,
   ordered support, and positivity of A and B. The complex interaction
   primitives are iA and -iB. The exact monodromy normalization multiplies
   U by `kappa=-(exp(H)-1)^2/(A*B)`, placing iH in the actual periodic
   spectrum at every finite target exponent p>=2.
4. `DyadicNormalizationBound.lean` proves
   `abs(kappa)<=12/(P-2)`. Indeed the numerator is at most exp(2H),
   the lower interaction cancels that exponential up to
   `exp(2H*epsilon)<=exp(1)<3`, and A>=(P-2)/4.
5. Diagonal similarity balances the component norms while preserving
   the actual spectral point. The original pair norm is exactly
   `2^(1/P) sqrt(abs(kappa)*norm(U_hat)*norm(V_hat))`, hence at most
   `2 sqrt(69120/(P-2))`. For P>=100000000 this is at most 1/16.
   The unchanged printed height is therefore at most `(3/2)^P<2^P`.
   The imaginary part also exceeds pi/4, excluding every disk centered
   on the real free lattice, independently of N.

The original finite-exponent pair norm is the P-th root of the combined
component coefficient energies from equation (1.2). The construction does
not replace it by a maximum norm or a physical-space norm. It uses genuine
continuous piecewise linear profiles and their original Fourier integrals;
no numerical truncation or Galerkin spectral assertion is involved.
The proof uses the existing actual monodromy/discriminant correspondence,
exponent compatibility, and domain-preserving diagonal similarity.

The verified positive results remain valid. `PrintedHeight.lean` gives
the printed height through p=2; `RefinedReciprocalNorm.lean` and
`PrintedHeightFour.lean` extend it through p=4.
`exists_source_periodicCounting_printed_height_up_to_four` in
`SourcePrintedHeightFourCounting.lean` retains the common open convex
source neighborhood, all larger cutoffs, central and distant algebraic
multiplicities, periodic/antiperiodic parity, spectral exhaustion, and
actual analytic moving rectangular projections for 1<=p<=4.
`periodicSpectrum_im_eq_zero_of_realType` retains spectral reality at all
finite exponents. The counterexample sources cannot be of real type.
Equal component norms alone do not imply real type.

At every finite exponent the height-N counting theorem
`exists_uniform_periodicCountingData` still gives one common neighborhood,
all sufficiently large cutoffs, full multiplicities and parity, and
exhaustion. Thus this erratum concerns the specified quantitative height,
not spectral discreteness or the existence of a central counting box.
The known sufficient height `(1+8pM)^p` and the component-product height
`(1+8p sqrt(norm(phi_1)*norm(phi_2)))^p` are separate proved alternatives.
No correction is adopted here.

Earlier estimates remain useful but are logically weaker evidence:
`reciprocal_power_coefficient_four_fails_at_five` refutes a sufficient
power-sum test, and `FreeResolventHeightNecessity.lean` rules out a
uniform free lp-to-l1 resolvent coefficient. Neither alone was a spectral
counterexample. The actual dyadic source above resolves the all-exponent
printed-height obligation negatively.

The necessary exponent dependence is now quantified in
`SourcePeriodicHeightNecessity.lean`. For every integer P>=3, any
nonnegative C_P giving the original-source strip bound
`abs(Im z)<=(1+C_P*norm(psi))^P` for all source spectra must satisfy
`P-2<=276480*C_P^2`. The same conclusion holds if only exhaustion by
a source-dependent central box and the high disks is required.
`sourcePeriodicHeightCoefficient_necessary` and
`sourcePeriodicCountingHeightCoefficient_necessary` prove these two
statements. The corresponding `not_exists_uniform_sourcePeriodic...`
theorems exclude every fixed nonnegative coefficient for all integer
exponents. These bounds follow from the actual balanced dyadic family;
they are not free-resolvent norm obstructions.

`SourcePeriodicExplicitHeight.lean` proves the separate proposed
correction `(1+8pM)^p` in the original source norm, for all finite p>=1.
`mem_resolventSet_of_sourcePeriodicExplicitHeight` includes both horizontal
edges and the entire closed exterior strip.
`sourcePeriodicSpectrum_abs_im_lt_explicit_height` gives strict exclusion
for spectral points. `sourceTheorem1_1_proposed_height` retains one open
convex source neighborhood, every larger cutoff, full central and distant
counting data and parity, central multiplicity 4N+2, exhaustion, equality
with the central cluster projection, and analyticity of the actual moving
rectangular integral. It specializes a general source counting transfer
for any nonnegative coefficient with a proved resolvent bound; the
existing printed-height API remains the coefficient-eight specialization.
No replacement has been adopted. The necessary square-root growth and
sufficient linear growth do not establish an optimal growth rate.

## Theorem 1.4: the all-p printed boundary height is false

Source: dissertation, printed p. 20 (statement) and p. 32 (proof).
The printed box has height `(1+8||phi||_p)^p` in the original period-one
source norm. Clause (iii) asserts that the box and quarter-pi disks contain
all Dirichlet and Neumann eigenvalues. Lean now proves a finite Fourier
counterexample to this assertion, already at p=1024.

For any natural P>=1024, put H=2^P and define

```
S = {n in Z : H <= n < 2^P*H},
A = sum_{n in S} pi*n/(H^2+(pi*n)^2),
a = 1/A,
u_n = a for n in S, u_{-n} = -a for n in S, and zero otherwise.
phi = (u,0), with u(t) = sum_n u_n exp(2*pi*i*n*t).
```

The following chain is verified with the original source and spectrum:

1. The classical triangular equation at z=iH has initial vector (1,1).
   Its solution satisfies the Dirichlet endpoint condition when
   `sum_n u_n/(H-i*pi*n)=2i`. The finite ordinary characteristic agrees
   with the classical one at every finite p>1. Thus this equation gives
   membership in the actual `BoundaryCondition.spectrum .dirichlet` of
   `periodOneBoundaryPotential`; no substitute spectrum is introduced.
2. Pairing the positive and negative coefficients gives `2i*a*A=2i`.
   On n>=H the kernel is at least 1/(6n), so each dyadic block contributes
   at least 1/12. There are P such blocks, hence A>=P/12>0.
3. There are at most 8^P signed coefficients, each of magnitude a. The
   original coefficient-pair norm at exponent P is therefore at most
   `8a <= 96/P <= 3/32`. No reflected-potential norm appears in this bound.
4. The printed height is at most `(7/4)^P < 2^P = H`. Also H>=2>pi/4,
   so iH belongs to none of the quarter-pi disks centered on the real
   free frequencies. This holds for every cutoff N, however large.

The files `TriangularFourierBoundary.lean`, `TriangularOddFourier.lean`,
`TriangularDyadicKernel.lean`, and `TriangularNormalizedBand.lean` prove
these ingredients without enumerating the finite band.
`SourceBoundaryHeightCounterexample.lean` supplies
`sourceBoundaryPrintedHeight_counterexample` for every natural P>=1024
and every N. `not_sourceTheorem1_4_printed_exhaustion` explicitly negates
`forall phi, exists N, spectrum subset printed-box union high-disks` at
p=1024. Since a neighborhood of phi contains phi itself, this also refutes
the stronger neighborhood assertion in the source. The exponent threshold
1024 is a convenient verified choice, not an optimality claim.

The proof on p. 32 applies periodic localization to the reflected
potential `phi^dir`. Lemma 4.3 supplies boundedness of the extension;
the available general estimate includes `intervalExtensionBound hp1 hp`.
Dropping that dependence and using the original source norm does not
follow from the periodic result. The new counterexample settles failure
of the printed all-p statement itself, beyond this gap in the proof.

At p=2 the extension is contractive, and `sourceTheorem1_4_two` still
proves every clause with the exact printed height and original norm.
The finite-p discreteness, reality, height-N counts, and Theorem 1.5's
locally uniform full-sequence bounds remain valid. This counterexample
concerns complex triangular sources and makes no claim against the
real-type spectrum. It does not refute Theorem 1.1's periodic height,
which remains proved through p=4 and is now separately refuted as an
all-exponent assertion by the dyadic construction above. No replacement
boundary height is adopted; other exponents not covered here remain to
be investigated.

### Proved proposed correction and an obstruction to every fixed constant

`SourceBoundaryExplicitHeight.lean` supplies a separate all-p statement
with height

```
H_p(M) = (1 + 8*p*E_p*M)^p,
E_p = BoundaryCondition.intervalExtensionBound hp1 hp
    = 2 * Fourier.halfIntervalBound hp1 hp.
```

E_p is the finite positive bound constructed from the half-interval map
and its discrete Hilbert-transform estimate. It depends on p, not the
source potential. The input M is a bound for the original source norm;
`norm_periodOneBoundaryPotential_le` proves the reflected maximum pair
norm is at most E_p*M. No inverse change-of-pair-norm factor is needed.
The explicit periodic Neumann estimate then gives the actual reflected
resolvent and both ordinary boundary resolvents on `|Im z|>=H_p(M)`.
Every boundary eigenvalue lies strictly inside this strip.

`sourceTheorem1_4_proposed_height` proves both central counts 2N+1,
simple high-disk roots, and exhaustion on one open convex source
neighborhood containing the base source and zero, for every larger cutoff.
The old printed-height transfer theorem is preserved as the coefficient-eight
specialization of `exists_source_boundaryCounting_height_of_bound`.
This is a proved proposed correction, not a proof of the false source
formula or an adopted replacement for it. No optimality is asserted.

There is also a stronger necessary condition. For every integer P>1,
`triangular_height_gt_coefficient` puts the earlier family's eigenvalue
above `(1+C*||phi||_P)^P` whenever C>=0 and 96*C<P.
`sourceBoundaryCountingHeightCoefficient_necessary` proves P<=96*C for
any coefficient that supplies exhaustion for every source at this
exponent, even if each source has its own cutoff.
`not_exists_uniform_sourceBoundaryCountingHeightCoefficient` therefore
rules out every fixed nonnegative replacement for eight at all exponents.
The corresponding global-strip necessity is proved separately. This is
an actual spectral obstruction, and it does not apply to the periodic
spectrum in Theorem 1.1.

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

## Section 2: norm convergence at the infinity endpoint

Source: dissertation, printed page 21, checked in the rendered PDF.
After defining Fourier-Lebesgue spaces for every real s and 1<=p<=infinity,
the source asserts that the Fourier series converges in the same norm.
There is no finite-exponent restriction on that sentence. It is false at
p=infinity.

`InfinityTruncation.lean` proves the exact endpoint criterion: finite
Fourier sums converge in a positive weighted infinity norm if and only if
the weighted coefficients tend to zero outside finite sets. For every
positive weight w, the coefficients 1/w(n) have norm one and every finite
truncation has error exactly one. Thus universal convergence holds exactly
at finite Banach exponents, including p=1.

`SourceSectionTwoConvergence.lean` realizes this counterexample as an actual
period-two tempered distribution with coefficients 1/(1+abs(n))^s for every
real s. Its Fourier sums still converge distributionally. Period two is a
valid instance of the source's arbitrary positive period, so this is an
actual source counterexample, not merely a defect in a coefficient model.

The valid alternatives are norm convergence at finite exponents; norm
convergence for weighted c0 inputs at infinity; or distributional convergence
at every Banach exponent. The last is already proved on the full real Sobolev
scale and remains unchanged. See `coverage/SECTION_2.md` for the precise scope;
the remaining Section 2 duality and gradient assertions are still being audited.

## Section 2: missing frequency reversal in scalar bilinear duality

Source: dissertation, printed pages 21–22, checked in the rendered PDF.
The scalar coefficients use the usual negative Fourier wave in their
extraction. On page 22 the source defines the unconjugated pairing as
sum_n u_n*v_n and calls it a natural extension of distributional action.
The corresponding physical pairing instead uses sum_n u_n*v_(-n).

`SourceSectionTwoPairingAudit.lean` gives an exact smooth period-one
counterexample: u=v=exp(2*pi*i*x). Its actual normalized coefficients have
only the value one at index one. The printed same-index sum is one, whereas
the physical integral of u*v over the unit period is zero. The theorem
`sourceSectionTwo_printed_bilinear_pairing_false` refutes the assertion even
when both inputs are smooth and periodic.

`ArbitraryPeriodBilinearParseval.lean` proves the corrected identity for
all positive periods L and all square-integrable physical inputs, retaining
the factor 1/L. Reversal may be placed in either factor by reindexing.
It separately preserves the ordinary sesquilinear formula with equal
indices and complex conjugation. Physical conjugation reverses the Fourier
index, which explains why the corrected bilinear formula is consistent
with the source's relation to the sesquilinear product.

`SobolevBilinearPairing.lean` constructs the corrected bounded bilinear map
on FL^(s,p) times FL^(-s,q), with absolute convergence and the exact product
of the original norms for every real s and every conjugate Banach pair,
including (1,infinity) and (infinity,1). `SobolevDistributionPairing.lean`
identifies it with normalized actual distributional action on Schwartz
periodizations. `SmoothPeriodicTestLift.lean` lifts every smooth period-two
test without an additional growth hypothesis, and
`SmoothPeriodicDistributionPairing.lean` proves the action identity for all
such tests and arbitrary periodic distributions with the stated coefficients.

Abstract same-index `Coeff.dualPairing` remains valid as coefficient
duality. Its physical interpretation inserts frequency reflection, as the
existing source-gradient constructions already do. The source's signed
pair basis does not remove this discrepancy in its preceding scalar formula.
Arbitrary-positive-period distribution transport is now proved in
`ArbitraryPeriodDistribution.lean` and `ArbitraryPeriodDistributionPairing.lean`.
The normalized coefficient tests periodize to (1/L) times the original
negative Fourier wave; the zero-mode window periodizes to exactly 1/L.
Inverse dilation preserves each raw coefficient, gives unique weighted
Fourier representation, and proves the corrected smooth-test pairing for
every positive period, every real regularity and both conjugate endpoints.
Full scalar duality, including p=1, is now proved with the corrected pairing
in `SobolevFullDuality.lean`; its representative has the exact operator norm.
`SobolevScalarGradient.lean` proves analytic scalar gradients and the Hessian
identity. `SobolevPairGradient.lean` now proves unique analytic pair-gradient
representation for every finite source exponent, including p=1, in the
original pair norms. The infinity-source restriction is detailed below.


## Section 2 gradient paragraph: the source exponent must remain finite

Printed page 21 explicitly restricts the scalar full-dual identification to
1<=p<infinity. That statement is proved, including p=1. The gradient
paragraph on page 22 does not repeat the restriction after introducing
pair spaces at all exponents. If that paragraph is read as asserting a
coefficient gradient for arbitrary analytic functionals on an infinity
source space, the extension is false.

`InfinityDuality.lean` constructs a bounded complex functional on linfinity
that annihilates every finitely supported sequence and is nonzero on the
constant-one sequence. The construction separates the constant sequence
from the closed finite-support subspace by Hahn-Banach on the quotient.
Every l1 coefficient representative would have all coefficients zero,
contradicting the nonzero value. The functional is everywhere analytic and
has no coefficient-gradient representation at any base point.
`Coeff.dualPairing_surjective_iff` proves the exact source-exponent scope:
full coefficient representation is onto the continuous dual if and only if
the source exponent is finite.

`SobolevInfinityDuality.lean` proves the obstruction at every real Sobolev
order and for the exact source weighted infinity pair norm
sup_n w(n)(|a(n)|+|b(n)|). It uses the corrected physical pairing, so changing
the erroneous scalar frequency convention does not remove this obstruction.
The first-component signed-frequency conversion preserves the pairing.

The positive statement is retained in full at finite source exponents.
`SobolevPairGradient.lean` proves unique bounded linear recovery and analytic
pair gradients in both the finite conjugate norm and the separate infinity
pair norm required when p=1. Equal endpoint components have exactly twice
the scalar norm; no maximum-norm replacement is made.

Consequently, the automatic Poisson-regularity sentence at the end of page
22 needs a finite-source restriction for each analytic functional, or an
additional assumption that an infinity-source differential is represented
by the required coefficient gradient. Analyticity alone cannot imply that
assumption. The positive interior statement is now proved by
`SobolevCommonBracket.lean`: full gradients give an absolutely convergent,
analytic bracket on the entire common-state intersection for finite
conjugate source exponents and every real Sobolev order. The intersection
represents the same actual distribution pair on every positive period.
`SobolevEndpointBivector.lean` proves bounded, absolutely convergent pairing
in the original endpoint pair norms when represented gradients are supplied.
Thus the bracket remains valid on these regular functionals.
`SobolevSourceCompatibility.lean` now proves agreement with the existing
physical bracket on the order-zero finite-conjugate overlap.
`SobolevBracketSwap.lean` proves antisymmetry after exchanging the actual
ambient domains and shared state, and both product rules are available.
`SobolevZeroBracket.lean` proves Jacobi on the order-zero Hilbert domain.
These results do not claim closure under nested brackets on every reciprocal
Sobolev intersection or remove the infinity-source obstruction.


## Section 2 sesquilinear convention: the original same-index formula is retained

The scalar discrepancy above concerns the unconjugated physical product.
The printed sesquilinear sum with equal indices is valid.
`SobolevSesquilinearPairing.lean` proves this distinction for all real orders
and both conjugate endpoints: physical conjugation conjugates and reverses
coefficients, so applying it in the second factor of the corrected bilinear
pairing gives the same-index sesquilinear sum.

`SobolevPairSesquilinear.lean` retains the original finite pair norms and
the separate frequencywise sum-norm infinity space in both endpoint
orientations, with constant-one bounds. The full scalar sesquilinear Riesz
map in `SobolevSesquilinearDuality.lean` is conjugate linear in the functional,
not complex linear. This agrees with linearity of the product in its first
argument and conjugate linearity in its second. The previous bilinear
gradient convention is unchanged. The infinity-source analytic obstruction
is also proved in the sesquilinear convention.

The smooth-test distributional identity and normalized L2 integral formula
hold at every positive period in `SobolevSesquilinearDistributionPairing.lean`.
The broader locally integrable-function action is now proved separately in
`PeriodicL1Functional.lean`, `PeriodicL1Pairing.lean`, and
`PeriodicL1Distribution.lean`. These use only interval integrability of the
input and smoothness and periodicity of the test, retaining the exact 1/L
normalization. The unique actual periodic distribution has the normalized
physical Fourier coefficients, and the opposite-index product series is
absolutely convergent. This closes the page-21 normalized action obligation
without inferring it from the L2 special case. The source qualifications
above remain unchanged.

## Proposition 3.1: full period-two scope and the same printed-height discrepancy

Printed page 23 states Proposition 3.1 for every period-two potential at
all finite exponents. Its central box repeats Theorem 1.1's height
`(1+8*norm(phi))^p`. `PeriodTwoPrintedHeightCounting.lean` now proves the
unchanged height and all counts on the entire period-two source space for
1<=p<=4, using the original component-sum norm. It does not assume even
support; the period-one parity clauses are conditional.

`Proposition3_1.lean` assembles the statement and transfers the existing
counterexample through the isometric period-one pair embedding. The
result `proposition3_1_printed_height_counterexample` preserves the norm
bound 1/16, equal component norms, even support, and the actual escaped
spectral point for every cutoff. `not_proposition3_1_all_p` negates all
printed clauses at once at exponent 100000000 through the failed
exhaustion clause. Consequently Proposition 3.1 cannot be certified as
printed for every finite p. Discreteness and real-type reality still hold
at every finite p, as does the separate height-N counting theorem. No
proposed height correction is adopted.

## Lemma 3.2(ii): the original p-to-one pair norm bound is false

Printed pages 23–24 use the source component-sum norm for both the p input
and l1 output, while the proof first estimates each component separately.
Combining those component estimates requires the factor 2^(1-1/p).
The pre-existing `HeightResolvent.lean` theorem explicitly uses the
maximum norm on pairs and remains valid in that norm.

`SourceFreeResolventCounterexample.lean` supplies an actual free-resolvent
counterexample in the original norms at p=2 and lambda=i/10000. Each input
component has only its zero Fourier coefficient, equal to one. The input
norm is sqrt(2), the output norm is 20000, and the printed bound
8/sqrt(abs(Im(lambda)))+1/abs(Im(lambda)) is exactly 10800. Since
20000/sqrt(2)>10800, the printed operator inequality fails. This uses
smooth finite data and a nonreal parameter off the free lattice; it is
neither an infinity-endpoint issue nor a failure merely of a proof estimate.

`PairComponentHolder.lean` proves the component factor and its attainment
by equal components. `SourceFreeResolvent.lean` proves the full corrected
height estimate with that factor, as well as the operator lower bound
2^(1-1/p)/abs(lambda) from the two zero modes. At p=1 the original printed
height bound still holds. No replacement is silently adopted for the
false general assertion.

Clauses (i) and (iii) are valid in the original norms: compactness on l1
is proved by conjugating the actual free resolvent, and the strip estimate
even holds with 4p/r in place of 8p/r. The downstream Corollary 3.3 region
has now been verified in the original norms in `SourceCorollary3_3.lean`.
The contractive conversion of the original potential norm implies the
valid maximum-product Neumann condition with exactly the printed
numerical region. `SourceResolvent.lean` transports the actual inverse,
its two identities, compactness, analyticity, and spectrum to the original
base and one-derivative domain norms. Thus Corollary 3.3 survives the
failure of Lemma 3.2(ii); no extra component factor is needed in its
sufficient region. Nonzero imaginary part is explicit, as required for
the finite denominators in the printed expression.
