# Section 21 ordered assertion comparison

The ordered Section 21 comparison covers 34 groups on printed pp. 96–98: 27 matched, five corrected and two contextual, with no partial or pending groups in this local ledger. It retains the actual primitive-power contours, physical H1 correction, common complex source neighborhood, uniform all-index/all-order gap bounds, negative cubic coefficient, absolute and locally uniform summation, original action frequency and complex bilinear Hessian. The opening sum binds the wrong dummy index; it is normalized directly. The four existing sign/algebra corrections are preserved. Qualifications concerning the original action image, the precise 2014 construction, Appendix G.2 and wider dissertation completeness remain. No new Lean proof or refutation is added.

Source: printed pp. 96–98, text lines 7963–8123. Line numbers count newline
characters and preserve form feeds. All three rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S21-001 | 7965–7966 | Historical inspiration and novelty attribution | contextual |
| S21-002 | 7967–7971 | Physical renormalization and real-analytic extension | corrected |
| S21-003 | 7972–7980 | Primitive-power moment definition and exact -1/pi normalization | matched |
| S21-004 | 7991–7991 | Finite source exponents above one and common construction | matched |
| S21-005 | 7993–7995 | Every moment analytic on a common source neighborhood | matched |
| S21-006 | 7997–7998 | All even moments vanish including order zero | matched |
| S21-007 | 8000–8003 | Uniform power-of-gap bound and collapsed-gap vanishing | matched |
| S21-008 | 8005–8006 | Real nonnegative moments and odd zero detection | matched |
| S21-009 | 8008–8009 | First moment equals actual action | matched |
| S21-010 | 8012–8014 | Joint primitive analyticity gives contour analyticity | matched |
| S21-011 | 8013–8016 | Analytic even-power continuation gives zero integral | matched |
| S21-012 | 8016–8016 | Uniform boundary supremum controls the power moments | matched |
| S21-013 | 8017–8017 | Real two-sided boundary values are signed arcosh | matched |
| S21-014 | 8018–8026 | Action integration by parts and primitive normalization shift | matched |
| S21-015 | 8029–8029 | Transition to the Hamiltonian formula | contextual |
| S21-016 | 8031–8036 | Equation 4.13 finite-gap Hamiltonian identity | corrected |
| S21-017 | 8038–8040 | Finite open-gap support and cubic analyticity | matched |
| S21-018 | 8042–8048 | Exterior cubic residue and enclosing counterclockwise circle | matched |
| S21-019 | 8050–8050 | Cube of the original additive normalization | corrected |
| S21-020 | 8052–8059 | Contour deformation and surviving first/third moments | matched |
| S21-021 | 8061–8068 | Combination into finite open-gap Hamiltonian sum | matched |
| S21-022 | 8079–8085 | Absolute locally uniform cubic sum and analytic limit | matched |
| S21-023 | 8086–8089 | Cubic sum equals the physical renormalization | matched |
| S21-024 | 8091–8091 | Real nonpositive Hamiltonian with zero only at zero | matched |
| S21-025 | 8093–8097 | Cubic moments have a locally bounded ell1 sequence via quartic gaps | matched |
| S21-026 | 8097–8098 | Convergence to the analytic extension | matched |
| S21-027 | 8098–8102 | Real cubic moments are nonnegative and detect open gaps | matched |
| S21-028 | 8102–8103 | Hamiltonian sign conclusion and exact source zero set | corrected |
| S21-029 | 8105–8105 | Theorem 18.3(i) follows from the source Hamiltonian extension | matched |
| S21-030 | 8105–8107 | Analytic action Hamiltonian on its original domain | matched |
| S21-031 | 8107–8111 | Sign and zero criterion on the nonnegative action-domain intersection | corrected |
| S21-032 | 8111–8112 | Action gradient recovers the retained frequency | matched |
| S21-033 | 8114–8117 | Hessian and frequency derivative at zero | matched |
| S21-034 | 8120–8120 | Strict local concavity by derivative continuity | matched |

## Compared passages

### S21-001: Historical inspiration and novelty attribution

- The historical inspiration and claim of novelty are contextual. The mathematical assertions are compared separately; no priority claim is formalized.

Contextual passage, outside the mathematical proof obligation.

### S21-002: Physical renormalization and real-analytic extension

- The physical H1 correction subtracts twice squared mass and the absolutely convergent weighted action sum. It is complex analytic near every real H1 source. H1 finite-gap density identifies it with the FL4 cubic-moment extension, which is analytic on a common neighborhood and real analytic on the entire real FL4 locus. The opening summation binds m while using n; the formal sum consistently binds n.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21HamiltonianData.physical_identity`
- `NLS.ZakharovShabat.SourceSection21HamiltonianData.real_analytic`
- `NLS.ZakharovShabat.sourceSobolevPhysicalCorrection`
- `NLS.ZakharovShabat.exists_sourceSobolevPhysicalCorrection_analytic_domain`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.renormalizedHamiltonian_eq_sobolevPhysicalCorrection`

The opening dummy index is normalized directly. The real H1 physical expression is identified with its FL4 extension; the constituent physical H1 terms are not assigned to every rough FL4 source.

### S21-003: Primitive-power moment definition and exact -1/pi normalization

- The actual primitive-power moment is -1/pi times the counterclockwise circle integral of the normalized primitive to the natural power m. The original Section21 package represents every signed n and every m, including zero, using one valid circle family and the same ambient primitive retained from Section19.

Public declarations:

- `NLS.ZakharovShabat.sourcePrimitivePowerCircle`
- `NLS.ZakharovShabat.SourceSection21MomentData.moment_contours`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-004: Finite source exponents above one and common construction

- For each finite p greater than one the moment atlas and common open connected source domain are constructed before any source, index or moment order. The entire real source locus remains in the domain.

Public declarations:

- `NLS.ZakharovShabat.sourceSection21_original_moments`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-005: Every moment analytic on a common source neighborhood

- Each actual moment is complex analytic on the common source neighborhood, with all signed indices and all natural powers sharing that neighborhood.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21MomentData.lemma21_1`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-006: All even moments vanish including order zero

- All even moments, including the zeroth moment, vanish at every complex source in the stated domain.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.moment_even`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-007: Uniform power-of-gap bound and collapsed-gap vanishing

- At each complex source one smaller neighborhood and one positive C give norm(R_n^m) <= C^m*norm(gamma_n)^(m+1), simultaneously for all signed n and natural m. Every collapsed complex gap kills every moment order.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21MomentData.locally_uniform`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.moment_of_collapsed`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-008: Real nonnegative moments and odd zero detection

- Every natural-order moment at a real source is real and nonnegative. Each odd-order moment vanishes exactly when the corresponding actual gap closes.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_moment_nonneg`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_odd_moment_eq_zero_iff`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-009: First moment equals actual action

- The first primitive-power moment equals the original complex spectral action throughout the common source domain.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.moment_one`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-010: Joint primitive analyticity gives contour analyticity

- The primitive has joint complex analyticity on the open moving-gap complement. Common fixed isolating circles lie in that joint domain, so parametric contour integration gives source analyticity of every power moment.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianDifferentialData.analytic`
- `NLS.ZakharovShabat.sourcePrimitivePowerCircle_analyticOnNhd`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-011: Analytic even-power continuation gives zero integral

- The selected-gap square has an analytic continuation through the selected gap. Raising that continuation to a natural power and applying the zero circle-integral theorem proves the even moments vanish.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.powerCircle_even_eq_zero`
- `NLS.ZakharovShabat.SourceSection19Data.square_analytic`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-012: Uniform boundary supremum controls the power moments

- One positive local constant bounds both sides of every gap by its actual gap norm. Integration of a boundary power supplies one additional gap-width factor, yielding the stated moment power bound uniformly in n and m.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.uniform_gap_bounds`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.norm_powerBoundaryIntegral_le`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-013: Real two-sided boundary values are signed arcosh

- The upper and lower real-gap boundary limits of the original normalized primitive are the positive and negative actual arcosh profile, respectively, including the endpoints.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.real_gap_boundary`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-014: Action integration by parts and primitive normalization shift

- Closed-circle integration by parts identifies -1/pi times the integral of F_n with the actual action circle. The same theorem can be instantiated at primitive normalization zero on that circle, giving the displayed identity for F_0 as well. The additive index shift is the original i*pi*n shift.

Public declarations:

- `NLS.ZakharovShabat.sourcePrimitivePowerCircle_one_eq_actionCircle`
- `NLS.ZakharovShabat.SourceSection19Data.index_shift`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-015: Transition to the Hamiltonian formula

- This sentence introduces the next result and adds no separate mathematical assertion.

Contextual passage, outside the mathematical proof obligation.

### S21-016: Equation 4.13 finite-gap Hamiltonian identity

- For every real finite-gap source, the physical finite-gap Hamiltonian minus twice squared mass and the actual weighted action sum equals -4/3 times the cubic-moment sum. The positive sign printed in equation 4.13 is corrected directly.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21MomentData.lemma21_2`

The recorded positive correction is used; historical refutations are preserved without adding witnesses.

### S21-017: Finite open-gap support and cubic analyticity

- Finite-gap means the set of indices with nonzero actual gaps is finite. The original primitive, and hence its cube, is analytic on the complement of precisely those open gaps; collapsed gaps have been filled.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.spectral_analytic`
- `NLS.ZakharovShabat.exists_sourceFiniteGap_contour_decomposition`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-018: Exterior cubic residue and enclosing counterclockwise circle

- For every sufficiently large positively oriented circle, the cubic integral equals (3*pi/4)*(H3-2*H1^2). Division by 2*pi*i gives the printed residue 3/(8*i). The threshold is positive and the contour encloses all open gaps.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceFullAbelian_hamiltonian_cube_contour_of_chart`

The printed residue coefficient 3/(8*i) is consistent with the existing exterior integral formula; no additional sign correction is introduced.

### S21-019: Cube of the original additive normalization

- The original normalization is F0=Fn-i*pi*n. Its cube has constant term +i*(pi*n)^3; the missing imaginary unit in the printed expansion is corrected. The term is constant in the spectral variable and contributes zero circle integral.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.cube_index_shift`

The recorded positive correction is used; historical refutations are preserved without adding witnesses.

### S21-020: Contour deformation and surviving first/third moments

- An exterior contour equals the finite sum of actual isolating-circle contours over open-gap indices. Expanding the cubic normalization leaves exactly pi*(3*(pi*n)^2*R_n^1-R_n^3), because orders zero and two vanish.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceFiniteGap_contour_decomposition`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.unshifted_cubic_circle`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-021: Combination into finite open-gap Hamiltonian sum

- Combining the exterior identity and the local cubic-circle contributions gives H3-2*H1^2 as the finite open-gap sum of weighted actions minus 4/3 cubic moments. Finite-support identities also identify these finite sums with their literal infinite sums.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.finiteGap_hamiltonian_eq_sum`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-022: Absolute locally uniform cubic sum and analytic limit

- The actual cubic series with coefficient -4/3 converges absolutely at every complex source and its symmetric partial sums converge locally uniformly on one common connected neighborhood. Its limit is complex analytic.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21HamiltonianData.proposition21_3`
- `NLS.ZakharovShabat.SourceSection21HamiltonianData.hamiltonian_hasSum`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-023: Cubic sum equals the physical renormalization

- The cubic series equals the original physical correction for every real H1 source, including the literal weighted action subtraction. On rougher FL4 sources the cubic series defines the extension; separate physical H1 energy terms are not asserted to exist there.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21HamiltonianData.physical_identity`

The identity of separate physical energy/mass/action terms is asserted on real H1. The actual cubic sum defines the extension on the common complex FL4 domain.

### S21-024: Real nonpositive Hamiltonian with zero only at zero

- On the entire real FL4 locus the actual cubic Hamiltonian is real and nonpositive, and it vanishes exactly at the zero source.

Public declarations:

- `NLS.ZakharovShabat.SourceSection21HamiltonianData.real_sign`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-025: Cubic moments have a locally bounded ell1 sequence via quartic gaps

- The cubic moment bound is quartic in the actual gap. The locally bounded ell4 gap sequence makes the cubic moments an actual locally bounded ell1 sequence; coefficient equality rules out the definition fallback on the common domain. Coordinate analyticity assembles a Banach analytic ell1 map.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.exists_cubicSequence_analytic`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-026: Convergence to the analytic extension

- Continuous linear summation of the analytic cubic ell1 map gives the analytic Hamiltonian. Continuous decreasing truncation tails yield locally uniform symmetric partial sums.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.exists_renormalizedHamiltonian_analytic`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-027: Real cubic moments are nonnegative and detect open gaps

- At every real source each cubic moment is real and nonnegative, and it vanishes exactly when its selected gap is closed. The strict positivity proof integrates the actual arcosh profile on an open gap.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_odd_moment_eq_zero_iff`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_moment_nonneg`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-028: Hamiltonian sign conclusion and exact source zero set

- Multiplication by the negative cubic coefficient makes the Hamiltonian nonpositive, correcting the proof text. Summability, positivity of any open-gap cubic moment, and the actual all-gaps-closed zero criterion give the exact source zero set.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_renormalizedHamiltonian_nonpos`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_renormalizedHamiltonian_eq_zero_iff`

The recorded positive correction is used; historical refutations are preserved without adding witnesses.

### S21-029: Theorem 18.3(i) follows from the source Hamiltonian extension

- The common original-family Proposition 21.3 package supplies the source-space extension used in Theorem 18.3(i).

Public declarations:

- `NLS.ZakharovShabat.SourceSection21HamiltonianData.proposition21_3`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-030: Analytic action Hamiltonian on its original domain

- The already chosen original frequency admits an analytic action Hamiltonian on a common connected open action domain. Its action recovery identifies the same source Hamiltonian. The retained domain contains all real-source actions and nonnegative summable actions; no extension to the whole nonnegative ell2 cone is inferred.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.exists_original_hamiltonian`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.analytic`

The action domain is the retained original action image, containing all real-source actions and the nonnegative ell1 cone. Neither the whole nonnegative ell2 cone nor global concavity is asserted.

### S21-031: Sign and zero criterion on the nonnegative action-domain intersection

- On the nonnegative part of the retained action domain, the same Hamiltonian is real and nonpositive and vanishes only at the zero action. This corrects the second nonnegative occurrence in the proof.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.sign`

The recorded positive correction is used; historical refutations are preserved without adding witnesses.

### S21-032: Action gradient recovers the retained frequency

- The actual action frequency is the scalar gradient of the chosen action Hamiltonian on its full retained action domain. Along the common complex source domain it equals the original Section20 moment frequency, coordinatewise and in ell2.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.gradient_eq`
- `NLS.ZakharovShabat.SourceSection21HamiltonianData.action_frequency_sequence`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

### S21-033: Hessian and frequency derivative at zero

- The derivative of the analytic gradient at zero is -2 times the ell2 identity. Under complex bilinear Hilbert duality this is the full scalar Hessian identity d2H(0)[v,w]=-2*sum(v_n*w_n), for arbitrary, including infinite-support, complex directions. The operator and bilinear formulations are identified through that duality.

Public declarations:

- `NLS.ZakharovShabat.sourceHamiltonian_gradient_derivative_and_hessian_zero`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.hessian_zero`

The scalar Hessian is complex bilinear; the identity-operator notation for the gradient derivative is interpreted through that explicit duality, not as a conjugate-linear Hessian.

### S21-034: Strict local concavity by derivative continuity

- Continuity of the analytic gradient derivative gives a positive-radius neighborhood in the action domain with Hessian real part bounded above by -norm(J)^2 on every real Hilbert direction. This proves the quantitative local strict concavity assertion; global concavity is not claimed.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.concavity`

The statement retains the common restricted source neighborhood, original mathematical objects and the domain qualifications stated above.

## Evidence and validation

The [original construction](../NLS/ZakharovShabat/SourceSection21Original.lean)
retains the same primitive, moment family, action Hamiltonian and frequency.
This review read 30 complete module bodies and resolved 46 declarations.
It reconciles the previous three named comparisons and their broad proof ranges
without replacing the historical corrections or refutation records. Reading
every transitive proof dependency again is not claimed. No new refutation was added.

The unchanged Lean snapshot reuses the successful full check at commit eda8d52513f52ce75d07b099cc67b1d3986d4523: 8,562 build jobs, 7,648 public examples and the transitive axiom audit of 44,637 NLS declarations, with 21 inherited warnings and zero new. This step changes only source-comparison documentation and its integrity record. Source hashes, all 46 declaration references, the current review index and local documentation links are checked again. These checks do not certify complete formalization.

Next: the ordered assertion comparison for Section 22.
