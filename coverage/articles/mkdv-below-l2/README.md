# mKdV below L² — initial private verification step

Status: **main theorems not yet verified**. The first private step checked four
classical/Fourier translation lemmas. The second step adds the physical
Birkhoff input adapter and absolute convergence of the H₄ candidate moment sum
for 1<p≤3. See [the current progress record](PROGRESS.md).

The user approved separate worktrees on 2026-11-02. Work is now on
`articles/mkdv-below-l2`, based on `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`.
The canonical main checkout and its compiled dependencies remain unchanged.

## Pinned source

Kappeler–Molnar, *On the wellposedness of the defocusing mKdV equation below L²*,
[arXiv:1606.07052v1](https://arxiv.org/abs/1606.07052v1),
[PDF](https://arxiv.org/pdf/1606.07052v1), downloaded 2026-11-02.
33 PDF pages; printed page numbers equal PDF page numbers.
SHA-256: `7ac1baa898365f4a556aec4d2e3182e82a9dbe782d8a183114ae81acb486e8c1`.
The PDF itself displays November 14, 2021 (including creation metadata), although
its arXiv watermark and requested version are v1, 22 June 2016. The hash pins the
actual served bytes; no claim of byte identity with a 2016 download is made.
PDF/text are scratch files at `work/source/1606.07052v1.{pdf,txt}`, outside
candidate tracked sources.

## Main statements and quantifiers

All spaces below are on T = R/Z; n ranges over Z. FL^p is the space of real
periodic distributions with norm equal to the ℓ^p norm of their Fourier
coefficients, not the distribution weak topology. FL_c^p is its complex pair
space, FL_r^p the conjugate pair locus. E_r^p is the real diagonal (u,u).
Sequence weights are (1+|n|)^s; compare any library weight by equivalence and
track normalizations before transporting physical assertions.

* **Theorem 1.1, p. 3.** For each finite p>2, the renormalized equation (2)
  is locally C⁰ wellposed on all real FL^p and globally C⁰ wellposed on a
  neighborhood of zero. Precisely, for each w there exist a neighborhood U
  of w and T>0 working for every v in U, with continuous solution map
  U → C([-T,T],FL^p) in the uniform trajectory norm. For the global clause,
  choose one neighborhood U₀ first, then every T>0 admits a continuous
  trajectory map on that U₀. Solutions have the smooth approximation meaning
  on p. 2: every smooth sequence converging to the datum has pointwise-in-time
  convergence to the same continuous curve. The original equation's solution
  map has no continuous extension at any datum of FL^p outside L².
  Corollary 7.2(iii), p. 30, explicitly strengthens/specifies this for every
  fixed t>0; a trajectory obstruction alone will not cover that claim.
* **Theorem 1.2, p. 5.** For every finite p≥2 there is a complex open
  neighborhood W_p of FL_r^p and an analytic map Φ_p: W_p → ℓ_c^p, fixing
  zero, real analytic and canonical, agreeing with Φ_q on common domains
  for every finite q≥2. On the real locus it is injective, a local
  diffeomorphism at every point, and has open dense image in ℓ_r^p.
  At p=2 it is the accepted Hilbert Birkhoff map and is onto, hence a
  bi-real analytic diffeomorphism. The family and cross-exponent agreement
  must be constructed together, not separately assumed.
* **Theorem 1.3, p. 6.** One physical normalized H₄ frequency map is defined
  on FL_r² with values in the intersection of ℓ^(-1,r), r>1, and is real
  analytic into each such target. For each finite p>2 it has a real analytic
  extension on FL_r^p with values in complex ℓ^(-1,p/2). Its refined remainder
  satisfies ω_n^(4)* + 12πn I_n = n(a_n+b_n), where a is ℓ^(p/3) and b
  belongs to every ℓ^r, r>1, with estimates locally uniform in the potential.
  When p<3 the ℓ^(p/3) term has exponent below one: do not replace its
  summability statement with a Banach-space hypothesis. Retain n=0 in
  the actual formula; dividing by n needs a separate zero-mode statement.

## Physical conventions

Equation (1): u_t = -u_xxx + 6u²u_x. Equation (2):
u_t = -u_xxx + 6(u²-M)u_x, M = ∫₀¹u²dx, conserved in time.
Fourier synthesis is ∑ a_n exp(2πinx); coefficients use exp(-2πinx).
The original-to-renormalized translation is v(t,x)=u(t,x-6Mt).
Its inverse uses x+6Mt. These signs directly satisfy equations (1)–(2);
we use this corrected sign for the conversion discussed on p. 29.
The physical coefficient multiplier is exp(-12πinMt), and its inverse
is exp(+12πinMt).

On the action side, H₁ = ∑ I_n and H₂ = ∑ 2πn I_n.
The normalization is ω_n^(4)* = ∂_{I_n}H₄ -(2πn)³ -6H₂ -12πnH₁,
not the dNLS H₃ frequency normalization. On E_r^p, H₂ vanishes where
classically defined, and ω_n^# = (2πn)³ + ω_n^(4)*. H₄ is scaled relative
to the accepted reference as explained on p. 5; retain the (-i)^(n+1)
scaling for hierarchy Hamiltonians n≥2.

## Checked new declarations

`NLS/Articles/MKdVBelowL2/SmoothRenormalization.lean` proves:

* `hasDerivAt_renormalizing_translation`: the actual time-space derivative
  of an original smooth solution, evaluated along (t,x-6Mt), gives exactly
  -u_xxx+6(u²-M)u_x.
* `hasDerivAt_original_translation`: the inverse chain rule gives exactly
  the original velocity along (t,x+6Mt).

The derivative assumptions are explicit pointwise classical hypotheses.
These are local calculus lemmas; M is an arbitrary fixed real parameter.
Neither conservation nor identification of M with the integral is silently
included. Spatial derivative transport and mass conservation remain necessary
to package a full classical-solution equivalence.

`NLS/Articles/MKdVBelowL2/TranslationFourier.lean` proves:

* `coefficient_renormalizing_translation`;
* `coefficient_original_translation`.

These identify the actual period-one Fourier integrals of synthesized ℓ¹
functions under the two physical translations. They reuse
`NLS.Fourier.periodOneCoefficient_translated_synthesis`; they do not assume
that a Birkhoff rotation is physical translation. Time-dependent smooth
profiles can instantiate the identity at each time. Extending this identity
as an operator on real FL^p distributions remains separate work.

## Existing proofs inspected and proposed reuse

* `NLS/Fourier/PeriodicFourierLebesgueSpace.lean`: original smooth-test
  distributions, coefficient isometry, finite-p Fourier truncation.
  `PeriodicFourierLebesgueStrictness.lean` proves actual distributions in
  FL^p outside FL². Its complex witness alone is not the required real datum.
* `NLS/Fourier/SpatialTranslation.lean`: exact period-one physical Fourier
  translation; used directly. `CircleTranslation.lean` concerns period two
  and actual L² classes, so do not silently substitute its π scale.
* `NLS/ZakharovShabat/SourceBirkhoffImageInverse.lean`: open image,
  injectivity, analytic image inverse, and zero value. The weighted variants
  `SourceBirkhoffWeightedImageInverse.lean` and
  `SourceBirkhoffWeightedComplexAnalytic.lean` retain native coefficient
  values and analytic domains. They are promising Theorem 1.2 dependencies,
  not yet an article theorem: instantiate their constructed physical data,
  identify rectangular vs complex coordinates, physical FL^p, cross-p
  agreement, canonical sign, dense image and p=2 surjectivity together.
* `NLS/Dynamics/PhaseContinuityEstimate.lean`, `PhaseContinuityChoice.lean`,
  and `NLS/SequenceSpaces/SpatialTranslation.lean`: reusable finite-head/tail
  phase control and continuous translation. No new competing proofs needed.
* `NLS/Dynamics/UnboundedPhaseObstruction.lean` and
  `VariableAmplitudePhaseObstruction.lean`: exclude uniform trajectory
  convergence under diverging positive frequencies and a nonzero amplitude.
  `PhaseSubsequenceSeparation.lean` permits variable separating times.
  None alone proves nonextension at a prescribed fixed time.
* `NLS/SequenceSpaces/RealActionMassNonextension.lean`: total action has no
  continuous extension at zero above ℓ¹. The mKdV obstruction must instead
  work at every real FL^p datum outside L² and preserve symmetric actions.
* `NLS/ZakharovShabat/SourceOrdinaryFrequencyNonextension.lean` is specific
  to the physical dNLS energy derivative, with a mass shift 4. Its equation
  theorem cannot replace mKdV's mass coefficient 12πn or H₄ identification.

## Outstanding dependencies and integration order

1. Consume the mKdV–NLS hierarchy task's H₄ restriction, diagonal symmetry,
   Poisson normalization and physical Hamiltonian identification. Do not
   create an alternative hierarchy bridge.
2. Finish Theorem 1.2's exact physical FL^p/Birkhoff adapter from the existing
   constructions, including dense image and conjugation/reflection symmetry.
3. Build the H₄ frequency representation and locally uniform estimates of
   Section 5 (Theorem 5.4, pp. 25–26), then prove Theorem 1.3. Existing
   dissertation H₃ frequency bounds are not this theorem.
4. Show the physical renormalized flow is the specified rotation, preserves
   the diagonal, and stays locally in the open Birkhoff image. A small ball
   gives the global-near-zero clause; prove smooth-approximation agreement.
5. Prove fixed-time nonextension by controlled smooth approximations with
   divergent and tunable mass, using a nonzero signed mode. Theorem 7.1(iii)
   is printed for all n, but the mass term vanishes at n=0; the argument
   should select n≠0. Corollary 7.2(iii) needs such a mode, available outside
   L² after the physical coordinate identification. Its reference to item
   (iv) of Theorem 7.1 is a cross-reference typo; 7.1 has three items.
6. After checkout authorization: integrate on `articles/mkdv-below-l2`,
   validate focused modules and imports, audit all main-theorem dependencies,
   then commit/push validated steps. Main integration remains sequential.

## Validation

Run `coverage/articles/mkdv-below-l2/check.sh` from this checkout. It uses the
pinned Lean 4.33.1 executable and canonical mathlib v4.33.1 compiled imports
read-only, with new outputs under this checkout's private
`.lake/mkdv-below-l2/lib/lean`. The script supports `CANONICAL_NLS_ROOT`,
`ELAN_HOME`, `LEAN_BIN` and `MKDV_BUILD_ROOT` overrides; it never invokes Lake
or writes through the imported symlinks.

All four proof modules check without diagnostics. `AxiomAudit.lean` audits all
30 new definitions, abbreviations and theorem declarations transitively;
only `propext`, `Classical.choice` and `Quot.sound` occur. No new axiom,
sorry or disabled linter was introduced. `validation.txt` captures the checks.
This is focused validation, not a full repository build or completed article
verification. Downloaded PDF/text and compiler outputs are not tracked.
