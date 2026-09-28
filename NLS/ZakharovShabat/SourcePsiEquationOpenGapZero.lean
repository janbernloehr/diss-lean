import NLS.ZakharovShabat.SourcePsiVariationOpenGapZero

/-!
# A zero of an entire psi numerator from a vanishing open-gap equation

This is the real-gap mean-value argument of Lemma 12.2, stated for an
arbitrary entire numerator. The variation and actual psi numerator
are separate instances of the same contour mechanism.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A vanishing canonical-root contour integral forces a zero of an
entire real-valued numerator in an enclosed open real gap. -/
theorem exists_entireNumerator_zero_on_openGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hfreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (f z).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C((x:ℂ),R),
      f z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      f μ = 0 := by
  let Φ : ℂ → ℂ := f
  let P : ℂ → ℂ := sourceStandardRootOmittedProduct hp hp1 m ψ
  let g : ℂ → ℂ := fun z => Φ z / P z
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψW : ψ ∈ W := hrealW hψ
  have hPanalytic : AnalyticOnNhd ℂ P
      (sourceStandardRootOmittedDomain hp hp1 ψ m) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 m W (hdata m).2.1 ψ hψW
  have hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) R) := by
    intro z hz
    exact (hf z (mem_univ _)).div (hPanalytic z (hdom hz))
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hdom hz))
  have hgap : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball (x:ℂ) R :=
    (sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m).trans hseg
  have hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (g z).im = 0 := by
    intro z hz
    have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (ball_subset_closedBall (hseg hzPeriod))
    have hΦreal : (Φ z).im = 0 := by
      simpa only [Φ] using hfreal z hz
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hzPeriod
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using hzIm.symm
    have hPreal : (P z).im = 0 := by
      simpa only [P,hzReal] using
        sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis
          hp hp1 ψ hψ m z.re (hzReal ▸ hzDom)
    simp [g,Complex.div_im,hΦreal,hPreal]
  have hpoint (z : ℂ) (hz : z ∈ sphere (x:ℂ) R) :
      g z / sourceStandardRoot hp hp1 ψ m z =
        (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (sphere_subset_closedBall hz)
    have hPz : P z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hzDom
    have hCz : sourceCanonicalRoot hp hp1 ψ z ≠ 0 :=
      sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (hcircle hz)
    have hSz : sourceStandardRoot hp hp1 ψ m z ≠ 0 := by
      intro hs
      apply hCz
      rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z,hs]
      simp
    dsimp [g,P]
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z]
    field_simp [hPz,hSz,Complex.I_ne_zero]
  have hInt :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) =
      (2*I) * (∮ z in C((x:ℂ),R),
        Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact hpoint z hz
  have hIntZero :
      (∮ z in C((x:ℂ),R),
        g z / sourceStandardRoot hp hp1 ψ m z) = 0 := by
    rw [hInt]
    change (2*I) *
      (∮ z in C((x:ℂ),R),
        f z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
    rw [hzero,mul_zero]
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_realCenteredCircle_real_mean_value
      hp hp1 ψ hψ m hopen g hgreal x R hR hseg hgap hg
  have hgzero : g μ = 0 := by
    rw [hIntZero] at hvalue
    simpa using hvalue.symm
  have hPμ : P μ ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
      (hdom (ball_subset_closedBall (hgap hμ)))
  refine ⟨μ,hμ,?_⟩
  have hΦzero : Φ μ = 0 := by
    have := congrArg (fun z : ℂ => z * P μ) hgzero
    simpa [g,hPμ] using this
  exact hΦzero

/-- A zero of the actual scalar psi equation gives a zero of its
entire numerator on an enclosed open real gap. -/
theorem exists_sourcePsiCandidate_zero_on_openGap_of_equation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : sourcePsiEquationCoordinate hp hp1 n m
      a ψ (x:ℂ) R = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      sourcePsiCandidate n (μ,a) = 0 := by
  have hnum : AnalyticOnNhd ℂ
      (fun z => sourcePsiCandidate n (z,a)) univ :=
    (differentiable_sourcePsiCandidate hp hp1 n a).differentiableOn
      |>.analyticOnNhd isOpen_univ
  have hnumReal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      (sourcePsiCandidate n (z,a)).im = 0 := by
    intro z hz
    have hzPeriod : z ∈ sourcePeriodicSegment hp hp1 ψ m :=
      sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hzPeriod
    have hc := sourcePsiCandidate_conj_of_real_roots
      hp hp1 n a hroots z
    rw [Complex.conj_eq_iff_im.mpr hzIm] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hnm : (((n-m : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral] at hzero
  have hIntZero := (mul_eq_zero.mp hzero).resolve_left hnm
  change (∮ z in C((x:ℂ),R),
      sourcePsiCandidate n (z,a) /
        sourceCanonicalRoot hp hp1 ψ z) = 0 at hIntZero
  exact exists_entireNumerator_zero_on_openGap
    hp hp1 ψ hψ m (fun z => sourcePsiCandidate n (z,a))
      hnum hnumReal hopen x R hR hseg hdom hcircle hIntZero

end NLS.ZakharovShabat
