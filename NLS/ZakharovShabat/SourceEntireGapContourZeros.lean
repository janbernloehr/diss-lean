import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedReal
import NLS.ZakharovShabat.SourceCanonicalRootProduct
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# Zeros of an entire numerator from real gap contours

The mean-value and collapsed-gap Cauchy arguments depend only on the
numerator's entirety and, for open gaps, its reality on the real axis.
These statements apply to both deleted psi variations and the full
product variation used for the limit operator.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A zero contour of an entire numerator that is real on the real
axis forces a zero in the enclosed open real periodic gap. -/
theorem exists_sourceEntireNumerator_zero_on_openGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (hFreal : ∀ x : ℝ, (F (x:ℂ)).im = 0)
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
      F z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    ∃ μ ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
      F μ = 0 := by
  let Φ : ℂ → ℂ := F
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
    exact (hF z (mem_univ _)).div (hPanalytic z (hdom hz))
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
    have hzIm : z.im = 0 :=
      sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hψ m z hzPeriod
    have hzReal : (z.re:ℂ) = z := by
      apply Complex.ext
      · rfl
      · simpa using hzIm.symm
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (ball_subset_closedBall (hseg hzPeriod))
    have hΦreal : (Φ z).im = 0 := by
      simpa only [Φ,hzReal] using
        hFreal z.re
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
        F z /
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

/-- A zero contour at a collapsed periodic gap forces any entire
numerator to vanish at the gap midpoint; no reality assumption is needed. -/
theorem sourceEntireNumerator_zero_at_collapsedGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0)
    (c₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈ ball c₀ R)
    (hdom : closedBall c₀ R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere c₀ R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c₀,R),
      F z /
        sourceCanonicalRoot hp hp1 ψ z) = 0) :
    F
      (sourceStandardRootMidpoint hp hp1 ψ m) = 0 := by
  let Φ : ℂ → ℂ := F
  let P : ℂ → ℂ := sourceStandardRootOmittedProduct hp hp1 m ψ
  let g : ℂ → ℂ := fun z => Φ z / P z
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψW : ψ ∈ W := hrealW hψ
  have hPanalytic : AnalyticOnNhd ℂ P
      (sourceStandardRootOmittedDomain hp hp1 ψ m) :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 m W (hdata m).2.1 ψ hψW
  have hg : AnalyticOnNhd ℂ g (closedBall c₀ R) := by
    intro z hz
    exact (hF z (mem_univ _)).div (hPanalytic z (hdom hz))
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (hdom hz))
  have hτsphere : ∀ z ∈ sphere c₀ R, z ≠ τ := by
    intro z hz he
    have hlt := mem_ball.mp hmid
    have heq := mem_sphere.mp hz
    rw [he] at heq
    exact (ne_of_lt hlt) heq
  have hpoint (z : ℂ) (hz : z ∈ sphere c₀ R) :
      g z / (τ-z) =
        (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    have hzDom : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
      hdom (sphere_subset_closedBall hz)
    have hPz : P z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hzDom
    have hCz : sourceCanonicalRoot hp hp1 ψ z ≠ 0 :=
      sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z (hcircle hz)
    have hSz : τ-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hτsphere z hz))
    change Φ z / P z / (τ-z) =
      (2*I) * (Φ z / sourceCanonicalRoot hp hp1 ψ z)
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z,
      sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap]
    change Φ z / P z / (τ-z) =
      (2*I) * (Φ z / (2*I*(τ-z)*P z))
    field_simp [hPz,hSz,Complex.I_ne_zero]
  have hInt :
      (∮ z in C(c₀,R), g z / (τ-z)) =
      (2*I) * (∮ z in C(c₀,R),
        Φ z / sourceCanonicalRoot hp hp1 ψ z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact hpoint z hz
  have hIntZero : (∮ z in C(c₀,R), g z / (τ-z)) = 0 := by
    rw [hInt]
    change (2*I) *
      (∮ z in C(c₀,R),
        F z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
    rw [hzero,mul_zero]
  have hCauchy :
      (∮ z in C(c₀,R), (z-τ)⁻¹ * g z) =
        2*(Real.pi:ℂ)*I*g τ := by
    simpa only [smul_eq_mul] using
      (hg.differentiableOn.circleIntegral_sub_inv_smul hmid)
  have hIntValue : (∮ z in C(c₀,R), g z / (τ-z)) =
      -(2*(Real.pi:ℂ)*I)*g τ := by
    have heq :
        (∮ z in C(c₀,R), g z / (τ-z)) =
          ∮ z in C(c₀,R), (-1:ℂ)*((z-τ)⁻¹*g z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hzt : z-τ ≠ 0 := sub_ne_zero.mpr (hτsphere z hz)
      have htz : τ-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hτsphere z hz))
      field_simp [hzt,htz]
      ring
    rw [heq,circleIntegral.integral_const_mul,hCauchy]
    ring
  have hgzero : g τ = 0 := by
    rw [hIntValue] at hIntZero
    have hc : -(2*(Real.pi:ℂ)*I) ≠ 0 := by
      apply neg_ne_zero.mpr
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    exact (mul_eq_zero.mp hIntZero).resolve_left hc
  have hPτ : P τ ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ τ m
      (hdom (ball_subset_closedBall hmid))
  have hΦzero : Φ τ = 0 := by
    have := congrArg (fun z : ℂ => z * P τ) hgzero
    simpa [g,hPτ] using this
  exact hΦzero

end NLS.ZakharovShabat
