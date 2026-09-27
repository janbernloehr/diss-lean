import NLS.ZakharovShabat.SourceNormalizedActionComplexExtension

/-!
# A complex contour expansion of the normalized action

Rationalizing the selected standard root separates the normalized
contour kernel into its collapsed-gap Cauchy kernel and a correction
proportional to the squared gap. The identity is algebraic and applies
to complex spectral and source parameters.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The correction term in the normalized-action contour kernel.
Its denominators are spectral, so it remains meaningful when the
squared gap vanishes. -/
def normalizedActionCircleKernelCorrection (τ q B z : ℂ) : ℂ :=
  let d := τ-z
  let w := normalizedStandardRoot τ q z
  (2*d+w)/(32*d*w*(d+w)^2) + B/(2*w*(d+w)) + B^2/w

/-- The algebraic kernel expansion with independent root variables. -/
private theorem kernel_expansion_algebra
    (d w q B : ℂ) (hd : d ≠ 0) (hw : w ≠ 0) (hplus : d+w ≠ 0)
    (hsq : w^2 = d^2-q/4) :
    (d/(4*(d+w)) + 2*d*B + q*B^2)/w =
      1/(8*d) + 2*B +
        q*((2*d+w)/(32*d*w*(d+w)^2) + B/(2*w*(d+w)) + B^2/w) := by
  have hq : q = 4*(d^2-w^2) := by linear_combination 4*hsq
  rw [hq]
  field_simp
  ring

/-- Exact expansion around the zero-gap Cauchy kernel. -/
theorem normalizedActionCircleKernel_eq_zeroGap_add_correction
    (τ q B z : ℂ) (hτ : τ ≠ z)
    (hw : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    normalizedActionCircleKernel τ q B z =
      -(1/8:ℂ)*(z-τ)⁻¹ + 2*B +
        q*normalizedActionCircleKernelCorrection τ q B z := by
  have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτ
  have hsq := normalizedStandardRoot_sq τ q z hτ
  have hzero : -(1/8:ℂ)*(z-τ)⁻¹ = 1/(8*(τ-z)) := by
    have hrel : z-τ = -(τ-z) := by ring
    rw [hrel]
    field_simp
  rw [hzero]
  exact kernel_expansion_algebra (τ-z) (normalizedStandardRoot τ q z)
    q B hd hw hplus hsq

/-- The correction is analytic at any exterior spectral point where
the selected root is analytic and its spectral denominators are
nonzero. -/
theorem normalizedActionCircleKernelCorrection_analyticAt
    (τ q B z : ℂ)
    (hroot : AnalyticAt ℂ (normalizedStandardRoot τ q) z)
    (hd : τ-z ≠ 0)
    (hw : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    AnalyticAt ℂ (normalizedActionCircleKernelCorrection τ q B) z := by
  let d : ℂ → ℂ := fun t => τ-t
  let w : ℂ → ℂ := normalizedStandardRoot τ q
  have hda : AnalyticAt ℂ d z := analyticAt_const.sub analyticAt_id
  have hwa : AnalyticAt ℂ w z := hroot
  have hsum : AnalyticAt ℂ (fun t => d t+w t) z := hda.add hwa
  have hnum : AnalyticAt ℂ (fun t => 2*d t+w t) z :=
    (analyticAt_const.mul hda).add hwa
  have hden1 : AnalyticAt ℂ
      (fun t => 32*d t*w t*(d t+w t)^2) z :=
    (((analyticAt_const.mul hda).mul hwa).mul (hsum.pow 2))
  have hden1ne : (32:ℂ)*(τ-z)*w z*(τ-z+w z)^2 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hd) hw)
      (pow_ne_zero 2 hplus)
  have hden2 : AnalyticAt ℂ (fun t => 2*w t*(d t+w t)) z :=
    (analyticAt_const.mul hwa).mul hsum
  have hden2ne : (2:ℂ)*w z*(τ-z+w z) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hw) hplus
  change AnalyticAt ℂ (fun t =>
    (2*d t+w t)/(32*d t*w t*(d t+w t)^2) +
      B/(2*w t*(d t+w t)) + B^2/w t) z
  exact ((hnum.div hden1 hden1ne).add
    (analyticAt_const.div hden2 hden2ne)).add
      (analyticAt_const.div hwa hw)

/-- The complex normalized contour quotient is its collapsed-gap
midpoint value plus a correction divisible by the squared gap. -/
theorem normalizedActionCircleQuotient_eq_midpoint_sub_correction
    (τ q B c : ℂ) (R : ℝ) (E : ℂ → ℂ)
    (hR : 0 < R) (hτ : τ ∈ ball c R)
    (hE : AnalyticOnNhd ℂ E (closedBall c R))
    (hK0 : CircleIntegrable
      (fun z => normalizedActionCircleKernel τ 0 B z * E z) c R)
    (hCorr : CircleIntegrable
      (fun z => normalizedActionCircleKernelCorrection τ q B z * E z) c R)
    (hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0) :
    normalizedActionCircleQuotient τ q B c R E =
      I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
        (∮ z in C(c,R),
          normalizedActionCircleKernelCorrection τ q B z * E z) := by
  have hqCorr : CircleIntegrable (fun z =>
      q * (normalizedActionCircleKernelCorrection τ q B z * E z)) c R := by
    have hs := hCorr.const_smul (a := q)
    change CircleIntegrable
      (q • fun z => normalizedActionCircleKernelCorrection τ q B z * E z) c R at hs
    have hfun :
        (q • fun z : ℂ => normalizedActionCircleKernelCorrection τ q B z * E z) =
          (fun z => q * (normalizedActionCircleKernelCorrection τ q B z * E z)) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hfun] at hs
    exact hs
  have hInt :
      (∮ z in C(c,R), normalizedActionCircleKernel τ q B z * E z) =
        (∮ z in C(c,R), normalizedActionCircleKernel τ 0 B z * E z) +
          q * (∮ z in C(c,R),
            normalizedActionCircleKernelCorrection τ q B z * E z) := by
    calc
      _ = ∮ z in C(c,R),
          normalizedActionCircleKernel τ 0 B z * E z +
            q * (normalizedActionCircleKernelCorrection τ q B z * E z) := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        have h := normalizedActionCircleKernel_eq_zeroGap_add_correction
          τ q B z (hden z hz).1 (hden z hz).2.1 (hden z hz).2.2
        have h0 := normalizedActionCircleKernel_zeroGap τ B z (hden z hz).1
        change normalizedActionCircleKernel τ q B z * E z =
          normalizedActionCircleKernel τ 0 B z * E z +
            q * (normalizedActionCircleKernelCorrection τ q B z * E z)
        rw [h,h0]
        ring
      _ = _ := by
        rw [circleIntegral.integral_add hK0 hqCorr,
          circleIntegral.integral_const_mul]
  have hzero := normalizedActionCircleQuotient_zeroGap τ B c R E hR hτ hE
  unfold normalizedActionCircleQuotient at hzero ⊢
  rw [hInt]
  rw [← hzero]
  ring

/-- The contour expansion needs only analyticity of the selected
root along the circle; integrability of both kernels follows. -/
theorem normalizedActionCircleQuotient_eq_midpoint_sub_correction_of_analyticRoot
    (τ q B c : ℂ) (R : ℝ) (E : ℂ → ℂ)
    (hR : 0 < R) (hτ : τ ∈ ball c R)
    (hE : AnalyticOnNhd ℂ E (closedBall c R))
    (hroot : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (normalizedStandardRoot τ q) z)
    (hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0) :
    normalizedActionCircleQuotient τ q B c R E =
      I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
        (∮ z in C(c,R),
          normalizedActionCircleKernelCorrection τ q B z * E z) := by
  have hK0 : CircleIntegrable
      (fun z => normalizedActionCircleKernel τ 0 B z * E z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hτz : τ ≠ z := (hden z hz).1
    have hroot0 : AnalyticAt ℂ (normalizedStandardRoot τ 0) z := by
      have hfun : normalizedStandardRoot τ 0 = fun t => τ-t := by
        funext t
        exact normalizedStandardRoot_zeroGap τ t
      rw [hfun]
      exact analyticAt_const.sub analyticAt_id
    have hw0 : normalizedStandardRoot τ 0 z ≠ 0 := by
      rw [normalizedStandardRoot_zeroGap]
      exact sub_ne_zero.mpr hτz
    have hplus0 : τ-z+normalizedStandardRoot τ 0 z ≠ 0 := by
      rw [normalizedStandardRoot_zeroGap]
      have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτz
      simpa only [← two_mul] using
        (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hd)
    exact ((normalizedActionCircleKernel_analyticAt τ 0 B z
      hroot0 hw0 hplus0).mul
        (hE z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hCorr : CircleIntegrable
      (fun z => normalizedActionCircleKernelCorrection τ q B z * E z) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have h := hden z hz
    exact ((normalizedActionCircleKernelCorrection_analyticAt τ q B z
      (hroot z hz) (sub_ne_zero.mpr h.1) h.2.1 h.2.2).mul
        (hE z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  exact normalizedActionCircleQuotient_eq_midpoint_sub_correction
    τ q B c R E hR hτ hE hK0 hCorr hden

/-- Around every real-type source and selected index, the complex
normalized action has an exact midpoint-plus-correction formula on
one complex neighborhood. The correction carries an explicit factor
of the squared gap, including at complex collapsed gaps. -/
theorem exists_local_sourceNormalizedActionComplexExtension_circleExpansion
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ U,
        sourceNormalizedActionComplexExtension hp hp1 n ψ =
          I * sourceCriticalRootRatioExtension hp hp1 n ψ
            (sourceStandardRootMidpoint hp hp1 ψ n) / 4 -
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            (Real.pi:ℂ)⁻¹ *
              (∮ z in C(c,R),
                normalizedActionCircleKernelCorrection
                  (sourceStandardRootMidpoint hp hp1 ψ n)
                  ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
                  (canonicalCriticalGapQuotient hp hp1
                    (periodOnePotential ψ) (periodOnePotential_mem ψ) n) z *
                  sourceCriticalRootRatioExtension hp hp1 n ψ z) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom,_,hdata⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_eq_realExtension
      hp hp1 φ hφ n
  obtain ⟨W,hWopen,hφW,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  refine ⟨V ∩ W,hVopen.inter hWopen,⟨hφV,hφW hφ⟩,c,R,hR,?_⟩
  intro ψ hψ
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let q := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1
  have hτ : τ ∈ ball c R :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hE : AnalyticOnNhd ℂ E (closedBall c R) := by
    intro z hz
    exact hEdata ψ hψ.2 n z (hother hz)
  have hrootEq (z : ℂ) :
      sourceStandardRoot hp hp1 ψ n z = normalizedStandardRoot τ q z := by
    simp only [sourceStandardRoot, τ, q, sourceStandardRootMidpoint,
      sourcePeriodicGapDisplacement_apply]
  have hzseg (z : ℂ) (hz : z ∈ sphere c R) :
      z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hzs
    have hzball := hseg hzs
    exact (ne_of_lt (mem_ball.mp hzball)) (mem_sphere.mp hz)
  have hroot : ∀ z ∈ sphere c R,
      AnalyticAt ℂ (normalizedStandardRoot τ q) z := by
    intro z hz
    have hfun : normalizedStandardRoot τ q = sourceStandardRoot hp hp1 ψ n := by
      funext t
      exact (hrootEq t).symm
    rw [hfun]
    exact sourceStandardRoot_analyticAt hp hp1 ψ n z (hzseg z hz)
  have hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0 := by
    intro z hz
    have hτz : τ ≠ z := by
      intro he
      exact hzseg z hz (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
    have hw : normalizedStandardRoot τ q z ≠ 0 := by
      rw [← hrootEq]
      exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzseg z hz)
    exact ⟨hτz,hw,normalizedStandardRoot_add_ne_zero τ q z hτz⟩
  have hexp := normalizedActionCircleQuotient_eq_midpoint_sub_correction_of_analyticRoot
    τ q B c R E hR hτ hE hroot hden
  have hcandidate : sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
      I*E τ/4 - q*(Real.pi:ℂ)⁻¹ *
        (∮ z in C(c,R), normalizedActionCircleKernelCorrection τ q B z * E z) := hexp
  rw [(hdata ψ hψ.1).2.2] at hcandidate
  exact hcandidate

end NLS.ZakharovShabat
