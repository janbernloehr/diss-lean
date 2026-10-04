import NLS.ZakharovShabat.SourceFullAbelianDifferential
import NLS.ZakharovShabat.SourceAngularCauchyEquation
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-! # Uniform Cauchy normalization from the full primitive

The interior Cauchy transform of the canonical full primitive divided by
one standard root solves the quadratic root equation. Multiplying back
by that root gives the actual spectral derivative and zero limits at
both complex endpoints, including collapsed gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceFullAbelianCauchyQuotient (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (j : ℤ) (c : ℂ) (R : ℝ) : ℂ × CoeffPair p → ℂ :=
  parametricCircleCauchyTransform (fun t => sourceFullAbelianPrimitive hp hp1 W 0 t /
    sourceStandardRoot hp hp1 t.2 j t.1) c R

def sourceFullAbelianCauchyPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (j : ℤ) (c : ℂ) (R : ℝ) (t : ℂ × CoeffPair p) : ℂ :=
  sourceStandardRoot hp hp1 t.2 j t.1 * sourceFullAbelianCauchyQuotient hp hp1 W j c R t

/-- The Cauchy quotient is analytic on the full interior disc, even
 though the actual primitive and selected root are only used on a circle. -/
theorem sourceFullAbelianCauchyQuotient_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (j : ℤ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set (CoeffPair p)) (hV : IsOpen V)
    (hcircle : ∀ t ∈ sphere c R ×ˢ V, t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2)
    (hF : AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W 0) (sphere c R ×ˢ V))
    (hQ : AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceStandardRoot hp hp1 t.2 j t.1) (sphere c R ×ˢ V)) :
    AnalyticOnNhd ℂ (sourceFullAbelianCauchyQuotient hp hp1 W j c R) (ball c R ×ˢ V) := by
  apply (analyticOnNhd_parametricCircleCauchyTransform _ c R hR V hV ?_).mono
    (prod_mono (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)
  intro t ht
  exact (hF t ht).div (hQ t ht)
    (sourceStandardRoot_ne_zero_off_segment hp hp1 t.2 j t.1
      (hcircle t ht j))

/-- Interior Cauchy projection carries the exact root equation from
 the actual normalized primitive on the circle to every interior point. -/
theorem sourceFullAbelianCauchyQuotient_equation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (E : SourceAbelianSpectralChart hp hp1 W ψ)
    (hcircle : ∀ w ∈ sphere c R, w ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ) (sourceStandardRootOmittedDomain hp hp1 ψ j))
    (z : ℂ) (hz : z ∈ ball c R) :
    sourceAngularSelectedPolynomial hp hp1 ψ j z *
        deriv (fun w => sourceFullAbelianCauchyQuotient hp hp1 W j c R (w,ψ)) z +
      (z-sourceStandardRootMidpoint hp hp1 ψ j)*sourceFullAbelianCauchyQuotient hp hp1 W j c R (z,ψ) =
      sourceCriticalRootGapNumerator hp hp1 ψ j z := by
  let Q := sourceStandardRoot hp hp1 ψ j
  let P : ℂ → ℂ := fun w => sourceFullAbelianPrimitive hp hp1 W 0 (w,ψ)
  let f : ℂ → ℂ := fun w => P w/Q w
  let g := sourceCriticalRootGapNumerator hp hp1 ψ j
  let τ := sourceStandardRootMidpoint hp hp1 ψ j
  let d := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4
  have hroot (w : ℂ) (hw : w ∈ sphere c R) := hcircle w hw
  have hQne (w : ℂ) (hw : w ∈ sphere c R) : Q w ≠ 0 := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ j w (hroot w hw j)
  have hQa (w : ℂ) (hw : w ∈ sphere c R) : AnalyticAt ℂ Q w := sourceStandardRoot_analyticAt hp hp1 ψ j w (hroot w hw j)
  have hPa (w : ℂ) (hw : w ∈ sphere c R) : AnalyticAt ℂ P w := by
    exact sourceFullAbelianPrimitive_spectral_analytic E 0 w
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hcircle w hw))
  have hf : AnalyticOnNhd ℂ f (sphere c R) := fun w hw => (hPa w hw).div (hQa w hw) (hQne w hw)
  have hg : AnalyticOnNhd ℂ g (closedBall c R) :=
    fun w hw => (analyticAt_const.sub analyticAt_id).mul (hE w (hother hw))
  have heq (w : ℂ) (hw : w ∈ sphere c R) : quadraticRootPolynomial τ d w*deriv f w+(w-τ)*f w = g w := by
    have hfact : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w / sourceCanonicalRoot hp hp1 ψ w = g w/Q w := by
      rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ j w (hroot w hw)]
      dsimp [g,sourceCriticalRootGapNumerator,Q]
      ring
    have hPd : HasDerivAt P (g w/Q w) w := by
      have hd := sourceFullAbelianPrimitive_hasDerivAt E 0 w (hcircle w hw)
      rw [hfact] at hd
      exact hd
    have hQd : HasDerivAt Q ((w-τ)/Q w) w := by
      have hd := (hQa w hw).differentiableAt.hasDerivAt
      rw [show deriv Q w = (w-τ)/Q w from deriv_sourceStandardRoot_off_segment hp hp1 ψ j w (hroot w hw j)] at hd
      exact hd
    have hfd := hPd.fun_div hQd (hQne w hw)
    have hsq : quadraticRootPolynomial τ d w = Q w^2 :=
      (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ j w).trans
        (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ j w (hroot w hw j)).symm
    rw [hsq,hfd.deriv]
    dsimp only [f]
    field_simp [hQne w hw]
    ring
  exact circleCauchyTransform_quadratic_equation f g τ d c R hR hf hg heq z hz

/-- The Cauchy construction has the actual quotient derivative. -/
theorem sourceFullAbelianCauchyPrimitive_hasDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (E : SourceAbelianSpectralChart hp hp1 W ψ)
    (hcircle : ∀ w ∈ sphere c R, w ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j)
    (hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 j ψ) (sourceStandardRootOmittedDomain hp hp1 ψ j))
    (hH : AnalyticOnNhd ℂ (fun w => sourceFullAbelianCauchyQuotient hp hp1 W j c R (w,ψ)) (ball c R))
    (z : ℂ) (hz : z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j) :
    HasDerivAt (fun w => sourceFullAbelianCauchyPrimitive hp hp1 W j c R (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j c R hother hz
  have hfact : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z =
      sourceCriticalRootGapNumerator hp hp1 ψ j z / sourceStandardRoot hp hp1 ψ j z := by
    rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ j z hroot]
    unfold sourceCriticalRootGapNumerator
    ring
  rw [hfact]
  apply hasDerivAt_root_mul_of_quadratic_equation _ _ (sourceStandardRootMidpoint hp hp1 ψ j)
    ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4) _ z
    (sourceStandardRoot_analyticAt hp hp1 ψ j z hz.2) (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ j z hz.2)
    _ (hH z hz.1) (sourceFullAbelianCauchyQuotient_equation hp hp1 W ψ j c R hR E hcircle hother hE z hz.1)
  filter_upwards [(isOpen_sourceAbelian_complexDisc hp hp1 ψ j c R).mem_nhds hz] with w hw
  exact (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ j w hw.2).trans
    (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ j w).symm

/-- Both endpoint limits are exactly zero, with no distinction between
 a nondegenerate complex gap and a collapsed pair. -/
theorem sourceFullAbelianCauchyPrimitive_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R)
    (hH : AnalyticOnNhd ℂ (fun w => sourceFullAbelianCauchyQuotient hp hp1 W j c R (w,ψ)) (ball c R))
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    Tendsto (fun w => sourceFullAbelianCauchyPrimitive hp hp1 W j c R (w,ψ))
      (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 0) := by
  have haB : a ∈ ball c R := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact hseg (left_mem_segment ℝ _ _)
    · exact hseg (right_mem_segment ℝ _ _)
  have hpoly : Tendsto (fun z => sourceAngularSelectedPolynomial hp hp1 ψ j z)
      (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 0) := by
    have h := (hasDerivAt_quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ j)
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4) a).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := ball c R \ sourcePeriodicSegment hp hp1 ψ j))
    have he : sourceAngularSelectedPolynomial hp hp1 ψ j a = 0 := by
      rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl <;> simp
    change Tendsto (sourceAngularSelectedPolynomial hp hp1 ψ j)
      (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a)
      (𝓝 (sourceAngularSelectedPolynomial hp hp1 ψ j a)) at h
    simpa only [he] using h
  have hs : Tendsto (fun z => (sourceStandardRoot hp hp1 ψ j z)^2)
      (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 0) := by
    apply hpoly.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ((sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ j z hz.2).trans
      (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ j z).symm).symm
  simpa only [sourceFullAbelianCauchyPrimitive,zero_mul] using
    (tendsto_zero_of_sq_tendsto_zero _ hs).mul ((hH a haB).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

end NLS.ZakharovShabat
