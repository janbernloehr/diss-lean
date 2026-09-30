import NLS.ComplexAnalysis.QuadraticCosinePrimitive
import NLS.ZakharovShabat.SourceAngularRealNumerator
import NLS.ZakharovShabat.SourceAngularEtaAnalyticRepresentative
import NLS.ZakharovShabat.SourceAngularEtaCauchyEquation
import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic

/-! # Actual beta and eta representatives are real on the real source locus

The interior Cauchy equations give regular cosine primitives across both
endpoints. Their rotated numerators are real for the actual normalized psi
family, so their imaginary constants vanish at pi. Real interlacing puts
every terminal angle on the real axis, independently of its branch.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularSelectedPolynomial_eq_halfGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) (δ : ℂ)
    (hδsq : δ^2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2) :
    sourceAngularSelectedPolynomial hp hp1 ψ m =
      quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ m) (δ^2) := by
  funext z
  simp only [sourceAngularSelectedPolynomial,quadraticRootPolynomial,hδsq]
  ring

namespace SourceAngularComplexDirichletAngleData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ} {V U : Set (CoeffPair p)}
  {δ ε : CoeffPair p → ℂ}

theorem angle_im_eq_zero_of_realType
    (D : SourceAngularComplexDirichletAngleData hp hp1 m V U δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    (ε ψ).im = 0 := by
  apply im_eq_zero_of_cosineGapPoint_mem_segment
    (sourceStandardRootMidpoint hp hp1 ψ m) (δ ψ) (ε ψ) (D.halfGap_ne_zero ψ hψ)
  rw [sourcePeriodicSegment_eq_of_halfGap_sq hp hp1 ψ m (δ ψ) (D.halfGap_sq ψ hψ)]
  change sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) ∈ _
  rw [(D.terminal_coordinates ψ hψ).1]
  exact canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet ψ hreal m

/-- The actual terminal coefficient is the regular cosine root,
including a periodic terminal where the sine vanishes. -/
theorem dirichlet_root_coefficient
    (D : SourceAngularComplexDirichletAngleData hp hp1 m V U δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hO : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) = -I*δ ψ*Complex.sin (ε ψ) := by
  have hfull := D.terminal_root ψ hψ
  simp only [sourceAngularBranchCosineRoot,(D.terminal_coordinates ψ hψ).1] at hfull
  rw [← hfull]
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ m hO
  have hK : 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hP
  field_simp [hK]
  rw [I_sq]
  ring

end SourceAngularComplexDirichletAngleData

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

theorem cosine_point_mem_gap
    (_D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (δ : ℂ)
    (hδsq : δ^2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2) (t : ℝ) :
    cosineGapPoint (sourceStandardRootMidpoint hp hp1 ψ m) δ (t:ℂ) ∈
      sourcePeriodicSegment hp hp1 ψ m := by
  rw [← sourcePeriodicSegment_eq_of_halfGap_sq hp hp1 ψ m δ hδsq]
  exact cosineGapPoint_real_mem_segment _ _ t

theorem quotientCauchyCandidate_cosine_im_eq_zero_of_realType
    (C : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (hmn : m ≠ n) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (δ : ℂ)
    (hδsq : δ^2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2) (t : ℝ) :
    (quadraticCosinePrimitive (sourceStandardRootMidpoint hp hp1 ψ m) δ
      (fun z => sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ (z,ψ)) (t:ℂ)).im = 0 := by
  have hgap := C.cosine_point_mem_gap ψ δ hδsq
  have hball (x : ℝ) := ball_subset_ball hrρ.le (C.gap_enclosed ψ hψ (hgap x))
  apply quadraticCosinePrimitive_im_eq_zero _ _ _ (sourceAngularGapNumerator hp hp1 n m s ψ)
  · intro x
    exact ((C.analyticOnNhd_quotientCauchyCandidate n ρ hrρ hρR _ ⟨hball x,hψ⟩).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  · intro x
    rw [← sourceAngularSelectedPolynomial_eq_halfGap hp hp1 ψ m δ hδsq]
    exact C.quotientCauchyCandidate_equation ψ hψ n hmn ρ hrρ hρR _ (hball x)
  · intro x
    exact sourceAngularGapNumerator_rotated_im_eq_zero_of_realType hp hp1 n m hs ψ hreal _
      (sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m _ (hgap x))
      (((C.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall (ball_subset_ball
          (C.inner_lt_outer.trans C.outer_lt_assigned).le (C.gap_enclosed ψ hψ (hgap x)))))

theorem etaQuotientCauchyCandidate_cosine_im_eq_zero_of_realType
    (C : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (δ : ℂ)
    (hδsq : δ^2 = (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2)^2) (t : ℝ) :
    (quadraticCosinePrimitive (sourceStandardRootMidpoint hp hp1 ψ m) δ
      (fun z => sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ)) (t:ℂ)).im = 0 := by
  have hgap := C.cosine_point_mem_gap ψ δ hδsq
  have hball (x : ℝ) := ball_subset_ball hrρ.le (C.gap_enclosed ψ hψ (hgap x))
  apply quadraticCosinePrimitive_im_eq_zero _ _ _ (fun z => sourceAngularGapNumerator hp hp1 m m s ψ z-I)
  · intro x
    exact ((C.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR _ ⟨hball x,hψ⟩).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  · intro x
    rw [← sourceAngularSelectedPolynomial_eq_halfGap hp hp1 ψ m δ hδsq]
    exact C.etaQuotientCauchyCandidate_equation ψ hψ ρ hrρ hρR _ (hball x)
  · intro x
    have hg := sourceAngularGapNumerator_rotated_im_eq_zero_of_realType hp hp1 m m hs ψ hreal _
      (sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m _ (hgap x))
      (((C.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall (ball_subset_ball
          (C.inner_lt_outer.trans C.outer_lt_assigned).le (C.gap_enclosed ψ hψ (hgap x)))))
    simpa only [mul_sub,Complex.sub_im,Complex.mul_im,Complex.neg_re,Complex.neg_im,
      I_re,I_im,neg_zero,mul_zero,zero_mul,zero_add,sub_zero] using hg

end SourceAngularJointAnnulusChartData

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

theorem beta_im_eq_zero_of_realType
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (hmn : m ≠ n) : (sourceAngularBeta hp hp1 n m s ψ).im = 0 := by
  have hψV := D.angle.source_subset hψ
  have hO := ((D.annulus.disc_family ψ hψV).contour_family.2 m).2.2.1
    (ball_subset_closedBall ((D.annulus.disc_family ψ hψV).dirichlet_mem_ball m))
  rw [← D.annulus.betaCauchyCandidate_eq_beta ψ hψV n hmn ρ D.inner_lt_cauchy D.cauchy_lt_outer]
  simp only [sourceAngularBetaCauchyCandidate,D.angle.dirichlet_root_coefficient ψ hψ hO]
  have hangle : ((ε ψ).re:ℂ) = ε ψ := by
    simpa [D.angle.angle_im_eq_zero_of_realType ψ hψ hreal] using Complex.re_add_im (ε ψ)
  have h := D.annulus.quotientCauchyCandidate_cosine_im_eq_zero_of_realType hs ψ hψV hreal n hmn
    ρ D.inner_lt_cauchy D.cauchy_lt_outer (δ ψ) (D.angle.halfGap_sq ψ hψ) (ε ψ).re
  simpa only [hangle,quadraticCosinePrimitive,
    show cosineGapPoint (sourceStandardRootMidpoint hp hp1 ψ m) (δ ψ) (ε ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m from (D.angle.terminal_coordinates ψ hψ).1] using h

theorem representative_im_eq_zero_of_realType
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε ψ).im = 0 := by
  have hψV := D.angle.source_subset hψ
  have hO := ((D.annulus.disc_family ψ hψV).contour_family.2 m).2.2.1
    (ball_subset_closedBall ((D.annulus.disc_family ψ hψV).dirichlet_mem_ball m))
  have hangle : ((ε ψ).re:ℂ) = ε ψ := by
    simpa [D.angle.angle_im_eq_zero_of_realType ψ hψ hreal] using Complex.re_add_im (ε ψ)
  have h := D.annulus.etaQuotientCauchyCandidate_cosine_im_eq_zero_of_realType hs ψ hψV hreal
    ρ D.inner_lt_cauchy D.cauchy_lt_outer (δ ψ) (D.angle.halfGap_sq ψ hψ) (ε ψ).re
  have hrem : (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ).im = 0 := by
    simp only [sourceAngularEtaRemainderCauchyCandidate,D.angle.dirichlet_root_coefficient ψ hψ hO]
    simpa only [hangle,quadraticCosinePrimitive,
      show cosineGapPoint (sourceStandardRootMidpoint hp hp1 ψ m) (δ ψ) (ε ψ) =
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m from (D.angle.terminal_coordinates ψ hψ).1] using h
  simp only [sourceAngularEtaCauchyRepresentative,Complex.add_im,Complex.sub_im,
    D.angle.angle_im_eq_zero_of_realType ψ hψ hreal,Complex.ofReal_im,hrem,sub_self,add_zero]

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
