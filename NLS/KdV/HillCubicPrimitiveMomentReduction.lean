import NLS.KdV.HillOddCenteredPrimitiveMoments
import NLS.ComplexAnalysis.ShiftedCubicWeightedCircle

/-! The exact cubic contour reduction for the actual Hill differential.
It retains the free cubic term and the coefficient -12 of the second
centered moment. It does not identify a physical Hamiltonian frequency. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem cubic_primitive_contour_eq_centeredMoment (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
      (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q)-
        I*(Real.pi:ℂ)*(m:ℤ))^3*P.abelianFrequencyDifferential n (z,q)) =
      -3*(I*(Real.pi:ℂ)*(m:ℤ))*P.centeredMoment W n m 1 q-
        (I*(Real.pi:ℂ)*(m:ℤ))^3*P.centeredMoment W n m 0 q := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hf : ContinuousOn (fun z => sourceFullAbelianPrimitive (by simp) (by norm_num) W
      (m:ℤ) (z,P.sourcePsi q)) (sphere (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))) := by
    intro z hz
    exact ((C.full_analytic (m:ℤ) (z,P.sourcePsi q) ⟨hq.2,D.sphere_subset_rootDomain hz⟩).comp
      (f := fun w : ℂ => (w,P.sourcePsi q)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun z => P.abelianFrequencyDifferential n (z,q))
      (sphere (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))) := by
    intro z hz
    exact ((P.analytic_abelianFrequencyDifferential_joint n (z,q) ⟨hq.1,D.sphere_subset_rootDomain hz⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
  have h1 := P.odd_centeredMoment_eq_zero C n m 0 q hq
  have h3 := P.odd_centeredMoment_eq_zero C n m 1 q hq
  have he := circleIntegral_shifted_cube_of_odd_moments_zero _ _
    (P.centers (m:ℤ):ℂ) (I*(Real.pi:ℂ)*(m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _).le hf hg
    (by simpa only [mul_zero,zero_add,pow_one] using h1)
    (by simpa only [mul_one] using h3)
  simpa only [centeredMoment,centeredMomentIntegrand,mul_one,mul_zero,pow_zero,one_mul] using he

theorem normalized_cubic_primitive_contour (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    (4/(I*(Real.pi:ℂ))) *
      (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
        (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q)-
          I*(Real.pi:ℂ)*(m:ℤ))^3*P.abelianFrequencyDifferential n (z,q)) =
      (2*(Real.pi:ℂ)*(n:ℤ))^3*(if m=n then 1 else 0)-
        12*(m:ℤ)*P.centeredMoment W n m 1 q := by
  rw [P.cubic_primitive_contour_eq_centeredMoment C n m q hq]
  have hp : (2*(Real.pi:ℂ))≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have h0 := congrArg (fun t : ℂ => (2*(Real.pi:ℂ))*t) (P.centeredMoment_zero_order W n m q hq.1)
  simp only [← mul_assoc,mul_inv_cancel₀ hp,one_mul] at h0
  rw [h0]
  split_ifs with hmn
  · subst m
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  · field_simp
    ring

end NLS.KdV.HillProductEquationPatch
