import NLS.KdV.HillAbelianCosinePrimitive
import NLS.ComplexAnalysis.RegularQuadraticCosinePrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianCosinePrimitive_eq_linear_add_quadratic
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (Q : ℂ → ℂ) (ρ : ℝ)
    (hδρ : ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ < ρ)
    (hQ : AnalyticOnNhd ℂ Q (ball (0:ℂ) ρ))
    (heq : ∀ w ∈ ball (0:ℂ) ρ,
      (w^2-(hillRealGapHalfLength q hq hr k : ℂ)^2)*deriv Q w+w*Q w =
        -I*hillAbelianSelectedGlobalPsi q hq hr n hn ((hillRealGapCenter q hq hr k : ℂ)+w)/
          hillDeflatedEnergyCanonicalRoot q hq hr k ((hillRealGapCenter q hq hr k : ℂ)+w)-(if k=n then 1 else 0))
    (θ : ℝ) :
    hillAbelianCosinePrimitive q hq hr n hn k (θ : ℂ) =
      (if k=n then 1 else 0)*((θ : ℂ)-(Real.pi : ℂ))+
        regularQuadraticCosinePrimitive 0 (hillRealGapHalfLength q hq hr k) Q (θ : ℂ) := by
  let δ : ℂ := hillRealGapHalfLength q hq hr k
  let κ : ℂ := if k=n then 1 else 0
  let Ω := segment ℝ (Real.pi : ℂ) (θ : ℂ)
  let D := hillAbelianCosineDifferential q hq hr n hn k
  have hreal (v : ℂ) (hv : v ∈ Ω) : v = (v.re : ℂ) := by
    have hi := im_eq_zero_of_mem_real_segment Real.pi θ v hv
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hi
  have hpoint (v : ℂ) (hv : v ∈ Ω) : cosineGapPoint 0 δ v ∈ ball (0:ℂ) ρ := by
    rw [hreal v hv]
    have hcos : ‖Complex.cos (v.re : ℂ)‖ ≤ 1 := by
      simpa only [← ofReal_cos,norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one v.re
    simp only [cosineGapPoint,zero_add,mem_ball,dist_zero_right,norm_mul]
    exact (mul_le_mul_of_nonneg_left hcos (norm_nonneg δ)).trans_lt (by simpa only [mul_one] using hδρ)
  have hD : ContinuousOn D Ω := by
    intro v hv
    rw [hreal v hv]
    exact (analyticAt_hillAbelianCosineDifferential_real q hq hr n hn k hk v.re).continuousAt.continuousWithinAt
  let P : ℂ → ℂ := fun v => κ*(v-(Real.pi : ℂ))+regularQuadraticCosinePrimitive 0 δ Q v
  have hP (v : ℂ) (hv : v ∈ Ω) : HasDerivAt P (D v) v := by
    have hEq : quadraticRootPolynomial 0 (δ^2) (cosineGapPoint 0 δ v)*
        deriv Q (cosineGapPoint 0 δ v)+(cosineGapPoint 0 δ v-0)*Q (cosineGapPoint 0 δ v) = D v-κ := by
      have he := heq (cosineGapPoint 0 δ v) (hpoint v hv)
      simpa only [quadraticRootPolynomial,sub_zero,D,κ,δ,hillAbelianCosineDifferential,cosineGapPoint,
        zero_add,mul_div_assoc] using he
    have hreg := hasDerivAt_regularQuadraticCosinePrimitive 0 δ v (D v-κ) Q
      (hQ _ (hpoint v hv)).differentiableAt hEq
    have hlin := ((hasDerivAt_id v).sub_const (Real.pi : ℂ)).const_mul κ
    convert hlin.add hreg using 1 <;> try rfl
    simp only [mul_one]
    ring
  have h := parametricConvexPrimitive_eq_sub_of_primitive
    (fun t : ℂ × ℂ => D t.1) Ω (Real.pi : ℂ) 0 (convex_segment _ _)
    (left_mem_segment ℝ _ _) hD P hP (θ : ℂ) (right_mem_segment ℝ _ _)
  change hillAbelianCosinePrimitive q hq hr n hn k (θ : ℂ) = _ at h
  simpa only [P,sub_self,mul_zero,regularQuadraticCosinePrimitive_pi,add_zero,sub_zero,κ,δ] using h

end NLS.KdV
