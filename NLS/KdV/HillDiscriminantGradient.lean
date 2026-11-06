import NLS.KdV.HillPhysicalDirectionPairing
import NLS.ZakharovShabat.L2GradientCurves
import NLS.ZakharovShabat.L2DiscriminantCotangent

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The scalar Hill trace cotangent, retaining the minus sign in the
constant-upper physical-potential embedding. -/
def hillDiscriminantGradientCurve (q : Coeff 2) (z : ℂ) : Curve ℂ :=
  -((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp
    (l2DiscriminantGradientCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z))

theorem fderiv_hillL2FrequencyDiscriminant_potential (q h : Coeff 2) (z : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDiscriminant p z) q) h=
      (fderiv ℂ (fun u : IntervalPairL2 => l2Discriminant u z)
        (physicalRestrictionL2 (hillFirstOrderPotential q))) (hillPhysicalDirection h) := by
  have hd := ((analyticOnNhd_l2Discriminant_potential z _ (mem_univ _)).differentiableAt.hasFDerivAt).comp
    q (hasFDerivAt_hillPhysicalPotential q)
  exact congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv

theorem hillDiscriminantGradient_represents_potential
    (q h : Coeff 2) (z : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDiscriminant p z) q) h=
      hillPhysicalDirectionPairing h (hillDiscriminantGradientCurve q z) := by
  rw [fderiv_hillL2FrequencyDiscriminant_potential,fderiv_l2Discriminant_eq_gradient_integral,
    hillPhysicalDirectionPairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_upper_zero_ae h] with x hx
  change (hillPhysicalDirection h).ofLp.1 x=0 at hx
  rw [hx,mul_zero,zero_add]
  change _= -(hillPhysicalDirection h).ofLp.2 x*
    (-((NLS.LinearVolterra.extend (l2DiscriminantGradientCurve
      (physicalRestrictionL2 (hillFirstOrderPotential q)) z) x).2))
  rw [extend_l2DiscriminantGradientCurve]
  ring

theorem continuous_hillDiscriminantGradientCurve_spectral (q : Coeff 2) :
    Continuous (hillDiscriminantGradientCurve q) :=
  (((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp).comp
    (continuous_l2DiscriminantGradientCurve_spectral (physicalRestrictionL2 (hillFirstOrderPotential q)))).neg

private theorem trace_gradient_basis (q : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillDiscriminantGradientCurve q z t=
      -(I*((l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) ⟨1,by norm_num⟩).1*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1-
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) ⟨1,by norm_num⟩).1*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1)*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1+
        I*((l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) ⟨1,by norm_num⟩).2*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1-
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) ⟨1,by norm_num⟩).2*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1)*
          (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1) := by
  simp only [hillDiscriminantGradientCurve,ContinuousMap.neg_apply,ContinuousMap.comp_apply,
    ContinuousMap.snd_apply,l2DiscriminantGradientCurve,
    ContinuousMap.add_apply,l2EndpointGradientCurve,l2EndpointGradient,Prod.snd_add,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',extend_coe]
  rfl

private theorem scalar_state_basis
    (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2FrequencyStateCurve q z v t=
      (v.1*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1+
        (I*v.2-z*v.1)*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1,
      (-I*z)*(v.1*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1+
        (I*v.2-z*v.1)*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1)+
      (-I)*(v.1*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).2+
        (I*v.2-z*v.1)*(l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).2)) := by
  have he := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v))
  rw [hillL2FrequencyStateCurve_apply,he]
  rfl

private theorem trace_gradient_polynomial_algebra (z a b A B E F : ℂ) :
    -(I*(A*b-B*a)*a+I*(E*b-F*a)*b)=
      (I*B)*(a+ -z*b)^2+
      (((-I*z)*(I*B)+(-I)*(I*F))-(A+ -z*B))*(a+ -z*b)*(I*b)-
      ((-I*z)*(A+ -z*B)+(-I)*(E+ -z*F))*(I*b)^2 := by
  ring_nf
  rw [I_pow_three]
  ring

/-- The actual scalar trace cotangent is the squared-solution
polynomial with the genuine endpoint monodromy coefficients. -/
theorem hillDiscriminantGradientCurve_eq_scalar_polynomial
    (q : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillDiscriminantGradientCurve q z t=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve q z (1,0) t).1^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
        (hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).1-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (hillL2FrequencyStateCurve q z (0,1) t).1^2 := by
  rw [trace_gradient_basis]
  simp only [scalar_state_basis,mul_zero,mul_one,sub_zero,zero_sub,one_mul,zero_mul,zero_add]
  exact trace_gradient_polynomial_algebra z
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t).1
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t).1
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) ⟨1,by norm_num⟩).1
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) ⟨1,by norm_num⟩).1
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) ⟨1,by norm_num⟩).2
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) ⟨1,by norm_num⟩).2

end NLS.KdV
