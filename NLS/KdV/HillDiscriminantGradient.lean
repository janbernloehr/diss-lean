import NLS.KdV.HillStateMonodromy
import NLS.KdV.HillDirichletGradients
import NLS.ZakharovShabat.L2CharacteristicGradients
import NLS.ZakharovShabat.L2DiscriminantCotangent

/-! # The actual scalar Hill discriminant gradient at every complex energy

The trace gradient is written in the original scalar cosine/sine basis.
Its full L² potential derivative is the physical unconjugated integral,
with the original lower-component sign retained explicitly.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillDiscriminantGradientCurve (q : Coeff 2) (E : ℂ) : Curve ℂ :=
  let C := hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0)
  let S := hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)
  let c := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C
  let s := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp S
  (S ⟨1,by norm_num⟩).1 • c^2+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1) • (c*s)-
      (C ⟨1,by norm_num⟩).2 • s^2

theorem hillDiscriminantGradientCurve_eq_l2 (q : Coeff 2) (E : ℂ) (t : Icc (0 : ℝ) 1) :
    hillDiscriminantGradientCurve q E t =
      -(l2DiscriminantGradient (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt E) t).2 := by
  let z := Complex.sqrt E
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let A := l2SolutionCurve u z (1,0)
  let B := l2SolutionCurve u z (0,1)
  have hC (r : Icc (0 : ℝ) 1) :
      hillL2FrequencyStateCurve q z (1,0) r = constantUpperStateMap z (A r-z • B r) := by
    have h := congrArg (fun Y : Curve (ℂ × ℂ) => Y r)
      (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (1,0)))
    simpa only [hillL2FrequencyStateCurve_apply,constantUpperInitialVector,one_mul,mul_one,mul_zero,
      zero_sub,zero_add,ContinuousMap.add_apply,ContinuousMap.smul_apply,one_smul,neg_smul,sub_eq_add_neg] using
      congrArg (constantUpperStateMap z) h
  have hS (r : Icc (0 : ℝ) 1) :
      hillL2FrequencyStateCurve q z (0,1) r = constantUpperStateMap z (I • B r) := by
    have h := congrArg (fun Y : Curve (ℂ × ℂ) => Y r)
      (l2SolutionCurve_linearCombination u z (constantUpperInitialVector z (0,1)))
    simpa only [hillL2FrequencyStateCurve_apply,constantUpperInitialVector,mul_one,mul_zero,
      sub_zero,ContinuousMap.add_apply,ContinuousMap.smul_apply,zero_smul,zero_add] using
      congrArg (constantUpperStateMap z) h
  dsimp only [hillDiscriminantGradientCurve]
  change _ = -(l2DiscriminantGradient u z t).2
  simp only [ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    ContinuousMap.pow_apply,ContinuousMap.mul_apply,ContinuousMap.comp_apply,ContinuousMap.fst_apply,smul_eq_mul]
  change (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
      (hillL2FrequencyStateCurve q z (1,0) t).1^2+
    ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
      ((hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).1)-
    (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
      (hillL2FrequencyStateCurve q z (0,1) t).1^2 = _
  rw [hC t,hS t,hC ⟨1,by norm_num⟩,hS ⟨1,by norm_num⟩]
  simp only [l2DiscriminantGradient,l2EndpointGradient,Prod.snd_add,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',constantUpperStateMap_apply,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,extend_coe]
  change _ = -(I*((A ⟨1,by norm_num⟩).1*(B t).1-(B ⟨1,by norm_num⟩).1*(A t).1)*(A t).1+
    I*((A ⟨1,by norm_num⟩).2*(B t).1-(B ⟨1,by norm_num⟩).2*(A t).1)*(B t).1)
  ring_nf
  simp only [show I^3 = -I by norm_num [pow_succ,I_sq]]
  ring

theorem fderiv_hillL2Discriminant_potential_integral (q h : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) h =
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
        extend (hillDiscriminantGradientCurve q E) x := by
  let z := Complex.sqrt E
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  have hd := (analyticOnNhd_l2Discriminant_potential z u (mem_univ _)).differentiableAt.hasFDerivAt.comp q
    (hasFDerivAt_hillPhysicalPotential q)
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) h =
    (fderiv ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u) (hillPhysicalDirection h) at he
  rw [he,fderiv_l2Discriminant_eq_gradient_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [hillPhysicalDirection_upper_zero_ae h,ae_restrict_mem measurableSet_Ioc] with x hx hxmem
  have ht : x ∈ Icc (0 : ℝ) 1 := ⟨hxmem.1.le,hxmem.2⟩
  have hg := hillDiscriminantGradientCurve_eq_l2 q E ⟨x,ht⟩
  change (hillPhysicalDirection h).ofLp.1 x = 0 at hx
  rw [hx,mul_zero,zero_add]
  rw [NLS.LinearVolterra.extend,projIcc_of_mem _ ht,hg]
  ring

end NLS.KdV
