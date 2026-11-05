import NLS.KdV.HillDirichletBranchDerivatives
import NLS.KdV.HillDirichletKernelNormalization

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillDirichlet_branch_fderiv_kernel_mass
    (q : Coeff 2) (hq : IsRealHillPotential q) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a q)
    (hz : ∀ᶠ p in 𝓝 q, hillL2DirichletCharacteristic p (a p)=0) (h : Coeff 2) :
    (fderiv ℂ a q) h=
      (I*l2KernelPairing (hillPhysicalDirection h)
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt (a q)) (0,I))
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt (a q)) (0,I))
        ⟨1,by norm_num⟩)/
      (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt (a q)) (0,1)) : ℂ) := by
  let energy := a q
  let z := Complex.sqrt energy
  let d := deriv (hillL2DirichletCharacteristic q) energy
  let g := hillL2DirichletSlope q energy
  let K := hillL2DirichletDirectionKernel q h z
  let M := scalarStateMass (hillL2FrequencyStateCurve q z (0,1))
  have hzeq : (fun p : Coeff 2 => hillL2DirichletCharacteristic p (a p))=ᶠ[𝓝 q]
      (fun _ => (0 : ℂ)) := hz
  have hzero : hillL2DirichletCharacteristic q energy=0 := hzeq.eq_of_nhds
  have hd : d≠0 := hillL2DirichletCharacteristic_deriv_ne_zero q hq energy hzero
  have hm : 0<M := hillL2FrequencyStateCurve_mass_pos q z (0,1)
    (by intro hh;have hh' := congrArg Prod.snd hh;norm_num at hh')
  have hn : d*g=(M : ℂ) := hillL2Dirichlet_derivative_normalization q hq energy hzero
  have hk := hillL2DirichletDirectionKernel_normalization q h energy hzero
  have hroot := hillDirichlet_branch_fderiv_apply q hq a ha hz h
  rw [fderiv_hillL2DirichletCharacteristic_potential] at hroot
  have hbal : (fderiv ℂ a q) h*d= -K := (eq_div_iff hd).mp hroot
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hm.ne')).mpr
  calc
    (fderiv ℂ a q) h*(M : ℂ) = ((fderiv ℂ a q) h*d)*g := by rw [← hn];ring
    _ = (-K)*g := by rw [hbal]
    _ = _ := by linear_combination -hk

theorem hillPhysicalDirection_upper_zero_ae (h : Coeff 2) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1),
      (intervalL2Representative (hillPhysicalDirection h) x).1=0 := by
  let U (q : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential q)
  have he : U h=hillPhysicalDirection h+U 0 := by
    change physicalRestrictionL2CLM (hillFirstOrderPotential h)=
      physicalRestrictionL2CLM (hillFirstOrderDirection h)+physicalRestrictionL2CLM (hillFirstOrderPotential 0)
    rw [← map_add]
    congr 1
    simp [hillFirstOrderPotential,hillFirstOrderDirection_apply]
  have hr := intervalL2Representative_add (hillPhysicalDirection h) (U 0)
  rw [← he] at hr
  filter_upwards [hr,hillFirstOrder_upper_eq_neg_one_ae h,hillFirstOrder_upper_eq_neg_one_ae 0] with x hx hh h0
  have hf := congrArg Prod.fst hx
  change (intervalL2Representative (U h) x).1=
    (intervalL2Representative (hillPhysicalDirection h) x).1+(intervalL2Representative (U 0) x).1 at hf
  change (intervalL2Representative (U h) x).1= -1 at hh
  change (intervalL2Representative (U 0) x).1= -1 at h0
  rw [hh,h0] at hf
  linear_combination -hf

theorem hillDirichlet_kernelPairing_eq_integral (q h : Coeff 2) (z : ℂ) :
    I*l2KernelPairing (hillPhysicalDirection h)
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I))
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)) ⟨1,by norm_num⟩=
    ∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1)^2 := by
  rw [l2KernelPairing_apply,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_upper_zero_ae h] with x hx
  change (hillPhysicalDirection h).ofLp.1 x=0 at hx
  simp only [hx,zero_mul,zero_add]
  have he : (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z (0,1)) x).1=
      (NLS.LinearVolterra.extend (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)) x).1 := by
    simp only [NLS.LinearVolterra.extend,hillL2FrequencyStateCurve_apply,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero]
  rw [he]
  ring_nf
  simp only [I_sq]
  ring

theorem hillDirichlet_branch_fderiv_integral
    (q : Coeff 2) (hq : IsRealHillPotential q) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a q)
    (hz : ∀ᶠ p in 𝓝 q, hillL2DirichletCharacteristic p (a p)=0) (h : Coeff 2) :
    (fderiv ℂ a q) h=
      (∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
        ((NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt (a q)) (0,1)) x).1)^2)/
      (scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt (a q)) (0,1)) : ℂ) := by
  rw [hillDirichlet_branch_fderiv_kernel_mass q hq a ha hz h,hillDirichlet_kernelPairing_eq_integral]

end NLS.KdV
