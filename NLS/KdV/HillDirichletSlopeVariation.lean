import NLS.KdV.HillDirichletSlopePotentialDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillScalarPotentialKernel_basis (q h : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    let u := physicalRestrictionL2 (hillFirstOrderPotential q)
    let H := hillPhysicalDirection h
    let B := l2SolutionCurve u z (0,I)
    let C := l2SolutionCurve u z (1,-z)
    constantUpperStateMap z (l2PotentialKernelCurve u H z (0,I) t)=
      (-(I*l2KernelPairing H B B t)) • constantUpperStateMap z (C t)+
        (I*l2KernelPairing H C B t) • constantUpperStateMap z (B t) := by
  dsimp only
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let H := hillPhysicalDirection h
  let B := l2SolutionCurve u z (0,I)
  let C := l2SolutionCurve u z (1,-z)
  let E1 := l2SolutionCurve u z (1,0)
  let E2 := l2SolutionCurve u z (0,1)
  have hB : B=I • E2 := by
    have hh := l2SolutionCurve_linearCombination u z (0,I)
    change B=(0 : ℂ) • E1+I • E2 at hh
    apply ContinuousMap.ext
    intro r
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y r) hh
    change B r=(0 : ℂ) • E1 r+I • E2 r at hp
    simpa only [zero_smul,zero_add,ContinuousMap.smul_apply] using hp
  have hC : C=E1-z • E2 := by
    have hh := l2SolutionCurve_linearCombination u z (1,-z)
    change C=(1 : ℂ) • E1+(-z) • E2 at hh
    apply ContinuousMap.ext
    intro r
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y r) hh
    change C r=(1 : ℂ) • E1 r+(-z) • E2 r at hp
    simpa only [one_smul,neg_smul,sub_eq_add_neg,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
      ContinuousMap.add_apply,ContinuousMap.neg_apply] using hp
  have he2 : E2=(-I) • B := by rw [hB,smul_smul];simp
  have he1 : E1=C-(I*z) • B := by
    have hh : E1=C+z • E2 := (eq_sub_iff_add_eq.mp hC).symm
    rw [he2,smul_smul,show z*(-I)= -(I*z) by ring] at hh
    apply ContinuousMap.ext
    intro r
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y r) hh
    change E1 r=C r-(I*z) • B r
    change E1 r=C r+(-(I*z)) • B r at hp
    simpa only [neg_smul,sub_eq_add_neg] using hp
  change constantUpperStateMap z
    (l2KernelPairing H E2 B t • E1 t-l2KernelPairing H E1 B t • E2 t)=_
  rw [he1,he2,l2KernelPairing_sub,l2KernelPairing_smul,l2KernelPairing_smul]
  simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul]
  dsimp only [C,B,H,u]
  apply Prod.ext <;>
    simp only [constantUpperStateMap_apply,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
      Prod.fst_add,Prod.snd_add,smul_eq_mul] <;>
    ring_nf

theorem hillScalarPotentialPairing_eq_integral
    (q h : Coeff 2) (z : ℂ) (v w : ℂ × ℂ) :
    I*l2KernelPairing (hillPhysicalDirection h)
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v))
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z w))
      ⟨1,by norm_num⟩=
    ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v) x).1*
      (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z w) x).1 := by
  rw [l2KernelPairing_apply,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_upper_zero_ae h] with x hx
  change (hillPhysicalDirection h).ofLp.1 x=0 at hx
  simp only [hx,zero_mul,zero_add]
  have he (a : ℂ × ℂ) : (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z a) x).1=
      (NLS.LinearVolterra.extend (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
        (constantUpperInitialVector z a)) x).1 := by
    simp only [NLS.LinearVolterra.extend,hillL2FrequencyStateCurve_apply,constantUpperStateMap_apply]
  rw [he v,he w]
  ring_nf
  simp only [I_sq]
  ring

theorem hillL2DirichletSlope_potential_integral
    (q h : Coeff 2) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p energy) q) h=
      -(∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).1^2)*
        (hillL2FrequencyStateCurve q (Complex.sqrt energy) (1,0) ⟨1,by norm_num⟩).2+
      (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (1,0)) x).1*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).1)*
        hillL2DirichletSlope q energy := by
  let z := Complex.sqrt energy
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let H := hillPhysicalDirection h
  let B := l2SolutionCurve u z (0,I)
  let C := l2SolutionCurve u z (1,-z)
  have hb := congrArg Prod.snd (hillScalarPotentialKernel_basis q h z ⟨1,by norm_num⟩)
  rw [fderiv_hillL2DirichletSlope_potential]
  change hillL2DirichletSlopeDirectionKernel q h z=_
  change hillL2DirichletSlopeDirectionKernel q h z=
    -(I*l2KernelPairing H B B ⟨1,by norm_num⟩)*(constantUpperStateMap z (C ⟨1,by norm_num⟩)).2+
      (I*l2KernelPairing H C B ⟨1,by norm_num⟩)*(constantUpperStateMap z (B ⟨1,by norm_num⟩)).2 at hb
  rw [hb]
  have hss := hillScalarPotentialPairing_eq_integral q h z (0,1) (0,1)
  have hcs := hillScalarPotentialPairing_eq_integral q h z (1,0) (0,1)
  simp only [constantUpperInitialVector,mul_zero,mul_one,sub_zero,zero_sub] at hss hcs
  change I*l2KernelPairing H B B ⟨1,by norm_num⟩=_ at hss
  change I*l2KernelPairing H C B ⟨1,by norm_num⟩=_ at hcs
  rw [hss,hcs]
  simp only [hillL2FrequencyStateCurve_apply,hillL2DirichletSlope,hillL2FrequencyDirichletSlope,
    constantUpperInitialVector,mul_zero,mul_one,sub_zero,zero_sub]
  congr 2
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  ring

end NLS.KdV
