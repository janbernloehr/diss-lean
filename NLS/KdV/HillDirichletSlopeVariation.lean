import NLS.KdV.HillDirichletGradients

/-! # The actual rough Dirichlet slope source derivative

The verified L2 variation kernel, transported by the actual scalar state map,
gives the two scalar fundamental-state pairings with their exact signs.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The actual endpoint slope derivative is the second component of the
verified L2 potential kernel, in the physical scalar coordinates. -/
theorem fderiv_hillL2FrequencyDirichletSlope_potential
    (q h : Coeff 2) (z : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDirichletSlope p z) q) h=
      (constantUpperStateMap z (l2PotentialKernelCurve
        (physicalRestrictionL2 (hillFirstOrderPotential q)) (hillPhysicalDirection h) z (0,I)
          ⟨1,by norm_num⟩)).2 := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let U (p : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential p)
  let S (w : IntervalPairL2) := l2SolutionCurve w z (0,I)
  have hS : DifferentiableAt ℂ S u :=
    ((analyticOnNhd_l2SolutionCurve_joint (0,I) (z,u) (mem_univ _)).comp
      (f := fun w : IntervalPairL2 => (z,w)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcomp := hS.hasFDerivAt.comp q (hasFDerivAt_hillPhysicalPotential q)
  let E : Curve (ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      ((constantUpperStateMap z).comp (ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩))
  have heval := E.hasFDerivAt.comp q hcomp
  have heq : (fun p : Coeff 2 => E (S (U p)))=(fun p : Coeff 2 => hillL2FrequencyDirichletSlope p z) := by
    funext p
    simp only [E,S,U,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',
      ContinuousMap.evalCLM_apply,hillL2FrequencyDirichletSlope,constantUpperInitialVector,mul_zero,mul_one,sub_zero]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) heval.fderiv
  change (fderiv ℂ (fun p : Coeff 2 => E (S (U p))) q) h=E ((fderiv ℂ S u) (hillPhysicalDirection h)) at he
  rw [heq] at he
  rw [he]
  dsimp only [S]
  rw [fderiv_l2SolutionCurve_potential_eq_kernel]
  rfl

/-- The scalar state map fixes the exact two fundamental coefficients of the
actual endpoint potential kernel. No Dirichlet-root assumption is needed. -/
theorem hillL2DirichletSlopeKernel_eq_pairings (q h : Coeff 2) (z : ℂ) :
    (constantUpperStateMap z (l2PotentialKernelCurve
      (physicalRestrictionL2 (hillFirstOrderPotential q)) (hillPhysicalDirection h) z (0,I)
        ⟨1,by norm_num⟩)).2=
      -(I*l2KernelPairing (hillPhysicalDirection h)
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I))
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)) ⟨1,by norm_num⟩)*
          (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2+
      (I*l2KernelPairing (hillPhysicalDirection h)
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,-z))
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)) ⟨1,by norm_num⟩)*
          (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2 := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let H := hillPhysicalDirection h
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let A := l2SolutionCurve u z (1,0)
  let C := l2SolutionCurve u z (0,1)
  let B := l2SolutionCurve u z (0,I)
  let F := l2SolutionCurve u z (1,-z)
  have hB : B=I • C := by
    have hh := l2SolutionCurve_linearCombination u z (0,I)
    change B=(0 : ℂ) • A+I • C at hh
    apply ContinuousMap.ext
    intro t
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y t) hh
    change B t=(0 : ℂ) • A t+I • C t at hp
    simpa only [zero_smul,zero_add,ContinuousMap.smul_apply] using hp
  have hF : F=A-z • C := by
    have hh := l2SolutionCurve_linearCombination u z (1,-z)
    change F=(1 : ℂ) • A+(-z) • C at hh
    apply ContinuousMap.ext
    intro t
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y t) hh
    change F t=(1 : ℂ) • A t+(-z) • C t at hp
    change F t=A t-z • C t
    simpa only [one_smul,neg_smul,sub_eq_add_neg] using hp
  have hkB : l2KernelPairing H B B e=I*l2KernelPairing H C B e := by
    have hh := congrArg (fun Y : Curve ℂ => Y e) (l2KernelPairing_smul H I C B)
    change l2KernelPairing H (I • C) B e=I*l2KernelPairing H C B e at hh
    rw [← hB] at hh
    exact hh
  have hkF : l2KernelPairing H F B e=l2KernelPairing H A B e-z*l2KernelPairing H C B e := by
    rw [hF,l2KernelPairing_sub,l2KernelPairing_smul]
    rfl
  have hFp := congrArg (fun Y : Curve (ℂ × ℂ) => Y e) hF
  have hBp := congrArg (fun Y : Curve (ℂ × ℂ) => Y e) hB
  change F e=A e-z • C e at hFp
  change B e=I • C e at hBp
  simp only [hillL2FrequencyStateCurve_apply,constantUpperInitialVector,mul_zero,mul_one,sub_zero,zero_sub]
  change (constantUpperStateMap z (l2KernelPairing H C B e • A e-l2KernelPairing H A B e • C e)).2=
    -(I*l2KernelPairing H B B e)*(constantUpperStateMap z (F e)).2+
      (I*l2KernelPairing H F B e)*(constantUpperStateMap z (B e)).2
  rw [hkB,hkF,hFp,hBp,map_sub,map_smul,map_smul,map_sub,map_smul,map_smul]
  simp only [Prod.snd_sub,Prod.smul_snd,smul_eq_mul]
  ring_nf
  simp only [I_sq]
  ring

/-- The normalized kernel pairing is the literal scalar forcing integral
for arbitrary actual rough fundamental states. -/
theorem hillScalar_kernelPairing_eq_integral (q h : Coeff 2) (z : ℂ) (v w : ℂ × ℂ) :
    I*l2KernelPairing (hillPhysicalDirection h)
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v))
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z w)) ⟨1,by norm_num⟩=
    ∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      (extend (hillL2FrequencyStateCurve q z v) x).1*(extend (hillL2FrequencyStateCurve q z w) x).1 := by
  rw [l2KernelPairing_apply,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_upper_zero_ae h] with x hx
  change (hillPhysicalDirection h).ofLp.1 x=0 at hx
  simp only [hx,zero_mul,zero_add,NLS.LinearVolterra.extend,hillL2FrequencyStateCurve_apply,
    constantUpperStateMap_apply]
  ring_nf
  simp only [I_sq]
  ring

/-- Actual scalar variation of the rough Dirichlet slope, valid at every energy. -/
theorem fderiv_hillL2DirichletSlope_integral (q h : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p E) q) h=
      -(hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2*
        (∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
          (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1^2)+
      hillL2DirichletSlope q E*
        (∫ x in (0 : ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
          (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0)) x).1*
          (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1) := by
  change (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDirichletSlope p (Complex.sqrt E)) q) h=_
  rw [fderiv_hillL2FrequencyDirichletSlope_potential q h (Complex.sqrt E),hillL2DirichletSlopeKernel_eq_pairings]
  have hA := hillScalar_kernelPairing_eq_integral q h (Complex.sqrt E) (0,1) (0,1)
  have hB := hillScalar_kernelPairing_eq_integral q h (Complex.sqrt E) (1,0) (0,1)
  simp only [constantUpperInitialVector,mul_zero,mul_one,sub_zero,zero_sub] at hA hB
  rw [hA,hB]
  have heq : (fun x : ℝ => -(hillPhysicalDirection h).ofLp.2 x*
      (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1*
      (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1)=
    (fun x : ℝ => -(hillPhysicalDirection h).ofLp.2 x*
      (extend (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)) x).1^2) := by funext x;ring
  rw [heq]
  have hβ : hillL2DirichletSlope q E=(hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2 := rfl
  rw [hβ]
  change -(∫ x in (0 : ℝ)..1, _)*_+_*(hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2=_
  ring

end NLS.KdV
