import NLS.KdV.HillDirichletPotentialDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillL2DirichletDirectionKernel_normalization
    (q h : Coeff 2) (energy : ℂ) (hz : hillL2DirichletCharacteristic q energy=0) :
    hillL2DirichletDirectionKernel q h (Complex.sqrt energy)*hillL2DirichletSlope q energy=
      (-I)*(l2KernelPairing (hillPhysicalDirection h)
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt energy) (0,I))
        (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt energy) (0,I))
        ⟨1,by norm_num⟩) := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let z := Complex.sqrt energy
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let A := l2SolutionCurve u z (1,0)
  let C := l2SolutionCurve u z (0,1)
  let B := l2SolutionCurve u z (0,I)
  let H := hillPhysicalDirection h
  have hB : B=I • C := by
    have hh := l2SolutionCurve_linearCombination u z (0,I)
    change B=(0 : ℂ) • A+I • C at hh
    apply ContinuousMap.ext
    intro r
    have hp := congrArg (fun Y : Curve (ℂ × ℂ) => Y r) hh
    change B r=(0 : ℂ) • A r+I • C r at hp
    simpa only [zero_smul,zero_add,ContinuousMap.smul_apply] using hp
  have hC : C=(-I) • B := by rw [hB,smul_smul];simp
  have hzero : (B t).1=0 := by
    simpa only [hillL2DirichletCharacteristic,hillL2FrequencyStateDirichlet,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero] using hz
  have hCzero : (C t).1=0 := by
    have hh := congrArg (fun Y : Curve (ℂ × ℂ) => (Y t).1) hC
    simpa only [ContinuousMap.smul_apply,Prod.smul_fst,smul_eq_mul,hzero,mul_zero] using hh
  have hdet : (A t).1*(C t).2=1 := by
    have hh : (A t).1*(C t).2-(C t).1*(A t).2=1 := by
      simpa [l2FundamentalMatrix,Matrix.det_fin_two] using det_l2FundamentalMatrix u z t
    simpa only [hCzero,zero_mul,sub_zero] using hh
  have hg : hillL2DirichletSlope q energy=(C t).2 := by
    simp only [hillL2DirichletSlope,hillL2FrequencyDirichletSlope,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero]
    change (-I*z)*(B t).1+(-I)*(B t).2=(C t).2
    rw [hzero,mul_zero,zero_add,hB]
    simp only [ContinuousMap.smul_apply,Prod.smul_snd,smul_eq_mul]
    ring_nf
    simp only [I_sq]
    ring
  have hp : l2KernelPairing H C B t=(-I)*l2KernelPairing H B B t := by
    rw [hC,l2KernelPairing_smul]
    rfl
  change (l2KernelPairing H C B t*(A t).1-l2KernelPairing H A B t*(C t).1)*
    hillL2DirichletSlope q energy=(-I)*l2KernelPairing H B B t
  rw [hCzero,mul_zero,sub_zero,hg,hp]
  calc
    _ = ((-I)*l2KernelPairing H B B t)*((A t).1*(C t).2) := by ring
    _ = _ := by rw [hdet,mul_one]

end NLS.KdV
