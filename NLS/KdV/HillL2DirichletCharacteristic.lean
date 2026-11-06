import NLS.KdV.HillL2Dirichlet
import NLS.KdV.ClassicalHillGreen

/-! Compatibility with the existing normalized frequency characteristic. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def hillL2DirichletCharacteristic (q : Coeff 2) (energy : ℂ) : ℂ :=
  (constantUpperStateMap (Complex.sqrt energy)
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (Complex.sqrt energy)
      (constantUpperInitialVector (Complex.sqrt energy) (0,1)) ⟨1,by norm_num⟩)).1

/-- The physical-state characteristic is the retained derivative-one scalar characteristic. -/
theorem hillL2DirichletCharacteristic_eq_retained (q : Coeff 2) (energy : ℂ) :
    hillL2DirichletCharacteristic q energy = hillL2Dirichlet q energy := by
  simp only [hillL2DirichletCharacteristic,hillL2Dirichlet,hillL2FrequencyDirichlet,
    constantUpperStateMap_apply,constantUpperInitialVector,mul_zero,mul_one,sub_zero]

theorem hillL2Dirichlet_eq_characteristic (q : Coeff 2) (energy : ℂ) :
    hillL2Dirichlet q energy = hillL2DirichletCharacteristic q energy :=
  (hillL2DirichletCharacteristic_eq_retained q energy).symm

theorem analyticOnNhd_hillL2DirichletCharacteristic_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2DirichletCharacteristic p.2 p.1) univ := by
  simpa only [hillL2DirichletCharacteristic_eq_retained] using analyticOnNhd_hillL2Dirichlet_joint

theorem hillL2DirichletCharacteristic_sq (q : Coeff 2) (z : ℂ) :
    hillL2DirichletCharacteristic q (z^2) = hillL2FrequencyDirichlet q z := by
  rw [hillL2DirichletCharacteristic_eq_retained,hillL2Dirichlet_sq]

theorem analyticOnNhd_hillL2DirichletCharacteristic (q : Coeff 2) :
    AnalyticOnNhd ℂ (hillL2DirichletCharacteristic q) univ := by
  intro z _
  exact (analyticOnNhd_hillL2DirichletCharacteristic_joint (z,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem hillL2DirichletCharacteristic_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (energy : ℂ) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) energy =
      (classicalHillFlow (hillUnitPotentialCurve Q) energy (0,1) 1).1 := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq energy (by norm_num : 0<2)
  rw [hillL2DirichletCharacteristic_sq,hillL2FrequencyDirichlet_eq_classical]
  rfl

theorem classicalHillFlow_energy_im_eq_zero_of_dirichlet
    (q : Curve ℂ) (hq : ∀ t, (q t).im=0) (energy : ℂ)
    (hend : (classicalHillFlow q energy (0,1) 1).1=0) : energy.im=0 := by
  have hi := classicalHillGreen_im_identity q energy (0,1) hq
  simp only [hend,map_zero,zero_mul,zero_im,sub_self] at hi
  have hm := integral_classicalHillFlow_position_normSq_pos q energy (0,1)
    (by intro h; have hh := congrArg Prod.snd h; norm_num at hh)
  exact neg_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right hm.ne')

theorem hillL2DirichletCharacteristic_zero_real_of_continuous
    (Q : C(AddCircle (2 : ℝ),ℂ)) (hQ : ∀ x, (Q x).im=0) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) energy=0) :
    energy.im=0 := by
  rw [hillL2DirichletCharacteristic_eq_classical] at hz
  exact classicalHillFlow_energy_im_eq_zero_of_dirichlet (hillUnitPotentialCurve Q)
    (fun t => hQ (t.val : AddCircle (2 : ℝ))) energy hz

end NLS.KdV
