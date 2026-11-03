import NLS.KdV.HillL2EnergyDiscriminant
import NLS.KdV.ClassicalHillFlow
import NLS.KdV.ClassicalHillGreen

/-! # The actual rough Hill Dirichlet characteristic and its entire energy descent. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def hillL2FrequencyDirichlet (q : Coeff 2) (z : ℂ) : ℂ :=
  (constantUpperStateMap z
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z (0,1)) ⟨1,by norm_num⟩)).1

theorem analyticOnNhd_hillL2FrequencyDirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichlet p.2 p.1) univ := by
  intro p _
  have hphi : AnalyticAt ℂ (fun a : ℂ × Coeff 2 => hillFirstOrderPotential a.2) p :=
    analyticAt_const.prod analyticAt_snd.neg
  have hu := (physicalRestrictionL2CLM.analyticAt (hillFirstOrderPotential p.2)).comp (f := fun a : ℂ × Coeff 2 => hillFirstOrderPotential a.2) hphi
  have hh := (analyticOnNhd_l2SolutionCurve_joint (0,I)
    (p.1,physicalRestrictionL2 (hillFirstOrderPotential p.2)) (mem_univ _)).comp
      (f := fun a : ℂ × Coeff 2 => (a.1,physicalRestrictionL2 (hillFirstOrderPotential a.2)))
      (analyticAt_fst.prod hu)
  have he := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hh
  convert! analyticAt_fst.comp he using 1
  simp only [hillL2FrequencyDirichlet,constantUpperStateMap_apply,constantUpperInitialVector,
    mul_zero,mul_one,sub_zero]
  rfl

theorem hillL2FrequencyDirichlet_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z : ℂ) :
    hillL2FrequencyDirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z =
      (classicalHillFlow (hillUnitPotentialCurve Q) (z^2) (0,1) 1).1 := by
  rw [hillL2FrequencyDirichlet,physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q),l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
  have h := classicalHillFlow_eq_constantUpper (hillUnitPotentialCurve Q) z (0,1) ⟨1,by norm_num⟩
  exact (congrArg Prod.fst h).symm

theorem hillL2FrequencyDirichlet_even (q : Coeff 2) (z : ℂ) :
    hillL2FrequencyDirichlet q (-z)=hillL2FrequencyDirichlet q z := by
  have hc (y : ℂ) : Continuous (fun a : Coeff 2 => hillL2FrequencyDirichlet a y) := by
    have h : Continuous (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichlet p.2 p.1) := continuous_iff_continuousAt.mpr
      (fun p : ℂ × Coeff 2 => (analyticOnNhd_hillL2FrequencyDirichlet_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun a : Coeff 2 => (y,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyDirichlet (Coeff.ofFinsupp (p := 2) a) (-z) =
      hillL2FrequencyDirichlet (Coeff.ofFinsupp (p := 2) a) z := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    rw [← he,hillL2FrequencyDirichlet_eq_classical,hillL2FrequencyDirichlet_eq_classical]
    congr 2
    ring
  have he : (fun a : Coeff 2 => hillL2FrequencyDirichlet a (-z)) =
      (fun a : Coeff 2 => hillL2FrequencyDirichlet a z) := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc (-z)) (hc z) (funext hfinite)
  exact congrFun he q

def hillL2DirichletCharacteristic (q : Coeff 2) (energy : ℂ) : ℂ :=
  hillL2FrequencyDirichlet q (Complex.sqrt energy)

theorem analyticOnNhd_hillL2DirichletCharacteristic_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2DirichletCharacteristic p.2 p.1) univ :=
  NLS.ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichlet p.2 p.1)
    analyticOnNhd_hillL2FrequencyDirichlet_joint hillL2FrequencyDirichlet_even
    Complex.sqrt NLS.ComplexAnalysis.complex_sqrt_sq

theorem hillL2DirichletCharacteristic_sq (q : Coeff 2) (z : ℂ) :
    hillL2DirichletCharacteristic q (z^2)=hillL2FrequencyDirichlet q z := by
  have hs : (Complex.sqrt (z^2))^2=z^2 := NLS.ComplexAnalysis.complex_sqrt_sq _
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z hs with h | h
  · simp only [hillL2DirichletCharacteristic,h]
  · simp only [hillL2DirichletCharacteristic,h,hillL2FrequencyDirichlet_even]

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
