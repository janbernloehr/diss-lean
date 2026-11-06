import NLS.KdV.HillDirichletSimplicity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillL2FrequencyDirichletSlope (q : Coeff 2) (z : ℂ) : ℂ :=
  (constantUpperStateMap z
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z (0,1)) ⟨1,by norm_num⟩)).2

theorem analyticOnNhd_hillL2FrequencyDirichletSlope_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichletSlope p.2 p.1) univ := by
  intro p _
  have hphi : AnalyticAt ℂ (fun a : ℂ × Coeff 2 => hillFirstOrderPotential a.2) p :=
    analyticAt_const.prod analyticAt_snd.neg
  have hu := (physicalRestrictionL2CLM.analyticAt (hillFirstOrderPotential p.2)).comp (f := fun a : ℂ × Coeff 2 => hillFirstOrderPotential a.2) hphi
  have hh := (analyticOnNhd_l2SolutionCurve_joint (0,I)
    (p.1,physicalRestrictionL2 (hillFirstOrderPotential p.2)) (mem_univ _)).comp
      (f := fun a : ℂ × Coeff 2 => (a.1,physicalRestrictionL2 (hillFirstOrderPotential a.2)))
      (analyticAt_fst.prod hu)
  have he := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hh
  have h1 : AnalyticAt ℂ (fun a : ℂ × Coeff 2 =>
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential a.2)) a.1 (0,I) ⟨1,by norm_num⟩).1) p :=
    analyticAt_fst.comp he
  have h2 : AnalyticAt ℂ (fun a : ℂ × Coeff 2 =>
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential a.2)) a.1 (0,I) ⟨1,by norm_num⟩).2) p :=
    analyticAt_snd.comp he
  have hz : AnalyticAt ℂ (fun a : ℂ × Coeff 2 => -I*a.1) p := analyticAt_const.mul analyticAt_fst
  have hh2 := (hz.mul h1).add ((analyticAt_const (v := (-I : ℂ))).mul h2)
  convert! hh2 using 1
  simp only [hillL2FrequencyDirichletSlope,constantUpperStateMap_apply,constantUpperInitialVector,
    mul_zero,mul_one,sub_zero]
  rfl

theorem hillL2FrequencyDirichletSlope_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z : ℂ) :
    hillL2FrequencyDirichletSlope (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z =
      (classicalHillFlow (hillUnitPotentialCurve Q) (z^2) (0,1) 1).2 := by
  rw [hillL2FrequencyDirichletSlope,physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q),l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
  have h := classicalHillFlow_eq_constantUpper (hillUnitPotentialCurve Q) z (0,1) ⟨1,by norm_num⟩
  exact (congrArg Prod.snd h).symm

theorem hillL2FrequencyDirichletSlope_even (q : Coeff 2) (z : ℂ) :
    hillL2FrequencyDirichletSlope q (-z)=hillL2FrequencyDirichletSlope q z := by
  have hc (y : ℂ) : Continuous (fun a : Coeff 2 => hillL2FrequencyDirichletSlope a y) := by
    have h : Continuous (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichletSlope p.2 p.1) := continuous_iff_continuousAt.mpr
      (fun p : ℂ × Coeff 2 => (analyticOnNhd_hillL2FrequencyDirichletSlope_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun a : Coeff 2 => (y,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyDirichletSlope (Coeff.ofFinsupp (p := 2) a) (-z) =
      hillL2FrequencyDirichletSlope (Coeff.ofFinsupp (p := 2) a) z := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    rw [← he,hillL2FrequencyDirichletSlope_eq_classical,hillL2FrequencyDirichletSlope_eq_classical]
    congr 2
    ring
  have he : (fun a : Coeff 2 => hillL2FrequencyDirichletSlope a (-z)) =
      (fun a : Coeff 2 => hillL2FrequencyDirichletSlope a z) := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc (-z)) (hc z) (funext hfinite)
  exact congrFun he q

def hillL2DirichletSlope (q : Coeff 2) (energy : ℂ) : ℂ :=
  hillL2FrequencyDirichletSlope q (Complex.sqrt energy)

theorem analyticOnNhd_hillL2DirichletSlope_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2DirichletSlope p.2 p.1) univ :=
  NLS.ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichletSlope p.2 p.1)
    analyticOnNhd_hillL2FrequencyDirichletSlope_joint hillL2FrequencyDirichletSlope_even
    Complex.sqrt NLS.ComplexAnalysis.complex_sqrt_sq

theorem hillL2DirichletSlope_sq (q : Coeff 2) (z : ℂ) :
    hillL2DirichletSlope q (z^2)=hillL2FrequencyDirichletSlope q z := by
  have hs : (Complex.sqrt (z^2))^2=z^2 := NLS.ComplexAnalysis.complex_sqrt_sq _
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z hs with h | h
  · simp only [hillL2DirichletSlope,h]
  · simp only [hillL2DirichletSlope,h,hillL2FrequencyDirichletSlope_even]

theorem analyticOnNhd_hillL2DirichletSlope (q : Coeff 2) :
    AnalyticOnNhd ℂ (hillL2DirichletSlope q) univ := by
  intro z _
  exact (analyticOnNhd_hillL2DirichletSlope_joint (z,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem hillL2DirichletSlope_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (energy : ℂ) :
    hillL2DirichletSlope (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) energy =
      (classicalHillFlow (hillUnitPotentialCurve Q) energy (0,1) 1).2 := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq energy (by norm_num : 0<2)
  rw [hillL2DirichletSlope_sq,hillL2FrequencyDirichletSlope_eq_classical]


theorem hillL2DirichletSlope_real (q : Coeff 2) (hq : IsRealHillPotential q) (x : ℝ) :
    (hillL2DirichletSlope q x).im=0 := by
  exact (hillL2FrequencyStateCurve_real q hq (Complex.sqrt x)
    (by rw [NLS.ComplexAnalysis.complex_sqrt_sq];exact Complex.ofReal_im x)
    (0,1) (by norm_num) ⟨1,by norm_num⟩).2

theorem hillL2DirichletSlope_ne_zero_at_dirichlet_zero
    (q : Coeff 2) (hq : IsRealHillPotential q) (energy : ℂ)
    (hz : hillL2DirichletCharacteristic q energy=0) : hillL2DirichletSlope q energy≠0 := by
  intro he
  have hn := hillL2Dirichlet_derivative_normalization q hq energy hz
  change deriv (hillL2DirichletCharacteristic q) energy*hillL2DirichletSlope q energy=_ at hn
  rw [he,mul_zero] at hn
  have hm := hillL2FrequencyStateCurve_mass_pos q (Complex.sqrt energy) (0,1)
    (by intro h;have hh := congrArg Prod.snd h;norm_num at hh)
  have hz' : NLS.ComplexAnalysis.scalarStateMass (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))=0 :=
    Complex.ofReal_eq_zero.mp hn.symm
  linarith

end NLS.KdV
