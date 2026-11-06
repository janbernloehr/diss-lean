import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.ClassicalHillDirichlet
import NLS.KdV.HillL2ConstantShift

/-! The actual L2 Hill Dirichlet characteristic, with the exact scalar
initial derivative normalization. Even square descent includes zero energy. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual first component with fixed first-order initial vector (0,i). -/
def hillL2FrequencyDirichlet (q : Coeff 2) (z : ℂ) : ℂ :=
  (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)
    ⟨1,by constructor <;> norm_num⟩).1

/-- Joint norm analyticity in the frequency and the original L2 potential. -/
theorem analyticOnNhd_hillL2FrequencyDirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichlet p.2 p.1) univ := by
  intro p _
  have hphi : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => hillFirstOrderPotential r.2) p :=
    analyticAt_const.prod analyticAt_snd.neg
  have hu := (physicalRestrictionL2CLM.analyticAt (hillFirstOrderPotential p.2)).comp
    (f := fun r : ℂ × Coeff 2 => hillFirstOrderPotential r.2) hphi
  have hs := (analyticOnNhd_l2SolutionCurve_joint (0,I)
    (p.1,physicalRestrictionL2 (hillFirstOrderPotential p.2)) (mem_univ _)).comp
      (f := fun r : ℂ × Coeff 2 => (r.1,physicalRestrictionL2 (hillFirstOrderPotential r.2)))
      (analyticAt_fst.prod hu)
  have he : AnalyticAt ℂ (fun r : ℂ × Coeff 2 =>
      l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential r.2)) r.1 (0,I)
        (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1)) p :=
    ((ContinuousMap.evalCLM ℂ
      (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1) :
        Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)).analyticAt _).comp hs
  exact analyticAt_fst.comp he

/-- Exact agreement with the independently constructed scalar IVP. -/
theorem hillL2FrequencyDirichlet_eq_classical (Q : C(AddCircle (2:ℝ),ℂ)) (z : ℂ) :
    hillL2FrequencyDirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z =
      classicalHillDirichlet (hillUnitPotentialCurve Q) (z^2) := by
  rw [hillL2FrequencyDirichlet,physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q),l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
  exact (classicalHillDirichlet_sq (hillUnitPotentialCurve Q) z).symm

/-- Frequency evenness follows from the actual scalar IVP and L2 density. -/
theorem hillL2FrequencyDirichlet_even (q : Coeff 2) (z : ℂ) :
    hillL2FrequencyDirichlet q (-z) = hillL2FrequencyDirichlet q z := by
  have hc (w : ℂ) : Continuous (fun a : Coeff 2 => hillL2FrequencyDirichlet a w) := by
    have h : Continuous (fun r : ℂ × Coeff 2 => hillL2FrequencyDirichlet r.2 r.1) :=
      analyticOnNhd_hillL2FrequencyDirichlet_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (w,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyDirichlet (Coeff.ofFinsupp (p := 2) a) (-z) =
      hillL2FrequencyDirichlet (Coeff.ofFinsupp (p := 2) a) z := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ,hillL2FrequencyDirichlet_eq_classical,hillL2FrequencyDirichlet_eq_classical,neg_sq]
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    (hc (-z)) (hc z) (funext hfinite)) q

/-- The actual L2 energy characteristic; the root choice is inessential. -/
def hillL2Dirichlet (q : Coeff 2) (lambda : ℂ) : ℂ :=
  hillL2FrequencyDirichlet q (Complex.sqrt lambda)

/-- Exact frequency pullback at every frequency, including zero. -/
theorem hillL2Dirichlet_sq (q : Coeff 2) (z : ℂ) :
    hillL2Dirichlet q (z^2) = hillL2FrequencyDirichlet q z := by
  have hsq := (ComplexAnalysis.complex_sqrt_sq (z^2))
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z hsq with h | h
  · simp only [hillL2Dirichlet,h]
  · simp only [hillL2Dirichlet,h,hillL2FrequencyDirichlet_even]

/-- The genuine scalar characteristic is jointly entire in energy and L2 potential. -/
theorem analyticOnNhd_hillL2Dirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2Dirichlet p.2 p.1) univ :=
  ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichlet p.2 p.1)
    analyticOnNhd_hillL2FrequencyDirichlet_joint hillL2FrequencyDirichlet_even
    Complex.sqrt ComplexAnalysis.complex_sqrt_sq

/-- Continuous potentials recover their actual position/derivative normalization. -/
theorem hillL2Dirichlet_eq_classical (Q : C(AddCircle (2:ℝ),ℂ)) (lambda : ℂ) :
    hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda =
      classicalHillDirichlet (hillUnitPotentialCurve Q) lambda := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [hillL2Dirichlet_sq,hillL2FrequencyDirichlet_eq_classical]

/-- The exact free zero-energy normalization, with no spurious root at zero. -/
theorem hillL2Dirichlet_free_zero : hillL2Dirichlet 0 0 = 1 := by
  have hcoef : SpectralWeight.one.toCoeff (hillContinuousCoefficients 0) = (0:Coeff 2) := by
    ext k
    simp [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,fourierCoeff]
  rw [← hcoef,hillL2Dirichlet_eq_classical]
  have hcurve : hillUnitPotentialCurve 0 = 0 := by ext t; rfl
  rw [hcurve,classicalHillDirichlet_free_zero]

/-- The actual L2 Dirichlet characteristic has the physical constant-shift law. -/
theorem hillL2Dirichlet_add_const (q : Coeff 2) (c lambda : ℂ) :
    hillL2Dirichlet (q+lp.single 2 0 c) (lambda+c) = hillL2Dirichlet q lambda := by
  have hc (mu : ℂ) : Continuous (fun a : Coeff 2 => hillL2Dirichlet a mu) := by
    have h : Continuous (fun r : ℂ × Coeff 2 => hillL2Dirichlet r.2 r.1) :=
      analyticOnNhd_hillL2Dirichlet_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (mu,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hcont (Q : C(AddCircle (2:ℝ),ℂ)) :
      hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)+lp.single 2 0 c)
        (lambda+c) = hillL2Dirichlet (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda := by
    have hcoef (P : C(AddCircle (2:ℝ),ℂ)) :
        continuousFourierCLM P = SpectralWeight.one.toCoeff (hillContinuousCoefficients P) := by
      ext k
      rw [continuousFourierCLM_apply]
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
    rw [← hcoef,← continuousFourierCLM_const c,← map_add,hcoef,
      hillL2Dirichlet_eq_classical]
    rw [hcoef Q,hillL2Dirichlet_eq_classical]
    have hcurve : hillUnitPotentialCurve (Q+ContinuousMap.const _ c) =
        hillUnitPotentialCurve Q+ContinuousMap.const _ c := by ext t; rfl
    rw [hcurve,classicalHillDirichlet_add_const,add_sub_cancel_right]
  have hfinite (a : ℤ →₀ ℂ) :
      hillL2Dirichlet (Coeff.ofFinsupp (p := 2) a+lp.single 2 0 c) (lambda+c) =
        hillL2Dirichlet (Coeff.ofFinsupp (p := 2) a) lambda := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ]
    exact hcont Q
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (lambda+c)).comp (continuous_id.add continuous_const)) (hc lambda) (funext hfinite)) q

/-- The normalized L2 energy characteristic agrees with the original state-vector characteristic. -/
theorem hillL2Dirichlet_eq_characteristic (q : Coeff 2) (E : ℂ) :
    hillL2Dirichlet q E = hillL2DirichletCharacteristic q E := by
  simp only [hillL2Dirichlet,hillL2DirichletCharacteristic,hillL2FrequencyDirichlet,
    hillL2FrequencyStateDirichlet,constantUpperStateMap_apply,constantUpperInitialVector,
    mul_zero,mul_one,sub_zero]

end NLS.KdV
