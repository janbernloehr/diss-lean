import NLS.KdV.HillL2Dirichlet
import NLS.KdV.HillDirichletSlope

/-! The terminal physical derivative of the normalized scalar Dirichlet solution.
The derivative, energy translation and square descent retain the actual IVP. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open NLS.ZakharovShabat
namespace NLS.KdV

/-- The physical terminal derivative, for initial position zero and derivative one. -/
def classicalHillDirichletTerminal (q : Curve ℂ) (lambda : ℂ) : ℂ :=
  (classicalHillFlow q lambda (0,1) 1).2

theorem classicalHillDirichletTerminal_sq (q : Curve ℂ) (z : ℂ) :
    classicalHillDirichletTerminal q (z^2) =
      (-I*z)*(classicalSolution (constantUpperPotential q) z (0,I) 1).1+
        (-I)*(classicalSolution (constantUpperPotential q) z (0,I) 1).2 := by
  have h := classicalHillFlow_eq_constantUpper q z (0,1)
    ⟨1,by constructor <;> norm_num⟩
  simpa only [classicalHillDirichletTerminal,constantUpperStateMap_apply,constantUpperInitialVector,
    mul_zero,mul_one,sub_zero] using congrArg Prod.snd h

theorem classicalHillDirichletTerminal_add_const (q : Curve ℂ) (c lambda : ℂ) :
    classicalHillDirichletTerminal (q+ContinuousMap.const _ c) lambda =
      classicalHillDirichletTerminal q (lambda-c) := by
  have he : classicalHillCoefficientCurve (q+ContinuousMap.const _ c) lambda =
      classicalHillCoefficientCurve q (lambda-c) := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro v
    change (v.2,((q t+c)-lambda)*v.1) = (v.2,(q t-(lambda-c))*v.1)
    congr 1
    ring
  change (solution (classicalHillCoefficientCurve (q+ContinuousMap.const _ c) lambda) (0,1) 1).2 = _
  rw [he]
  rfl


/-- The actual physical derivative reconstructed from the fixed first-order state. -/
def hillL2FrequencyDirichletTerminal (q : Coeff 2) (z : ℂ) : ℂ :=
  let v := l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,I)
    ⟨1,by constructor <;> norm_num⟩
  (-I*z)*v.1+(-I)*v.2

/-- Joint norm analyticity in the frequency and the original L2 potential. -/
theorem analyticOnNhd_hillL2FrequencyDirichletTerminal_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichletTerminal p.2 p.1) univ := by
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
  exact ((analyticAt_const.mul analyticAt_fst).mul (analyticAt_fst.comp he)).add
    (analyticAt_const.mul (analyticAt_snd.comp he))

/-- Exact agreement with the independently constructed scalar IVP. -/
theorem hillL2FrequencyDirichletTerminal_eq_classical (Q : C(AddCircle (2:ℝ),ℂ)) (z : ℂ) :
    hillL2FrequencyDirichletTerminal (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z =
      classicalHillDirichletTerminal (hillUnitPotentialCurve Q) (z^2) := by
  rw [hillL2FrequencyDirichletTerminal,physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q),l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
  exact (classicalHillDirichletTerminal_sq (hillUnitPotentialCurve Q) z).symm

/-- Frequency evenness follows from the actual scalar IVP and L2 density. -/
theorem hillL2FrequencyDirichletTerminal_even (q : Coeff 2) (z : ℂ) :
    hillL2FrequencyDirichletTerminal q (-z) = hillL2FrequencyDirichletTerminal q z := by
  have hc (w : ℂ) : Continuous (fun a : Coeff 2 => hillL2FrequencyDirichletTerminal a w) := by
    have h : Continuous (fun r : ℂ × Coeff 2 => hillL2FrequencyDirichletTerminal r.2 r.1) :=
      analyticOnNhd_hillL2FrequencyDirichletTerminal_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (w,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyDirichletTerminal (Coeff.ofFinsupp (p := 2) a) (-z) =
      hillL2FrequencyDirichletTerminal (Coeff.ofFinsupp (p := 2) a) z := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ,hillL2FrequencyDirichletTerminal_eq_classical,hillL2FrequencyDirichletTerminal_eq_classical,neg_sq]
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    (hc (-z)) (hc z) (funext hfinite)) q

/-- The actual terminal physical derivative; the square-root choice is inessential. -/
def hillL2DirichletTerminal (q : Coeff 2) (lambda : ℂ) : ℂ :=
  hillL2FrequencyDirichletTerminal q (Complex.sqrt lambda)

/-- Exact frequency pullback at every frequency, including zero. -/
theorem hillL2DirichletTerminal_sq (q : Coeff 2) (z : ℂ) :
    hillL2DirichletTerminal q (z^2) = hillL2FrequencyDirichletTerminal q z := by
  have hsq := (ComplexAnalysis.complex_sqrt_sq (z^2))
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z hsq with h | h
  · simp only [hillL2DirichletTerminal,h]
  · simp only [hillL2DirichletTerminal,h,hillL2FrequencyDirichletTerminal_even]

/-- The terminal physical derivative is jointly entire in energy and L2 potential. -/
theorem analyticOnNhd_hillL2DirichletTerminal_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2DirichletTerminal p.2 p.1) univ :=
  ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillL2FrequencyDirichletTerminal p.2 p.1)
    analyticOnNhd_hillL2FrequencyDirichletTerminal_joint hillL2FrequencyDirichletTerminal_even
    Complex.sqrt ComplexAnalysis.complex_sqrt_sq

/-- Continuous potentials recover their actual position/derivative normalization. -/
theorem hillL2DirichletTerminal_eq_classical (Q : C(AddCircle (2:ℝ),ℂ)) (lambda : ℂ) :
    hillL2DirichletTerminal (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda =
      classicalHillDirichletTerminal (hillUnitPotentialCurve Q) lambda := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [hillL2DirichletTerminal_sq,hillL2FrequencyDirichletTerminal_eq_classical]

/-- The terminal physical derivative has the exact constant-shift law. -/
theorem hillL2DirichletTerminal_add_const (q : Coeff 2) (c lambda : ℂ) :
    hillL2DirichletTerminal (q+lp.single 2 0 c) (lambda+c) = hillL2DirichletTerminal q lambda := by
  have hc (mu : ℂ) : Continuous (fun a : Coeff 2 => hillL2DirichletTerminal a mu) := by
    have h : Continuous (fun r : ℂ × Coeff 2 => hillL2DirichletTerminal r.2 r.1) :=
      analyticOnNhd_hillL2DirichletTerminal_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => (mu,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  have hcont (Q : C(AddCircle (2:ℝ),ℂ)) :
      hillL2DirichletTerminal (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)+lp.single 2 0 c)
        (lambda+c) = hillL2DirichletTerminal (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda := by
    have hcoef (P : C(AddCircle (2:ℝ),ℂ)) :
        continuousFourierCLM P = SpectralWeight.one.toCoeff (hillContinuousCoefficients P) := by
      ext k
      rw [continuousFourierCLM_apply]
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
    rw [← hcoef,← continuousFourierCLM_const c,← map_add,hcoef,
      hillL2DirichletTerminal_eq_classical]
    rw [hcoef Q,hillL2DirichletTerminal_eq_classical]
    have hcurve : hillUnitPotentialCurve (Q+ContinuousMap.const _ c) =
        hillUnitPotentialCurve Q+ContinuousMap.const _ c := by ext t; rfl
    rw [hcurve,classicalHillDirichletTerminal_add_const,add_sub_cancel_right]
  have hfinite (a : ℤ →₀ ℂ) :
      hillL2DirichletTerminal (Coeff.ofFinsupp (p := 2) a+lp.single 2 0 c) (lambda+c) =
        hillL2DirichletTerminal (Coeff.ofFinsupp (p := 2) a) lambda := by
    let Q := continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact fourierCoeff_continuousSynthesis _ k
    rw [← hQ]
    exact hcont Q
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (lambda+c)).comp (continuous_id.add continuous_const)) (hc lambda) (funext hfinite)) q

/-- The reused terminal derivative is exactly the original physical slope. -/
theorem hillL2DirichletTerminal_eq_slope (q : Coeff 2) (E : ℂ) :
    hillL2DirichletTerminal q E=hillL2DirichletSlope q E := by
  simp only [hillL2DirichletTerminal,hillL2FrequencyDirichletTerminal,
    hillL2DirichletSlope,hillL2FrequencyDirichletSlope,constantUpperStateMap_apply,
    constantUpperInitialVector,mul_zero,mul_one,sub_zero]

end NLS.KdV
