import NLS.KdV.HillIndexedDiscriminantSources
import NLS.Fourier.ContinuousConjugation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Pointwise real continuous potentials have the original conjugate-reflected Hill coefficients. -/
theorem isReal_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ),ℂ))
    (hQ : ∀ x, (Q x).im=0) : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) := by
  have hstar : star Q=Q := by
    ext x
    exact Complex.conj_eq_iff_im.mpr (hQ x)
  intro k
  have h := congrArg (fun p : Coeff 2 => p (-k)) (Fourier.continuousFourierCLM_star Q)
  rw [hstar] at h
  simpa only [lp.star_apply,Complex.star_def,Coeff.reflection_apply,neg_neg,SpectralWeight.toCoeff_apply,
    hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply] using h

/-- The actual coefficient source of a real closed physical curve is a real Hill direction. -/
theorem isReal_hillClosedCurveCoefficients (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) (hreal : ∀ t, (f t).im=0) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillClosedCurveCoefficients f hf)) := by
  apply isReal_hillContinuousCoefficients
  intro x
  refine Quotient.inductionOn x ?_
  intro t
  change (f (projIcc 0 1 (by norm_num)
    ((AddCircle.equivIoc (1 : ℝ) 0) (t : AddCircle (1 : ℝ))).val)).im=0
  exact hreal _

/-- The actual spatial discriminant gradient is real at real spectral energy. -/
theorem hillEnergyDiscriminantGradientSpatialCurve_real (p : Coeff 2) (hp : IsRealHillPotential p)
    (E : ℝ) (t : Icc (0 : ℝ) 1) : (hillEnergyDiscriminantGradientSpatialCurve p E t).im=0 := by
  let S := hillL2FrequencyStateCurve p (Complex.sqrt (E : ℂ)) (0,1)
  let C := hillL2FrequencyStateCurve p (Complex.sqrt (E : ℂ)) (1,0)
  have hC (u : Icc (0 : ℝ) 1) : (C u).1.im=0 ∧ (C u).2.im=0 :=
    hillL2FrequencyStateCurve_real p hp _ (by rw [complex_sqrt_sq];rfl) (1,0) (by norm_num) u
  have hS (u : Icc (0 : ℝ) 1) : (S u).1.im=0 ∧ (S u).2.im=0 :=
    hillL2FrequencyStateCurve_real p hp _ (by rw [complex_sqrt_sq];rfl) (0,1) (by norm_num) u
  change ((2*(S ⟨1,by norm_num⟩).1)*((C t).1*(C t).2)+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1)*((C t).2*(S t).1+(C t).1*(S t).2)-
    (2*(C ⟨1,by norm_num⟩).2)*((S t).1*(S t).2)).im=0
  simp only [add_im,sub_im,mul_im,(hC t).1,(hC t).2,(hS t).1,(hS t).2,
    (hC ⟨1,by norm_num⟩).1,(hC ⟨1,by norm_num⟩).2,
    (hS ⟨1,by norm_num⟩).1,(hS ⟨1,by norm_num⟩).2,
    im_ofNat,mul_zero,zero_mul,add_zero,sub_zero]

/-- The actual fixed-real-energy discriminant Hamiltonian source is a real Hill direction. -/
theorem isReal_hillEnergyHamiltonianSource (p : Coeff 2) (hp : IsRealHillPotential p) (E : ℝ) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource p E)) := by
  apply isReal_hillClosedCurveCoefficients
  intro t
  change (-(hillEnergyDiscriminantGradientSpatialCurve p E t)).im=0
  rw [neg_im,hillEnergyDiscriminantGradientSpatialCurve_real p hp E t,neg_zero]

/-- The indexed actual isospectral sources stay in the real physical source form. -/
theorem isReal_hillIndexedDiscriminantHamiltonianSource
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q n hn)) :=
  isReal_hillEnergyHamiltonianSource _ q.property.2 _

end NLS.KdV
