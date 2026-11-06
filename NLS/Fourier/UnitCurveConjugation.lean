import NLS.Fourier.UnitWaveCurves

/-! # Physical conjugation of unit-interval Fourier curve data -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra
namespace NLS.Fourier

theorem unitCurveCoefficientsCLM_star (f : Curve ℂ) :
    unitCurveCoefficientsCLM (star f)=star (Coeff.reflection (unitCurveCoefficientsCLM f)) := by
  ext k
  simp only [unitCurveCoefficientsCLM_apply,unitCurveCoefficients_apply,lp.star_apply,Coeff.reflection_apply]
  change periodOneCoefficient (fun x => conj (extend f x)) k=conj (periodOneCoefficient (extend f) (-k))
  simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn]
  exact unitFourierCoefficient_conj _ _

/-- Physical conjugation commutes with the canonical even insertion. -/
theorem periodDouble_star_reflection {p : ℝ≥0∞} [Fact (1≤p)] (a : Coeff p) :
    Coeff.periodDouble (star (Coeff.reflection a))=star (Coeff.reflection (Coeff.periodDouble a)) := by
  ext k
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,Coeff.periodDouble_even]
    change conj (a (-(k/2)))=conj (Coeff.periodDouble a (-(2*(k/2))))
    rw [show -(2*(k/2))=2*(-(k/2)) by ring,Coeff.periodDouble_even]
  · have he : k=2*(k/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd]
    change 0=conj (Coeff.periodDouble a (-(2*(k/2)+1)))
    rw [show -(2*(k/2)+1)=2*(-(k/2)-1)+1 by ring,Coeff.periodDouble_odd,map_zero]

theorem periodDouble_unitCurveCoefficientsCLM_star (f : Curve ℂ) :
    Coeff.periodDouble (unitCurveCoefficientsCLM (star f))=
      star (Coeff.reflection (Coeff.periodDouble (unitCurveCoefficientsCLM f))) := by
  rw [unitCurveCoefficientsCLM_star,periodDouble_star_reflection]

theorem star_unitWaveCurve (k : ℤ) : star (unitWaveCurve k)=unitWaveCurve (-k) := by
  ext t
  change conj (wave (2*k) t)=wave (2*(-k)) t
  rw [show 2*(-k)=-(2*k) by ring,wave_neg]

/-- Conjugating an actual unit-wave derivative reverses its frequency. -/
theorem star_unitWaveCurve_derivative (k : ℤ) :
    star ((I*(Real.pi:ℂ)*(2*k:ℤ)) • unitWaveCurve k)=
      (I*(Real.pi:ℂ)*(2*(-k):ℤ)) • unitWaveCurve (-k) := by
  ext t
  change conj ((I*(Real.pi:ℂ)*(2*k:ℤ))*wave (2*k) t)=
    (I*(Real.pi:ℂ)*(2*(-k):ℤ))*wave (2*(-k)) t
  rw [show 2*(-k)=-(2*k) by ring,wave_neg]
  simp only [map_mul,conj_I,conj_ofReal,map_intCast,Int.cast_neg]
  ring

end NLS.Fourier
