import NLS.Fourier.ContinuousSynthesis
import NLS.Fourier.IntervalL2Realization
import NLS.Fourier.IntervalCoefficientScaling
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Absolute Fourier summability forces matching interval endpoints

An ℓ¹ coefficient sequence synthesizes a continuous periodic function.
Interval L² uniqueness identifies it with the original continuous data,
including both endpoints. No converse or endpoint matching is assumed.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.Fourier

/-- Absolute summability of actual period-two integrals forces endpoint agreement. -/
theorem periodTwo_endpoints_eq_of_memlp_one (f : ℝ → ℂ) (hf : Continuous f)
    (hm : Memℓp (periodTwoCoefficient f) 1) : f 0 = f 2 := by
  let a : Coeff 1 := ⟨periodTwoCoefficient f,hm⟩
  let g : ℝ → ℂ := fun x => continuousSynthesis a (x : AddCircle (2 : ℝ))
  have hg : Continuous g := (continuousSynthesis a).continuous.comp (by fun_prop)
  have hmf := memLp_two_interval hf 0 2 (by norm_num)
  have hmg := memLp_two_interval hg 0 2 (by norm_num)
  have he : periodTwoL2Coefficients f hmf = periodTwoL2Coefficients g hmg := by
    ext n
    exact (periodTwoCoefficient_continuousSynthesis a n).symm
  have hfg : f =ᵐ[volume.restrict (Ioc 0 2)] g := by
    have h1 := circlePullback_periodTwoL2Coefficients f hmf
    have h2 := circlePullback_periodTwoL2Coefficients g hmg
    rw [he] at h1
    exact h1.symm.trans h2
  rw [restrict_Ioc_eq_restrict_Icc] at hfg
  have h := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 2) hfg hf.continuousOn hg.continuousOn
  calc
    f 0 = g 0 := h (by norm_num)
    _ = g 2 := by simp [g,AddCircle.coe_period]
    _ = f 2 := (h (by norm_num)).symm

/-- The endpoint obstruction applies to every positive interval length. -/
theorem interval_endpoints_eq_of_memlp_one (T : ℝ) (hT : 0 < T)
    (f : ℝ → ℂ) (hf : Continuous f) (hm : Memℓp (intervalFourierCoefficient T f) 1) :
    f 0 = f T := by
  have hd : Continuous (intervalDilation (T/2) f) := hf.comp (continuous_const.mul continuous_id)
  have hm' : Memℓp (periodTwoCoefficient (intervalDilation (T/2) f)) 1 := by
    simpa only [periodTwoCoefficient_intervalDilation_eq hT] using hm
  simpa [intervalDilation] using periodTwo_endpoints_eq_of_memlp_one _ hd hm'

/-- A continuous interval function with a boundary jump cannot have ℓ¹ Fourier coefficients. -/
theorem not_memlp_intervalFourierCoefficient_one_of_endpoints_ne
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f) (hne : f 0 ≠ f T) :
    ¬Memℓp (intervalFourierCoefficient T f) 1 :=
  fun hm => hne (interval_endpoints_eq_of_memlp_one T hT f hf hm)

end NLS.Fourier
