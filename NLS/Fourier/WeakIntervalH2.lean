import NLS.FunctionalAnalysis.WeakDerivativeUnitIntervalAC
import NLS.Fourier.UnitIntervalL2Equiv
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The full weak H2 domain on the unit interval

The data are actual Lebesgue L2 classes for the value and its first two
distributional derivatives, tested only against compact interior tests.
There are no endpoint, periodicity or preselected-continuity conditions.
-/
noncomputable section
open Set MeasureTheory NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.Fourier

structure WeakIntervalH2 where
  value : IntervalL2
  first : IntervalL2
  second : IntervalL2
  weak_first : HasUnitIntervalWeakDerivative value first
  weak_second : HasUnitIntervalWeakDerivative first second

theorem WeakIntervalH2.exists_ac_representative (f : WeakIntervalH2) :
    ∃ F : ℝ → ℂ, Continuous F ∧ AbsolutelyContinuousOnInterval F 0 1 ∧
      f.value =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] F ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt F (f.first x) x :=
  exists_unitInterval_ac_of_weak_derivative f.value f.first
    ((Lp.memLp f.value).integrable (by norm_num)) ((Lp.memLp f.first).integrable (by norm_num)) f.weak_first

theorem WeakIntervalH2.exists_ac_derivative_representative (f : WeakIntervalH2) :
    ∃ D : ℝ → ℂ, Continuous D ∧ AbsolutelyContinuousOnInterval D 0 1 ∧
      f.first =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] D ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt D (f.second x) x :=
  exists_unitInterval_ac_of_weak_derivative f.first f.second
    ((Lp.memLp f.first).integrable (by norm_num)) ((Lp.memLp f.second).integrable (by norm_num)) f.weak_second

theorem WeakIntervalH2.continuous_representative_unique (f : WeakIntervalH2)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hfF : f.value =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] F)
    (hfG : f.value =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] G) : EqOn F G (Icc 0 1) := by
  have he := hfF.symm.trans hfG
  rw [restrict_Ioc_eq_restrict_Icc] at he
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ) ≠ 1) he hF.continuousOn hG.continuousOn

end NLS.Fourier
