import NLS.Fourier.MemLpBoundedLatticeFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Uniform L2 sampling over partial physical intervals

Measurable cutoffs contract the original coefficient norm, giving the same sampling bound over every partial interval.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Restricting an interval L2 density to any measurable set contracts
its actual Fourier coefficient norm. -/
theorem norm_unitIntervalMemLpCoefficients_indicator_le
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (S : Set ℝ) (hS : MeasurableSet S) :
    ‖unitIntervalMemLpCoefficients (S.indicator f) (hf.indicator hS)‖ ≤
      ‖unitIntervalMemLpCoefficients f hf‖ := by
  have hsq : ‖unitIntervalMemLpCoefficients (S.indicator f) (hf.indicator hS)‖^2 ≤
      ‖unitIntervalMemLpCoefficients f hf‖^2 := by
    rw [norm_sq_unitIntervalMemLpCoefficients,norm_sq_unitIntervalMemLpCoefficients]
    simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_ae ((hf.indicator hS).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    exact Filter.Eventually.of_forall (fun x => pow_le_pow_left₀ (norm_nonneg _)
      (norm_indicator_le_norm_self (s := S) (f := f) (a := x)) 2)
  nlinarith [norm_nonneg (unitIntervalMemLpCoefficients (S.indicator f) (hf.indicator hS)),
    norm_nonneg (unitIntervalMemLpCoefficients f hf)]

/-- Fourier integrals over every partial physical interval have a common
L2 sampling bound at arbitrary bounded complex lattice displacements.
The density need only be L2, so the endpoint cutoff may be discontinuous. -/
theorem exists_partial_interval_bounded_lattice_fourier_coefficients
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (δ : NLS.Coeff ⊤) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ a : NLS.Coeff 2,
      (∀ n, a n = ∫ x in (0:ℝ)..t, f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) ∧
      ‖a‖ ≤ Real.exp (2*‖δ‖)*‖unitIntervalMemLpCoefficients f hf‖ := by
  obtain ⟨a,ha,hn⟩ := exists_memLp_bounded_lattice_fourier_coefficients
    ((Iic t).indicator f) (hf.indicator measurableSet_Iic) δ
  refine ⟨a,?_,hn.trans (mul_le_mul_of_nonneg_left
    (norm_unitIntervalMemLpCoefficients_indicator_le f hf (Iic t) measurableSet_Iic) (Real.exp_pos _).le)⟩
  intro n
  rw [ha n]
  have he : (fun x : ℝ => (Iic t).indicator f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) =
      (Iic t).indicator (fun x => f x*exp (-2*I*((Real.pi:ℂ)*n+δ n)*x)) := by
    funext x
    by_cases hx : x ≤ t <;> simp [Set.indicator,hx]
  rw [he]
  exact intervalIntegral.integral_indicator ht

end NLS.Fourier
