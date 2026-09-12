import NLS.Fourier.FoldedInterval
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Parseval identities in the interval normalization

These identities connect the physical Fourier integrals to square sums. They
supply the Hilbert-space estimate needed before treating other exponents.
-/

noncomputable section
open Complex MeasureTheory Set
namespace NLS.Fourier

/-- Continuous input is square integrable on a bounded interval. -/
theorem memLp_two_interval {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) (hab : a ≤ b) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
    ((hf.norm.pow 2).intervalIntegrable a b)

/-- The repository's normalized coefficient is mathlib's interval coefficient. -/
theorem periodTwoCoefficient_eq_fourierCoeffOn (f : ℝ → ℂ) (n : ℤ) :
    periodTwoCoefficient f n = fourierCoeffOn (by norm_num : (0 : ℝ) < 2) f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_ofNat,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  unfold periodTwoCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have he : Complex.exp (2 * Real.pi * I * (-n : ℤ) * x / 2) = wave (-n) x := by
    unfold wave
    congr 1
    ring
  dsimp only
  rw [he]
  ring

/-- Period-one coefficients use twice the half-interval normalization. -/
theorem fourierCoeffOn_one (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n =
      2 * halfCoefficient f (2 * n) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, sub_zero, Complex.ofReal_one, div_one, one_smul]
  have he (x : ℝ) : Complex.exp (2 * Real.pi * I * (-n : ℤ) * x) = wave (-(2 * n)) x := by
    unfold wave
    push_cast
    congr 1
    ring
  simp only [he, smul_eq_mul, halfCoefficient]
  rw [show (fun x : ℝ => wave (-(2 * n)) x * f x) =
    (fun x => f x * wave (-(2 * n)) x) by funext x; ring]
  ring

/-- Parseval for the normalized period-two coefficients. -/
theorem hasSum_sq_periodTwoCoefficient {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    HasSum (fun n => ‖periodTwoCoefficient f n‖ ^ 2)
      ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, ‖f x‖ ^ 2) := by
  simpa only [periodTwoCoefficient_eq_fourierCoeffOn, sub_zero, smul_eq_mul, one_div] using
    hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 2) hf

/-- The energy of a finite period-one Fourier polynomial is its coefficient square sum. -/
theorem integral_sq_polynomial (a : ℤ →₀ ℂ) :
    (∫ x in (0 : ℝ)..1, ‖polynomial a x‖ ^ 2) = ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
    (memLp_two_interval (continuous_polynomial a) 0 1 (by norm_num))
  have hc (n : ℤ) : fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (polynomial a) n = a n := by
    rw [fourierCoeffOn_one, halfCoefficient_polynomial_even]
    ring
  simp only [hc, sub_zero, inv_one, one_smul] at h
  rw [← h.tsum_eq]
  exact tsum_eq_sum fun n hn => by simp [Finsupp.notMem_support_iff.mp hn]

/-- A reflected block remains square integrable even if the join has a jump. -/
theorem memLp_two_folded (ε : ℂ) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    MemLp (folded ε f g) 2 (volume.restrict (Ioc 0 2)) := by
  classical
  have hg' : Continuous (fun x : ℝ => ε * g (2 - x)) := by fun_prop
  exact MemLp.piecewise measurableSet_Iic
    ((memLp_two_interval hf 0 2 (by norm_num)).restrict _)
    ((memLp_two_interval hg' 0 2 (by norm_num)).restrict _)

/-- Reflection preserves the second half's energy, and the two halves add. -/
theorem integral_sq_folded (ε : ℂ) (hε : ‖ε‖ = 1) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x in (0 : ℝ)..2, ‖folded ε f g x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2 := by
  have h01 : EqOn (fun x => ‖folded ε f g x‖ ^ 2) (fun x => ‖f x‖ ^ 2) (uIoc 0 1) := by
    intro x hx
    have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
    simp [folded, hx']
  have h12 : EqOn (fun x => ‖folded ε f g x‖ ^ 2) (fun x => ‖g (2 - x)‖ ^ 2) (uIoc 1 2) := by
    intro x hx
    have hx' : 1 < x := (show x ∈ Ioc (1 : ℝ) 2 from by simpa using hx).1
    simp [folded, not_le.mpr hx', hε]
  have hi01 : IntervalIntegrable (fun x => ‖folded ε f g x‖ ^ 2) volume 0 1 :=
    ((hf.norm.pow 2).intervalIntegrable 0 1).congr h01.symm
  have hg' : Continuous (fun x : ℝ => ‖g (2 - x)‖ ^ 2) := by fun_prop
  have hi12 : IntervalIntegrable (fun x => ‖folded ε f g x‖ ^ 2) volume 1 2 :=
    (hg'.intervalIntegrable 1 2).congr h12.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi12,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h01),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h12),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => ‖g x‖ ^ 2) 2]
  norm_num

end NLS.Fourier
