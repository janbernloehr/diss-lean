import NLS.FunctionalAnalysis.IntervalH1Conjugation

/-! # Strict positivity of the physical unit-interval scalar mass -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.FunctionalAnalysis

theorem integral_curve_mul_conj_re_pos (y : Curve ℂ) (hy : y ≠ 0) :
    0 < (∫ s in (0 : ℝ)..1, extend y s*conj (extend y s)).re := by
  let m := ∫ s in (0 : ℝ)..1, extend y s*conj (extend y s)
  have hi : IntervalIntegrable (fun s : ℝ => extend y s*conj (extend y s)) volume 0 1 :=
    ((continuous_extend y).mul (Complex.continuous_conj.comp (continuous_extend y))).intervalIntegrable 0 1
  have hn : 0 ≤ m.re := by
    have he := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ s in (0 : ℝ)..1, (extend y s*conj (extend y s)).re) = m.re at he
    rw [← he]
    apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    intro s _
    simp only [mul_re,conj_re,conj_im]
    nlinarith [sq_nonneg (extend y s).re,sq_nonneg (extend y s).im]
  have hm : conj m = m := by
    dsimp only [m]
    rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [map_mul,conj_conj]
    ring
  have him : m.im = 0 := by
    have he := congrArg Complex.im hm
    simp only [conj_im] at he
    linarith
  apply lt_of_le_of_ne hn
  intro he
  have hz : m = 0 := Complex.ext he.symm him
  exact integral_curve_mul_conj_ne_zero y hy hz

end NLS.FunctionalAnalysis
