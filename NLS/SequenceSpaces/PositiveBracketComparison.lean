import NLS.SequenceSpaces.PeriodOneMassResolvent

/-! The literal positive-index weight1/n is bounded by twice the
inverse bracket1/(1+n), uniformly down to the first index. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

theorem memlp_div_pnat_of_memlp_inverseBracket {p : ℝ≥0∞} (f : ℕ+ → ℂ)
    (h : Memℓp (fun n : ℕ+ => inverseBracketCoefficients (n:ℕ)*f n) p) :
    Memℓp (fun n : ℕ+ => f n/(n:ℕ)) p := by
  apply (h.norm.const_mul (2:ℝ)).mono
  intro n
  let k : ℝ := (n:ℕ)
  have hk : (1:ℝ) ≤ k := by dsimp [k]; exact_mod_cast n.property
  have hkpos : 0 < k := by linarith
  have hB : ‖inverseBracketCoefficients (n:ℕ)‖ = (1+k)⁻¹ := by
    have hb := norm_inverseBracketCoefficients_apply (n:ℕ)
    simp only [Int.cast_natCast] at hb
    rw [abs_of_nonneg (show (0:ℝ) ≤ ((n:ℕ):ℝ) from Nat.cast_nonneg _)] at hb
    exact hb
  have hineq : ‖f n‖/k ≤ (2*‖f n‖)/(1+k) := by
    apply (div_le_div_iff₀ hkpos (by positivity : 0 < 1+k)).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hk) (norm_nonneg (f n))
    nlinarith
  change ‖f n/(n:ℕ)‖ ≤ 2*‖inverseBracketCoefficients (n:ℕ)*f n‖
  calc
    ‖f n/(n:ℕ)‖ = ‖f n‖/k := by rw [norm_div,Complex.norm_natCast]
    _ ≤ (2*‖f n‖)/(1+k) := hineq
    _ = 2*‖inverseBracketCoefficients (n:ℕ)*f n‖ := by rw [norm_mul,hB]; ring

end NLS
