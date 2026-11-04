import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The quadratic spectral map converts a frequency gap and terminal
midpoint displacement into the corresponding energy weights. No gap,
action or terminal sheet is divided by, so collapse is included. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_frequency_weight_le_quadratic_energy_weight (μ τ γ : ℂ) (K G : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hτ : ‖τ‖ ≤ K*‖μ+τ‖) (hγ : ‖γ‖ ≤ G*‖τ‖) :
    ‖τ‖*(‖γ‖+‖μ-τ‖) ≤ (1+K+K*G)*
      (‖2*τ*γ‖+‖μ^2-τ^2-γ^2/4‖) := by
  let E := ‖μ^2-τ^2-γ^2/4‖
  let H := ‖2*τ*γ‖
  let D := 1+K+K*G
  have hE : 0 ≤ E := norm_nonneg _
  have hH : 0 ≤ H := norm_nonneg _
  have hprod : ‖μ-τ‖*‖μ+τ‖ ≤ E+‖γ‖^2/4 := by
    rw [← norm_mul,show (μ-τ)*(μ+τ) = (μ^2-τ^2-γ^2/4)+γ^2/4 by ring]
    exact (norm_add_le _ _).trans_eq (by rw [norm_div,norm_pow,Complex.norm_ofNat])
  have hγ2 : ‖γ‖^2 ≤ G*‖τ‖*‖γ‖ := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hγ (norm_nonneg γ)
  have hγ4 : ‖γ‖^2/4 ≤ G*‖τ‖*‖γ‖ := by
    nlinarith [sq_nonneg ‖γ‖]
  have htd : ‖τ‖*‖μ-τ‖ ≤ K*E+K*G*‖τ‖*‖γ‖ := by
    calc
      _ ≤ K*(‖μ-τ‖*‖μ+τ‖) := by
        simpa only [mul_assoc,mul_comm ‖μ-τ‖] using
          mul_le_mul_of_nonneg_right hτ (norm_nonneg (μ-τ))
      _ ≤ K*(E+‖γ‖^2/4) := mul_le_mul_of_nonneg_left hprod hK
      _ ≤ K*(E+G*‖τ‖*‖γ‖) := mul_le_mul_of_nonneg_left (add_le_add (le_refl E) hγ4) hK
      _ = _ := by ring
  have htg : ‖τ‖*‖γ‖ ≤ H := by
    dsimp only [H]
    simp only [norm_mul,Complex.norm_ofNat]
    nlinarith [mul_nonneg (norm_nonneg τ) (norm_nonneg γ)]
  have hDleft : 1+K*G ≤ D := by dsimp only [D]; linarith
  have hDright : K ≤ D := by dsimp only [D]; nlinarith
  calc
    _ ≤ (1+K*G)*(‖τ‖*‖γ‖)+K*E := by nlinarith [htd]
    _ ≤ (1+K*G)*H+K*E := add_le_add
      (mul_le_mul_of_nonneg_left htg (show 0 ≤ 1+K*G from by positivity)) (le_refl (K*E))
    _ ≤ D*H+D*E := add_le_add
      (mul_le_mul_of_nonneg_right hDleft hH) (mul_le_mul_of_nonneg_right hDright hE)
    _ = _ := by dsimp only [D,H,E]; ring

end NLS.ComplexAnalysis
