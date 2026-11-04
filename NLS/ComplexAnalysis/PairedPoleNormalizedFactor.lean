import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! A paired-pole factor normalized at a midpoint. Separate distances
to both poles control it without introducing an index-dependent scale. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def pairedPoleNormalizedFactor (β τ : ℂ) (Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((β-τ)/(β-z))*((β+τ)/(β+z))*Q z

theorem pairedPoleNormalizedFactor_eq_quadratic (β τ : ℂ) (Q : ℂ → ℂ) (z : ℂ) :
    pairedPoleNormalizedFactor β τ Q z = ((β^2-τ^2)/(β^2-z^2))*Q z := by
  unfold pairedPoleNormalizedFactor
  rw [div_mul_div_comm]
  congr 2 <;> ring

theorem pairedPoleNormalizedFactor_midpoint (β τ : ℂ) (Q : ℂ → ℂ)
    (hminus : β-τ ≠ 0) (hplus : β+τ ≠ 0) :
    pairedPoleNormalizedFactor β τ Q τ = Q τ := by
  simp only [pairedPoleNormalizedFactor,div_self hminus,div_self hplus,one_mul]

theorem analyticOnNhd_pairedPoleNormalizedFactor (β τ : ℂ) (Q : ℂ → ℂ) (S : Set ℂ)
    (hQ : AnalyticOnNhd ℂ Q S)
    (hminus : ∀ z ∈ S, β-z ≠ 0) (hplus : ∀ z ∈ S, β+z ≠ 0) :
    AnalyticOnNhd ℂ (pairedPoleNormalizedFactor β τ Q) S := by
  intro z hz
  exact ((analyticAt_const.div (analyticAt_const.sub analyticAt_id) (hminus z hz)).mul
    (analyticAt_const.div (analyticAt_const.add analyticAt_id) (hplus z hz))).mul (hQ z hz)

theorem norm_ratio_le_of_midpoint_distance (u v : ℂ) (A d : ℝ)
    (hd : 0 < d) (hA : 0 ≤ A) (hden : d ≤ ‖v‖) (hsub : ‖u-v‖ ≤ A) :
    ‖u/v‖ ≤ 1+A/d := by
  have hv : 0 < ‖v‖ := hd.trans_le hden
  have hu : ‖u‖ ≤ ‖v‖+A := by
    have h := norm_le_norm_sub_add u v
    linarith
  rw [norm_div]
  calc
    _ ≤ (‖v‖+A)/‖v‖ := div_le_div_of_nonneg_right hu hv.le
    _ = 1+A/‖v‖ := by field_simp
    _ ≤ 1+A/d := add_le_add le_rfl (div_le_div_of_nonneg_left hA hd hden)

theorem norm_pairedPoleNormalizedFactor_le (β τ : ℂ) (Q : ℂ → ℂ) (z : ℂ)
    (A d e M : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (he : 0 < e) (_hM : 0 ≤ M)
    (hminus : d ≤ ‖β-z‖) (hplus : e ≤ ‖β+z‖)
    (hmid : ‖z-τ‖ ≤ A) (hQ : ‖Q z‖ ≤ M) :
    ‖pairedPoleNormalizedFactor β τ Q z‖ ≤ (1+A/d)*(1+A/e)*M := by
  have hm : ‖(β-τ)/(β-z)‖ ≤ 1+A/d :=
    norm_ratio_le_of_midpoint_distance _ _ A d hd hA hminus (by
      rw [show (β-τ)-(β-z) = z-τ by ring]
      exact hmid)
  have hp : ‖(β+τ)/(β+z)‖ ≤ 1+A/e :=
    norm_ratio_le_of_midpoint_distance _ _ A e he hA hplus (by
      have hh : (β+τ)-(β+z) = -(z-τ) := by ring
      rw [hh,norm_neg]
      exact hmid)
  simp only [pairedPoleNormalizedFactor,norm_mul]
  exact mul_le_mul (mul_le_mul hm hp (norm_nonneg _) (by positivity)) hQ (norm_nonneg _) (by positivity)

end NLS.ComplexAnalysis
