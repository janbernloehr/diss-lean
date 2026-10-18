import NLS.ZakharovShabat.NLSWKBAntiErrorDecomposition
import NLS.ZakharovShabat.SobolevWKBInitialDecay

/-! # Extra decay of the diagonal anti-discriminant contribution

The actual diagonal remainders occur with small initial-coordinate factors and therefore gain one additional inverse-frequency order.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal contribution to the anti-discriminant error gains an
extra inverse-frequency factor. Thus only the two off-diagonal remainders
require sharper sampling estimates. -/
theorem exists_uniform_nlsWKB_diagonal_remainder_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBInitialUpper a b N z*(nlsWKBFirstRemainder a b ha.continuous hb.continuous N z t).1+
          nlsWKBInitialLower a b N z*(nlsWKBSecondRemainder a b ha.continuous hb.continuous N z t).2‖ ≤
            C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s N hNs R hR
  obtain ⟨D,hD,hfirst⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s N hs hNs R hR H
  obtain ⟨E,hE,hsecond⟩ := exists_uniform_nlsWKB_second_leading_oscillatory_error_bound s N hs hNs R hR H
  refine ⟨B*(D+E),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  obtain ⟨hp,hq⟩ := hinit ab hab a b ha hb hpa hpb hca hcb z hz
  have h₁ := hfirst ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  have h₂ := hsecond ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  change ‖nlsWKBFirstRemainder a b ha.continuous hb.continuous N z t‖ ≤ _ at h₁
  change ‖nlsWKBSecondRemainder a b ha.continuous hb.continuous N z t‖ ≤ _ at h₂
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hleft := mul_le_mul hq ((norm_fst_le _).trans h₁) (norm_nonneg _) (by positivity : 0 ≤ B*‖(2*I*z)⁻¹‖)
  have hright := mul_le_mul hp ((norm_snd_le _).trans h₂) (norm_nonneg _) (by positivity : 0 ≤ B*‖(2*I*z)⁻¹‖)
  apply (add_le_add hleft hright).trans_eq
  rw [show N+2=(N+1)+1 by omega,pow_succ]
  ring

end NLS.ZakharovShabat
