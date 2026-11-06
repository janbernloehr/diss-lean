import NLS.KdV.FreeEnergyAnnulusFrequencyBounds
import NLS.KdV.HillHminusOneUniformAnnularRoot
import NLS.ComplexAnalysis.AnalyticLinearSourcePullback

/-! # Uniform L2 separation on every full positive energy annulus -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillL2_all_annular_radicand_lower_bound :
    ∃ η b : ℝ, 0 < η ∧ 0 < b ∧ ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+, ∀ E : ℂ,
      (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ → ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ) →
        b ≤ ‖hillL2Radicand (Coeff.periodDouble u) E‖ := by
  have hr : 0 < 1/(6*Real.pi) := by positivity
  have hrpi : 1/(6*Real.pi) ≤ Real.pi/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 6*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨δ,b,hδ,hb,_,hroot⟩ := exists_hillHminus_uniform_annular_root_bound _ hr hrpi
  obtain ⟨η,hη,hsource⟩ := exists_common_ball_linear_preimage periodOneL2Inclusion δ 1 hδ
    (by norm_num) univ isOpen_univ (mem_univ _)
  refine ⟨η,b^2,hη,sq_pos_of_pos hb,?_⟩
  intro u hu k E hlo hhi
  obtain ⟨hz,_,_,hfar⟩ := hillFreeEnergyAnnulus_frequency_bounds k E hlo hhi
  have hh := hroot _ (hsource u hu).1 k (sqrt E) hz hfar
  have he := congrArg norm (hillHminusContinuedRoot_sq (E,periodOneL2Inclusion u)
    (by simpa only [sq_sqrt] using hh.1))
  rw [norm_pow,hillHminusRadicand_eq_hillL2] at he
  have hl : b ≤ ‖hillHminusContinuedRoot (E,periodOneL2Inclusion u)‖ := by
    simpa only [sq_sqrt] using hh.2
  rw [← he]
  nlinarith

end NLS.KdV
